;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 9th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
;; To be compatible with Arithmetic books
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir
              :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)

(include-book "../utils/pseudo-term")
(include-book "../utils/fresh-vars")
(include-book "hint-interface")
(include-book "evaluator")
(include-book "basics")

(set-state-ok t)

(defalist sym-int-alist
  :key-type symbolp
  :val-type integerp
  :true-listp t
  :pred sym-int-alistp)

(defthm assoc-equal-of-sym-int-alist
  (implies (and (sym-int-alistp y)
                (assoc-equal x y))
           (and (consp (assoc-equal x y))
                (integerp (cdr (assoc-equal x y))))))

(defalist pseudo-term-sym-alist
  :key-type pseudo-termp
  :val-type symbolp
  :true-listp t
  :pred pseudo-term-sym-alistp)

(defthm assoc-equal-of-pseudo-term-sym-alist
  (implies (and (pseudo-term-sym-alistp y)
                (assoc-equal x y))
           (and (consp (assoc-equal x y))
                (symbolp (cdr (assoc-equal x y))))))

(defthm crock
  (implies (symbolp x) (pseudo-termp x)))

(define new-vars-for-actuals ((actuals pseudo-term-listp)
                              (alst pseudo-term-sym-alistp)
                              (names symbol-listp))
  :measure (len (pseudo-term-list-fix actuals))
  :returns (mv (vars pseudo-term-listp)
               (new-alst pseudo-term-sym-alistp)
               (new-names symbol-listp))
  (b* ((actuals (pseudo-term-list-fix actuals))
       (alst (pseudo-term-sym-alist-fix alst))
       (names (symbol-list-fix names))
       ((unless (consp actuals))
        (mv nil alst names))
       ((cons ac-hd ac-tl) actuals)
       ((mv new-ac-tl alst-1 names-1)
        (new-vars-for-actuals ac-tl alst names))
       ((if (or (acl2::variablep ac-hd)
                (acl2::fquotep ac-hd)))
        (mv (cons ac-hd new-ac-tl) alst-1 names-1))
       (new-var (new-fresh-var names)))
    (mv (cons new-var new-ac-tl)
        (acons ac-hd new-var alst-1)
        (cons new-var names-1))))

(encapsulate ()
  (local
   (in-theory (disable assoc-equal lambda-of-pseudo-lambdap
                       symbol-listp)))

(define get-formals-body ((fn symbolp)
                          state)
  :returns (mv (formals symbol-listp)
               (body pseudo-termp))
  (b* ((fn (symbol-fix fn))
       (formula (acl2::meta-extract-formula-w fn (w state)))
       ((unless (pseudo-termp formula))
        (prog2$
         (er hard? 'expand-cp=>get-formals-body
             "Formula got by meta-extract ~p0 is not a pseudo-termp." fn)
         (mv nil nil)))
       ((mv ok lhs rhs)
        (case-match formula
          (('equal lhs rhs)
           (mv t lhs rhs))
          (& (mv nil nil nil))))
       ((unless (and ok (consp lhs) (symbol-listp (cdr lhs))))
        (prog2$ (er hard? 'expand-cp=>get-formals-body
                    "Malformed function definition formula: ~p0~%" formula)
                (mv nil nil))))
    (mv (cdr lhs) rhs)))
)

(define update-fn-lvls ((fn symbolp)
                        (fn-info maybe-smt-function-p)
                        (fn-lvls sym-int-alistp))
  :returns (new-lvls
            sym-int-alistp
            :hints (("Goal"
                     :in-theory (disable assoc-equal-of-sym-int-alist)
                     :use ((:instance assoc-equal-of-sym-int-alist
                                      (x (symbol-fix fn))
                                      (y (sym-int-alist-fix fn-lvls)))))))
  (b* ((fn (symbol-fix fn))
       (fn-info (maybe-smt-function-fix fn-info))
       (fn-lvls (sym-int-alist-fix fn-lvls))
       (lvl (assoc-equal fn fn-lvls))
       ((if lvl) (acons fn (1- (cdr lvl)) fn-lvls))
       ((if fn-info)
        (acons fn (1- (smt-function->expansion-depth fn-info)) fn-lvls)))
    (acons fn 0 fn-lvls)))

(encapsulate ()
  (local
   (in-theory (disable symbolp-of-fn-call-of-pseudo-termp
                       pseudo-term-listp-of-symbol-listp
                       acl2::symbol-listp-when-not-consp
                       acl2::pseudo-termp-opener
                       pairlis$
                       acl2::pseudo-term-listp-cdr
                       pseudo-term-listp-of-cdr-pseudo-termp-if
                       default-car
                       acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp
                       acl2::true-listp-of-car-when-true-list-listp
                       true-list-listp
                       (:executable-counterpart smt-basics))))

(defines expand-term
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :hints (("Goal"
           :in-theory (disable pseudo-termp
                               pseudo-term-listp)))

  (define expand-lambda ((term pseudo-termp)
                         (hints smtlink-hint-p)
                         (fn-lvls sym-int-alistp)
                         (alst pseudo-term-sym-alistp)
                         (names symbol-listp)
                         (clock natp)
                         state)
    :guard (and (consp term)
                (pseudo-lambdap (car term))
                (not (zp clock)))
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix term))
                   1)
    :returns (mv (new-term pseudo-termp)
                 (new-alst pseudo-term-sym-alistp)
                 (new-names symbol-listp))
    (b* ((term (pseudo-term-fix term))
         (alst (pseudo-term-sym-alist-fix alst))
         (clock (nfix clock))
         (names (symbol-list-fix names))
         ((unless (mbt (and (consp term)
                            (pseudo-lambdap (car term))
                            (not (zp clock)))))
          (mv term alst names))
         ((cons fncall actuals) term)
         ((mv new-actuals alst-1 names-1)
          (expand-term-list actuals hints fn-lvls alst names clock state))
         ;; if a new-actual is a variable, then don't generate a new one
         ((mv actual-vars alst-2 names-2)
          (new-vars-for-actuals new-actuals alst-1 names-1))
         (formals (lambda-formals fncall))
         (body (lambda-body fncall))
         (substed-body
          (acl2::substitute-into-term body (pairlis$ formals actual-vars)))
         ((mv new-body alst-3 names-3)
          (expand-term substed-body hints fn-lvls alst-2
                       names-2 (1- clock) state))
         ((if (acl2::variablep new-body)) (mv new-body alst-3 names-3))
         (body-var (new-fresh-var names-3)))
      (mv body-var
          (acons new-body body-var alst-3)
          (cons body-var names-3))))

  (define expand-fncall ((term pseudo-termp)
                         (hints smtlink-hint-p)
                         (fn-lvls sym-int-alistp)
                         (alst pseudo-term-sym-alistp)
                         (names symbol-listp)
                         (clock natp)
                         state)
    :guard (and (consp term)
                (symbolp (car term))
                (not (equal (car term) 'quote))
                (not (zp clock)))
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix term))
                   1)
    :returns (mv (new-term pseudo-termp)
                 (new-alst pseudo-term-sym-alistp)
                 (new-names symbol-listp))
    (b* ((term (pseudo-term-fix term))
         (hints (smtlink-hint-fix hints))
         ((smtlink-hint h) hints)
         (alst (pseudo-term-sym-alist-fix alst))
         (clock (nfix clock))
         (names (symbol-list-fix names))
         ((unless (mbt (and (consp term)
                            (symbolp (car term))
                            (not (equal (car term) 'quote))
                            (not (zp clock)))))
          (mv term alst names))
         ((cons fncall actuals) term)
         ((mv new-actuals alst-1 names-1)
          (expand-term-list actuals hints fn-lvls alst names clock state))
         ((mv actual-vars alst-2 names-2)
          (new-vars-for-actuals new-actuals alst-1 names-1))
         (basic-function (member-equal fncall (SMT-basics)))
         (flex? (fncall-of-fixtypes fncall h.types-info))
         (lvl (assoc-equal fncall fn-lvls))
         (user-defined (is-function fncall h.functions))
         ;; There are three cases:
         ;; 1. fn is a basic function (including fty functions), just return;
         ;; 2. fn exists in fn-lvls, its level reaches 0, then just leave it
         ;; there;
         ;; 3. fn exists in fn-lvls, its level is not 0, then expand for 1;
         ;; 4. the user wants to expand the function for 0 levels;
         ;; 5. otherwise, expand for 1 level
         ((if (or basic-function flex?
                  (and lvl (<= (cdr lvl) 0))
                  (and (not lvl)
                       user-defined
                       (<= (smt-function->expansion-depth user-defined) 0))))
          (mv `(,fncall ,@new-actuals) alst-2 names-2))
         ((mv formals body) (get-formals-body fncall state))
         (substed-body
          (acl2::substitute-into-term body (pairlis$ formals actual-vars)))
         (new-lvls (update-fn-lvls fncall user-defined fn-lvls))
         ((mv new-body alst-3 names-3)
          (expand-term substed-body hints new-lvls alst-2
                       names-2 (1- clock) state))
         ((if (acl2::variablep new-body)) (mv new-body alst-3 names-3))
         (body-var (new-fresh-var names-3)))
      (mv body-var
          (acons new-body body-var alst-3)
          (cons body-var names-3)))
    )

  (define expand-term ((term pseudo-termp)
                       (hints smtlink-hint-p)
                       (fn-lvls sym-int-alistp)
                       (alst pseudo-term-sym-alistp)
                       (names symbol-listp)
                       (clock natp)
                       state)
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix term))
                   2)
    :returns (mv (new-term pseudo-termp)
                 (new-alst pseudo-term-sym-alistp)
                 (new-names symbol-listp))
    (b* ((term (pseudo-term-fix term))
         (alst (pseudo-term-sym-alist-fix alst))
         (clock (nfix clock))
         (names (symbol-list-fix names))
         ((if (zp clock)) (mv term alst names))
         (exist? (assoc-equal term alst))
         ((if exist?) (mv (cdr exist?) alst names))
         ((if (acl2::variablep term)) (mv term alst names))
         ((if (acl2::quotep term)) (mv term alst names))
         ((cons fn &) term)
         ((if (pseudo-lambdap fn))
          (expand-lambda term hints fn-lvls alst names clock state)))
      (expand-fncall term hints fn-lvls alst names clock state)))

  (define expand-term-list ((term-lst pseudo-term-listp)
                            (hints smtlink-hint-p)
                            (fn-lvls sym-int-alistp)
                            (alst pseudo-term-sym-alistp)
                            (names symbol-listp)
                            (clock natp)
                            state)
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-list-fix term-lst))
                   0)
    :returns (mv (new-term-lst pseudo-term-listp)
                 (new-alst pseudo-term-sym-alistp)
                 (new-names symbol-listp))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (alst (pseudo-term-sym-alist-fix alst))
         (clock (nfix clock))
         (names (symbol-list-fix names))
         ((unless (consp term-lst)) (mv nil alst names))
         ((cons term-hd term-tl) term-lst)
         ((mv new-hd alst-1 names-1)
          (expand-term term-hd hints fn-lvls alst names clock state))
         ((mv new-tl alst-2 names-2)
          (expand-term-list term-tl hints fn-lvls alst-1 names-1 clock state)))
      (mv (cons new-hd new-tl) alst-2 names-2)))
  )
)

(defthm crock2
  (alistp (pairlis$ x y)))

(verify-guards expand-term
  :hints (("Goal"
           :in-theory (e/d ()
                           ((:executable-counterpart smt-basics)
                            pseudo-term-listp-of-symbol-listp
                            member-equal
                            symbolp-of-car-when-member-equal-of-sym-int-alistp
                            acl2::symbol-listp-when-not-consp
                            symbolp-of-fn-call-of-pseudo-termp
                            pseudo-term-listp-of-cdr-pseudo-termp-if
                            symbolp-of-caar-when-sym-int-alistp
                            type-decl-p-definition
                            acl2::pseudo-term-listp-cdr
                            assoc-equal-of-sym-int-alist))
           :use ((:instance assoc-equal-of-sym-int-alist
                            (x (car term))
                            (y fn-lvls))))))

(define generate-equalities ((alst pseudo-term-sym-alistp))
  :returns (res pseudo-termp)
  :measure (len alst)
  :hints (("Goal"
           :in-theory (enable pseudo-term-sym-alist-fix)))
  (b* ((alst (pseudo-term-sym-alist-fix alst))
       ((unless (consp alst)) ''t)
       ((cons alst-hd alst-tl) alst)
       ((cons term var) alst-hd))
    `(if (equal ,term ,var)
         ,(generate-equalities alst-tl)
       'nil)))

(defmacro correct-expand-term<-list> (fn term/lst)
  `(b* (((mv new new-alst &)
         (,fn ,term/lst hints fn-lvls alst names clock state)))
     `(implies (generate-equalities ,new-alst)
               (equal ,new ,,term/lst))))

stop
(defthm-expand-term-flag
  (defthm correctness-of-expand-lambda
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a))
             (ev-smtcp
              (correct-expand-term<-list> expand-lambda term)
              a))
    :flag expand-lambda
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (generate-equalities) ())
                   :expand ((expand-lambda term hints fn-lvls alst
                                           names clock state))))))
  (defthm correctness-of-expand-fncall
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a))
             (ev-smtcp
              (correct-expand-term<-list> expand-fncall term)
              a))
    :flag expand-fncall
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (generate-equalities) ())
                   :expand ((expand-fncall term hints fn-lvls alst
                                           names clock state))))))
  (defthm correctness-of-expand-term
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a))
             (ev-smtcp
              (correct-expand-term<-list> expand-term term)
              a))
    :flag expand-term
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (generate-equalities) ())
                   :expand ((expand-term term hints fn-lvls alst
                                         names clock state))))))
  (defthm correctness-of-expand-term-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-term-listp term-lst)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a))
             (ev-smtcp
              (correct-expand-term<-list> expand-term-list term-lst)
              a))
    :flag expand-term-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (generate-equalities) ())
                   :expand ((expand-term-list term-lst hints fn-lvls alst
                                              names clock state)
                            (expand-term-list nil hints fn-lvls alst
                                              names clock state))))))
  :hints(("Goal"
          :in-theory (disable ))))
