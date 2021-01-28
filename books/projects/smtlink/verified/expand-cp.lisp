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

(define pseudo-lambda/fnp (x)
  :returns (ok booleanp)
  (or (and (symbolp x)
           (not (equal x 'quote)))
      (pseudo-lambdap x))
  ///
  (more-returns
   (ok (implies (and ok (not (pseudo-lambdap x)))
                (symbolp x))
       :name symbolp-of-pseudo-lambda/fnp)))

(define pseudo-lambda/fn-fix ((x pseudo-lambda/fnp))
  (mbe :logic (if (pseudo-lambda/fnp x) x nil)
       :exec x))

(encapsulate ()
  (local
   (in-theory (enable pseudo-lambda/fn-fix)))

(deffixtype pseudo-lambda/fn
  :pred pseudo-lambda/fnp
  :fix pseudo-lambda/fn-fix
  :equiv pseudo-lambda/fn-equiv
  :define t)

(defthm pseudo-lambda/fn-of-pseudo-lambda/fn-fix
  (pseudo-lambda/fnp (pseudo-lambda/fn-fix x)))

(defthm equal-of-pseudo-lambda/fnp
  (implies (pseudo-lambda/fnp x)
           (equal (pseudo-lambda/fn-fix x) x)))
)

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

(local
 (defthm crock1
   (implies (symbolp x) (pseudo-termp x)))
)

(define dont-generate-freshvar ((term pseudo-termp))
  :returns (ok booleanp)
  (b* ((term (pseudo-term-fix term)))
    (or (acl2::variablep term)
        (acl2::fquotep term)))
  ///
  (more-returns
   (ok (implies (and ok (pseudo-termp term))
                (or (acl2::variablep term)
                    (acl2::fquotep term)))
       :name implies-of-dont-generate-freshvar)))

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
       ((if (dont-generate-freshvar ac-hd))
        (mv (cons ac-hd new-ac-tl) alst-1 names-1))
       (new-var (new-fresh-var names)))
    (mv (cons new-var new-ac-tl)
        (acons ac-hd new-var alst-1)
        (cons new-var names-1)))
  ///
  (more-returns
   (vars (implies (pseudo-term-listp actuals)
                  (equal (len vars) (len actuals)))
         :name len-of-new-vars-for-actuals)))

(encapsulate ()
  (local
   (in-theory (e/d (pairlis$)
                   (assoc-equal lambda-of-pseudo-lambdap
                                symbol-listp))))

  (local
   (defthm crock
     (alistp (pairlis$ x y))))

  (define function-substitution ((term pseudo-termp)
                               state)
  :guard (and (consp term)
              (pseudo-lambda/fnp (car term)))
  :returns (mv (ok booleanp)
               (substed pseudo-termp))
  (b* ((term (pseudo-term-fix term))
       ((unless (mbt (and (consp term)
                          (pseudo-lambda/fnp (car term)))))
        (mv nil ''t))
       ((cons fn actuals) term)
       ((if (pseudo-lambdap fn))
        (mv t (acl2::substitute-into-term
               (lambda-body fn)
               (pairlis$ (lambda-formals fn) actuals))))
       (formula (acl2::meta-extract-formula-w fn (w state)))
       ((unless (pseudo-termp formula))
        (prog2$
         (er hard? 'expand-cp=>function-substitution
             "Formula got by meta-extract ~p0 is not a pseudo-termp.~%" fn)
         (mv nil term)))
       ((mv ok lhs rhs)
        (case-match formula
          (('equal lhs rhs)
           (mv t lhs rhs))
          (& (mv nil nil nil))))
       ((unless (and ok (pseudo-termp lhs)))
        (prog2$ (er hard? 'expand-cp=>function-substitution
                    "Formula got by meta-extract ~p0 is not an equality.~%" fn)
                (mv nil term)))
       ((mv match-ok subst)
        (acl2::simple-one-way-unify lhs term nil))
       ((unless match-ok)
        (prog2$
         (er hard? 'expand-cp=>function-substitution "simple-one-way-unify failed.~%")
         (mv nil term)))
       (substed-body (acl2::substitute-into-term rhs subst)))
    (mv t substed-body)))
)

(defthm correctness-of-function-substitution
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp term)
                (consp term)
                (pseudo-lambda/fnp (car term))
                (alistp a)
                (mv-nth 0 (function-substitution term state)))
           (equal (ev-smtcp (mv-nth 1 (function-substitution term state)) a)
                  (ev-smtcp term a)))
  :hints (("Goal"
           :in-theory (e/d (function-substitution)
                           (w pseudo-termp
                              ev-smtcp-meta-extract-formula))
           :use ((:instance ev-smtcp-meta-extract-formula
                            (name (car term))
                            (st state)
                            (a (ev-smtcp-alist
                                (mv-nth 1
                                        (acl2::simple-one-way-unify
                                         (cadr (meta-extract-formula (car term) state))
                                         term nil))
                                a)))))))

(define update-fn-lvls ((fn pseudo-lambda/fnp)
                        (hints smtlink-hint-p)
                        (fn-lvls sym-int-alistp))
  :returns (new-lvls
            sym-int-alistp
            :hints (("Goal"
                     :in-theory (disable assoc-equal-of-sym-int-alist)
                     :use ((:instance assoc-equal-of-sym-int-alist
                                      (x (pseudo-lambda/fn-fix fn))
                                      (y (sym-int-alist-fix fn-lvls)))))))
  (b* ((fn (pseudo-lambda/fn-fix fn))
       (hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       (fn-lvls (sym-int-alist-fix fn-lvls))
       ((if (pseudo-lambdap fn)) fn-lvls)
       (lvl (assoc-equal fn fn-lvls))
       ((if lvl) (acons fn (1- (cdr lvl)) fn-lvls))
       (fn-hint (is-function fn h.functions))
       ((if fn-hint)
        (acons fn (1- (smt-function->expansion-depth fn-hint)) fn-lvls)))
    (acons fn 0 fn-lvls)))

(define dont-expand ((fn pseudo-lambda/fnp)
                     (hints smtlink-hint-p)
                     (fn-lvls sym-int-alistp))
  :returns (ok booleanp)
  (b* ((fn (pseudo-lambda/fn-fix fn))
       ((if (pseudo-lambdap fn)) nil)
       (fn-lvls (sym-int-alist-fix fn-lvls))
       (hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       (basic? (member-equal fn (SMT-basics)))
       (fty? (fncall-of-fixtypes fn h.types-info))
       (lvl (assoc-equal fn fn-lvls))
       (user-hint (is-function fn h.functions)))
    (or (not (equal basic? nil))
        fty?
        (and lvl (<= (cdr lvl) 0))
        (and (not lvl)
             user-hint
             (<= (smt-function->expansion-depth user-hint) 0))))
  ///
  (more-returns
   (ok (implies (and (pseudo-lambda/fnp fn) ok)
                (symbolp fn))
       :name implies-of-dont-expand))

  (defthm not-symbolp-dont-expand
    (implies (and (pseudo-lambda/fnp x)
                  (not (symbolp x)))
             (null (dont-expand x hints fn-lvls)))
    :hints (("Goal"
             :in-theory (enable pseudo-lambda/fnp)))))

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
                       true-list-listp)))

(defines expand-term
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :hints (("Goal"
           :in-theory (disable pseudo-termp
                               pseudo-term-listp)))

  (define expand-fncall/lambda ((term pseudo-termp)
                                (hints smtlink-hint-p)
                                (fn-lvls sym-int-alistp)
                                (alst pseudo-term-sym-alistp)
                                (names symbol-listp)
                                (clock natp)
                                state)
    :guard (and (not (zp clock)) (consp term)
                (pseudo-lambda/fnp (car term)))
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
         ((unless (mbt (and (not (zp clock)) (consp term)
                            (pseudo-lambda/fnp (car term)))))
          (mv term alst names))
         ((cons fn actuals) term)
         ((mv new-actuals alst-1 names-1)
          (expand-term-list actuals hints fn-lvls alst names clock state))
         ((mv actual-vars alst-2 names-2)
          (new-vars-for-actuals new-actuals alst-1 names-1))
         ((if (dont-expand fn h fn-lvls))
          (mv `(,fn ,@actual-vars) alst-2 names-2))
         ((mv ok substed-body) (function-substitution `(,fn ,@actual-vars) state))
         ((unless ok) (mv term alst names))
         (new-lvls (update-fn-lvls fn hints fn-lvls))
         ((mv new-body alst-3 names-3)
          (expand-term substed-body hints new-lvls alst-2
                       names-2 (1- clock) state))
         ((if (dont-generate-freshvar new-body)) (mv new-body alst-3 names-3))
         (body-var (new-fresh-var names-3)))
      (mv body-var
          (acons new-body body-var alst-3)
          (cons body-var names-3))))

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
         ((if (dont-generate-freshvar term)) (mv term alst names)))
      (expand-fncall/lambda term hints fn-lvls alst names clock state)))

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
      (mv (cons new-hd new-tl) alst-2 names-2))))
)

(define cdr-induct-expand-term-list (term-lst hints fn-lvls alst names clock state)
  :irrelevant-formals-ok t
  :verify-guards nil
  (b* (((if (atom term-lst)) nil)
       ((mv & new-alst new-names)
        (expand-term (car term-lst) hints fn-lvls alst names clock state)))
    (cdr-induct-expand-term-list
     (cdr term-lst) hints fn-lvls new-alst new-names clock state)))

(defthm len-of-expand-term-list
  (implies (and (pseudo-term-listp term-lst)
                (smtlink-hint-p hints)
                (sym-int-alistp fn-lvls)
                (pseudo-term-sym-alistp alst)
                (symbol-listp names)
                (natp clock))
           (equal (len (mv-nth 0 (expand-term-list term-lst hints fn-lvls
                                                   alst names clock
                                                   state)))
                  (len term-lst)))
  :hints (("Goal"
           :in-theory (enable expand-term-list cdr-induct-expand-term-list)
           :induct (cdr-induct-expand-term-list term-lst hints fn-lvls alst
                                                names clock state))))

(verify-guards expand-term
  :hints (("Goal" :in-theory (e/d (pseudo-lambda/fnp dont-generate-freshvar)
                                  ()))))

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

(defthm correctness-of-generate-equalities
  (implies (and (alistp a)
                (pseudo-termp term)
                (pseudo-term-sym-alistp alst)
                (assoc-equal term alst)
                (ev-smtcp (generate-equalities alst) a))
           (equal (ev-smtcp (cdr (assoc-equal term alst)) a)
                  (ev-smtcp term a)))
  :hints (("Goal"
           :induct (generate-equalities alst)
           :in-theory (e/d (generate-equalities)
                           (pseudo-termp)))))

(defthm genequalities-of-new-vars-for-actuals
  (implies (and (pseudo-term-sym-alistp alst)
                (alistp a)
                (ev-smtcp
                 (generate-equalities
                  (mv-nth 1 (new-vars-for-actuals actuals alst names)))
                 a))
           (ev-smtcp (generate-equalities alst) a))
  :hints (("Goal"
           :in-theory (enable new-vars-for-actuals
                              generate-equalities))))

(defthm genequalities-of-new-vars-for-actuals-2
  (implies (and (pseudo-term-listp actuals)
                (pseudo-term-sym-alistp alst)
                (alistp a)
                (ev-smtcp
                 (generate-equalities
                  (mv-nth 1 (new-vars-for-actuals actuals alst names)))
                 a))
           (equal (ev-smtcp-lst
                   (mv-nth 0 (new-vars-for-actuals actuals alst names))
                   a)
                  (ev-smtcp-lst actuals a)))
  :hints (("Goal"
           :in-theory (enable new-vars-for-actuals
                              generate-equalities))))

(defthm genequalities-of-acons
  (implies (and (pseudo-term-sym-alistp alst)
                (alistp a)
                (ev-smtcp (generate-equalities (cons (cons term var) alst)) a))
           (ev-smtcp (generate-equalities alst) a))
  :hints (("Goal"
           :in-theory (enable generate-equalities))))

(defthm-expand-term-flag
  (defthm genequalities-of-expand-fncall/lambda
    (implies (and (pseudo-term-sym-alistp alst)
                  (alistp a))
             (b* (((mv & new-alst &)
                   (expand-fncall/lambda term hints fn-lvls alst names
                                         clock state)))
               (implies (ev-smtcp (generate-equalities new-alst) a)
                        (ev-smtcp (generate-equalities alst) a))))
    :flag expand-fncall/lambda
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-fncall/lambda term hints fn-lvls
                                                  alst names clock state)
                            (expand-fncall/lambda nil hints fn-lvls
                                                  alst names clock state)
                            (expand-fncall/lambda term hints fn-lvls alst names
                                                  0 state))))))
  (defthm genequalities-of-expand-term
    (implies (and (pseudo-term-sym-alistp alst)
                  (alistp a))
             (b* (((mv & new-alst &)
                   (expand-term term hints fn-lvls alst names clock state)))
               (implies (ev-smtcp (generate-equalities new-alst) a)
                        (ev-smtcp (generate-equalities alst) a))))
    :flag expand-term
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-term term hints fn-lvls alst names
                                         clock state)
                            (expand-term term hints fn-lvls alst names
                                         0 state)
                            (expand-term nil hints fn-lvls alst names
                                         clock state))))))
  (defthm genequalities-of-expand-term-list
    (implies (and (pseudo-term-sym-alistp alst)
                  (alistp a))
             (b* (((mv & new-alst &)
                   (expand-term-list term-lst hints fn-lvls alst names
                                     clock state)))
               (implies (ev-smtcp (generate-equalities new-alst) a)
                        (ev-smtcp (generate-equalities alst) a))))
    :flag expand-term-list
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-term-list term-lst hints fn-lvls alst
                                              names clock state)
                            (expand-term-list nil hints fn-lvls alst
                                              names clock state)
                            ))))))

(defthm correctness-of-expand-term-inductive
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (consp term)
                  (not (equal (car term) 'quote))
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a)
                  (b* (((mv new new-alst &)
                        (expand-fncall/lambda term hints fn-lvls alst names clock state)))
                    (implies (ev-smtcp (generate-equalities new-alst) a)
                             (equal (ev-smtcp new a)
                                    (ev-smtcp term a)))))
             (b* (((mv new new-alst &)
                   (expand-term term hints fn-lvls alst names clock state)))
               (implies (ev-smtcp (generate-equalities new-alst) a)
                        (equal (ev-smtcp new a)
                               (ev-smtcp term a)))))
    :hints (("Goal"
             :expand ((expand-term term hints fn-lvls alst names
                                   clock state)
                      (expand-term term hints fn-lvls alst names
                                   0 state)
                      (expand-term nil hints fn-lvls alst names
                                   clock state)))))

(defthm correctness-of-expand-term-list-inductive
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp term-lst)
                (consp term-lst)
                (smtlink-hint-p hints)
                (sym-int-alistp fn-lvls)
                (pseudo-term-sym-alistp alst)
                (symbol-listp names)
                (natp clock)
                (alistp a)
                (b* (((mv new-hd alst-1 names-1)
                      (expand-term (car term-lst) hints fn-lvls alst names
                                   clock state))
                     ((mv new-tl alst-2 &)
                      (expand-term-list (cdr term-lst) hints fn-lvls alst-1 names-1
                                        clock state)))
                  (and (implies (ev-smtcp (generate-equalities alst-1) a)
                                (equal (ev-smtcp new-hd a)
                                       (ev-smtcp (car term-lst) a)))
                       (implies (ev-smtcp (generate-equalities alst-2) a)
                                (equal (ev-smtcp-lst new-tl a)
                                       (ev-smtcp-lst (cdr term-lst) a))))))
           (b* (((mv new new-alst &)
                 (expand-term-list term-lst hints fn-lvls alst names
                                   clock state)))
             (implies (ev-smtcp (generate-equalities new-alst) a)
                      (equal (ev-smtcp-lst new a)
                             (ev-smtcp-lst term-lst a)))))
  :hints (("Goal"
           :in-theory (e/d () (genequalities-of-acons
                               pseudo-term-sym-alistp-of-cons
                               pseudo-term-listp-of-symbol-listp))
           :expand ((expand-term-list term-lst hints fn-lvls alst
                                      names clock state)
                    (expand-term-list nil hints fn-lvls alst
                                      names clock state)))))

(local
 (defthm crock2
   (implies (and (pseudo-term-listp new-actuals)
                 (pseudo-termp term)
                 (not (equal (car term) 'quote))
                 (consp term)
                 (equal (ev-smtcp-lst new-actuals a)
                        (ev-smtcp-lst (cdr term) a)))
            (equal (ev-smtcp (cons (car term) new-actuals) a)
                   (ev-smtcp term a)))
   :hints (("Goal"
            :in-theory (e/d (ev-smtcp-of-fncall-args) ()))))
 )

(defthm correctness-of-expand-fncall/lambda-inductive-1
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (consp term)
                  (pseudo-lambda/fnp (car term))
                  (dont-expand (car term) hints fn-lvls)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a)
                  (b* (((mv new-actuals alst-1 &)
                        (expand-term-list (cdr term) hints fn-lvls alst names
                                          clock state)))
                    (and (implies (ev-smtcp (generate-equalities alst-1) a)
                                  (equal (ev-smtcp-lst new-actuals a)
                                         (ev-smtcp-lst (cdr term) a))))))
             (b* (((mv new new-alst &)
                   (expand-fncall/lambda term hints fn-lvls alst names
                                         clock state)))
               (implies (ev-smtcp (generate-equalities new-alst) a)
                        (equal (ev-smtcp new a)
                               (ev-smtcp term a)))))
    :hints (("Goal"
             :in-theory (e/d (pseudo-lambda/fnp)
                             (pseudo-termp))
             :expand ((expand-fncall/lambda term hints fn-lvls
                                            alst names clock state)
                      (expand-fncall/lambda nil hints fn-lvls
                                            alst names clock state)))))

(defthm correctness-of-expand-fncall/lambda-inductive-2
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp term)
                (consp term)
                (pseudo-lambda/fnp (car term))
                (not (dont-expand (car term) hints fn-lvls))
                (smtlink-hint-p hints)
                (sym-int-alistp fn-lvls)
                (pseudo-term-sym-alistp alst)
                (symbol-listp names)
                (natp clock)
                (alistp a)
                (b* (((cons fn actuals) term)
                     ((mv new-actuals alst-1 names-1)
                      (expand-term-list actuals hints fn-lvls alst names
                                        clock state))
                     ((mv actual-vars alst-2 names-2)
                      (new-vars-for-actuals new-actuals alst-1 names-1))
                     ((mv ok substed-body)
                      (function-substitution `(,fn ,@actual-vars) state))
                     ((unless ok) t)
                     (new-lvls (update-fn-lvls fn hints fn-lvls))
                     ((mv new-body alst-3 &)
                      (expand-term substed-body hints new-lvls alst-2
                                   names-2 (1- clock) state)))
                  (and (implies (ev-smtcp (generate-equalities alst-1) a)
                                (equal (ev-smtcp-lst new-actuals a)
                                       (ev-smtcp-lst actuals a)))
                       (implies (ev-smtcp (generate-equalities alst-3) a)
                                (equal (ev-smtcp new-body a)
                                       (ev-smtcp substed-body a))))))
           (b* (((mv new new-alst &)
                 (expand-fncall/lambda term hints fn-lvls alst names
                                       clock state)))
             (implies (ev-smtcp (generate-equalities new-alst) a)
                      (equal (ev-smtcp new a)
                             (ev-smtcp term a)))))
  :hints (("Goal"
           :in-theory (e/d (pseudo-lambda/fnp)
                           (pseudo-termp
                            genequalities-of-expand-term
                            correctness-of-generate-equalities
                            ))
           :use ((:instance correctness-of-generate-equalities
                            (term (MV-NTH
                                   0
                                   (expand-term
                                    (MV-NTH
                                     1
                                     (FUNCTION-SUBSTITUTION
                                      (CONS
                                       (CAR TERM)
                                       (MV-NTH
                                        0
                                        (NEW-VARS-FOR-ACTUALS
                                         (MV-NTH 0
                                                 (EXPAND-TERM-LIST (CDR TERM)
                                                                   HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                         (MV-NTH 1
                                                 (EXPAND-TERM-LIST (CDR TERM)
                                                                   HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                         (MV-NTH 2
                                                 (EXPAND-TERM-LIST (CDR TERM)
                                                                   HINTS
                                                                   FN-LVLS ALST NAMES CLOCK STATE)))))
                                      STATE))
                                    hints
                                    (update-fn-lvls (car term)
                                                    hints fn-lvls)
                                    (mv-nth
                                     1
                                     (new-vars-for-actuals
                                      (mv-nth 0
                                              (expand-term-list (cdr term)
                                                                hints fn-lvls alst names clock state))
                                      (mv-nth 1
                                              (expand-term-list (cdr term)
                                                                hints fn-lvls alst names clock state))
                                      (mv-nth 2
                                              (expand-term-list (cdr term)
                                                                hints fn-lvls alst names clock state))))
                                    (mv-nth
                                     2
                                     (new-vars-for-actuals
                                      (mv-nth 0
                                              (expand-term-list (cdr term)
                                                                hints fn-lvls alst names clock state))
                                      (mv-nth 1
                                              (expand-term-list (cdr term)
                                                                hints fn-lvls alst names clock state))
                                      (mv-nth 2
                                              (expand-term-list (cdr term)
                                                                hints fn-lvls alst names clock state))))
                                    (+ -1 clock)
                                    state)))
                            (alst (CONS
                                   (CONS
                                    (MV-NTH
                                     0
                                     (expand-term
                                      (MV-NTH
                                       1
                                       (FUNCTION-SUBSTITUTION
                                        (CONS
                                         (CAR TERM)
                                         (MV-NTH
                                          0
                                          (NEW-VARS-FOR-ACTUALS
                                           (MV-NTH 0
                                                   (EXPAND-TERM-LIST (CDR TERM)
                                                                     HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                           (MV-NTH 1
                                                   (EXPAND-TERM-LIST (CDR TERM)
                                                                     HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                           (MV-NTH 2
                                                   (EXPAND-TERM-LIST (CDR TERM)
                                                                     HINTS
                                                                     FN-LVLS ALST NAMES CLOCK STATE)))))
                                        STATE))
                                      hints
                                      (update-fn-lvls (car term)
                                                      hints fn-lvls)
                                      (mv-nth
                                       1
                                       (new-vars-for-actuals
                                        (mv-nth 0
                                                (expand-term-list (cdr term)
                                                                  hints fn-lvls alst names clock state))
                                        (mv-nth 1
                                                (expand-term-list (cdr term)
                                                                  hints fn-lvls alst names clock state))
                                        (mv-nth 2
                                                (expand-term-list (cdr term)
                                                                  hints fn-lvls alst names clock state))))
                                      (mv-nth
                                       2
                                       (new-vars-for-actuals
                                        (mv-nth 0
                                                (expand-term-list (cdr term)
                                                                  hints fn-lvls alst names clock state))
                                        (mv-nth 1
                                                (expand-term-list (cdr term)
                                                                  hints fn-lvls alst names clock state))
                                        (mv-nth 2
                                                (expand-term-list (cdr term)
                                                                  hints fn-lvls alst names clock state))))
                                      (+ -1 clock)
                                      state))
                                    (NEW-FRESH-VAR
                                     (MV-NTH
                                      2
                                      (expand-term
                                       (MV-NTH
                                        1
                                        (FUNCTION-SUBSTITUTION
                                         (CONS
                                          (CAR TERM)
                                          (MV-NTH
                                           0
                                           (NEW-VARS-FOR-ACTUALS
                                            (MV-NTH 0
                                                    (EXPAND-TERM-LIST (CDR TERM)
                                                                      HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                            (MV-NTH 1
                                                    (EXPAND-TERM-LIST (CDR TERM)
                                                                      HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                            (MV-NTH 2
                                                    (EXPAND-TERM-LIST (CDR TERM)
                                                                      HINTS
                                                                      FN-LVLS ALST NAMES CLOCK STATE)))))
                                         STATE))
                                       hints
                                       (update-fn-lvls (car term)
                                                       hints fn-lvls)
                                       (mv-nth
                                        1
                                        (new-vars-for-actuals
                                         (mv-nth 0
                                                 (expand-term-list (cdr term)
                                                                   hints fn-lvls alst names clock state))
                                         (mv-nth 1
                                                 (expand-term-list (cdr term)
                                                                   hints fn-lvls alst names clock state))
                                         (mv-nth 2
                                                 (expand-term-list (cdr term)
                                                                   hints fn-lvls alst names clock state))))
                                       (mv-nth
                                        2
                                        (new-vars-for-actuals
                                         (mv-nth 0
                                                 (expand-term-list (cdr term)
                                                                   hints fn-lvls alst names clock state))
                                         (mv-nth 1
                                                 (expand-term-list (cdr term)
                                                                   hints fn-lvls alst names clock state))
                                         (mv-nth 2
                                                 (expand-term-list (cdr term)
                                                                   hints fn-lvls alst names clock state))))
                                       (+ -1 clock)
                                       state))))
                                   (MV-NTH
                                    1
                                    (expand-term
                                     (MV-NTH
                                      1
                                      (FUNCTION-SUBSTITUTION
                                       (CONS
                                        (CAR TERM)
                                        (MV-NTH
                                         0
                                         (NEW-VARS-FOR-ACTUALS
                                          (MV-NTH 0
                                                  (EXPAND-TERM-LIST (CDR TERM)
                                                                    HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                          (MV-NTH 1
                                                  (EXPAND-TERM-LIST (CDR TERM)
                                                                    HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                          (MV-NTH 2
                                                  (EXPAND-TERM-LIST (CDR TERM)
                                                                    HINTS
                                                                    FN-LVLS ALST NAMES CLOCK STATE)))))
                                       STATE))
                                     hints
                                     (update-fn-lvls (car term)
                                                     hints fn-lvls)
                                     (mv-nth
                                      1
                                      (new-vars-for-actuals
                                       (mv-nth 0
                                               (expand-term-list (cdr term)
                                                                 hints fn-lvls alst names clock state))
                                       (mv-nth 1
                                               (expand-term-list (cdr term)
                                                                 hints fn-lvls alst names clock state))
                                       (mv-nth 2
                                               (expand-term-list (cdr term)
                                                                 hints fn-lvls alst names clock state))))
                                     (mv-nth
                                      2
                                      (new-vars-for-actuals
                                       (mv-nth 0
                                               (expand-term-list (cdr term)
                                                                 hints fn-lvls alst names clock state))
                                       (mv-nth 1
                                               (expand-term-list (cdr term)
                                                                 hints fn-lvls alst names clock state))
                                       (mv-nth 2
                                               (expand-term-list (cdr term)
                                                                 hints fn-lvls alst names clock state))))
                                     (+ -1 clock)
                                     state)))))
                 (:instance genequalities-of-expand-term
                            (term (MV-NTH
                                   1
                                   (FUNCTION-SUBSTITUTION
                                    (CONS
                                     (CAR TERM)
                                     (MV-NTH
                                      0
                                      (NEW-VARS-FOR-ACTUALS
                                       (MV-NTH 0
                                               (EXPAND-TERM-LIST (CDR TERM)
                                                                 HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                       (MV-NTH 1
                                               (EXPAND-TERM-LIST (CDR TERM)
                                                                 HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                       (MV-NTH 2
                                               (EXPAND-TERM-LIST (CDR TERM)
                                                                 HINTS
                                                                 FN-LVLS ALST NAMES CLOCK STATE)))))
                                    STATE)))
                            (fn-lvls (UPDATE-FN-LVLS (CAR TERM)
                                                     HINTS FN-LVLS))
                            (alst (MV-NTH
                                   1
                                   (NEW-VARS-FOR-ACTUALS
                                    (MV-NTH 0
                                            (EXPAND-TERM-LIST (CDR TERM)
                                                              HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                    (MV-NTH 1
                                            (EXPAND-TERM-LIST (CDR TERM)
                                                              HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                    (MV-NTH 2
                                            (EXPAND-TERM-LIST (CDR TERM)
                                                              HINTS FN-LVLS ALST NAMES CLOCK STATE)))))
                            (names (MV-NTH
                                    2
                                    (NEW-VARS-FOR-ACTUALS
                                     (MV-NTH 0
                                             (EXPAND-TERM-LIST (CDR TERM)
                                                               HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                     (MV-NTH 1
                                             (EXPAND-TERM-LIST (CDR TERM)
                                                               HINTS FN-LVLS ALST NAMES CLOCK STATE))
                                     (MV-NTH 2
                                             (EXPAND-TERM-LIST (CDR TERM)
                                                               HINTS FN-LVLS ALST NAMES CLOCK STATE)))))
                            (clock (+ -1 CLOCK)))
                 )
           :expand ((expand-fncall/lambda term hints fn-lvls
                                          alst names clock state)
                    (expand-fncall/lambda nil hints fn-lvls
                                          alst names clock state)
                    (expand-fncall/lambda term hints fn-lvls alst names 0 state)))))

(defthm-expand-term-flag
  (defthm correctness-of-expand-fncall/lambda
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a))
             (b* (((mv new new-alst &)
                   (expand-fncall/lambda term hints fn-lvls alst names
                                         clock state)))
               (implies (ev-smtcp (generate-equalities new-alst) a)
                        (equal (ev-smtcp new a)
                               (ev-smtcp term a)))))
    :flag expand-fncall/lambda
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () (genequalities-of-acons
                                       pseudo-term-sym-alistp-of-cons
                                       pseudo-term-listp-of-symbol-listp))
                   :expand ((expand-fncall/lambda term hints fn-lvls
                                                  alst names clock state)
                            (expand-fncall/lambda nil hints fn-lvls
                                                  alst names clock state)
                            (expand-fncall/lambda term hints fn-lvls alst names
                                                  0 state))))))
  (defthm correctness-of-expand-term
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a))
             (b* (((mv new new-alst &)
                   (expand-term term hints fn-lvls alst names clock state)))
               (implies (ev-smtcp (generate-equalities new-alst) a)
                        (equal (ev-smtcp new a)
                               (ev-smtcp term a)))))
    :flag expand-term
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-term term hints fn-lvls alst names
                                         clock state)
                            (expand-term term hints fn-lvls alst names
                                         0 state)
                            (expand-term nil hints fn-lvls alst names
                                         clock state))))))
  (defthm correctness-of-expand-term-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-term-listp term-lst)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a))
             (b* (((mv new new-alst &)
                   (expand-term-list term-lst hints fn-lvls alst names
                                     clock state)))
               (implies (ev-smtcp (generate-equalities new-alst) a)
                        (equal (ev-smtcp-lst new a)
                               (ev-smtcp-lst term-lst a)))))
    :flag expand-term-list
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-term-list term-lst hints fn-lvls alst
                                              names clock state)
                            (expand-term-list nil hints fn-lvls alst
                                              names clock state)
                            )))))
  :hints(("Goal"
          :in-theory (disable member-equal))))

;; -----------------------------------------------------

(define expand-cp ((cl pseudo-term-listp)
                   (hints t)
                   state)
  (b* (((unless (smtlink-hint-p hints))
        (value (list cl)))
       ((smtlink-hint h) hints)
       (goal (disjoin cl))
       ((mv new-term alst &)
        (expand-term goal hints nil nil (acl2::all-vars goal)
                     h.wrld-fn-len state)))
    (value (list (list `(implies ,(generate-equalities alst) ,new-term))))))

(local (in-theory (enable expand-cp)))

(defthm correctness-of-expand-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (expand-cp cl hints state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d () ())))
  :rule-classes :clause-processor)
