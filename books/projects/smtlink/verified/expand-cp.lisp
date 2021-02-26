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
(include-book "std/alists/alist-fix" :dir :system)
(include-book "centaur/fty/top" :dir :system)
;; To be compatible with Arithmetic books
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)

(include-book "../utils/pseudo-term")
(include-book "../utils/fresh-vars")
(include-book "hint-interface")
(include-book "generalize")
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

(local
 (defthm symbol-is-pseudo-term
   (implies (symbolp x) (pseudo-termp x)))
 )

(defthm subsetp-equal-over-simple-term-vars-lst
  (implies (and (symbol-listp avoid)
                (pseudo-term-listp term-lst)
                (consp term-lst)
                (subsetp-equal (acl2::simple-term-vars-lst term-lst)
                               avoid))
           (and (subsetp-equal (acl2::simple-term-vars (car term-lst))
                               avoid)
                (subsetp-equal (acl2::simple-term-vars-lst (cdr term-lst))
                               avoid)))
  :hints (("Goal"
           :in-theory (enable acl2::simple-term-vars-lst))))

(defthm subsetp-equal-over-simple-term-vars
  (implies (and (symbol-listp avoid)
                (pseudo-termp term)
                (consp term)
                (not (equal (car term) 'quote))
                (subsetp-equal (acl2::simple-term-vars term) avoid))
           (subsetp-equal (acl2::simple-term-vars-lst (cdr term)) avoid))
  :hints (("Goal"
           :in-theory (enable acl2::simple-term-vars))))

(defthm subsetp-equal-of-assoc-equal
  (implies (and (symbol-listp avoid)
                (pseudo-termp term)
                (pseudo-term-sym-alistp alst)
                (assoc-equal term alst)
                (subsetp-equal (strip-cdrs alst) avoid))
           (subsetp-equal (acl2::simple-term-vars (cdr (assoc-equal term alst)))
                          avoid))
  :hints (("Goal"
           :in-theory (enable acl2::simple-term-vars))))

(define new-var-for-term ((term pseudo-termp)
                          (alst pseudo-term-sym-alistp)
                          (avoid symbol-listp))
  :guard (and (subsetp-equal (acl2::simple-term-vars term) avoid)
              (subsetp-equal (strip-cdrs alst) avoid))
  :returns (mv (var pseudo-termp)
               (new-alst pseudo-term-sym-alistp)
               (new-avoid symbol-listp))
  (b* ((term (pseudo-term-fix term))
       (alst (pseudo-term-sym-alist-fix alst))
       (avoid (symbol-list-fix avoid))
       ((if (dont-generate-freshvar term))
        (mv term alst avoid))
       (new-var (new-fresh-var avoid)))
    (mv new-var (acons term new-var alst) (cons new-var avoid)))
  ///
  ;; (defthm no-duplicatesp-of-new-var-for-term
  ;;   (implies (and (pseudo-term-sym-alistp alst)
  ;;                 (symbol-listp avoid)
  ;;                 (no-duplicatesp-equal (strip-cdrs alst))
  ;;                 (subsetp-equal (strip-cdrs alst) avoid))
  ;;            (no-duplicatesp-equal
  ;;             (strip-cdrs
  ;;              (mv-nth 1 (new-var-for-term term alst avoid))))))

  (defthm alst-subset-of-new-var-for-term
    (b* (((mv & new-alst new-avoid)
          (new-var-for-term term alst avoid)))
    (implies (and (pseudo-termp term)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp avoid)
                  (subsetp-equal (strip-cdrs alst) avoid))
             (subsetp-equal (strip-cdrs new-alst) new-avoid))))

  (defthm avoid-subset-of-new-var-for-term
    (b* (((mv & & new-avoid)
          (new-var-for-term term alst avoid)))
      (implies (and (pseudo-termp term)
                    (pseudo-term-sym-alistp alst)
                    (symbol-listp avoid))
               (subsetp-equal avoid new-avoid))))

  (define new-var-for-term-env ((term pseudo-termp)
                                (avoid symbol-listp)
                                (a alistp))
    :guard (subsetp-equal (acl2::simple-term-vars term) avoid)
    :returns (new-a alistp)
    (b* ((term (pseudo-term-fix term))
         (avoid (symbol-list-fix avoid))
         (a (acl2::alist-fix a))
         ((if (dont-generate-freshvar term)) a)
         (new-var (new-fresh-var avoid)))
      (append (replace-alist-to-bindings `((,term . ,new-var)) a) a))))

(defthm correctness-of-new-var-for-term
  (implies (and (pseudo-termp term)
                (pseudo-term-sym-alistp alst)
                (symbol-listp avoid)
                (alistp a))
           (equal (ev-smtcp
                   (mv-nth 0 (new-var-for-term term alst avoid))
                   (new-var-for-term-env term avoid a))
                  (ev-smtcp term a)))
  :hints (("Goal"
           :in-theory (enable new-var-for-term new-var-for-term-env))))

(define new-vars-for-term-list ((term-lst pseudo-term-listp)
                                (alst pseudo-term-sym-alistp)
                                (avoid symbol-listp))
  :measure (len (pseudo-term-list-fix term-lst))
  :guard (and (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
              (subsetp-equal (strip-cdrs alst) avoid))
  :returns (mv (vars pseudo-term-listp)
               (new-alst pseudo-term-sym-alistp)
               (new-avoid symbol-listp))
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       (alst (pseudo-term-sym-alist-fix alst))
       (avoid (symbol-list-fix avoid))
       ((unless (consp term-lst))
        (mv nil alst avoid))
       ((cons lst-hd lst-tl) term-lst)
       ((mv var-hd alst-1 avoid-1)
        (new-var-for-term lst-hd alst avoid))
       ((mv vars-tl alst-2 avoid-2)
        (new-vars-for-term-list lst-tl alst-1 avoid-1)))
    (mv (cons var-hd vars-tl) alst-2 avoid-2))
  ///
  (more-returns
   (vars (implies (pseudo-term-listp term-lst)
                  (equal (len vars) (len term-lst)))
         :name len-of-new-vars-for-term-list))

  ;; (defthm no-duplicatesp-of-new-var-for-term-list
  ;;   (implies (and (pseudo-term-sym-alistp alst)
  ;;                 (symbol-listp avoid)
  ;;                 (no-duplicatesp-equal (strip-cdrs alst))
  ;;                 (subsetp-equal (strip-cdrs alst) avoid))
  ;;            (no-duplicatesp-equal
  ;;             (strip-cdrs
  ;;              (mv-nth 1 (new-vars-for-term-list term-lst alst avoid))))))

  (defthm alst-subset-of-new-vars-for-term-list
    (b* (((mv & new-alst new-avoid)
          (new-vars-for-term-list term-lst alst avoid)))
      (implies (and (pseudo-term-listp term-lst)
                    (pseudo-term-sym-alistp alst)
                    (symbol-listp avoid)
                    (subsetp-equal (strip-cdrs alst) avoid))
               (subsetp-equal (strip-cdrs new-alst) new-avoid))))

  ;; (defthm avoid-subset-of-new-vars-for-term-lst
  ;;   (b* (((mv & & new-avoid)
  ;;         (new-vars-for-term-list term-lst alst avoid)))
  ;;     (implies (and (pseudo-termp term)
  ;;                   (pseudo-term-sym-alistp alst)
  ;;                   (symbol-listp avoid))
  ;;              (subsetp-equal avoid new-avoid))))

  (define new-vars-for-term-list-env ((term-lst pseudo-term-listp)
                                      (alst pseudo-term-sym-alistp)
                                      (avoid symbol-listp)
                                      (a alistp))
    :guard (and (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
                (subsetp-equal (strip-cdrs alst) avoid))
    :returns (new-a alistp)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (alst (pseudo-term-sym-alist-fix alst))
         (avoid (symbol-list-fix avoid))
         (a (acl2::alist-fix a))
         ((unless (consp term-lst)) a)
         ((cons lst-hd lst-tl) term-lst)
         ((mv & alst-1 avoid-1)
          (new-var-for-term lst-hd alst avoid))
         (a-hd (new-var-for-term-env lst-hd avoid a))
         (a-tl (new-vars-for-term-list-env lst-tl alst-1 avoid-1 a-hd)))
      a-tl)))

(skip-proofs
 (defthm lemma1
   (equal (ev-smtcp
           (mv-nth 0
                   (new-var-for-term (car term-lst)
                                     alst avoid))
           (new-vars-for-term-list-env (cdr term-lst)
                                       (mv-nth 1
                                               (new-var-for-term (car term-lst)
                                                                 alst avoid))
                                       (mv-nth 2
                                               (new-var-for-term (car term-lst)
                                                                 alst avoid))
                                       (new-var-for-term-env (car term-lst)
                                                             avoid a)))
          (ev-smtcp
           (mv-nth 0
                   (new-var-for-term (car term-lst)
                                     alst avoid))
           (new-var-for-term-env (car term-lst)
                                 avoid a)))
   ))

(skip-proofs
 (defthm lemma2
   (implies (and (pseudo-term-listp term-lst)
                 (symbol-listp avoid)
                 (alistp a)
                 (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid))
            (equal (ev-smtcp-lst (cdr term-lst)
                                 (new-var-for-term-env (car term-lst)
                                                       avoid a))
                   (ev-smtcp-lst (cdr term-lst) a)))
   :hints (("Goal"
            :in-theory (enable new-var-for-term-env))))
 )

(defthm correctness-of-new-vars-for-term-list
  (implies (and (pseudo-term-listp term-lst)
                (pseudo-term-sym-alistp alst)
                (symbol-listp avoid)
                (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
                (subsetp-equal (strip-cdrs alst) avoid)
                (alistp a))
           (equal (ev-smtcp-lst
                   (mv-nth 0 (new-vars-for-term-list term-lst alst avoid))
                   (new-vars-for-term-list-env term-lst alst avoid a))
                  (ev-smtcp-lst term-lst a)))
  :hints (("Goal"
           :in-theory (e/d (new-vars-for-term-list
                            new-vars-for-term-list-env)
                           ()))))

(encapsulate ()
  (local
   (in-theory (e/d (pairlis$)
                   (assoc-equal lambda-of-pseudo-lambdap
                                symbol-listp))))

  (local
   (defthm crock3
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

(skip-proofs
(defthm term-vars-of-function-substitution
  (implies (and (pseudo-termp term)
                (consp term)
                (pseudo-lambda/fnp (car term))
                (mv-nth 0 (function-substitution term state)))
           (equal (acl2::simple-term-vars (mv-nth 1 (function-substitution term state)))
                  (acl2::simple-term-vars term)))
  :hints (("Goal"
           :in-theory (enable function-substitution acl2::simple-term-vars))))
)

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
           :in-theory (disable pseudo-termp pseudo-term-listp)))

  (define expand-fncall/lambda ((term pseudo-termp)
                                (hints smtlink-hint-p)
                                (fn-lvls sym-int-alistp)
                                (alst pseudo-term-sym-alistp)
                                (avoid symbol-listp)
                                (clock natp)
                                state)
    :guard (and (not (zp clock)) (consp term)
                (pseudo-lambda/fnp (car term))
                (subsetp-equal (acl2::simple-term-vars term) avoid)
                (subsetp-equal (strip-cdrs alst) avoid))
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix term))
                   1)
    :returns (mv (new-term pseudo-termp)
                 (new-alst pseudo-term-sym-alistp)
                 (new-avoid symbol-listp))
    (b* ((term (pseudo-term-fix term))
         (hints (smtlink-hint-fix hints))
         ((smtlink-hint h) hints)
         (alst (pseudo-term-sym-alist-fix alst))
         (avoid (symbol-list-fix avoid))
         (clock (nfix clock))
         ((unless (mbt (and (not (zp clock)) (consp term)
                            (pseudo-lambda/fnp (car term))
                            (subsetp-equal (acl2::simple-term-vars term) avoid)
                            (subsetp-equal (strip-cdrs alst) avoid))))
          (mv term alst avoid))
         ((cons fn actuals) term)
         ((mv new-actuals alst-1 avoid-1)
          (expand-term-list actuals hints fn-lvls alst avoid clock state))
         ((mv actual-vars alst-2 avoid-2)
          (new-vars-for-term-list new-actuals alst-1 avoid-1))
         ((if (dont-expand fn h fn-lvls))
          (mv `(,fn ,@actual-vars) alst-2 avoid-2))
         ((mv ok substed-body) (function-substitution `(,fn ,@actual-vars) state))
         ((unless ok) (mv term alst avoid))
         (new-lvls (update-fn-lvls fn hints fn-lvls))
         ((mv new-body alst-3 avoid-3)
          (expand-term substed-body hints new-lvls alst-2 avoid-2 (1- clock)
                       state))
         ((mv body-var alst-4 avoid-4) (new-var-for-term new-body alst-3 avoid-3)))
      (mv body-var alst-4 avoid-4)))

  (define expand-term ((term pseudo-termp)
                       (hints smtlink-hint-p)
                       (fn-lvls sym-int-alistp)
                       (alst pseudo-term-sym-alistp)
                       (avoid symbol-listp)
                       (clock natp)
                       state)
    :guard (and (subsetp-equal (acl2::simple-term-vars term) avoid)
                (subsetp-equal (strip-cdrs alst) avoid))
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix term))
                   2)
    :returns (mv (new-term pseudo-termp)
                 (new-alst pseudo-term-sym-alistp)
                 (new-avoid symbol-listp))
    (b* ((term (pseudo-term-fix term))
         (alst (pseudo-term-sym-alist-fix alst))
         (avoid (symbol-list-fix avoid))
         (clock (nfix clock))
         ((unless (mbt (and (subsetp-equal (acl2::simple-term-vars term) avoid)
                            (subsetp-equal (strip-cdrs alst) avoid))))
          (mv term alst avoid))
         ((if (zp clock)) (mv term alst avoid))
         (exist? (assoc-equal term alst))
         ((if exist?) (mv (cdr exist?) alst avoid))
         ((if (dont-generate-freshvar term)) (mv term alst avoid)))
      (expand-fncall/lambda term hints fn-lvls alst avoid clock state)))

  (define expand-term-list ((term-lst pseudo-term-listp)
                            (hints smtlink-hint-p)
                            (fn-lvls sym-int-alistp)
                            (alst pseudo-term-sym-alistp)
                            (avoid symbol-listp)
                            (clock natp)
                            state)
    :guard (and (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
                (subsetp-equal (strip-cdrs alst) avoid))
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-list-fix term-lst))
                   0)
    :returns (mv (new-term-lst pseudo-term-listp)
                 (new-alst pseudo-term-sym-alistp)
                 (new-avoid symbol-listp))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (alst (pseudo-term-sym-alist-fix alst))
         (avoid (symbol-list-fix avoid))
         (clock (nfix clock))
         ((unless (mbt (and (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
                            (subsetp-equal (strip-cdrs alst) avoid))))
          (mv term-lst alst avoid))
         ((unless (consp term-lst)) (mv nil alst avoid))
         ((cons term-hd term-tl) term-lst)
         ((mv new-hd alst-1 avoid-1)
          (expand-term term-hd hints fn-lvls alst avoid clock state))
         ((mv new-tl alst-2 avoid-2)
          (expand-term-list term-tl hints fn-lvls alst-1 avoid-1 clock state)))
      (mv (cons new-hd new-tl) alst-2 avoid-2))))
)

(define cdr-induct-expand-term-list (term-lst hints fn-lvls alst avoid clock state)
  :irrelevant-formals-ok t
  :verify-guards nil
  (b* (((if (atom term-lst)) nil)
       ((mv & new-alst new-avoid)
        (expand-term (car term-lst) hints fn-lvls alst avoid clock state)))
    (cdr-induct-expand-term-list
     (cdr term-lst) hints fn-lvls new-alst new-avoid clock state)))

(defthm len-of-expand-term-list
  (implies (and (pseudo-term-listp term-lst)
                (smtlink-hint-p hints)
                (sym-int-alistp fn-lvls)
                (pseudo-term-sym-alistp alst)
                (symbol-listp avoid)
                (natp clock))
           (equal (len (mv-nth 0 (expand-term-list term-lst hints fn-lvls
                                                   alst avoid clock
                                                   state)))
                  (len term-lst)))
  :hints (("Goal"
           :in-theory (enable expand-term-list cdr-induct-expand-term-list)
           :induct (cdr-induct-expand-term-list term-lst hints fn-lvls alst
                                                avoid clock state))))

(skip-proofs
(defthm-expand-term-flag
  (defthm subset-equal-of-expand-fncall/lambda
    (implies (and (pseudo-termp term)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp avoid)
                  (natp clock)
                  (subsetp-equal (acl2::simple-term-vars term) avoid)
                  (subsetp-equal (strip-cdrs alst) avoid))
             (b* (((mv new-term new-alst new-avoid)
                   (expand-fncall/lambda term hints fn-lvls alst avoid clock
                                         state)))
               (and (subsetp-equal avoid new-avoid)
                    (subsetp-equal (acl2::simple-term-vars new-term) new-avoid)
                    (subsetp-equal (strip-cdrs new-alst) new-avoid))))
    :flag expand-fncall/lambda
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-fncall/lambda term hints fn-lvls
                                                  alst avoid clock state)
                            (expand-fncall/lambda nil hints fn-lvls
                                                  alst avoid clock state)
                            (expand-fncall/lambda term hints fn-lvls alst names
                                                  0 state))))))
  (defthm subset-equal-of-expand-term
    (implies (and (pseudo-termp term)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp avoid)
                  (natp clock)
                  (subsetp-equal (acl2::simple-term-vars term) avoid)
                  (subsetp-equal (strip-cdrs alst) avoid))
             (b* (((mv new-term new-alst new-avoid)
                   (expand-term term hints fn-lvls alst avoid clock state)))
               (and (subsetp-equal avoid new-avoid)
                    (subsetp-equal (acl2::simple-term-vars new-term) new-avoid)
                    (subsetp-equal (strip-cdrs new-alst) new-avoid))))
    :flag expand-term
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-term term hints fn-lvls alst avoid
                                         clock state)
                            (expand-term term hints fn-lvls alst avoid
                                         0 state)
                            (expand-term nil hints fn-lvls alst avoid
                                         clock state))))))
  (defthm subset-equal-of-expand-term-list
    (implies (and (pseudo-term-listp term-lst)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp avoid)
                  (natp clock)
                  (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
                  (subsetp-equal (strip-cdrs alst) avoid))
             (b* (((mv new-term-lst new-alst new-avoid)
                   (expand-term-list term-lst hints fn-lvls alst avoid
                                     clock state)))
               (and (subsetp-equal avoid new-avoid)
                    (subsetp-equal (acl2::simple-term-vars-lst new-term-lst)
                                   new-avoid)
                    (subsetp-equal (strip-cdrs new-alst) new-avoid))))
    :flag expand-term-list
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-term-list term-lst hints fn-lvls alst
                                              avoid clock state)
                            (expand-term-list nil hints fn-lvls alst
                                              avoid clock state)))))))
)

(defthm simple-term-vars-of-fncall
  (implies (and (pseudo-termp term)
                (consp term)
                (not (equal (car term) 'quote)))
           (equal (acl2::simple-term-vars term)
                  (acl2::simple-term-vars-lst (cdr term))))
  :hints (("Goal"
           :in-theory (enable acl2::simple-term-vars
                              acl2::simple-term-vars-lst))))

(skip-proofs
(verify-guards expand-term
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (pseudo-lambda/fnp dont-generate-freshvar)
                           (IMPLIES-OF-DONT-EXPAND DEFAULT-CDR strip-cdrs
                                                   ;; term-vars-of-function-substitution
                                                   ))
           ;; :use ((:instance term-vars-of-function-substitution
           ;;                  (term (CONS
           ;;                         (CAR TERM)
           ;;                         (MV-NTH
           ;;                          0
           ;;                          (NEW-VARS-FOR-TERM-LIST
           ;;                           (MV-NTH 0
           ;;                                   (EXPAND-TERM-LIST (CDR TERM)
           ;;                                                     HINTS FN-LVLS ALST AVOID CLOCK STATE))
           ;;                           (MV-NTH 1
           ;;                                   (EXPAND-TERM-LIST (CDR TERM)
           ;;                                                     HINTS FN-LVLS ALST AVOID CLOCK STATE))
           ;;                           (MV-NTH 2
           ;;                                   (EXPAND-TERM-LIST (CDR TERM)
           ;;                                                     HINTS
           ;;                                                     FN-LVLS ALST
           ;;                                                     AVOID CLOCK
           ;;                                                     STATE))))))))
           )))
)

(defines expand-term-env
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :hints (("Goal"
           :in-theory (disable pseudo-termp pseudo-term-listp)))

  (define expand-fncall/lambda-env ((term pseudo-termp)
                                    (hints smtlink-hint-p)
                                    (fn-lvls sym-int-alistp)
                                    (alst pseudo-term-sym-alistp)
                                    (avoid-vars symbol-listp)
                                    (clock natp)
                                    state
                                    (a alistp))
    :guard (and (not (zp clock)) (consp term)
                (pseudo-lambda/fnp (car term))
                (subsetp-equal (acl2::simple-term-vars term) avoid-vars)
                (subsetp-equal (strip-cdrs alst) avoid-vars))
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix term))
                   1)
    :returns (new-a alistp)
    (b* ((term (pseudo-term-fix term))
         (hints (smtlink-hint-fix hints))
         ((smtlink-hint h) hints)
         (alst (pseudo-term-sym-alist-fix alst))
         (avoid-vars (symbol-list-fix avoid-vars))
         (clock (nfix clock))
         (a (acl2::alist-fix a))
         ((unless (mbt (and (not (zp clock)) (consp term)
                            (pseudo-lambda/fnp (car term))
                            (subsetp-equal (acl2::simple-term-vars term) avoid-vars)
                            (subsetp-equal (strip-cdrs alst) avoid-vars))))
          a)
         ((cons fn actuals) term)
         ((mv new-actuals alst-1 avoid-1)
          (expand-term-list actuals hints fn-lvls alst avoid-vars clock state))
         (a-1
          (expand-term-list-env actuals hints fn-lvls alst avoid-vars clock
                                state a))
         ((mv actual-vars alst-2 avoid-2)
          (new-vars-for-term-list new-actuals alst-1 avoid-1))
         (a-2 (new-vars-for-term-list-env new-actuals alst-1 avoid-1 a-1))
         ((if (dont-expand fn h fn-lvls)) a-2)
         ((mv ok substed-body) (function-substitution `(,fn ,@actual-vars) state))
         ((unless ok) a)
         (new-lvls (update-fn-lvls fn hints fn-lvls))
         ((mv new-body & avoid-3)
          (expand-term substed-body hints new-lvls alst-2 avoid-2 (1- clock)
                       state))
         (a-3 (expand-term-env substed-body hints new-lvls alst-2 avoid-2
                               (1- clock) state a-2))
         (a-4 (new-var-for-term-env new-body avoid-3 a-3)))
      a-4))

  (define expand-term-env ((term pseudo-termp)
                           (hints smtlink-hint-p)
                           (fn-lvls sym-int-alistp)
                           (alst pseudo-term-sym-alistp)
                           (avoid-vars symbol-listp)
                           (clock natp)
                           state
                           (a alistp))
    :guard (and (subsetp-equal (acl2::simple-term-vars term) avoid-vars)
                (subsetp-equal (strip-cdrs alst) avoid-vars))
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix term))
                   2)
    :returns (new-a alistp)
    (b* ((term (pseudo-term-fix term))
         (alst (pseudo-term-sym-alist-fix alst))
         (clock (nfix clock))
         (a (acl2::alist-fix a))
         ((unless (mbt (and (subsetp-equal (acl2::simple-term-vars term) avoid-vars)
                            (subsetp-equal (strip-cdrs alst) avoid-vars))))
          a)
         ((if (zp clock)) a)
         (exist? (assoc-equal term alst))
         ((if exist?)
          (append (replace-alist-to-bindings (list exist?) a) a))
         ((if (dont-generate-freshvar term)) a))
      (expand-fncall/lambda-env term hints fn-lvls alst avoid-vars clock state
                                a)))

  (define expand-term-list-env ((term-lst pseudo-term-listp)
                                (hints smtlink-hint-p)
                                (fn-lvls sym-int-alistp)
                                (alst pseudo-term-sym-alistp)
                                (avoid-vars symbol-listp)
                                (clock natp)
                                state
                                (a alistp))
    :guard (and (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid-vars)
                (subsetp-equal (strip-cdrs alst) avoid-vars))
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-list-fix term-lst))
                   0)
    :returns (new-a alistp)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (alst (pseudo-term-sym-alist-fix alst))
         (clock (nfix clock))
         (a (acl2::alist-fix a))
         ((unless (mbt (and (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid-vars)
                            (subsetp-equal (strip-cdrs alst) avoid-vars))))
          a)
         ((unless (consp term-lst)) a)
         ((cons term-hd term-tl) term-lst)
         ((mv & alst-1 avoid-1)
          (expand-term term-hd hints fn-lvls alst avoid-vars clock state))
         (a-1 (expand-term-env term-hd hints fn-lvls alst avoid-vars clock
                               state a)))
      (expand-term-list-env term-tl hints fn-lvls alst-1 avoid-1 clock state
                            a-1))))

(verify-guards expand-term-env
  :hints (("Goal" :in-theory (e/d (pseudo-lambda/fnp dont-generate-freshvar)
                                  ()))))

stop-here

(defthm crock2
  (implies (cdr (assoc-equal term alst))
           (equal (car (assoc-equal term alst)) term)))

(defthm-expand-term-env-flag
  (defthm correctness-of-expand-fncall/lambda
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (pseudo-termp avoid-term)
                  (natp clock)
                  (alistp a))
             (equal (ev-smtcp
                     (mv-nth 0 (expand-fncall/lambda term hints fn-lvls alst
                                                     avoid-term clock state))
                     (mv-nth 0 (expand-fncall/lambda-env term hints fn-lvls alst
                                                         avoid-term clock state
                                                         a)))
                    (ev-smtcp term a)))
    :flag expand-fncall/lambda-env
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (equal-of-new-var-for-term-env
                                    equal-of-new-vars-for-term-list-env)
                                   (symbol-listp
                                    ;; equivalence-of-expand-term-list-with-env
                                    ;; equivalence-of-expand-term-with-env
                                    ;; correctness-of-new-var-for-term
                                    ;; correctness-of-function-substitution
                                    ;; correctness-of-new-vars-for-term-list
                                    ;; ev-smtcp-of-fncall-args
                                    ))
                              :expand ((expand-fncall/lambda term hints fn-lvls
                                                             alst avoid-term clock state)
                                       (expand-fncall/lambda-env term hints fn-lvls
                                                                 alst avoid-term clock
                                                                 state a)
                                       (expand-fncall/lambda nil hints fn-lvls
                                                             alst avoid-term clock state)
                                       (expand-fncall/lambda-env nil hints fn-lvls
                                                                 alst avoid-term clock
                                                                 state a)
                                       (expand-fncall/lambda term hints fn-lvls alst avoid-term
                                                             0 state)
                                       (expand-fncall/lambda-env term hints fn-lvls alst
                                                                 avoid-term 0 state a))))))
  (defthm correctness-of-expand-term
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (pseudo-termp avoid-term)
                  (natp clock)
                  (alistp a))
             (equal (ev-smtcp
                     (mv-nth 0 (expand-term term hints fn-lvls alst avoid-term
                                            clock state))
                     (mv-nth 0 (expand-term-env term hints fn-lvls alst
                                                avoid-term clock state a)))
                    (ev-smtcp term a)))
    :flag expand-term-env
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-term term hints fn-lvls alst avoid-term
                                         clock state)
                            (expand-term-env term hints fn-lvls alst avoid-term
                                             clock state a)
                            (expand-term term hints fn-lvls alst avoid-term
                                         0 state)
                            (expand-term-env term hints fn-lvls alst avoid-term
                                             0 state a)
                            (expand-term nil hints fn-lvls alst avoid-term
                                         clock state)
                            (expand-term-env nil hints fn-lvls alst avoid-term
                                             clock state a))))))
  (defthm correctness-of-expand-term-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-term-listp term-lst)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (pseudo-termp avoid-term)
                  (natp clock)
                  (alistp a))
             (equal (ev-smtcp-lst
                     (mv-nth 0 (expand-term-list term-lst hints fn-lvls alst
                                                 avoid-term clock state))
                     (mv-nth 0 (expand-term-list-env term-lst hints fn-lvls alst
                                                     avoid-term clock state
                                                     a)))
                    (ev-smtcp-lst term-lst a)))
    :flag expand-term-list-env
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-term-list term-lst hints fn-lvls alst
                                              avoid-term clock state)
                            (expand-term-list-env term-lst hints fn-lvls alst
                                                  avoid-term clock state a)
                            (expand-term-list nil hints fn-lvls alst
                                              avoid-term clock state)
                            (expand-term-list-env nil hints fn-lvls alst
                                                  avoid-term clock state
                                                  a))))))
  :hints(("Goal"
          :in-theory (disable member-equal))))

stop

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

stop

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

(defthm-expand-term-flag
  (defthm correctness-of-expand-fncall/lambda
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp
                   (mv-nth 0 (expand-fncall/lambda term hints fn-lvls alst
                                                   names clock state))
                   (mv-nth 0 (expand-fncall/lambda-env term hints fn-lvls alst
                                                       names clock state a))))
             (ev-smtcp term a))
    :flag expand-fncall/lambda
    :hints ((and stable-under-simplificationp
                 '(;; :in-theory (e/d () (genequalities-of-acons
                   ;;                     pseudo-term-sym-alistp-of-cons
                   ;;                     pseudo-term-listp-of-symbol-listp))
                   :expand ((expand-fncall/lambda term hints fn-lvls
                                                  alst names clock state)
                            (expand-fncall/lambda-env term hints fn-lvls
                                                      alst names clock state a)
                            (expand-fncall/lambda nil hints fn-lvls
                                                  alst names clock state)
                            (expand-fncall/lambda-env nil hints fn-lvls
                                                      alst names clock state a)
                            (expand-fncall/lambda term hints fn-lvls alst names
                                                  0 state)
                            (expand-fncall/lambda-env term hints fn-lvls alst names
                                                      0 state a))
                   ))))
  (defthm correctness-of-expand-term
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp
                   (mv-nth 0 (expand-term term hints fn-lvls alst names clock
                                          state))
                   (mv-nth 0 (expand-term-env term hints fn-lvls alst names
                                              clock state a))))
             (ev-smtcp term a))
    :flag expand-term
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-term term hints fn-lvls alst names
                                         clock state)
                            (expand-term-env term hints
                                             fn-lvls alst names clock state a)
                            (expand-term term hints fn-lvls alst names
                                         0 state)
                            (expand-term-env term
                                             hints fn-lvls alst names 0 state a)
                            (expand-term nil hints fn-lvls alst names
                                         clock state)
                            (expand-term-env nil hints fn-lvls alst names
                                             clock state a))
                   ))))
  (defthm correctness-of-expand-term-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-term-listp term-lst)
                  (smtlink-hint-p hints)
                  (sym-int-alistp fn-lvls)
                  (pseudo-term-sym-alistp alst)
                  (symbol-listp names)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp-lst
                   (mv-nth 0 (expand-term-list term-lst hints fn-lvls alst
                                               names clock state))
                   (mv-nth 0 (expand-term-list-env term-lst hints fn-lvls alst
                                                   names clock state a))))
             (ev-smtcp-lst term-lst a))
    :flag expand-term-list
    :hints ((and stable-under-simplificationp
                 '(:expand ((expand-term-list term-lst hints fn-lvls alst
                                              names clock state)
                            (expand-term-list-env term-lst hints fn-lvls alst
                                                  names clock state a)
                            (expand-term-list nil hints fn-lvls alst
                                              names clock state)
                            (expand-term-list-env nil hints fn-lvls alst
                                                  names clock state a))
                   ))))
  :hints(("Goal"
          :in-theory (disable member-equal))))


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
