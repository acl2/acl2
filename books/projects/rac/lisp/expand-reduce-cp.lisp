;; Mayank Manjrekar <mankmonjre@gmail.com>
;; Oct 2023

(in-package "ACL2")

(include-book "clause-processors/term-vars" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "meta/pseudo-termp-lemmas" :dir :system)

;; expand-all beta reduces all lambda applications, and expands function
;; applications for functions in the list of function symbols `fns`.
(defines expand-all
  :flag-local nil
  :verify-guards nil
  :measure-debug t
  (define expand-all ((term pseudo-termp)
                       (substs pseudo-term-substp)
                       (fns symbol-listp)
                       state)
    :measure (if (consp fns)
                 (cons (cons 1 (len fns)) (acl2-count term))
               (acl2-count term))
    :returns (mv (ok booleanp)
                 (redux pseudo-termp
                        :hyp
                        (and (pseudo-termp term)
                             (pseudo-term-substp substs))))
    (cond
     ((atom term)
      ;; return substitution from substs. default is nil.
      (if (and term (mbt (symbolp term)))
          (mv t (cdr (assoc term substs)))
        (mv nil nil)))
     ((quotep term)
      (mv t term))
     ((flambda-applicationp term)
      ;; term is a lambda application. We expand the actuals first, and
      ;; substitute the arguments into the lambda body.
      (b* (((mv ok reduced-args) (expand-all-lst (fargs term) substs fns state))
           (fn (ffn-symb term))
           (formals (lambda-formals fn))
           (body (lambda-body fn))
           (substs (pairlis$ formals reduced-args)))
        (if ok
            (expand-all body substs fns state)
          (mv nil nil))))
     (t
      ;; term is a function application. We expand actuals first, and
      ;; substitute the arguments into the body obtained from fn-get-def.
      (b* ((fn (ffn-symb term))
           ((mv ok reduced-args) (expand-all-lst (fargs term) substs fns state))
           ((unless ok) (mv nil nil)))
        (if (member fn fns)
            (b* (((mv ok formals body) (fn-get-def fn state))
                 ((unless (and ok
                               ;; The following two conditions are necessary
                               ;; for guard proof and proof of correctness
                               ;; respectively.
                               (pseudo-termp body)
                               (equal (len formals) (len (fargs term)))))
                  (mv nil nil))
                 (fns (remove1 fn fns))
                 (substs (pairlis$ formals reduced-args)))
              (expand-all body substs fns state))
          (mv t (hons fn reduced-args)))))))
  (define expand-all-lst ((terms pseudo-term-listp)
                           (substs pseudo-term-substp)
                           (fns symbol-listp)
                           state)
    :measure  (if (consp fns)
                  (cons (cons 1 (len fns)) (acl2-count terms))
                (acl2-count terms))
    :returns (mv (ok booleanp)
                 (redux-list pseudo-term-listp
                             :hyp
                             (and (pseudo-term-listp terms)
                                  (pseudo-term-substp substs))))
    (if (atom terms)
        (mv t nil)
      (b* (((mv ok first) (expand-all (car terms) substs fns state))
           ((unless ok) (mv nil nil))
           ((mv ok rest) (expand-all-lst (cdr terms) substs fns state)))
        (if ok
            (mv t (hons first rest))
          (mv nil nil)))))

  :prepwork
  ((local
    (defthm len-of-remove1-equal-member
      (implies (member x y)
               (equal (len (remove1 x y)) (1- (len y)))))))

  ///
  (local
   (encapsulate ()
     (defthm consp-len-lst
       (and (implies (consp x)
                     (not (equal (len x) 0)))
            (implies (not (consp x))
                     (equal (len x) 0))))
     (defthm true-listp-when-symbol-listp
       (implies (symbol-listp x)
                (true-listp x)))
     (defthm symbol-listp-of-remove1
       (implies (symbol-listp y)
                (symbol-listp (remove1 x y))))
     (defthm alistp-not-consp
       (implies (and (alistp x)
                     (not (consp (assoc-equal y x))))
                (not (assoc-equal y x))))
     (defthm alistp-of-pseudo-term-substp
       (implies (pseudo-term-substp x)
                (alistp x))
       :hints (("Goal" :in-theory (e/d (pseudo-term-substp) ()))))))

  (verify-guards expand-all))

(define expand-reduce-cp ((cl pseudo-term-listp)
                          fns ;; symbol-listp
                          state)
  :returns (mv (ok booleanp)
               (cl-list pseudo-term-list-listp
                        :hyp
                        (pseudo-term-listp cl))
               state)
  (if (and (symbol-listp fns)
           (equal (len cl) 1)
           (consp (car cl))
           (eql (caar cl) 'equal))
      (b* ((lhs (cadar cl))
           (rhs (caddar cl))
           (lhs-vars (simple-term-vars lhs))
           (rhs-vars (simple-term-vars rhs))
           ((mv ok lhs) (expand-all lhs (pairlis$ lhs-vars lhs-vars) fns state))
           ((unless ok) (mv nil (list cl) state))
           ((mv ok rhs) (expand-all rhs (pairlis$ rhs-vars rhs-vars) fns state))
           ((unless ok) (mv nil (list cl) state)))
        (if (hons-equal lhs rhs)
            (mv nil '(('t)) state)
          (mv nil `(((equal ,lhs ,rhs))) state)))
    (mv nil (list cl) state))

  :prepwork
  ((local
    (defthm pseudo-term-listp-of-two-symbol-listp
      (implies (and (symbol-listp x) (symbol-listp y))
               (pseudo-term-substp (pairlis$ x y)))))))

;; The following is borrowed from clause-processors/unify-substs.lisp. It
;; creates an alist of evaluated substitutions for a given subsitution `substs`
;; under the environment `al`.
(local
 (define mextract-ev-alist (substs al)
   :verify-guards nil
   (if (atom substs)
       nil
     (cons (cons (caar substs) (mextract-ev (cdar substs) al))
           (mextract-ev-alist (cdr substs) al)))
   ///
   (defthm assoc-equal-mextract-ev-alist
     (equal (cdr (assoc-equal k (mextract-ev-alist substs al)))
            (mextract-ev (cdr (assoc-equal k substs)) al)))

   (defthm assoc-equal-mextract-ev-alist-iff
     (implies k
              (iff (assoc-equal k (mextract-ev-alist substs al))
                   (assoc-equal k substs))))

   (defthm assoc-equal-mextract-ev-alist-when-assoc
     (implies (assoc k substs)
              (assoc k (mextract-ev-alist substs al))))

   (defthm mextract-ev-alist-pairlis$
     (equal (mextract-ev-alist (pairlis$ a b) al)
            (pairlis$ a
                      (mextract-ev-lst b al))))

   (defthm mextract-ev-alist-of-cons
     (equal (mextract-ev-alist (cons x y) a)
            (cons (cons (car x) (mextract-ev (cdr x) a))
                  (mextract-ev-alist y a))))))

;; If expand-all returns ok, the evaluation of the redux is equal to the
;; evalation of the original term under a different environment
;; `(mextract-ev-alist substs alist)`.
(local
 (defthm-expand-all-flag
   (defthm expand-all-correct
     (b* (((mv ok redux) (expand-all term substs fns state)))
       (implies (and ok
                     (mextract-ev-global-facts))
                (equal (mextract-ev redux alist)
                       (mextract-ev term (mextract-ev-alist substs alist)))))
     :flag expand-all)
   (defthm expand-all-lst-correct
     (b* (((mv ok redux-lst) (expand-all-lst terms substs fns state)))
       (implies (and ok
                     (mextract-ev-global-facts))
                (equal (mextract-ev-lst redux-lst alist)
                       (mextract-ev-lst terms (mextract-ev-alist substs alist)))))
     :flag expand-all-lst)
   :hints (("Goal" :expand ()
                   :in-theory (e/d (expand-all
                                    expand-all-lst
                                    simple-term-vars-lst
                                    simple-term-vars
                                    mextract-ev-of-fncall-args)
                                   (mextract-ev-fn-get-def)))
           ("Subgoal *1/4"
            :use ((:instance mextract-ev-fn-get-def
                   (fn (car term))
                   (args (cdr term))
                   (state state)
                   (st state)
                   (a (mextract-ev-alist substs alist))))))))

;; NOTE: This is different from sublis-var1 in that the default mapping for a
;; variable in sublis-var1 is x -> x, while in substitute-in-term, the default
;; mapping is x -> nil. This makes the statement of the theorem
;; substitute-in-term-correct simple.
(local
 (defines substitute-in-term
   (define substitute-in-term ((x pseudo-termp)
                               (substs alistp))
     :returns (xx pseudo-termp
                  :hyp (and (pseudo-termp x)
                            (pseudo-term-substp substs))
                  :hints ((and stable-under-simplificationp
                               '(:expand ((pseudo-termp x))))))
     (cond ((atom x)
            (and x (mbt (symbolp x))
                 (cdr (assoc-equal x substs))))
           ((eq (car x) 'quote) x)
           (t (cons (car x) (substitute-in-lst (cdr x) substs)))))
   (define substitute-in-lst ((x pseudo-term-listp)
                              (substs alistp))
     :returns (xx (and (implies (and (pseudo-term-listp x)
                                     (pseudo-term-substp substs))
                                (pseudo-term-listp xx))
                       (equal (len xx) (len x))))
     (if (atom x)
         nil
       (cons (substitute-in-term (car x) substs)
             (substitute-in-lst (cdr x) substs))))
   ///
   (defthm-substitute-in-term-flag
     eval-of-substitute-in-term-lemma
     (defthm eval-of-substitute-in-term
       (equal (mextract-ev x (mextract-ev-alist substs a))
              (mextract-ev (substitute-in-term x substs) a))
       :hints ((and stable-under-simplificationp
                    '(:in-theory (enable mextract-ev-of-fncall-args))))
       :flag substitute-in-term)
     (defthm eval-of-substitute-in-lst
       (equal (mextract-ev-lst x (mextract-ev-alist substs a))
              (mextract-ev-lst (substitute-in-lst x substs) a))
       :flag substitute-in-lst))))

;; We now wish to show that the substitution-in-term of a term under an
;; identity substitution in which all free variables are accounted for is the
;; same term. See substitute-in-term-of-id lemma.

(local
 (defthm assoc-pairlis$-id
  (equal (assoc-equal x (pairlis$ y y))
         (if (member x y)
             (cons x x)
           nil))
  :hints (("Goal" :in-theory (e/d () ())))))

(local (set-induction-depth-limit 3))

(local
 (defthm subsetq-of-union-equal-1
  (equal (subsetp (union-equal k1 k2) v)
         (and (subsetp k1 v)
              (subsetp k2 v)))
  :hints (("Goal" :induct (len k1)))))

(local
 (defthm subsetp-id-1
  (implies (subsetp x y)
           (subsetp x (cons z y)))
  :hints (("Goal" :in-theory (e/d () ())))))

(local
 (defthm subsetp-id
  (subsetp x x)))

(local
 (defthm-simple-term-vars-flag
   substitute-in-term-identity-lemma
   (defthm substitute-in-term-of-id
     (b* ((subst (pairlis$ vars vars)))
       (implies (and (pseudo-termp x)
                     (subsetp (simple-term-vars x) vars))
                (equal (substitute-in-term x subst)
                       x)))
     :flag simple-term-vars)
   (defthm substitute-in-list-of-id
     (b* ((subst (pairlis$ vars vars)))
       (implies (and (pseudo-term-listp x)
                     (subsetp (simple-term-vars-lst x) vars))
                (equal (substitute-in-lst x subst)
                       x)))
     :flag simple-term-vars-lst)
   :hints (("Goal" :in-theory (e/d (simple-term-vars
                                    simple-term-vars-lst
                                    substitute-in-lst
                                    substitute-in-term)
                                   ())))))

;; Combining expand-all-correct, eval-of-substitute-in-term, and
;; substitute-in-term-of-id, we obtain correctness-of-expand-all

(local
 (defthmd correctness-of-expand-all
   (b* ((vars (simple-term-vars term))
        (substs (pairlis$ vars vars))
        ((mv ok redux) (expand-all term substs fns state)))
     (implies (and ok
                   (mextract-ev-global-facts)
                   (pseudo-termp term))
              (equal (mextract-ev redux alist)
                     (mextract-ev term alist))))
   :hints (("Goal" :in-theory (e/d () (mextract-ev-alist-pairlis$))))))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm expand-reduce-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp alist)
                (mextract-ev-global-facts)
                (mextract-ev (conjoin-clauses
                              (clauses-result
                               (expand-reduce-cp cl fns state)))
                             alist))
           (mextract-ev (disjoin cl) alist))
  :hints (("Goal" :in-theory (e/d (expand-reduce-cp
                                   disjoin) ())
                  :use ((:instance correctness-of-expand-all
                         (term (cadr (car cl))))
                        (:instance correctness-of-expand-all
                         (term (caddr (car cl)))))
                  :do-not-induct t))
  :rule-classes :clause-processor)
