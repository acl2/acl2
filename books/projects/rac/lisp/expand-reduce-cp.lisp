;; Mayank Manjrekar <mankmonjre@gmail.com>
;; Feb 2024

(in-package "ACL2")

(include-book "clause-processors/term-vars" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "meta/pseudo-termp-lemmas" :dir :system)
(include-book "misc/hons-help" :dir :system)

(defevaluator ercp-ev ercp-ev-lst
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b)
   (mv-nth a b)
   (cons a b))
  :namedp t)

(def-meta-extract ercp-ev ercp-ev-lst)

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

(defines push-mv-nths
  ;; push mv-nths through if blocks
  :flag-local nil
  (define push-mv-nths ((term pseudo-termp))
    (cond ((and (equal (len term) 3)
                (eq (car term) 'mv-nth)
                (equal (len (caddr term)) 4)
                (eq (caaddr term) 'if))
           (b* ((mv-num (cadr term))
                (if-expr (caddr term))
                (test (cadr if-expr))
                (t-br (caddr if-expr))
                (f-br (cadddr if-expr))
                (test (push-mv-nths test))
                (t-br (push-mv-nths (hons-list 'mv-nth mv-num t-br)))
                (f-br (push-mv-nths (hons-list 'mv-nth mv-num f-br))))
             (hons-list 'if test t-br f-br)))
          ((and (equal (len term) 3)
                (eq (car term) 'mv-nth)
                (equal (len (caddr term)) 3)
                (eq (caaddr term) 'cons))
           (b* ((mv-num (cadr term))
                (mv-term (caddr term)))
             (if (and (quotep mv-num)
                      (natp (unquote mv-num)))
                 (b* ((mv-num (unquote mv-num)))
                   (if (eql mv-num 0)
                       (push-mv-nths (cadr mv-term))
                     (b* ((mv-num (kwote (1- mv-num))))
                       (push-mv-nths (hons-list 'mv-nth mv-num (caddr mv-term))))))
               (hons-list 'mv-nth mv-num (push-mv-nths mv-term)))))
          ((or (atom term)
               (quotep term))
           term)
          (t
           (hons (car term) (push-mv-nths-args (cdr term))))))
  (define push-mv-nths-args ((terms pseudo-term-listp))
    (if (consp terms)
        (hons (push-mv-nths (car terms))
              (push-mv-nths-args (cdr terms)))
      terms)))

(local
 (defthm len-push-mv-nths-args
   (equal (len (push-mv-nths-args x)) (len x))
   :hints (("Goal" :in-theory (e/d (push-mv-nths-args) ())))))

(local
 (defthm-push-mv-nths-flag
   (defthm return-type-of-push-mv-nths
     (implies (pseudo-termp term)
              (pseudo-termp (push-mv-nths term)))
     :flag push-mv-nths)
   (defthm return-type-of-push-mv-nths-args
     (implies (pseudo-term-listp terms)
              (pseudo-term-listp (push-mv-nths-args terms)))
     :flag push-mv-nths-args)
   :hints (("Goal" :in-theory (e/d (push-mv-nths-args
                                    push-mv-nths) ()))
           (and stable-under-simplificationp
                '(:expand ((pseudo-termp (cons (car term)
                                          (push-mv-nths-args (cdr term))))))))))

(local
 (defthm pseudo-term-listp-of-two-symbol-listp
   (implies (and (symbol-listp x) (symbol-listp y))
            (pseudo-term-substp (pairlis$ x y)))))

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
      (b* ((fns (cons 'mv-list fns))
           (lhs (cadar cl))
           (rhs (caddar cl))
           (lhs-vars (simple-term-vars lhs))
           (rhs-vars (simple-term-vars rhs))
           ((mv ok lhs) (expand-all lhs (pairlis$ lhs-vars lhs-vars) fns state))
           ((unless ok) (mv nil (list cl) state))
           ((mv ok rhs) (expand-all rhs (pairlis$ rhs-vars rhs-vars) fns state))
           ((unless ok) (mv nil (list cl) state))
           (lhs (push-mv-nths lhs))
           (rhs (push-mv-nths rhs)))
        (if (hons-equal lhs rhs)
            (mv nil '(('t)) state)
          (b* ((- (cw "~%expand-reduce clause-processor failed!~%")))
          (mv nil `(((equal ,lhs ,rhs))) state))))
    (mv nil (list cl) state)))

;; The following is borrowed from clause-processors/unify-substs.lisp. It
;; creates an alist of evaluated substitutions for a given subsitution `substs`
;; under the environment `al`.
(local
 (define ercp-ev-alist (substs al)
   :verify-guards nil
   (if (atom substs)
       nil
     (cons (cons (caar substs) (ercp-ev (cdar substs) al))
           (ercp-ev-alist (cdr substs) al)))
   ///
   (defthm assoc-equal-ercp-ev-alist
     (equal (cdr (assoc-equal k (ercp-ev-alist substs al)))
            (ercp-ev (cdr (assoc-equal k substs)) al)))

   (defthm assoc-equal-ercp-ev-alist-iff
     (implies k
              (iff (assoc-equal k (ercp-ev-alist substs al))
                   (assoc-equal k substs))))

   (defthm assoc-equal-ercp-ev-alist-when-assoc
     (implies (assoc k substs)
              (assoc k (ercp-ev-alist substs al))))

   (defthm ercp-ev-alist-pairlis$
     (equal (ercp-ev-alist (pairlis$ a b) al)
            (pairlis$ a
                      (ercp-ev-lst b al))))

   (defthm ercp-ev-alist-of-cons
     (equal (ercp-ev-alist (cons x y) a)
            (cons (cons (car x) (ercp-ev (cdr x) a))
                  (ercp-ev-alist y a))))))

;; Assuming (ercp-ev-global-facts), meta-extract-formula produces a theorem
(local
 (defthm ercp-ev-formula
   (implies (and (ercp-ev-meta-extract-global-facts)
                 (equal (w st) (w state)))
            (ercp-ev (meta-extract-formula name st) a))
   :hints(("Goal" :use ((:instance ercp-ev-meta-extract-global-badguy-sufficient
                         (obj (list :formula name))))))))

(local
 (defthm ercp-ev-fn-get-def
   (b* (((mv ok formals body) (fn-get-def fn st)))
     (implies (and ok
                   (ercp-ev-meta-extract-global-facts)
                   (equal (w st) (w state))
                   (equal (len args) (len formals)))
              (equal (ercp-ev (cons fn args) a)
                     (ercp-ev body (pairlis$ formals
                                             (ercp-ev-lst args a))))))
   :hints(("Goal" :in-theory (e/d (ercp-ev-of-fncall-args
                                   acl2::match-tree-opener-theory
                                   acl2::match-tree-alist-opener-theory)
                                  (ercp-ev-formula
                                   meta-extract-global-fact+
                                   meta-extract-formula
                                   take))
                  :use ((:instance ercp-ev-formula
                         (name fn)
                         (acl2::st st)
                         (a (pairlis$ (mv-nth 1 (fn-get-def fn st))
                                      (ercp-ev-lst args a)))))))))

;; If expand-all returns ok, the evaluation of the redux is equal to the
;; evalation of the original term under a different environment
;; `(ercp-ev-alist substs alist)`.
(local
 (defthm-expand-all-flag
   (defthm expand-all-correct
     (b* (((mv ok redux) (expand-all term substs fns state)))
       (implies (and ok
                     (ercp-ev-meta-extract-global-facts))
                (equal (ercp-ev redux alist)
                       (ercp-ev term (ercp-ev-alist substs alist)))))
     :flag expand-all)
   (defthm expand-all-lst-correct
     (b* (((mv ok redux-lst) (expand-all-lst terms substs fns state)))
       (implies (and ok
                     (ercp-ev-meta-extract-global-facts))
                (equal (ercp-ev-lst redux-lst alist)
                       (ercp-ev-lst terms (ercp-ev-alist substs alist)))))
     :flag expand-all-lst)
   :hints (("Goal" :expand ()
                   :in-theory (e/d (expand-all
                                    expand-all-lst
                                    simple-term-vars-lst
                                    simple-term-vars
                                    ercp-ev-of-fncall-args)
                                   (ercp-ev-fn-get-def)))
           ("Subgoal *1/4"
            :use ((:instance ercp-ev-fn-get-def
                   (fn (car term))
                   (args (cdr term))
                   (state state)
                   (st state)
                   (a (ercp-ev-alist substs alist))))))))

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
       (equal (ercp-ev x (ercp-ev-alist substs a))
              (ercp-ev (substitute-in-term x substs) a))
       :hints ((and stable-under-simplificationp
                    '(:in-theory (enable ercp-ev-of-fncall-args))))
       :flag substitute-in-term)
     (defthm eval-of-substitute-in-lst
       (equal (ercp-ev-lst x (ercp-ev-alist substs a))
              (ercp-ev-lst (substitute-in-lst x substs) a))
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
                   (ercp-ev-meta-extract-global-facts)
                   (pseudo-termp term))
              (equal (ercp-ev redux alist)
                     (ercp-ev term alist))))
   :hints (("Goal" :in-theory (e/d () (ercp-ev-alist-pairlis$))))))

(local
 (defthm mv-nth-of-cons-alt
   (implies (posp n)
            (equal (mv-nth n (cons a b))
                   (mv-nth (1- n) b)))
   :hints (("Goal" :in-theory (e/d (mv-nth) ())))))

(local
 (defthm-push-mv-nths-flag correctness-of-push-mv-nth-lemma
   (defthmd correctness-of-push-mv-nth
     (b* ((redux (push-mv-nths term)))
       (implies (pseudo-termp term)
                (equal (ercp-ev redux alist)
                       (ercp-ev term alist))))
     :flag push-mv-nths)
   (defthmd correctness-of-push-mv-nth-args
     (b* ((redux (push-mv-nths-args terms)))
       (implies (pseudo-term-listp terms)
                (equal (ercp-ev-lst redux alist)
                       (ercp-ev-lst terms alist))))
     :flag push-mv-nths-args)
   :hints (("Goal" :in-theory (e/d (push-mv-nths
                                    push-mv-nths-args
                                    ercp-ev-of-fncall-args) ())))))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm expand-reduce-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp alist)
                (ercp-ev-meta-extract-global-facts)
                (ercp-ev (conjoin-clauses
                        (clauses-result
                         (expand-reduce-cp cl fns state)))
                       alist))
           (ercp-ev (disjoin cl) alist))
  :hints (("Goal" :in-theory (e/d (expand-reduce-cp
                                   disjoin)
                                  ())
                  :use ((:instance correctness-of-expand-all
                         (term (cadr (car cl)))
                         (fns (cons 'mv-list fns)))
                        (:instance correctness-of-expand-all
                         (term (caddr (car cl)))
                         (fns (cons 'mv-list fns)))
                        (:instance correctness-of-push-mv-nth
                         (term (mv-nth
                                1
                                (expand-all (cadr (car cl))
                                            (pairlis$ (simple-term-vars (cadr (car cl)))
                                                      (simple-term-vars (cadr (car cl))))
                                            (cons 'mv-list fns)
                                            state))))
                        (:instance correctness-of-push-mv-nth
                         (term (mv-nth
                                1
                                (expand-all (caddr (car cl))
                                            (pairlis$ (simple-term-vars (caddr (car cl)))
                                                      (simple-term-vars (caddr (car cl))))
                                            (cons 'mv-list fns)
                                            state)))))
                  :do-not-induct t))
  :rule-classes :clause-processor)
