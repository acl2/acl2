; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Alessandro Coglio, Eric Smith, and Stephen Westfold for discussions
; that contributed to the design of the utility, address-subterm-governors-lst.
; Moreover, Eric Smith modified the book to increase certification speed (by
; adding in-theory events and hints).

; See the top of pattern-matching-ext.lisp for comments describing what this
; that book is trying to accomplish.  That book includes this one, which
; includes lemmas to support some guard verification and also includes code
; comments.  Since this book is included locally in pattern-matching-ext.lisp,
; we don't bother to mark lemmas below as local.

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/std/basic/symbol-package-name-non-cl" :dir :system)

(local (in-theory (disable mv-nth)))
(local (in-theory (disable true-listp))) ;for speed
(local (in-theory (disable reverse))) ;for speed

(defund drop-formals (formals actuals vars acc-f acc-a)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp actuals)
                              (true-listp vars)
                              (true-listp acc-f)
                              (true-listp acc-a))))

; At the top level, acc-f and acc-a are nil, and we return (mv formals'
; actuals'), where formals' and actuals' are the sublists of formals and
; actuals such that for each formal that is not a member of vars, we drop both
; that formal and the corresponding actual.  Moreover, if every remaining
; formal equals its corresponding remaining actual, we drop all formals and
; actuals.  We accumulate into acc-f and acc-a to obtain reversed formals' and
; actuals', resp.

  (cond ((endp formals)
         (cond ((equal acc-f acc-a)
                (mv nil nil))
               (t
                (mv (reverse acc-f) (reverse acc-a)))))
        ((not (member-eq (car formals) vars))
         (drop-formals (cdr formals) (cdr actuals) vars acc-f acc-a))
        (t
         (drop-formals (cdr formals) (cdr actuals) vars
                       (cons (car formals) acc-f)
                       (cons (car actuals) acc-a)))))

(assert-event
 (mv-let (new-formals new-actuals)
   (let* ((term '((LAMBDA (X A) (LEN (CAR A))) (CAR A) A))
          (fn (ffn-symb term))
          (formals (lambda-formals fn))
          (body (lambda-body fn))
          (vars (all-vars body))
          (actuals (fargs term)))
     (drop-formals formals actuals vars nil nil))
   (and (null new-formals)
        (null new-actuals))))

(defthm symbol-listp-revappend ; for symbol-listp-mv-nth-0-drop-formals
  (implies (symbol-listp x)
           (equal (symbol-listp (revappend x y))
                  (symbol-listp y))))

(defthm symbol-listp-mv-nth-0-drop-formals
  (implies (and (symbol-listp formals)
                (symbol-listp acc-f))
           (symbol-listp
            (mv-nth 0 (drop-formals formals actuals vars acc-f acc-a))))
  :rule-classes
  ((:forward-chaining
    :trigger-terms ((mv-nth 0 (drop-formals formals actuals vars acc-f acc-a)))))
  :hints (("Goal" :in-theory (enable drop-formals reverse))))

(defthm true-listp-revappend ; for true-listp-mv-nth-1-drop-formals
  (implies (true-listp x)
           (equal (true-listp (revappend x y))
                  (true-listp y)))
  :hints (("Goal" :in-theory (enable true-listp))))

(defthm true-listp-mv-nth-1-drop-formals
  (implies (force (true-listp acc-a))
           (true-listp
            (mv-nth 1 (drop-formals formals actuals vars acc-f acc-a))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable drop-formals reverse))))

; The following is adapted directly from axioms.lisp, 8/6/2017; see all-vars1
; and all-vars1-lst in that file.
(encapsulate
  ()
  (local
   (defun all-vars1/all-vars1-lst (flg lst ans)
     (if (eq flg 'all-vars1)
         (cond ((variablep lst) (add-to-set-eq lst ans))
               ((fquotep lst) ans)
               (t (all-vars1/all-vars1-lst 'all-vars-lst1 (cdr lst) ans)))
       (cond ((endp lst) ans)
             (t (all-vars1/all-vars1-lst 'all-vars-lst1 (cdr lst)
                                         (all-vars1/all-vars1-lst 'all-vars1 (car lst) ans)))))))

  (local
   (defthm step-1-lemma
     (equal (all-vars1/all-vars1-lst flg lst ans)
            (if (equal flg 'all-vars1) (all-vars1 lst ans) (all-vars1-lst lst ans)))))

  (local
   (defthm step-2-lemma
     (implies (and (symbol-listp ans)
                   (if (equal flg 'all-vars1)
                       (pseudo-termp lst)
                     (pseudo-term-listp lst)))
              (symbol-listp (all-vars1/all-vars1-lst flg lst ans)))))

  (defthm symbol-listp-all-vars1
    (implies (and (symbol-listp ans)
                  (pseudo-termp lst))
             (symbol-listp (all-vars1 lst ans)))
    :hints (("Goal" :use (:instance step-2-lemma (flg 'all-vars1))))))

; Start support for guard proof for ext-make-lambda-application.

(defthm len-revappend
  (equal (len (revappend x y))
         (+ (len x) (len y))))

(defthm drop-formals-preserves-equal-len
  (implies (and (true-listp actuals)
                (symbol-listp formals)
                (equal (len acc-f) (len acc-a)))
           (equal (len (mv-nth 0 (drop-formals formals actuals vars
                                          acc-f acc-a)))
                  (len (mv-nth 1
                               (drop-formals formals actuals vars
                                             acc-f acc-a)))))
  :hints (("Goal" :in-theory (enable drop-formals reverse))))

(defthm equal-len-0-rewrite
  (equal (equal (len x) 0)
         (not (consp x))))

(defthm drop-formals-preserves-equal-len-0
  (implies (and (true-listp actuals)
                (symbol-listp formals))
           (iff (mv-nth 1
                        (drop-formals formals actuals (all-vars1 body nil)
                                      nil nil))
                (mv-nth 0 (drop-formals formals actuals (all-vars1 body nil)
                                   nil nil))))
  :hints (("Goal"
           :in-theory (disable drop-formals-preserves-equal-len)
           :use ((:instance drop-formals-preserves-equal-len
                            (vars (all-vars1 body nil))
                            (acc-f nil)
                            (acc-a nil))))))

(defund ext-make-lambda-application (formals body actuals)

; We return a lambda application equivalent to (let ((f1 a1) ... (fn an))
; body), where formals is (f1 ... fn) and actuals is (a1 ... an).  In general
; body may contain variables not among the formals.  The result is a legal
; lambda application, in which the variables of the lambda-body are among the
; lambda-formals; moreover, we attempt to avoid needless formals.

  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-termp body)
                              (true-listp actuals)
                              (eql (len formals) (len actuals)))))
  (b* ((vars (all-vars body))
       ((mv formals actuals)
        (drop-formals formals actuals vars nil nil))
       ((when (null formals))
        (assert$ (null actuals)
                 body))
       (extra-vars (set-difference-eq vars formals))
       (formals (append? formals extra-vars))
       (actuals (append? actuals extra-vars)))
    (fcons-term (make-lambda formals body)
                actuals)))

(defun ext-new-formal (root-var n)
  (declare (xargs :mode :program))
  (intern$ (concatenate 'string
                        (symbol-name root-var)
                        "{"
                        (coerce (explode-nonnegative-integer n 10 nil)
                                'string)
                        "}")
           (symbol-package-name-non-cl root-var)))

(defun ext-maybe-rename-formal (root-var var avoid-vars n)
  (declare (xargs :mode :program))
  (cond ((member-eq var avoid-vars)
         (let ((new-var (ext-new-formal root-var n)))
           (ext-maybe-rename-formal root-var new-var avoid-vars (1+ n))))
        (t var)))

(defun ext-rename-formals (formals avoid-vars)
  (declare (xargs :mode :program))
  (cond ((endp formals) nil)
        (t (cons (ext-maybe-rename-formal (car formals) (car formals)
                                          avoid-vars 1)
                 (ext-rename-formals (cdr formals) avoid-vars)))))

(defun ext-restore-formals (old-formals new-formals bad-formals)
  (declare (xargs :mode :program))
  (cond ((endp old-formals) (mv nil nil))
        (t (mv-let (formals1 alist-new-to-old)
             (ext-restore-formals (cdr old-formals)
                                  (cdr new-formals)
                                  bad-formals)
             (cond ((member-eq (car old-formals) bad-formals)
                    (mv (cons (car new-formals) formals1)
                        alist-new-to-old))
                   (t
                    (mv (cons (car old-formals) formals1)
                        (acons (car new-formals)
                               (car old-formals)
                               alist-new-to-old))))))))

(defun ext-rename-for-substitution (formals actuals subterm body)

; This function returns a tuple (mv formals1 subterm1 body1) with properties
; explained below.

; The motivation is to substitute subterm at some address of body, but without
; capturing variables of subterm by the bindings of formals to actuals.  In
; essence we simply alpha-convert ((lambda formals body) . actuals) to ((lambda
; formals1 body1) . actuals) so that we can perform that substitution without
; capture.  However, we try to optimize by avoiding needless renaming: we map
; actuals to formals in the process of producing body1.

; Before giving a formal specification of this function, let us see how it
; works on an example.  We want to substitute the new subterm (h (f2 u v)) at
; the position of (g v) in the following term, where we view the variables of h
; as being "global", not bound by the LET:

;   (let ((u (f1 u v))
;         (v (f2 u v)))
;     (f3 u (g v)))

; Here is the translation of that term.

;   ((LAMBDA (U V) (F3 U (G V)))
;    (F1 U V)
;    (F2 U V))

; If we naively move (h (f2 u v)) inside the bindings, there is variable
; capture.  However, notice that (f2 u v) is the value of v in the bindings.
; So it is legal to substitute (h v) inside the bindings, and we should wind up
; with:

;   (let ((u (f1 u v))
;         (v (f2 u v)))
;     (f3 u (h v)))

; That is, we should get the following result.

;   (let ((formals '(u v))
;         (actuals '((f1 u v) (f2 u v)))
;         (subterm '(h (f2 u v)))
;         (body '(f3 u (g v))))
;     (ext-rename-for-substitution formals actuals subterm body))
;   = {return new (formals subterm body)
;   ((U V) (H V) (F3 U (G V)))

; On the other hand, if we aren't fortunate enough to be able to substitute
; legally inside the bindings, then we rename formals.  Here is an example:

;   (let ((formals '(u v))
;         (actuals '((f1 u v) (f2 u v)))
;         (subterm '(h u))
;         (body '(f3 u (g v))))
;     (ext-rename-for-substitution formals actuals subterm body))
;   = {return new (formals subterm body)
;   ((U{1} V) (H U) (F3 U{1} (G V)))

; Let's look at how the first of these two examples is carried out by our
; algorithm. For readability we write untranslated terms below even though we
; actually operate on translated terms.

;;;;; Start example

; The problem is to substitute (h (f2 u v)) at the position of (g v) here:

;   (let ((u (f1 u v))
;         (v (f2 u v)))
;     (f3 u (g v)))

; First alpha-convert the original term to avoid capture upon substituting (h
; (f2 u v)):

;   (let ((u1 (f1 u v))
;         (v1 (f2 u v)))
;     (f3 u1 (g v1)))

; Apply the bindings in reverse to (h (f2 u v)), to obtain (h v1).

; Now substitute (h v1) inside the bindings at the position of (g v1).

;   (let ((u1 (f1 u v))
;         (v1 (f2 u v)))
;     (f3 u1 (h v1)))

; Note that u and v don't occur in the resulting lambda-body -- equivalently,
; they don't occur in the generalized term, (h v1).  So we rename u1 and v1
; back to u and v, resp.

;   (let ((u (f1 u v))
;         (v (f2 u v)))
;     (f3 u (h v)))

;;;;; End of example

; In general, we may not be able to eliminate the captured variables from the
; subterm.  In that case, the caller may need generate extra formals beyond
; formals1 when producing the final lambda.

; The spec is simply as follows, for returned (mv formals1 subterm1 body1).
; First, (lambda formals1 body1) is an alpha-conversion of (lambda formals
; body).  Second, subterm1 is the result of generalizing subterm by mapping
; actuals to formals1.  And finally, ((lambda formals subterm) . actuals) is
; provably equal to ((lambda formals1 subterm1) . actuals); informally, the
; meaning of subterm when binding formals to actuals equals the meaning of
; subterm1 when binding formals1 to actuals.  An informal requirement is that
; formals1 only changes variables in formals when necessary.

  (declare (xargs :mode :program))
  (b* ((subterm-vars (all-vars subterm))
       (formals0 (ext-rename-formals formals subterm-vars))
       (new-subterm (sublis-expr (pairlis$ actuals formals0) subterm))
       (bad-formals (intersection-eq (all-vars new-subterm) formals))
       ((mv formals1 alist-new-to-old)
        (ext-restore-formals formals formals0 bad-formals))
       (body1 (sublis-expr (pairlis$ formals formals1) body))
       (subterm1 (sublis-expr alist-new-to-old new-subterm)))
    (mv formals1 subterm1 body1)))

(mutual-recursion

; This mutual-recursion is based on deposit-term(-lst) from the ACL2 sources.
; Here we use fcons-term instead of cons-term, to avoid any normalization, and
; also the list addr may contain 0 (one or more times), designating a dive into
; a lambda-body.

(defun ext-fdeposit-term-rec (term addr subterm)

; The basic idea is simply to walk through the given term according to the
; given address addr, and then deposit the given subterm at the destination,
; where that subterm is viewed "globally", not with respect to any
; lambda-bindings in term.  Let u be the subterm of term at address addr, and
; let B* be the lambda-bindings above that subterm; we thus obtain a term that
; we write as (bind B* u).  Assume the invariant above for the call
; (ext-fdeposit-term-rec term addr subterm).  Then we claim this fundamental
; property: the result r is provably equal to term assuming provable equality
; of the terms (bind B* u) and subterm.  Note: It is easy to prove the
; following generalization by induction in the special case that (all-vars
; subterm) is disjoint from the set of variables bound by A* and B*: Assuming
; provable equality of (bind A* (bind B* u)) with subterm, then (bind A* r) is
; provably equal to (bind A* term).

; As we deposit subterm at addr in term, we attempt to use variables
; lambda-bound in term.  We use examples to illustrate how this works as we
; address some issues.

; Example 1.  Suppose we want to substitute (len (car a)) for (length (and
; (consp x) x)) into the term (let ((x (car a))) (length (and (consp x) x))).
; Of course, those are untranslated terms; here is the corresponding call for
; translated terms.

;   (let ((term '((lambda (x) (length (if (consp x) x 'nil)))
;                 (car a)))
;         (addr '(0))
;         (subterm '(len (car a))))
;     (ext-fdeposit-term-rec term addr subterm))

; We would like the result to yield (let ((x (car a))) (len x)), or more
; accurately, its translation, ((LAMBDA (X) (LEN X)) (CAR A)).  However, the
; naive result is

;   ((LAMBDA (X A) (LEN (CAR A))) (CAR A) A)

; which could be simplified to

;   ((LAMBDA (A) (LEN (CAR A))) A)

; and then to:

;   (LEN (CAR A))

; But instead of doing such simplification, consider how we can get from the
; input term

;   ((lambda (x) (length (if (consp x) x 'nil))) (car a))

; to the desired result:

;   ((LAMBDA (X) (LEN X)) (CAR A))

; The trick is that when we enter the lambda-body, we see that X is bound to
; (CAR A), so we apply the substitution binding (CAR A) to X, thus replacing
; the term to be substituted, (len (car a)), by (len x).

; Example 2.  Capture is an issue but can sometimes be avoided.  Consider the
; following slight variant of the example above: substitute (len (car x)) for
; (length (and (consp x) x)) into the term (let ((x (car x))) (length (and
; (consp x) x))).

;   (let ((term '((lambda (x) (length (if (consp x) x 'nil)))
;                 (car x)))
;         (addr '(0))
;         (subterm '(len (car x))))
;     (ext-fdeposit-term-rec term addr subterm))

; The reasoning doesn't change: we get ((LAMBDA (X) (LEN X)) (CAR X)) by
; generalizing (car x) to x, according to the lambda-binding of x to (car x),
; in (len (car x)).

; Example 3.  But now let's change the example to illustrate the capture issue.
; We start with this (untranslated) term: (let ((x (car x))) (f x)).  Now
; substitute (g (car x) x) for (f x).  If we are careless, then we generalize
; (car x) to x as before when substituting into the body of the let (or
; lambda), which would give us (let ((x (car x))) (g x x)).  The second x,
; however, refers to the global value of x, and has thus unfortunately been
; captured by the binding!  We must basically alpha-convert before substituting
; in this case; so we start with (let ((x1 (car x))) (f x1)) and substitute (g
; (car x) x) for (f x1), yielding (let ((x1 (car x))) (g x1 x)).

; A key issue, then, is to determine when alpha-conversion is necessary; more
; specifically, to determine which lambda-bound variables need to be renamed.
; From the example above it clearly suffices to prepare to substitute and then
; see if any bound variables remain.  But Example 2 shows that this condition
; is needlessly restrictive.

; A simple solution that is clearly correct is to rename only those bound
; variables that might be necessary, then generalize and substitute, and
; finally rename back when that is legal.  Let us apply this approach to the
; examples above.  The bound variables of the lambda body is {x} in all three
; examples.  In Example 1 we are substituting (len (car a)), and there is no
; intersection {x} and free variables {a} of the term to be substituted, so no
; alpha conversion is necessary.  In Example 2, where the free variables of
; (len (car x)) is {x}, we alpha convert before substituting (with
; generalization) to obtain ((lambda (x1) (len x1)) (car x)); then we rename
; back, since there is no capture, i.e., x is not free in the lambda-body (len
; x1), and obtain the desired result ((lambda (x) (len x)) (car x)).  It
; suffices to check that x is not free in the lambda-formals, since that
; implies that x is not free in the lambda-body (if we constructed a legal
; lambda).  Now consider Example 3.  Alpha conversion is necessary as in
; Example 2, so we substitute (g (car x) x) for (f x) into ((lambda (x1) (f
; x1)) (car x)), obtaining ((lambda (x1 x) (g x1 x)) (car x) x).  We cannot
; rename back because x occurs in the lambda-formals.

; We might consider optimizing to determine in advance which variables need to
; be renamed.  But for now we'll keep it simple.

  (declare (xargs :mode :program))
  (cond
   ((endp addr) subterm)
   ((eql (car addr) 0) ; dive into the lambda-body
    (assert$
     (lambda-applicationp term)
     (b* ((fn (ffn-symb term))
          (formals (lambda-formals fn))
          (body (lambda-body fn))
          (actuals (fargs term))
          ((mv formals1 subterm1 body1)
           (ext-rename-for-substitution formals actuals subterm body))
          (body2 (ext-fdeposit-term-rec body1
                                        (cdr addr)
                                        subterm1)))
       (ext-make-lambda-application formals1 body2 actuals))))
   (t
    (fcons-term
     (ffn-symb term)
     (ext-fdeposit-term-lst (fargs term) (car addr) (cdr addr) subterm)))))

(defun ext-fdeposit-term-lst (lst n addr subterm)
  (declare (xargs :mode :program))
  (cond ((= 1 n)
         (cons (ext-fdeposit-term-rec (car lst) addr subterm)
               (cdr lst)))
        (t (cons (car lst)
                 (ext-fdeposit-term-lst (cdr lst) (1- n) addr subterm)))))

)

(defun ext-fdeposit-term (term addr subterm)

; This function returns the result of putting subterm at extended address addr
; in term.  It assumes that error checking is not necessary, i.e. that addr is
; given correctly relative to term.  Term is traversed top-down.  For examples
; see the tests below.

  (declare (xargs :mode :program))
  (ext-fdeposit-term-rec term addr subterm))

(defconst *ext-failure*

; This can be any value that is not an untranslated term.

  '(:failure))

(encapsulate
  ()
  (local (include-book "std/strings/coerce" :dir :system))
  (defthm ext-preprocess-pat-guard-helper
    (implies (and (stringp name)
                  (not (equal name "")))
             (consp (coerce name 'list)))
    :rule-classes :type-prescription))

(mutual-recursion

(defun ext-preprocess-pat (pat inside-@)

; Pat is an untranslated term.  We return the result of replacing each @ with
; (:@ _) and each @xx with (:@ _xx).  We preserve the package in the second
; case but we don't bother in the first, since _ is handled as a completely
; anonymous variable.

; We return *ext-failure*, which is not an untranslated term, if there are
; nested :@ calls after eliminating @ and @xx.  More precisely: that
; description is accurate if inside-@ is nil (as is the case for a top-level
; call), but if inside-@ is non-nil, then we allow no :@ calls.

  (declare (xargs :guard t
                  :measure (acl2-count pat)))
  (cond ((symbolp pat)
         (let ((name (symbol-name pat)))
           (cond ((equal name "@")
                  (if inside-@
                      *ext-failure*
                    (list :@ '_)))
                 ((equal name "") pat)
                 ((equal (char name 0) #\@)
                  (if inside-@
                      *ext-failure*
                    (list :@
                          (intern-in-package-of-symbol
                           (concatenate 'string
                                        "_@"
                                        (subseq name 1 (length name)))
                           pat))))
                 (t pat))))
        ((atom pat) pat)
        ((or (eq (car pat) 'quote)
             (not (consp (cdr pat))))
         pat)
        ((eq (car pat) :@) ; expecting (null (cddr pat)), but not checked
         (if inside-@
             *ext-failure*
           (let ((pat2 (ext-preprocess-pat (cadr pat) t)))
             (if (equal pat2 *ext-failure*)
                 *ext-failure*
               (list :@ pat2)))))
        ((and (member-eq (car pat) '(let let*)) ; !! handle b*?
              (true-listp pat))
         `(,(car pat)
           ,(ext-preprocess-pat-let-bindings (cadr pat) inside-@)
           ,@(butlast (cddr pat) 1)
           ,(ext-preprocess-pat (car (last pat)) inside-@)))
        (t (let ((args (ext-preprocess-pat-lst (cdr pat) inside-@)))
             (if (null args)
                 *ext-failure*
               (cons (car pat) args))))))

(defun ext-preprocess-pat-let-bindings (bindings inside-@)
  (declare (xargs :guard t))
  (cond ((atom bindings) bindings)
        (t (cons (let ((b (car bindings)))
                   (cond ((true-listp b) ; always true?
                          (list (car b) ; shouldn't be pattern var; could check
                                (ext-preprocess-pat (cadr b) inside-@)))
                         (t b)))
                 (ext-preprocess-pat-let-bindings (cdr bindings) inside-@)))))

(defun ext-preprocess-pat-lst (pat inside-@)

; Returns nil if there is a failure.

  (declare (xargs :guard (consp pat)
                  :measure (acl2-count pat)
                  :ruler-extenders :lambdas))
  (let ((x1 (and (mbt (consp pat))
                 (ext-preprocess-pat (car pat) inside-@))))
    (cond
     ((equal x1 *ext-failure*)
      nil)
     ((atom (cdr pat))
      (cons x1 (cdr pat)))
     (t
      (let ((x2 (ext-preprocess-pat-lst (cdr pat) inside-@)))
        (and x2
             (cons x1 x2)))))))
)

(defun ext-geneqv-at-subterm (term addr geneqv pequiv-info ens wrld)

; This definition is adapted from the ACL2 sources definition of
; geneqv-at-subterm.

; Address is a valid extended address for the term, term.  This function
; returns a geneqv g such that if one substitutes a subterm u of term at the
; given address such that (g term u), resulting in a term term', then (geneqv
; term term').  As usual, we may return nil for to represent the geneqv for
; equal.

  (declare (xargs :mode :program))
  (cond ((null addr)
         geneqv)
        ((zerop (car addr)) ; dive into lambda body
         (assert$
          (lambda-applicationp term)
          (ext-geneqv-at-subterm (lambda-body (ffn-symb term))
                                 (cdr addr)
                                 geneqv pequiv-info ens wrld)))
        (t
         (let ((child-geneqv0
                (nth (1- (car addr))

; It seems inefficient to compute the entire geneqv-lst, but we prefer not to
; write a separate function to obtain just the nth element of that list.

                     (geneqv-lst (ffn-symb term) geneqv ens wrld))))
           (mv-let
            (deep-pequiv-lst shallow-pequiv-lst)
            (pequivs-for-rewrite-args (ffn-symb term) geneqv pequiv-info wrld
                                      ens)
            (mv-let
             (pre-rev cur/post)
             (split-at-position (car addr) (fargs term) nil)
             (mv-let
              (child-geneqv child-pequiv-info)
              (geneqv-and-pequiv-info-for-rewrite
               (ffn-symb term)
               (car addr)
               pre-rev cur/post
               nil ; alist for cur/post (and, pre-rev in this case)
               geneqv child-geneqv0
               deep-pequiv-lst shallow-pequiv-lst
               wrld)
              (ext-geneqv-at-subterm (car cur/post)
                                     (cdr addr)
                                     child-geneqv child-pequiv-info
                                     ens wrld))))))))

(defun pat-var-p (term)
  (declare (xargs :guard (symbolp term)))
  (let ((name (symbol-name term)))
    (and (not (equal name ""))
         (eql (char name 0) #\_))))

(mutual-recursion

; These are based on ACL2 source functions all-vars1 and all-vars1-lst.

(defun non-pat-vars1 (term ans)

; Term is a translated pattern to which ext-preprocess-pat has already been
; applied; so there may be calls of :@, but there are no variables whose name
; begins with "@".  We collect into ans all variables of term that do not start
; with underscore (_).

  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp ans))))
  (cond ((variablep term)
         (if (pat-var-p term)
             ans
           (add-to-set-eq term ans)))
        ((fquotep term) ans)
        (t (non-pat-vars1-lst (fargs term) ans))))

(defun non-pat-vars1-lst (lst ans)

; Lst is a list of subterms of a translated pattern to which ext-preprocess-pat
; has already been applied; so there may be calls of :@, but there are no
; variables whose name begins with "@".

  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (symbol-listp ans))
                  :mode :program))
  (cond ((endp lst) ans)
        (t (non-pat-vars1-lst (cdr lst)
                              (non-pat-vars1 (car lst) ans)))))

)

(defun pat-unify-subst (pat)

; When instantiating a pattern, only variables starting with the underscore
; character (_) may be instantiated.  So we "seed" our matching algorithm with
; a substitution that binds all other variables of pat to themselves.

  (declare (xargs :guard (pseudo-termp pat)
                  :mode :program))
  (let ((vars (non-pat-vars1 pat nil)))
    (pairlis$ vars vars)))

(defun equal-mod-patvars (pat-formals fn-formals)

; See comments about this function in ext-one-way-unify1-simple.

; !! This assumes that translate sorts extra-formals into lambdas in the same
; order; maybe we need to deal with that by permuting some formals and
; corresponding args.

  (declare (xargs :guard (and (symbol-listp pat-formals)
                              (symbol-listp fn-formals))))
  (cond ((or (endp fn-formals)
             (endp pat-formals))
         t)
        ((eq (car pat-formals) (car fn-formals))
         (equal-mod-patvars (cdr pat-formals) (cdr fn-formals)))
        ((pat-var-p (car pat-formals))
         (equal-mod-patvars (cdr pat-formals) fn-formals))
        (t (let ((rest-fn-formals (member-eq (car pat-formals) fn-formals)))
             (and rest-fn-formals
                  (equal-mod-patvars (cdr pat-formals)
                                     (cdr rest-fn-formals)))))))

(mutual-recursion

(defun ext-one-way-unify1-simple (pat term alist)

; This function is adapted from one-way-unify1 in the ACL2 sources, but it
; differs as follows:

; - avoids special treatment for constants and EQUAL;
; - allows variables named "_" to match anything without extending alist; and
; - is not a no-change loser.

; We return (mv flg new-alist), where flg indicates success and if flg is nil,
; then new-alist is irrelevant.

  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (alistp alist))
                  :measure (acl2-count term)
                  :verify-guards nil))
  (cond
   ((variablep pat)
    (cond ((equal (symbol-name pat) "_")
           (mv t alist))
          (t (let ((pair (assoc-eq pat alist)))
               (cond (pair (cond ((equal (cdr pair) term)
                                  (mv t alist))
                                 (t (mv nil nil))))
                     (t (mv t (cons (cons pat term) alist))))))))
   ((fquotep pat)
    (mv (equal pat term) alist))
   ((variablep term) (mv nil nil))
   ((fquotep term) (mv nil nil))
   (t (let ((fn-pat (ffn-symb pat))
            (fn-term (ffn-symb term)))
        (cond
         ((and (symbolp fn-pat)
               (eq fn-pat fn-term))
          (ext-one-way-unify1-simple-lst (fargs pat) (fargs term) alist))
         ((and (flambdap fn-pat)
               (flambdap fn-term)

; Note that fn-pat may bind extra pattern variables.  Consider for example:

;   pat  = (let ((a _1) (b _) (c _))
;            (list (cons _2 _) (cons _3 _2)))
;   term = (let ((a  x) (b y) (c  z))
;            (list (cons a b) (cons c a)))

; Their translations are:

;   pat:
;   ((LAMBDA (A B C |_3| _ |_2|)
;            (CONS (CONS |_2| _)
;                  (CONS (CONS |_3| |_2|) 'NIL)))
;    |_1| _ _ |_3| _ |_2|)

; term:
;   ((LAMBDA (A B C)
;            (CONS (CONS A B)
;                  (CONS (CONS C A) 'NIL)))
;    X Y Z)

; A solution is to drop pattern variables, which we expect to have been added
; to the end.

; Moreover, formals can be missing from the pattern variables (but non-pattern
; pattern variables must all be among the formals).  Consider:

;   pat  = (let* ((x _) (y (:@ _))) _)
;   term = (let* ((x (cons u v)) (y (cons a b))) (cons x y))

; Their translations are:

;   pat:
;   ((LAMBDA (X _)
;            ((LAMBDA (Y _) _) (:@ _) _))
;    _ _)

;   term:
;   ((LAMBDA (X B A)
;            ((LAMBDA (Y X) (CONS X Y))
;             (CONS A B)
;             X))
;    (CONS U V)
;    B A)

               (equal-mod-patvars (lambda-formals fn-pat)
                                  (lambda-formals fn-term)))
          (mv-let (ans alist)
            (ext-one-way-unify1-simple-lst
             (take (length (lambda-formals fn-term)) (fargs pat))
             (fargs term)
             alist)
            (cond (ans (ext-one-way-unify1-simple (lambda-body fn-pat)
                                                  (lambda-body fn-term)
                                                  alist))
                  (t (mv nil nil)))))
         (t (mv nil nil)))))))

(defun ext-one-way-unify1-simple-lst (pl tl alist)
  (declare (xargs :guard (and (pseudo-term-listp pl)
                              (pseudo-term-listp tl)
                              (alistp alist))
                  :measure (acl2-count tl)))
  (cond ((endp tl) (mv t alist))
        (t (mv-let (ans alist)
             (ext-one-way-unify1-simple (car pl) (car tl) alist)
             (cond (ans (ext-one-way-unify1-simple-lst (cdr pl) (cdr tl) alist))
                   (t (mv nil alist)))))))
)

(defthm pseudo-term-revappend
  (implies (and (pseudo-term-listp lst)
                (pseudo-term-listp ac))
           (pseudo-term-listp (revappend lst ac))))

(defthm pseudo-term-listp-first-n-ac
  (implies (and (pseudo-term-listp lst)
                (pseudo-term-listp ac))
           (pseudo-term-listp (first-n-ac i lst ac))))

; Mihir M. mod, 04/2019: Adapt to the new definition of take.
(defthm pseudo-term-listp-take
  (implies (pseudo-term-listp lst)
           (pseudo-term-listp (take i lst))))

(include-book "tools/flag" :dir :system)

(make-flag ext-one-way-unify1-simple)

(defthm-flag-ext-one-way-unify1-simple
  (defthm alistp-ext-one-way-unify1-simple-guard-helper
    (implies
     (alistp alist)
     (alistp (mv-nth 1 (ext-one-way-unify1-simple pat term alist))))
    :flag ext-one-way-unify1-simple)
  (defthm alistp-ext-one-way-unify1-simple-lst
    (implies
     (alistp alist)
     (alistp (mv-nth 1 (ext-one-way-unify1-simple-lst pl tl alist))))
    :flag ext-one-way-unify1-simple-lst))

(verify-guards ext-one-way-unify1-simple)

(defun apply-subst-to-alist (s alist formals)
  (declare (xargs :guard (and (symbol-alistp s)
                              (pseudo-term-listp (strip-cdrs s))
                              (symbol-alistp alist)
                              (pseudo-term-listp (strip-cdrs alist))
                              (symbol-listp formals))))
  (cond ((endp alist) nil)
        ((member-eq (caar alist) formals)
         (apply-subst-to-alist s (cdr alist) formals))
        (t (acons (caar alist)
                  (sublis-var s (cdar alist))
                  (apply-subst-to-alist s (cdr alist) formals)))))

(defun extend-bindings (formals actuals bindings)

; Bindings is a substitution.  We extend that substitution by binding formals
; to actuals/bindings.

  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp actuals)
                              (eql (len formals) (len actuals))
                              (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings)))))
  (cond ((endp formals) bindings)
        (t (acons (car formals)
                  (sublis-var bindings (car actuals))
                  (extend-bindings (cdr formals) (cdr actuals) bindings)))))

(mutual-recursion

(defun ext-address-subterm-governors-lst2 (pat term alist posn-lst bindings
                                               govs)

; If term is an instance of pat/alist, viewing :@ as invisible, then return (mv
; t alist' lst) where alist' extends alist such that term = pat/alist', and lst
; is a list of triples (list* A U B G) for address A, lexical subterm U of term
; at A, binding alist B mapping variables to terms relative to the global
; environment such that U/B is truly (semantically) the subterm at A, and
; corresponding governors G.  Note that A and govs are accumulated in reverse
; order into posn-lst and govs, respectively, but they are put in proper order
; as they are returned.  There is one triple for each position of an :@ call in
; pat; an input assumption on pat is that these are not nested.

; If however term is not an instance of pat/alist, return (mv nil nil nil).

  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (symbol-alistp alist)
                              (nat-listp posn-lst)
                              (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (true-listp govs))
                  :verify-guards nil))
  (cond
   ((or (variablep pat)
        (fquotep pat))
    (mv-let (flg unify-subst)
      (ext-one-way-unify1-simple pat term alist)
      (cond (flg (mv t nil unify-subst))
            (t (mv nil nil nil)))))
   ((eq (ffn-symb pat) :@)
    (mv-let (flg unify-subst)
      (ext-one-way-unify1-simple (fargn pat 1) term alist)
      (cond (flg (mv t
                     (list (list* (reverse posn-lst)
                                  term
                                  bindings
                                  (reverse govs)))
                     unify-subst))
            (t (mv nil nil nil)))))
   ((or (variablep term)
        (fquotep term))
    (mv nil nil nil))
   ((and (flambdap (ffn-symb pat))
         (flambdap (ffn-symb term))
         (equal-mod-patvars (lambda-formals (ffn-symb pat))
                            (lambda-formals (ffn-symb term))))
    (b* (((mv flg lst1 alist)
          (ext-address-subterm-governors-lst2
           (lambda-body (ffn-symb pat))
           (lambda-body (ffn-symb term))
           alist
           (cons 0 posn-lst)
           (extend-bindings (lambda-formals (ffn-symb term))
                            (fargs term)
                            bindings)
           govs))
         ((when (not flg))
          (mv nil nil nil))
         ((mv flg lst2 alist)
          (ext-address-subterm-governors-lst2-lst
           (fargs pat) (fargs term) alist 1 posn-lst bindings govs))
         ((when (not flg))
          (mv nil nil nil)))
      (mv t (append lst1 lst2) alist)))
   ((not (equal (ffn-symb pat) (ffn-symb term)))
    (mv nil nil nil))
   ((eq (ffn-symb pat) 'if)
    (b* (((mv flg lst1 alist)
          (ext-address-subterm-governors-lst2 (fargn pat 1)
                                              (fargn term 1)
                                              alist
                                              (cons 1 posn-lst)
                                              bindings
                                              govs))
         ((when (not flg))
          (mv nil nil nil))
         ((mv flg lst2 alist)
          (ext-address-subterm-governors-lst2 (fargn pat 2)
                                              (fargn term 2)
                                              alist
                                              (cons 2 posn-lst)
                                              bindings
                                              (cons (sublis-var
                                                     bindings
                                                     (fargn term 1))
                                                    govs)))
         ((when (not flg))
          (mv nil nil nil))
         ((mv flg lst3 alist)
          (ext-address-subterm-governors-lst2 (fargn pat 3)
                                              (fargn term 3)
                                              alist
                                              (cons 3 posn-lst)
                                              bindings
                                              (cons (sublis-var
                                                     bindings
                                                     (dumb-negate-lit
                                                      (fargn term 1)))
                                                    govs)))
         ((when (not flg))
          (mv nil nil nil)))
      (mv t (append lst1 lst2 lst3) alist)))
   (t (ext-address-subterm-governors-lst2-lst
       (fargs pat) (fargs term) alist 1 posn-lst bindings govs))))

(defun ext-address-subterm-governors-lst2-lst (pat-lst term-lst alist posn
                                                       posn-lst bindings govs)
  (declare (xargs :guard (and (pseudo-term-listp pat-lst)
                              (pseudo-term-listp term-lst)
                              (symbol-alistp alist)
                              (posp posn)
                              (nat-listp posn-lst)
                              (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (true-listp govs))))
  (cond ((endp pat-lst) (mv t nil alist))
        (t (b* (((mv flg lst1 alist)
                 (ext-address-subterm-governors-lst2 (car pat-lst)
                                                     (car term-lst)
                                                     alist
                                                     (cons posn posn-lst)
                                                     bindings
                                                     govs))
                ((when (not flg))
                 (mv nil nil nil))
                ((mv flg lst2 alist)
                 (ext-address-subterm-governors-lst2-lst (cdr pat-lst)
                                                         (cdr term-lst)
                                                         alist
                                                         (1+ posn)
                                                         posn-lst
                                                         bindings
                                                         govs))
                ((when (not flg))
                 (mv nil nil nil)))
             (mv t (append lst1 lst2) alist)))))
)

; Start proof of (verify-guards ext-address-subterm-governors-lst2))

(make-flag ext-address-subterm-governors-lst2)

(defthm-flag-ext-one-way-unify1-simple
  (defthm symbol-alistp-ext-one-way-unify1-simple-guard-helper
    (implies
     (and (symbol-alistp alist)
          (pseudo-termp pat))
     (symbol-alistp
      (mv-nth 1 (ext-one-way-unify1-simple pat term alist))))
    :flag ext-one-way-unify1-simple)
  (defthm symbol-alistp-ext-one-way-unify1-simple-lst
    (implies
     (and (symbol-alistp alist)
          (pseudo-term-listp pl))
     (symbol-alistp
      (mv-nth 1 (ext-one-way-unify1-simple-lst pl tl alist))))
    :flag ext-one-way-unify1-simple-lst))

(in-theory (disable ext-one-way-unify1-simple
                    ext-one-way-unify1-simple-lst
                    sublis-var
                    ; quotep cons-term
                    ;dumb-negate-lit
                    ))

(defthm-flag-ext-address-subterm-governors-lst2
  (defthm true-listp-ext-address-subterm-governors-lst2
    (true-listp (mv-nth 1
                        (ext-address-subterm-governors-lst2
                         pat term alist posn-lst bindings govs)))
    :flag ext-address-subterm-governors-lst2)
  (defthm ext-one-way-unify1-simple-lst-guard-helper
    (true-listp (mv-nth 1
                        (ext-address-subterm-governors-lst2-lst
                         pat-lst term-lst alist posn posn-lst
                         bindings govs)))
    :flag ext-address-subterm-governors-lst2-lst))

(defthm symbol-alistp-append
  (implies (symbol-alistp x)
           (equal (symbol-alistp (append x y))
                  (symbol-alistp y))))

(defthm-flag-ext-address-subterm-governors-lst2
  (defthm symbol-alistp-ext-address-subterm-governors-lst2
    (implies (and (symbol-alistp alist)
                  (pseudo-termp pat))
             (symbol-alistp (mv-nth 2
                                    (ext-address-subterm-governors-lst2
                                     pat term alist posn-lst
                                     bindings govs))))
    :flag ext-address-subterm-governors-lst2)
  (defthm alistp-ext-address-subterm-governors-lst2-lst
    (implies (and (symbol-alistp alist)
                  (pseudo-term-listp pat-lst))
             (symbol-alistp
              (mv-nth 2
                      (ext-address-subterm-governors-lst2-lst
                       pat-lst term-lst alist posn posn-lst
                       bindings govs))))
    :flag ext-address-subterm-governors-lst2-lst))

(defthm pseudo-term-listp-implies-pseudo-termp-car
  (implies (pseudo-term-listp x)
           (pseudo-termp (car x))))

; Start subproof of pseudo-term-listp-strip-cdrs-extend-bindings

(local (include-book "system/sublis-var" :dir :system))

(defthm pseudo-termp-sublis-var
  (implies (and (pseudo-termp x)
                (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings)))
           (pseudo-termp (sublis-var bindings x)))
  :hints (("Goal" :in-theory (enable sublis-var))))

(defthm pseudo-term-listp-strip-cdrs-extend-bindings
  (implies (and (pseudo-term-listp actuals)
                (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings)))
           (pseudo-term-listp (strip-cdrs (extend-bindings formals
                                                           actuals
                                                           bindings))))
  :hints (("Goal" :in-theory (enable sublis-var))))

(defthm symbol-alistp-extend-bindings
  (implies (and (symbol-listp formals)
                (symbol-alistp bindings))
           (symbol-alistp (extend-bindings formals
                                           actuals
                                           bindings))))

(verify-guards ext-address-subterm-governors-lst2)

(mutual-recursion

(defun ext-address-subterm-governors-lst1 (pat term alist posn-lst bindings
                                               govs)

; We do a pre-order traversal to find the first subterm S matching pat to term
; with respect to alist, and return the corresponding list of triples (list* A
; U G) for address A, subterm U of term at A, and corresponding governors G,
; but where the reverses of A and G extend posn-lst and govs (resp.) by pushing
; new elements on the front as we dive into term.  Important: that list is
; non-empty if pat has at least one call of :@ (which it does at the top
; level), and all returned triples are viewed with respect to the input, term,
; even though they all point to subterms of S.

  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (symbol-alistp alist)
                              (nat-listp posn-lst)
                              (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (true-listp govs))))
  (mv-let (flg tuples unify-subst)
    (ext-address-subterm-governors-lst2 pat term alist posn-lst bindings govs)
    (declare (ignore unify-subst))
    (cond
     (flg tuples)
     (t
      (and (nvariablep term)
           (not (fquotep term))
           (cond
            ((eq (ffn-symb term) 'if)
             (or (ext-address-subterm-governors-lst1 pat
                                                     (fargn term 1)
                                                     alist
                                                     (cons 1 posn-lst)
                                                     bindings
                                                     govs)
                 (ext-address-subterm-governors-lst1 pat
                                                     (fargn term 2)
                                                     alist
                                                     (cons 2 posn-lst)
                                                     bindings
                                                     (cons (sublis-var
                                                            bindings
                                                            (fargn term 1))
                                                           govs))
                 (ext-address-subterm-governors-lst1 pat
                                                     (fargn term 3)
                                                     alist
                                                     (cons 3 posn-lst)
                                                     bindings
                                                     (cons (sublis-var
                                                            bindings
                                                            (dumb-negate-lit
                                                             (fargn term 1)))
                                                           govs))))
            ((flambdap (ffn-symb term))
             (or
; Pat matches an actual parameter of the call.
              (ext-address-subterm-governors-lst1-lst pat (fargs term) alist
                                                      1 posn-lst
                                                      bindings govs)
; Pat matches the body of the lambda.
              (ext-address-subterm-governors-lst1
               pat
               (lambda-body (ffn-symb term))
               alist
               (cons 0 posn-lst)
               (extend-bindings (lambda-formals (ffn-symb term))
                                (fargs term)
                                bindings)
               govs)))
            (t (ext-address-subterm-governors-lst1-lst pat (fargs term) alist
                                                       1 posn-lst
                                                       bindings govs))))))))

(defun ext-address-subterm-governors-lst1-lst (pat term-lst alist posn posn-lst
                                                   bindings govs)
  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-term-listp term-lst)
                              (symbol-alistp alist)
                              (posp posn)
                              (nat-listp posn-lst)
                              (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (true-listp govs))))
  (cond
   ((endp term-lst)
    nil)
   (t
    (or (ext-address-subterm-governors-lst1 pat (car term-lst) alist
                                            (cons posn posn-lst)
                                            bindings govs)
        (ext-address-subterm-governors-lst1-lst pat (cdr term-lst) alist
                                                (1+ posn) posn-lst
                                                bindings govs)))))
)

(defun ext-address-subterm-governors-lst-world (untrans-pat term ctx wrld
                                                            state-vars)

; Untrans-pat, a user-supplied pattern, is first preprocessed, replacing each @
; with (:@ _) and each @xx with (:@ _xx).  The result is translated and then
; matched appropriately against term.

; Also see :doc simplify-defun, specifically the documentation for
; :simplify-body, for a discussion of translation and the matching algorithm.

; Examples (after defstub for each function symbol used as shown):

; (defstub p (x) t)
; (defstub q (x) t)
; (defstub g (x) t)
; (defstub f2 (x y) t)

;   ACL2 !>(ext-address-subterm-governors-lst
;               '(if (p _x)
;                    (g (if (q (:@ a0)) _ (f2 y @)))
;                  _v)
;               '(if (p x0)
;                    (g (if (q a0) w0 (f2 y (h x))))
;                  v0)
;               'top state)
;   (NIL (((2 1 1 1) A0 (P X0))
;         ((2 1 3 2) (H X) (P X0) (NOT (Q A0)))))
;   ACL2 !>

; Here is a similar example, but where the pattern matches a proper subterm.

;   ACL2 !>(ext-address-subterm-governors-lst
;                  '(if (p _x)
;                       (g (if (q (:@ a0)) _ (f2 y @)))
;                     _v)
;                  '(g (f2 a (if (p x0)
;                                (g (if (q a0) w0 (f2 y (h x))))
;                              v0)))
;                  'top state)
;   (NIL (((1 2 2 1 1 1) A0 (P X0))
;         ((1 2 2 1 3 2)
;          (H X)
;          (P X0)
;          (NOT (Q A0)))))
;   ACL2 !>

  (declare (xargs :mode :program
                  :guard (and (pseudo-termp term)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))))
  (b* ((untrans-pat1
        (ext-preprocess-pat untrans-pat nil)) ; @ -> (:@ _), @xx -> (:@ _@xx)
       ((when (equal untrans-pat1 *ext-failure*))
        (er-cmp ctx
                "The :simplify-body pattern must not specify nested ~
                 simplification sites (using @ or (:@ ...))."))
       ((mv erp pat) (translate-cmp untrans-pat1
                                    t  ; stobjs-out
                                    t  ; logic-modep
                                    t  ; known-stobjs
                                    ctx
                                    (cons '(:@ FORMALS X) wrld)
                                    state-vars))
       ((when erp)
        (mv erp pat))
       ((when (not (member-eq :@ (all-ffn-symbs pat nil))))

; Note: we could code a faster test by avoiding building a list of all function
; symbols in pat, but the extra computation is probably trivial so why bother.

        (er-cmp ctx
                "The :simplify-body pattern must specify at least one ~
                 simplification site (using @ or (:@ ...)).  The ~
                 user-specified pattern is equivalent to~|  ~y0, which is ~
                 thus illegal."
                pat))
       (unify-subst (pat-unify-subst pat))
       (lst (ext-address-subterm-governors-lst1 pat term unify-subst
                                                nil nil nil)))
    (cond
     ((null lst)
      (er-cmp ctx
              "No subterm of ~x0 matches the pattern ~x1."
              (untranslate term nil wrld)
              pat))
     (t (value-cmp lst)))))

(defun ext-address-subterm-governors-lst (untrans-pat term ctx state)
  (declare (xargs :mode :program
                  :guard (pseudo-termp term)
                  :stobjs state))
  (ext-address-subterm-governors-lst-world untrans-pat term ctx
                                           (w state)
                                           (default-state-vars t)))

(defun ext-address-subterm-governors-lst-state (untrans-pat term ctx state)
  (declare (xargs :mode :program
                  :guard (pseudo-termp term)
                  :stobjs state))
  (cmp-to-error-triple
   (ext-address-subterm-governors-lst untrans-pat term ctx state)))
