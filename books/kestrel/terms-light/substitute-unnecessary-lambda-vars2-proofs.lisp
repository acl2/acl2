; Proofs about substitute-unnecessary-lambda-vars-in-term2
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "substitute-unnecessary-lambda-vars2")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "no-nils-in-termp")
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))

(local (in-theory (enable make-lambda-with-hint)))

(local (in-theory (disable strip-cdrs
                           strip-cars
                           symbol-alistp
                           intersection-equal-commutative-iff
                           )))

;(local (in-theory (enable pseudo-term-listp-when-symbol-listp)))

(local
  (defthm symbol-listp-of-formals-whose-args-call-none
    (implies (symbol-listp formals)
             (symbol-listp (formals-whose-args-call-none formals args hands-off-fns)))
    :hints (("Goal" :in-theory (enable formals-whose-args-call-none)))))

(local
  (defthm subsetp-equal-of-formals-whose-args-call-none-gen
    (implies (subsetp-equal formals x)
             (subsetp-equal (formals-whose-args-call-none formals args hands-off-fns) x))
    :hints (("Goal" :in-theory (enable formals-whose-args-call-none)))))

(local
  (defthm no-duplicatesp-equal-of-formals-whose-args-call-none
    (implies (no-duplicatesp-equal formals)
             (no-duplicatesp-equal (formals-whose-args-call-none formals args hands-off-fns)))
    :hints (("Goal" :in-theory (enable formals-whose-args-call-none)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm len-of-substitute-unnecessary-lambda-vars-in-terms2
  (equal (len (substitute-unnecessary-lambda-vars-in-terms2 terms print hands-off-fns))
         (len terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable (:i len)))))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm no-nils-in-termp-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term))
             (no-nils-in-termp (substitute-unnecessary-lambda-vars-in-term2 term print hands-off-fns)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm no-nils-in-termsp-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms))
             (no-nils-in-termsp (substitute-unnecessary-lambda-vars-in-terms2 terms print hands-off-fns)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  ;(no-nils-in-termp term)
                  )
             (subsetp-equal (free-vars-in-term (substitute-unnecessary-lambda-vars-in-term2 term print hands-off-fns))
                            (free-vars-in-term term)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm subsetp-equal-of-free-vars-in-terms-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  ;(no-nils-in-termsp terms)
                  )
             (subsetp-equal (free-vars-in-terms (substitute-unnecessary-lambda-vars-in-terms2 terms print hands-off-fns))
                            (free-vars-in-terms terms)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

(defthm subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2-gen
  (implies (and (subsetp-equal (free-vars-in-term term) x)
                (pseudo-termp term))
           (subsetp-equal (free-vars-in-term (substitute-unnecessary-lambda-vars-in-term2 term print hands-off-fns))
                          x))
  :hints (("Goal" :use subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2
           :in-theory (disable subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2))))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm lambdas-closed-in-termp-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term))
             (lambdas-closed-in-termp (substitute-unnecessary-lambda-vars-in-term2 term print hands-off-fns)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm lambdas-closed-in-termsp-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms))
             (lambdas-closed-in-termsp (substitute-unnecessary-lambda-vars-in-terms2 terms print hands-off-fns)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm no-duplicate-lambda-formals-in-termp-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (no-duplicate-lambda-formals-in-termp (substitute-unnecessary-lambda-vars-in-term2 term print hands-off-fns)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm no-duplicate-lambda-formals-in-termsp-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termsp (substitute-unnecessary-lambda-vars-in-terms2 terms print hands-off-fns)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

;; the point of this is to change the alist used for the lambda case (standard trick):
(mutual-recursion
 (defun induct-substitute-unnecessary-lambda-vars-in-term2 (term print hands-off-fns alist)
   (declare (xargs :guard (pseudo-termp term)
                   :measure (acl2-count term)
                   :verify-guards nil)
            (irrelevant alist))
   (if (or (variablep term)
           (quotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((args (fargs term))
            (args (induct-substitute-unnecessary-lambda-vars-in-terms2 args print hands-off-fns alist)) ;process the args first
            (fn (ffn-symb term)))
       (if (consp fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((formals (lambda-formals fn))
                  (lambda-body (lambda-body fn))
                  ;;apply recursively to the lambda body:
                  (lambda-body (induct-substitute-unnecessary-lambda-vars-in-term2 lambda-body print hands-off-fns
                                                                                   ;; note this:
                                                                                   (pairlis$ (lambda-formals fn) (empty-eval-list args alist))))
                  (formal-arg-alist (pairlis$ formals args))
                  ;; (trivial-formals (trivial-formals formals args))
                  ;; (formals-bound-to-mv-nths (vars-bound-to-mv-nths formals args))
                  (non-trivial-formals (non-trivial-formals formals args))
                  ;; We try to substitute for a lambda var if:
                  ;; 1) It appears only once in the lambda-body
                  ;; and
                  ;; 2) It is not bound to itself (trivial formals
                  ;; don't really "count against" us, since lambdas must be closed)
                  ;; and
                  ;; ;; 3) It is not bound to an mv-nth (to avoid messing up MV-LET patterns)
                  ;; ;; and
                  ;; 4) It is bound to a term that does not mention any of the remaining non-trivial formals.
                  (formals-to-maybe-subst (vars-that-appear-only-once non-trivial-formals lambda-body))
                  (formals-to-maybe-subst (formals-whose-args-call-none formals-to-maybe-subst (map-lookup-equal formals-to-maybe-subst formal-arg-alist) hands-off-fns))
                  ;; (formals-to-maybe-subst (set-difference-eq formals-to-maybe-subst trivial-formals))
                  ;; (formals-to-maybe-subst (set-difference-eq formals-to-maybe-subst formals-bound-to-mv-nths)) ; todo: make this optional
                  ;; (formals-to-drop (vars-expressible-without-clashes formals-to-maybe-subst formal-arg-alist non-trivial-formals)) ; would be ok to mention formals we are substituting?
                  ;; We can't subst for any formal whose arg mentions a non-trivial formal that remains:
                  ;(bad-arg-vars (set-difference-eq non-trivial-formals formals-to-maybe-subst))
                  ;; Not being able so subst for a formal means it may block other formals (in whose args it appears):
                  ;(formals-to-subst (maybe-remove-more-formals formals-to-maybe-subst formal-arg-alist bad-arg-vars))
                  (formals-to-keep (set-difference-eq non-trivial-formals formals-to-maybe-subst)) ; may be extended by classify-lambda-formals
                  )
             (mv-let (formals-to-subst formals-to-keep)
               (classify-lambda-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)
               (declare (ignore formals-to-keep)) ; todo
               (if formals-to-subst
                   (progn$ (and print (cw "Will subst for ~x0 in lambda.~%" formals-to-subst))
                           (subst-formals-in-lambda-application formals lambda-body args formals-to-subst))
                 `((lambda ,formals ,lambda-body) ,@args))))
         ;;not a lambda application, so just rebuild the function call:
         (cons-with-hint fn args term)))))

 (defun induct-substitute-unnecessary-lambda-vars-in-terms2 (terms print hands-off-fns alist)
   (declare (xargs :measure (acl2-count terms)
                   :guard (pseudo-term-listp terms))
            (irrelevant alist))
   (if (endp terms)
       nil
     (cons-with-hint (induct-substitute-unnecessary-lambda-vars-in-term2 (first terms) print hands-off-fns alist)
                     (induct-substitute-unnecessary-lambda-vars-in-terms2 (rest terms) print hands-off-fns alist)
                     terms))))

(make-flag induct-substitute-unnecessary-lambda-vars-in-term2)

;; The induct function is equal to the original function!
(defthm-flag-induct-substitute-unnecessary-lambda-vars-in-term2
  (defthm induct-substitute-unnecessary-lambda-vars-in-term2-becomes
    (equal (induct-substitute-unnecessary-lambda-vars-in-term2 term print hands-off-fns alist)
           (substitute-unnecessary-lambda-vars-in-term2 term print hands-off-fns))
    :flag induct-substitute-unnecessary-lambda-vars-in-term2)
  (defthm induct-substitute-unnecessary-lambda-vars-in-terms2-becomes
    (equal (induct-substitute-unnecessary-lambda-vars-in-terms2 terms print hands-off-fns alist)
           (substitute-unnecessary-lambda-vars-in-terms2 terms print hands-off-fns))
    :flag induct-substitute-unnecessary-lambda-vars-in-terms2))

;; substitute-unnecessary-lambda-vars-in-term2 does not change the meaning of terms
(defthm-flag-induct-substitute-unnecessary-lambda-vars-in-term2
  (defthm empty-eval-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term)
                  (lambdas-closed-in-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (equal (empty-eval (substitute-unnecessary-lambda-vars-in-term2 term print hands-off-fns) alist)
                    (empty-eval term alist)))
    :flag induct-substitute-unnecessary-lambda-vars-in-term2)
  (defthm empty-eval-list-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  (lambdas-closed-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (equal (empty-eval-list (substitute-unnecessary-lambda-vars-in-terms2 terms print hands-off-fns) alist)
                    (empty-eval-list terms alist)))
    :flag induct-substitute-unnecessary-lambda-vars-in-terms2)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;empty-eval-of-fncall-args-back ; rename
                            empty-eval-of-fncall-args
                            ;not-member-equal-of-nil-when-no-nils-in-termsp
                            true-listp-when-symbol-listp-rewrite-unlimited
                            ) (;empty-eval-of-fncall-args
                            empty-eval-of-fncall-args-back
                            )))))
