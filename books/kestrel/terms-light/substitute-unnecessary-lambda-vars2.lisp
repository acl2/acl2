; Substituting lambda vars that only appear once
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "classify-lambda-formals")
(include-book "count-vars")
(include-book "substitute-lambda-formals") ; for subst-formals-in-lambda-application; make those names more consistent
(include-book "no-duplicate-lambda-formals-in-termp")
;(include-book "no-nils-in-termp")
(include-book "kestrel/alists-light/lookup-eq-def" :dir :system)
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp2" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))

(local (in-theory (disable mv-nth)))

(local (in-theory (disable strip-cdrs
                           strip-cars
                           symbol-alistp
                           intersection-equal-symmetric-iff
                           )))

(local (in-theory (enable pseudo-term-listp-when-symbol-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: deprecate the other one? but add back special treatment of for mv-nth (more generally, any set of functions to avoid)
(mutual-recursion
 (defun substitute-unnecessary-lambda-vars-in-term2 (term print)
   (declare (xargs :guard (and (pseudo-termp term)
                               ;; (no-duplicate-lambda-formals-in-termp term) ; because of the call of subst-formals-in-lambda-application
                               )
                   :measure (acl2-count term)
                   :verify-guards nil ; done below
                   ))
   (if (or (variablep term)
           (quotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((args (fargs term))
            (args (substitute-unnecessary-lambda-vars-in-terms2 args print)) ;process the args first
            (fn (ffn-symb term)))
       (if (consp fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((formals (lambda-formals fn))
                  (lambda-body (lambda-body fn))
                  ;;apply recursively to the lambda body:
                  (lambda-body (substitute-unnecessary-lambda-vars-in-term2 lambda-body print))
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
               (progn$ (and print "Will subst for ~x0 in lambda.~%" formals-to-subst)
                       (subst-formals-in-lambda-application formals lambda-body args formals-to-subst))))
         ;;not a lambda application, so just rebuild the function call:
         (cons-with-hint fn args term)))))

 (defun substitute-unnecessary-lambda-vars-in-terms2 (terms print)
   (declare (xargs :measure (acl2-count terms)
                   :guard (and (pseudo-term-listp terms)
                               ;; (no-duplicate-lambda-formals-in-termsp terms)
                               )))
   (if (endp terms)
       nil
     (cons-with-hint (substitute-unnecessary-lambda-vars-in-term2 (first terms) print)
                     (substitute-unnecessary-lambda-vars-in-terms2 (rest terms) print)
                     terms))))

(defthm len-of-substitute-unnecessary-lambda-vars-in-terms2
  (equal (len (substitute-unnecessary-lambda-vars-in-terms2 terms print))
         (len terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable (:i len)))))

(make-flag substitute-unnecessary-lambda-vars-in-term2)

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm pseudo-termp-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (pseudo-termp term)
             (pseudo-termp (substitute-unnecessary-lambda-vars-in-term2 term print)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm pseudo-term-listp-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (substitute-unnecessary-lambda-vars-in-terms2 terms print)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

(verify-guards substitute-unnecessary-lambda-vars-in-term2)

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm no-nils-in-termp-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term))
             (no-nils-in-termp (substitute-unnecessary-lambda-vars-in-term2 term print)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm no-nils-in-termsp-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms))
             (no-nils-in-termsp (substitute-unnecessary-lambda-vars-in-terms2 terms print)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  ;(no-nils-in-termp term)
                  )
             (subsetp-equal (free-vars-in-term (substitute-unnecessary-lambda-vars-in-term2 term print))
                            (free-vars-in-term term)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm subsetp-equal-of-free-vars-in-terms-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  ;(no-nils-in-termsp terms)
                  )
             (subsetp-equal (free-vars-in-terms (substitute-unnecessary-lambda-vars-in-terms2 terms print))
                            (free-vars-in-terms terms)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

(defthm subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2-gen
  (implies (and (subsetp-equal (free-vars-in-term term) x)
                (pseudo-termp term))
           (subsetp-equal (free-vars-in-term (substitute-unnecessary-lambda-vars-in-term2 term print))
                          x))
  :hints (("Goal" :use subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2
           :in-theory (disable subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2))))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm lambdas-closed-in-termp-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term))
             (lambdas-closed-in-termp (substitute-unnecessary-lambda-vars-in-term2 term print)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm lambdas-closed-in-termsp-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms))
             (lambdas-closed-in-termsp (substitute-unnecessary-lambda-vars-in-terms2 terms print)))
    :flag substitute-unnecessary-lambda-vars-in-terms2)
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp ;todo
                                     ))))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm no-duplicate-lambda-formals-in-termp-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (no-duplicate-lambda-formals-in-termp (substitute-unnecessary-lambda-vars-in-term2 term print)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm no-duplicate-lambda-formals-in-termsp-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termsp (substitute-unnecessary-lambda-vars-in-terms2 terms print)))
    :flag substitute-unnecessary-lambda-vars-in-terms2)
  :hints (("Goal" :in-theory (enable no-duplicate-lambda-formals-in-termp ;todo
                                     ))))

;; the point of this is to change the alist used for the lambda case (standard trick):
(mutual-recursion
 (defun induct-substitute-unnecessary-lambda-vars-in-term2 (term print alist)
   (declare (xargs :guard (pseudo-termp term)
                   :measure (acl2-count term)
                   :verify-guards nil)
            (irrelevant alist))
   (if (or (variablep term)
           (quotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((args (fargs term))
            (args (induct-substitute-unnecessary-lambda-vars-in-terms2 args print alist)) ;process the args first
            (fn (ffn-symb term)))
       (if (consp fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((formals (lambda-formals fn))
                  (lambda-body (lambda-body fn))
                  ;;apply recursively to the lambda body:
                  (lambda-body (induct-substitute-unnecessary-lambda-vars-in-term2 lambda-body print
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
               (progn$ (and print "Will subst for ~x0 in lambda.~%" formals-to-subst)
                       (subst-formals-in-lambda-application formals lambda-body args formals-to-subst))))
         ;;not a lambda application, so just rebuild the function call:
         (cons-with-hint fn args term)))))

 (defun induct-substitute-unnecessary-lambda-vars-in-terms2 (terms print alist)
   (declare (xargs :measure (acl2-count terms)
                   :guard (pseudo-term-listp terms))
            (irrelevant alist))
   (if (endp terms)
       nil
     (cons-with-hint (induct-substitute-unnecessary-lambda-vars-in-term2 (first terms) print alist)
                     (induct-substitute-unnecessary-lambda-vars-in-terms2 (rest terms) print alist)
                     terms))))

(make-flag induct-substitute-unnecessary-lambda-vars-in-term2)

;; The induct function is equal to the original function!
(defthm-flag-induct-substitute-unnecessary-lambda-vars-in-term2
  (defthm induct-substitute-unnecessary-lambda-vars-in-term2-becomes
    (equal (induct-substitute-unnecessary-lambda-vars-in-term2 term print alist)
           (substitute-unnecessary-lambda-vars-in-term2 term print))
    :flag induct-substitute-unnecessary-lambda-vars-in-term2)
  (defthm induct-substitute-unnecessary-lambda-vars-in-terms2-becomes
    (equal (induct-substitute-unnecessary-lambda-vars-in-terms2 terms print alist)
           (substitute-unnecessary-lambda-vars-in-terms2 terms print))
    :flag induct-substitute-unnecessary-lambda-vars-in-terms2))

;; substitute-unnecessary-lambda-vars-in-term2 does not change the meaning of terms
(defthm-flag-induct-substitute-unnecessary-lambda-vars-in-term2
  (defthm empty-eval-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term)
                  (lambdas-closed-in-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (equal (empty-eval (substitute-unnecessary-lambda-vars-in-term2 term print) alist)
                    (empty-eval term alist)))
    :flag induct-substitute-unnecessary-lambda-vars-in-term2)
  (defthm empty-eval-list-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  (lambdas-closed-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (equal (empty-eval-list (substitute-unnecessary-lambda-vars-in-terms2 terms print) alist)
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
