; Substituting lambda vars that only appear once
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note: Consider calling drop-trivial-lambdas after calling this utility.  Or
;; build that into this (perhaps as an option).

;; TODO: This may have to be iterated multiple times if there are multiple
;; nested lambdas inside the one we are operating on.  Add an example.

(include-book "classify-lambda-formals")
(include-book "count-vars")
(include-book "substitute-lambda-formals") ; for subst-formals-in-lambda-application; make those names more consistent
(include-book "make-lambda-with-hint")
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))

;; Gather the formals whose corresponding args call none of the hands-off-fns.
(defund formals-whose-args-call-none (formals args hands-off-fns)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp args)
                              (equal (len formals) (len args))
                              (true-listp hands-off-fns))))
  (if (endp formals)
      nil
    (let ((formal (first formals))
          (arg (first args)))
      (if (and (consp arg)
               (member-equal (ffn-symb arg) hands-off-fns))
          (formals-whose-args-call-none (rest formals) (rest args) hands-off-fns)
        (cons-with-hint formal (formals-whose-args-call-none (rest formals) (rest args) hands-off-fns) formals)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: deprecate the other one?
(mutual-recursion
 (defun substitute-unnecessary-lambda-vars-in-term2 (term print hands-off-fns)
   (declare (xargs :guard (and (pseudo-termp term)
                               (true-listp hands-off-fns) ; usually symbols buy perhaps lambdas as well
                               )
                   :measure (acl2-count term)
                   :verify-guards nil ; done below
                   ))
   (if (or (variablep term)
           (quotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((args (fargs term))
            (args (substitute-unnecessary-lambda-vars-in-terms2 args print hands-off-fns)) ;process the args first
            (fn (ffn-symb term)))
       (if (consp fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((formals (lambda-formals fn))
                  (lambda-body (lambda-body fn))
                  ;;apply recursively to the lambda body:
                  (lambda-body (substitute-unnecessary-lambda-vars-in-term2 lambda-body print hands-off-fns))
                  (formal-arg-alist (pairlis$ formals args)) ; todo: avoid consing?
                  ;; We try to substitute for a lambda var if:
                  ;; 1) It is not bound to itself (trivial formals
                  ;; don't really "count against" us, since lambdas must be closed)
                  ;; and
                  ;; 2) It appears only once in the lambda-body.
                  ;; and
                  ;; 3) It is not bound to any of the hands-off-fns (e.g. mv-nth, to avoid messing up MV-LET patterns)
                  ;; and
                  ;; 4) It is bound to a term that does not mention any of the remaining non-trivial formals.
                  (non-trivial-formals (non-trivial-formals formals args))
                  (formals-to-maybe-subst (vars-that-appear-only-once non-trivial-formals lambda-body))
                  (formals-to-maybe-subst (formals-whose-args-call-none formals-to-maybe-subst (map-lookup-equal formals-to-maybe-subst formal-arg-alist) hands-off-fns))
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
                 (cons-with-hint (make-lambda-with-hint formals lambda-body fn) args term))))
         ;; not a lambda application, so just rebuild the function call:
         (cons-with-hint fn args term)))))

 (defun substitute-unnecessary-lambda-vars-in-terms2 (terms print hands-off-fns)
   (declare (xargs :measure (acl2-count terms)
                   :guard (and (pseudo-term-listp terms)
                               (true-listp hands-off-fns) ; usually symbols buy perhaps lambdas as well
                               )))
   (if (endp terms)
       nil
     (cons-with-hint (substitute-unnecessary-lambda-vars-in-term2 (first terms) print hands-off-fns)
                     (substitute-unnecessary-lambda-vars-in-terms2 (rest terms) print hands-off-fns)
                     terms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthm len-of-substitute-unnecessary-lambda-vars-in-terms2
    (equal (len (substitute-unnecessary-lambda-vars-in-terms2 terms print hands-off-fns))
           (len terms))
    :hints (("Goal" :induct (len terms)
             :in-theory (enable (:i len))))))

(make-flag substitute-unnecessary-lambda-vars-in-term2)

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm pseudo-termp-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (pseudo-termp term)
             (pseudo-termp (substitute-unnecessary-lambda-vars-in-term2 term print hands-off-fns)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm pseudo-term-listp-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (substitute-unnecessary-lambda-vars-in-terms2 terms print hands-off-fns)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

(verify-guards substitute-unnecessary-lambda-vars-in-term2)
