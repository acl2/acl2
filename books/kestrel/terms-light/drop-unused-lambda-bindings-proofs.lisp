; Proof of correctness of drop-unused-lambda-bindings
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book proves that the meaning of terms (expressed wrt an evaluator) is
;; preserved by drop-unused-lambda-bindings.

;; TODO: Prove that the result has no unused lambda vars.

(include-book "drop-unused-lambda-bindings")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "no-nils-in-termp")
(include-book "lambdas-closed-in-termp")
(include-book "kestrel/evaluators/empty-eval" :dir :system)
;(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/alists-light/map-lookup-equal" :dir :system)
(local (include-book "filter-formals-and-actuals-proofs"))
(local (include-book "helpers"))
(local (include-book "empty-eval-helpers"))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))

(local (in-theory (enable make-lambda-with-hint)))

;; The point of this is to change the alist:
(mutual-recursion
 (defun drop-unused-lambda-bindings-induct (term alist)
   (declare (irrelevant alist))
   (if (variablep term)
       term
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           term
         (let ((args (drop-unused-lambda-bindings-induct-lst (fargs term) alist)))
           (if (consp fn)
               ;; it's a lambda:
               (let* ((body (lambda-body fn))
                      (body (drop-unused-lambda-bindings-induct body (pairlis$ (lambda-formals fn) (empty-eval-list args alist))))
                      (formals (lambda-formals fn))
                      (body-vars (free-vars-in-term body)))
                 (mv-let (formals args)
                   (filter-formals-and-actuals formals args body-vars)
                   ;; could put this back, or call make-lambdas-application-simple:
                   ;;(if (equal formals args)
                       ;; If the remaining formals are the same as the args, we
                       ;; don't need a lambda at all:
                       ;; TODO: Or rely on drop-trivial-lambdas for that?
                   ;;    body
                   `((lambda ,formals ,body) ,@args)
                   ;)
                   ))
             ;; not a lambda:
             (cons-with-hint fn args term)))))))
 (defun drop-unused-lambda-bindings-induct-lst (terms alist)
   (declare (irrelevant alist))
   (if (endp terms)
       nil
     (cons-with-hint (drop-unused-lambda-bindings-induct (first terms) alist)
                     (drop-unused-lambda-bindings-induct-lst (rest terms) alist)
                     terms))))

(local (make-flag drop-unused-lambda-bindings-induct))

;; The induct function is the equivalent to the original function
(local
 (defthm-flag-drop-unused-lambda-bindings-induct
   (defthm drop-unused-lambda-bindings-induct-removal
     (equal (drop-unused-lambda-bindings-induct term alist)
            (drop-unused-lambda-bindings term))
     :flag drop-unused-lambda-bindings-induct)
   (defthm drop-unused-lambda-bindings-induct-lst-removal
     (equal (drop-unused-lambda-bindings-induct-lst terms alist)
            (drop-unused-lambda-bindings-lst terms))
     :flag drop-unused-lambda-bindings-induct-lst)
   :hints (("Goal" :in-theory (enable drop-unused-lambda-bindings
                                      drop-unused-lambda-bindings-lst
                                      drop-unused-lambda-bindings-induct
                                      drop-unused-lambda-bindings-induct-lst)))))

(defthm-flag-drop-unused-lambda-bindings
  (defthm subsetp-equal-of-free-vars-in-term-of-drop-unused-lambda-bindings
    (implies (and (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (subsetp-equal (free-vars-in-term (drop-unused-lambda-bindings term))
                            (free-vars-in-term term)))
    :flag drop-unused-lambda-bindings)
  (defthm subsetp-equal-of-free-vars-in-terms-of-drop-unused-lambda-bindings-lst
    (implies (and (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (subsetp-equal (free-vars-in-terms (drop-unused-lambda-bindings-lst terms))
                            (free-vars-in-terms terms)))
    :flag drop-unused-lambda-bindings-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((free-vars-in-term term))
           :in-theory (enable drop-unused-lambda-bindings
                              drop-unused-lambda-bindings-lst
                              free-vars-in-terms-when-symbol-listp))))

(defthm subsetp-equal-of-free-vars-in-term-of-drop-unused-lambda-bindings-gen
  (implies (and (subsetp-equal (free-vars-in-term term) x)
                (pseudo-termp term)
                (no-duplicate-lambda-formals-in-termp term))
           (subsetp-equal (free-vars-in-term (drop-unused-lambda-bindings term))
                          x)))

(defthm-flag-drop-unused-lambda-bindings-induct
  (defthm drop-unused-lambda-bindings-correct
    (implies (and (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  (lambdas-closed-in-termp term))
             (equal (empty-eval (drop-unused-lambda-bindings term) alist)
                    (empty-eval term alist)))
    :flag drop-unused-lambda-bindings-induct)
  (defthm drop-unused-lambda-bindings-lst-correct
    (implies (and (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms)
                  (lambdas-closed-in-termsp terms))
             (equal (empty-eval-list (drop-unused-lambda-bindings-lst terms) alist)
                    (empty-eval-list terms alist)))
    :flag drop-unused-lambda-bindings-induct-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (empty-eval-of-fncall-args alists-equiv-on-redef)
                           (empty-eval-of-fncall-args-back)))))

;; todo: show it preserves logic-termp

(defthm-flag-drop-unused-lambda-bindings
  (defthm no-nils-in-termp-of-drop-unused-lambda-bindings
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term))
             (no-nils-in-termp (drop-unused-lambda-bindings term)))
    :flag drop-unused-lambda-bindings)
  (defthm no-nils-in-termsp-of-drop-unused-lambda-bindings-lst
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms))
             (no-nils-in-termsp (drop-unused-lambda-bindings-lst terms)))
    :flag drop-unused-lambda-bindings-lst)
  :hints (("Goal" :in-theory (enable no-nils-in-termsp-when-symbol-listp))))

(defthm-flag-drop-unused-lambda-bindings
  (defthm lambdas-closed-in-termp-of-drop-unused-lambda-bindings
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (lambdas-closed-in-termp (drop-unused-lambda-bindings term)))
    :flag drop-unused-lambda-bindings)
  (defthm lambdas-closed-in-termsp-of-drop-unused-lambda-bindings-lst
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (lambdas-closed-in-termsp (drop-unused-lambda-bindings-lst terms)))
    :flag drop-unused-lambda-bindings-lst)
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp-when-symbol-listp))))

(defthm-flag-drop-unused-lambda-bindings
  (defthm no-duplicate-lambda-formals-in-termp-of-drop-unused-lambda-bindings
    (implies (and (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (no-duplicate-lambda-formals-in-termp (drop-unused-lambda-bindings term)))
    :flag drop-unused-lambda-bindings)
  (defthm no-duplicate-lambda-formals-in-termsp-of-drop-unused-lambda-bindings-lst
    (implies (and (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termsp (drop-unused-lambda-bindings-lst terms)))
    :flag drop-unused-lambda-bindings-lst)
  :hints (("Goal" :in-theory (enable no-duplicate-lambda-formals-in-termsp-when-symbol-listp))))
