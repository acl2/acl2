; Proof of correctness of expand-lambdas-in-term
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book proves that the meaning of terms (expressed wrt an evaluator) is
;; preserved by expand-lambdas-in-term.

;; TODO: Prove that the result is lambda-free.

(include-book "expand-lambdas-in-term")
(include-book "make-lambda-term-simple")
(include-book "no-nils-in-termp")
(include-book "kestrel/evaluators/empty-eval" :dir :system)
(local (include-book "sublis-var-simple-proofs"))
(local (include-book "kestrel/evaluators/empty-eval-theorems" :dir :system))
(local (include-book "kestrel/alists-light/alists-equiv-on" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/less-than" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/alists-light/map-lookup-equal" :dir :system))

(local (in-theory (disable member-equal symbol-listp set-difference-equal pseudo-term-listp len strip-cadrs strip-cdrs)))

;todo: automate some of this?

(defthm cdr-of-expand-lambdas-in-terms
  (equal (cdr (expand-lambdas-in-terms terms))
         (expand-lambdas-in-terms (cdr terms)))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable (:i len) expand-lambdas-in-terms))))

(local
 (mutual-recursion
  ;; The whole point of this is to recur on a different alist in the lambda case
  (defund expand-lambdas-in-term-induct (term a)
    (declare (xargs :measure (acl2-count term))
             (irrelevant a))
    (if (or (variablep term)
            (fquotep term))
        term
      (let* ((args (fargs term))
             (args (expand-lambdas-in-terms-induct args a))
             (fn (ffn-symb term)))
        (if (flambdap fn)
            (let* ((lambda-body (expand-lambdas-in-term-induct (lambda-body fn)
                                                               (pairlis$ (lambda-formals fn) (empty-eval-list args a)) ;note this!
                                                               )))
              (sublis-var-simple (pairlis$ (lambda-formals fn) args) lambda-body))
          `(,fn ,@args)))))

  (defund expand-lambdas-in-terms-induct (terms a)
    (declare (xargs :measure (acl2-count terms))
             (irrelevant a))
    (if (endp terms)
        nil
      (cons (expand-lambdas-in-term-induct (first terms) a)
            (expand-lambdas-in-terms-induct (rest terms) a))))))

;; Expanding lambdas does not introduce any new free vars.
(defthm-flag-expand-lambdas-in-term
  (defthm subsetp-equal-of-free-vars-in-term-of-expand-lambdas-in-term
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term))
             (subsetp-equal (free-vars-in-term (expand-lambdas-in-term term))
                            (free-vars-in-term term)))
    :flag expand-lambdas-in-term)
  (defthm subsetp-equal-of-free-vars-in-terms-of-expand-lambdas-in-terms
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms))
             (subsetp-equal (free-vars-in-terms (expand-lambdas-in-terms terms))
                            (free-vars-in-terms terms)))
    :flag expand-lambdas-in-terms)
  :hints (("Goal" :expand ((expand-lambdas-in-term terms)
                           (free-vars-in-term term))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expand-lambdas-in-term
                            empty-eval-of-fncall-args
                            free-vars-in-terms
                            lambdas-closed-in-termp)
                           (empty-eval-of-fncall-args-back)))))

(defthm subsetp-equal-of-free-vars-in-term-of-expand-lambdas-in-term-gen
  (implies (and (pseudo-termp term)
                (lambdas-closed-in-termp term)
                (subsetp-equal (free-vars-in-term term) free))
           (subsetp-equal (free-vars-in-term (expand-lambdas-in-term term))
                          free)))

(defthm not-member-equal-of-free-var-in-term-of-expand-lambdas-in-term
  (implies (and (not (member-equal var (free-vars-in-term term)))
                (pseudo-termp term)
                (lambdas-closed-in-termp term))
           (not (member-equal var (free-vars-in-term (expand-lambdas-in-term term))))))

(local (make-flag expand-lambdas-in-term-induct))

(local
 (defthm-flag-expand-lambdas-in-term-induct
   (defthm expand-lambdas-in-term-induct-removal
     (equal (expand-lambdas-in-term-induct term a)
            (expand-lambdas-in-term term))
     :flag expand-lambdas-in-term-induct)
   (defthm expand-lambdas-in-terms-induct-removal
     (equal (expand-lambdas-in-terms-induct terms a)
            (expand-lambdas-in-terms terms))
     :flag expand-lambdas-in-terms-induct)
   :hints (("Goal" :in-theory (enable expand-lambdas-in-term
                                      expand-lambdas-in-terms
                                      expand-lambdas-in-term-induct
                                      expand-lambdas-in-terms-induct)))))

;; Correctness of expand-lambdas-in-term: The meaning of terms is preserved.
;; TODO: Can some assumptions be dropped?
(defthm-flag-expand-lambdas-in-term-induct
  (defthm expand-lambdas-in-term-correct
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term)
                  (lambdas-closed-in-termp term))
             (equal (empty-eval (expand-lambdas-in-term term) a)
                    (empty-eval term a)))
    :flag expand-lambdas-in-term-induct)
  (defthm expand-lambdas-in-terms-correct
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  (lambdas-closed-in-termsp terms))
             (equal (empty-eval-list (expand-lambdas-in-terms terms) a)
                    (empty-eval-list terms a)))
    :flag expand-lambdas-in-terms-induct)
  :hints (("Goal" :expand ((expand-lambdas-in-term terms)
                           (free-vars-in-term term)
                           (lambdas-closed-in-termp term))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expand-lambdas-in-term
                            empty-eval-of-fncall-args
                            free-vars-in-terms)
                           (empty-eval-of-fncall-args-back)))))
