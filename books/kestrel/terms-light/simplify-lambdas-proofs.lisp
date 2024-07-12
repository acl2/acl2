; Proofs about simplify-lambdas
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The proofs in this book use the if-and-not-eval because simplify-ors requires it.

(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "simplify-lambdas")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "lambdas-closed-in-termp")
(include-book "simplify-ors-proofs")
(include-book "drop-unused-lambda-bindings-proofs")
(include-book "substitute-constants-in-lambdas-proofs")

;; switches the evaluator
(defthm drop-unused-lambda-bindings-correct-for-if-and-not-eval
  (implies (and (pseudo-termp term)
                (no-duplicate-lambda-formals-in-termp term)
                (lambdas-closed-in-termp term))
           (equal (if-and-not-eval (drop-unused-lambda-bindings term) alist)
                  (if-and-not-eval term alist)))
  :hints (("Goal" :use (:functional-instance
                        drop-unused-lambda-bindings-correct
                        (empty-eval if-and-not-eval)
                        (empty-eval-list if-and-not-eval-list)))))

;; switches the evaluator
(defthm substitute-constants-in-lambdas-correct-for-if-and-not-eval
  (implies (and (pseudo-termp term)
                (no-nils-in-termp term)
                (no-duplicate-lambda-formals-in-termp term)
                (lambdas-closed-in-termp term))
           (equal (if-and-not-eval (substitute-constants-in-lambdas term) alist)
                  (if-and-not-eval term alist)))
  :hints (("Goal" :use (:functional-instance
                        substitute-constants-in-lambdas-correct
                        (empty-eval if-and-not-eval)
                        (empty-eval-list if-and-not-eval-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm simplify-lambdas-one-step-correct
  (implies (and (pseudo-termp term)
                (no-nils-in-termp term)
                (no-duplicate-lambda-formals-in-termp term)
                (lambdas-closed-in-termp term))
           (equal (if-and-not-eval (simplify-lambdas-one-step term) alist)
                  (if-and-not-eval term alist)))
  :hints (("Goal" :in-theory (enable simplify-lambdas-one-step))))

(defthm no-nils-in-termp-of-simplify-lambdas-one-step
  (implies (and (pseudo-termp term)
                (no-nils-in-termp term)
                (no-duplicate-lambda-formals-in-termp term)
                (lambdas-closed-in-termp term))
           (no-nils-in-termp (simplify-lambdas-one-step term)))
  :hints (("Goal" :in-theory (enable simplify-lambdas-one-step))))

(defthm lambdas-closed-in-termp-of-simplify-lambdas-one-step
  (implies (and (pseudo-termp term)
                (no-nils-in-termp term)
                (no-duplicate-lambda-formals-in-termp term)
                (lambdas-closed-in-termp term))
           (lambdas-closed-in-termp (simplify-lambdas-one-step term)))
  :hints (("Goal" :in-theory (enable simplify-lambdas-one-step))))

(defthm no-duplicate-lambda-formals-in-termp-of-simplify-lambdas-one-step
  (implies (and (pseudo-termp term)
                (no-nils-in-termp term)
                (no-duplicate-lambda-formals-in-termp term))
           (no-duplicate-lambda-formals-in-termp (simplify-lambdas-one-step term)))
  :hints (("Goal" :in-theory (enable simplify-lambdas-one-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm simplify-lambdas-loop-correct
  (implies (and (pseudo-termp term)
                (no-nils-in-termp term)
                (no-duplicate-lambda-formals-in-termp term)
                (lambdas-closed-in-termp term))
           (equal (if-and-not-eval (simplify-lambdas-loop count term) alist)
                  (if-and-not-eval term alist)))
  :hints (("Goal" :in-theory (enable simplify-lambdas-loop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm simplify-lambdas-correct
  (implies (and (pseudo-termp term)
                (no-nils-in-termp term)
                (no-duplicate-lambda-formals-in-termp term)
                (lambdas-closed-in-termp term))
           (equal (if-and-not-eval (simplify-lambdas term print) alist)
                  (if-and-not-eval term alist)))
  :hints (("Goal" :in-theory (enable simplify-lambdas))))
