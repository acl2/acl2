; Proof of correctness clean-up-lambdas
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book proves that the meaning of terms (expressed wrt an evaluator) is
;; preserved by drop-unused-lambda-bindings.

;; TODO: Prove that the result is lambda-free.

(include-book "clean-up-lambdas")
;(include-book "make-lambda-term-simple")
;(include-book "no-nils-in-termp")
(include-book "kestrel/evaluators/empty-eval" :dir :system)

;; todo: finish this, but first change drop-unused-lambda-bindings to call make-lambda-application-simple
;; (defthm-flag-drop-unused-lambda-bindings
;;   (defthm theorem-for-drop-unused-lambda-bindings
;;     (implies (pseudo-termp term)
;;              (equal (empty-eval (drop-unused-lambda-bindings term) a)
;;                     (empty-eval term a)))
;;     :flag drop-unused-lambda-bindings)
;;   (defthm theorem-for-drop-unused-lambda-bindings-lst
;;     (implies (pseudo-term-listp terms)
;;              (equal (empty-eval-list (drop-unused-lambda-bindings-lst terms) a)
;;                     (empty-eval-list terms a)))
;;     :flag drop-unused-lambda-bindings-lst)
;;   :hints (("Goal" :in-theory (e/d (empty-eval-of-fncall-args) (empty-eval-of-fncall-args-back)))))
