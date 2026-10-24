; Correctness of the ACL2 system function unmake-true-list-cons-nest
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; UNMAKE-TRUE-LIST-CONS-NEST (in translate.lisp) takes a term that builds a
;; true list (a quoted list or a nest of calls of CONS ending in 'NIL) and
;; returns the list of terms for the elements, or :FAIL.  It is used to recover
;; the arguments of a call of CW (see unmake-formal-pairlis2).

;; We state its correctness using an evaluator that knows only CONS.

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)

(local (include-book "kestrel/terms-light/termp" :dir :system))

(defevaluator+ cons-nest-eval cons)

;; When it doesn't fail, the terms returned evaluate to the elements of the
;; list that FORMAL-ARGS evaluates to.
(defthm unmake-true-list-cons-nest-correct
  (implies (not (equal (unmake-true-list-cons-nest formal-args) :fail))
           (equal (cons-nest-eval-list (unmake-true-list-cons-nest formal-args) a)
                  (cons-nest-eval formal-args a)))
  :hints (("Goal" :in-theory (enable unmake-true-list-cons-nest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The terms returned are subterms of FORMAL-ARGS or quoted constants, so they
;; have the properties of FORMAL-ARGS.  (Termp implies no-nils-in-termp,
;; lambdas-closed-in-termp, and no-duplicate-lambda-formals-in-termp.)

(defthm pseudo-term-listp-of-unmake-true-list-cons-nest
  (implies (and (pseudo-termp formal-args)
                (not (equal (unmake-true-list-cons-nest formal-args) :fail)))
           (pseudo-term-listp (unmake-true-list-cons-nest formal-args)))
  :hints (("Goal" :in-theory (enable unmake-true-list-cons-nest))))

(defthm term-listp-of-unmake-true-list-cons-nest
  (implies (and (termp formal-args w)
                (not (equal (unmake-true-list-cons-nest formal-args) :fail)))
           (term-listp (unmake-true-list-cons-nest formal-args) w))
  :hints (("Goal" :in-theory (enable unmake-true-list-cons-nest termp))))
