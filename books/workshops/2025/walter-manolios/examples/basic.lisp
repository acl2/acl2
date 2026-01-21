;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-basic
  (:use :cl :z3)
  (:import-from :z3 :expect-error))

(in-package :z3-basic)

(solver-init)
;; Create a new scope and enter it. We can (solver-pop) later to exit this scope.
;; We'll see how scopes can be used later.
(solver-push)

(z3-assert (x :bool y :int)
           (and x (>= y 5)))
;; If the assertion(s) can be determined to be satisfiable, returns :sat
;; Otherwise it returns :unknown or :unsat
(check-sat)
;; Returns the model object, if assertions were determined to be
;; satisfiable.
(get-model)
;; This gets the model as a list of assignments suitable for use in a
;; let binding
(get-model-as-assignment)

;; As an example, let's check that the assertion expression really
;; evaluates to true under the model Z3 found.
(eval `(let ,(get-model-as-assignment) (and x (>= y 5))))

;; We can also use the eval-under-model function, which interprets the
;; given expression as a Z3 AST, evaluates it under the current model,
;; and translates the result into a Lisp value.
(eval-under-model (and x (>= y 5)))


;;;; SCOPES ;;;;
;; Say we want to see what happens if we add the assertion (not x).
;; We can create a new scope and enter it. This scope contains all of the assertions and assumptions that were introduced in the current scope.
;; Z3 may also be able to reuse some work that it already did when we called (check-sat) in the above scope.
(solver-push)
;; Note that we don't need to declare x this time, as it was provided
;; previously. We could if we wanted to though, so long as we provided
;; the same sort for x that we did previously.
(z3-assert
 (not x))
;; This returns :UNSAT because no model can make both (and x (>= y 5)) and (not x) true.
(check-sat)
;; It is an error to ask for a model if check-sat indicated :UNSAT
(expect-error (get-model))

;; This will exit the scope that we just created. At this point, the only assertion that remains is (and x (>= y 5)).
(solver-pop)
;; To confirm, we now get :SAT just like we did before.
(check-sat)
;; Now we'll return to the top level scope, which currently contains no assertions or assumptions.
(solver-pop)

;;;; DON'T-CARES ;;;;
;; In some situations, Z3 may note that a variable doesn't matter
(solver-push)
(z3-assert (x :bool y :int)
           (and (or x (not x)) (>= y 5)))
(check-sat)
;; Note that X doesn't appear in the assignment returned by check-sat!
(get-model)
(solver-pop)

;;;; SPECIFYING VARIABLE SORTS ;;;
(solver-push)
;; If multiple variables have the same sort, they can be declared
;; together as follows:
(z3-assert (x y :int p q :bool)
           (and (xor p q)
                (> x y)))
(check-sat)
(get-model)

;; It is not possible to specify the same variable with multiple sorts
;; in a z3-assert form:
(expect-error
 (z3-assert (z :int z :bool)
            (and z (> z 3))))

;; Variables are "remembered" across z3-assert calls, and it is not
;; necessary to restate the sort of a variable when using it later. If
;; no variable declarations are needed for an assertion, that argument
;; can be elided (so only a single argument is provided to z3-assert,
;; the statement to assert)
(z3-assert (> y 0))
(check-sat)
;; Note that y must now be strictly positive.
(get-model)

;; It is an error to re-declare a known variable with a different
;; type.
(expect-error
 (z3-assert (x :bool)
            (not x)))

;; If we pop past the stack entry where a known variable was first
;; used in an assertion, we can then define a new instance of that
;; variable with a different sort.
(solver-pop)

(z3-assert (x :bool)
           (not x))
(check-sat)
(get-model)

;; Let's reset the solver (to remove all assertions and pop to the top
;; entry of the stack)
(solver-reset)

(solver-push)

;; One can also explicitly declare variables ahead of time
(declare-const x :int)
(declare-const y :int)

(z3-assert (= (+ x y) 10))
(check-sat)
(get-model)
(solver-pop)
