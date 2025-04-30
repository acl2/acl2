;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-quantifiers
  (:use :cl :z3))

(in-package :z3-quantifiers)

(solver-init)

;; Z3 supports constraints that contain quantifiers.
;; The syntax is (exists <bound variables> <body>) or (forall <bound variables> <body>).
;; The list of bound variables uses the same syntax that z3-assert uses for specifying variables.
;; Multiple variables may be bound in each quantifier.

;; Here's a simple example. This is valid, so Z3 may arbitrarily
;; decide which of t or nil to assign to x.
(solver-push)
(z3-assert (x :bool)
           (exists (y :bool) (== x y)))
(check-sat)
;; In fact, it assigns neither!
(get-model)
(solver-pop)

;; This is unsatisfiable.
(solver-push)
(z3-assert (x :bool)
           (forall (y :bool) (== x y)))
(check-sat)
(solver-pop)

;; If a variable is only ever used inside of the body of quantifiers,
;; then it may not appear in the final assignment.
(solver-push)
(z3-assert (x :int)
           (and (forall (y :int) (== (* x y)
                                     (* y x)))
                (forall (y :int z :int) (== (* x (+ y z))
                                            (+ (* x y) (* x z))))))
(check-sat)
(get-model)
(solver-pop)

;; Asserting that x is the multiplicative identity will result in
;; x being assigned 1.
(solver-push)
(z3-assert (x :int)
           (forall (y :int) (== (* x y) y)))
(check-sat)
(get-model)
(solver-pop)

;; One can also assert the existence of a multiplicative identity as follows:
(solver-push)
(z3-assert ()
           (exists (x :int) (forall (y :int) (== (* x y) y))))
(check-sat)
(get-model)
(solver-pop)

;; Note that bound variables will shadow variables with the same name
;; and type that appear in the surrounding context.
(solver-push)
(z3-assert (x :int)
           (and (== x 0)
                (exists (x :int) (forall (y :int) (== (* x y) y)))))
(check-sat)
(get-model)
(solver-pop)
