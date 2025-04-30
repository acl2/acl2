;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-tactics
  (:use :cl :z3))

(in-package :z3-tactics)

(solver-init)

;; First we'll create a solver from the SAT tactic.
;; This tactic can't reason about integer arithmetic.
;; Note that this tactic also is unable to perform incremental solving.
;; Push and pop still work, but each check-sat will run "from scratch"
;; without reusing any previous results.
(set-solver (make-solver-from-tactic (make-tactic "sat")))

(z3-assert (x :bool y :int)
           (and x (>= y 5)))
;; This returns UNKNOWN because the SAT tactic can't reason about y,
;; and it is neccesary to do so to produce a model containing y.
(check-sat)

;; If we add another assertion such we can show that the conjunction
;; of this and the previous assertion is UNSAT without needing to
;; reason about y, the SAT tactic is able to determine UNSAT.
(z3-assert (x :bool y :int)
           (not x))
(check-sat)


;; Now we'll create a solver from the SMT tactic.
;; This should essentially use the same theory as the default solver.
(set-solver (make-solver-from-tactic (make-tactic "smt")))

(solver-push)

;; This time, since we're using a tactic that can reason about
;; integers, we get an assignment here instead of UNKNOWN.
(z3-assert (x :bool y :int)
           (and x (>= y 5)))
(check-sat)
(get-model)

;; We use solver-push and solver-pop here to show that they work, even
;; though the solver doesn't support incremental solving.

(solver-push)
(z3-assert (x :bool y :int)
           (not x))
;; should be UNSAT
(check-sat)

(solver-pop)

;; Should give us an assignment again.
(check-sat)
(get-model)
