;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-optimize
  (:use :cl :z3))

(in-package :z3-optimize)

(solver-init)
(setf *default-solver* (make-optimizer))

;; The optimizer allows hard constraints to be added just like normal
;; solvers.
(solver-push)
(z3-assert (x :bool y :int)
           (and x (>= y 5)))
(check-sat)
(get-model)
(solver-pop)

;; But you can also add minimization and maximization objectives.
;; this is example 5.8.1 from
;; https://www.sfu.ca/math-coursenotes/Math%20157%20Course%20Notes/sec_Optimization.html
(solver-push)
(z3-assert (price :int nsold :int)
           (= nsold (+ 5000 (* 100 (- 150 price)))))
(optimize-maximize (price :int nsold :int)
                   (- (* nsold (- price 50)) 2000))
(check-sat)
(get-model)
(solver-pop)

;; You can also add soft constraints.
;; Note that soft constraints should be added before the objective
;; function, otherwise the soft constraints will not be taken into account.
;; See https://github.com/Z3Prover/z3/issues/2216
;; That's why we need to pop and add the same assertion and
;; optimization objective again, because we need the z3-assert-soft to
;; go in between them.
(solver-push)
(z3-assert (price :int nsold :int)
           (= nsold (+ 5000 (* 100 (- 150 price)))))
(z3-assert-soft (price :int nsold :int)
                (< nsold 7000)
                10) ;; weight (penalty for breaking this constraint)
(optimize-maximize (price :int nsold :int)
                   (- (* nsold (- price 50)) 2000))
(check-sat)
(get-model)
(solver-pop)
