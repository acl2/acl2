;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-uninterp-fns
  (:use :cl :z3)
  (:import-from :z3 :expect-error))

(in-package :z3-uninterp-fns)

(solver-init)

(solver-push)
;; To use an uninterpreted function in a z3-assert, you must declare
;; its signature in the same place that you declare variables.
;; (:fn (:int) ;int) represents a function that takes in a single
;; parameter that has :int sort, and produces a value of :int sort.
(z3-assert (f (:fn (:int) :int))
           ;; Uninterpeted functions are called just like interpreted
           ;; ones.
           (and (= (f 0) 3)
                (= (f 1) 8)))
(check-sat)
(get-model)
;; The model produced will contain an entry for the uninterpreted
;; function f. This entry consists of a list (:fn <type> <alist>),
;; where <type> is a list where the first element contains the sorts
;; of the parameters of f, and the second element is the sort of the
;; result of f, and <alist> is an alist representing a map from
;; parameter values to the function's value. Additionally, there will
;; be an entry in the alist whose car is :default, representing the
;; default value of the function when no other entry matches the
;; provided arguments.
(get-model-as-assignment)
(solver-pop)

(solver-push)
;; You can use variables and uninterpreted functions together.
(z3-assert (x :int f (:fn (:int) :int))
           (= (f x) (+ x 1)))
(check-sat)
(get-model)
(solver-pop)

(solver-push)
;; You can use multiple uninterpreted functions together and use their
;; results in calls to each other.
(z3-assert (f (:fn (:int) :string)
            g (:fn (:string) (_ :bitvec 4))
            h (:fn ((_ :bitvec 4)) :int))
           (and (= (h (g (f 3))) 5)
                (= (h (g (f 1))) 20)
                (= (f 1) "hello")
                (= (f 2) "world!")))
(check-sat)
(get-model)
(get-model-as-assignment)
(solver-pop)

(solver-push)
;; Uninterpreted functions can take multiple arguments.
(z3-assert (f (:fn (:int :int) :string))
           (and (= (f 0 0) "h")
                (= (f 0 1) "i")
                (= (f 1 0) "b")
                (= (f 1 1) "y")
                (= (f 1 2) "e")))
(check-sat)
(get-model)
(get-model-as-assignment)
(solver-pop)

(solver-push)
(z3-assert (f (:fn (:int) :int)
            x :int)
           (and (= (f x) x)
                (not (= (f (f x)) x))))
(check-sat)
(solver-pop)

;; Note that variables and uninterpreted function names are treated
;; identically by the interface, insofar as it is not possible to have
;; an uninterpreted function and a variable with the same name.

(solver-push)
(z3-assert (f :int) (= f 0))
;; This will fail.
(expect-error
 (z3-assert (f (:fn (:int) :int)) (= (f 0) 4)))
;; This will also fail.
(expect-error
 (z3-assert (g :int g (:fn (:int) :int))
            (= (g g) g)))
(solver-push)
