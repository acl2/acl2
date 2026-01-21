;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-sets
  (:use :cl :z3))

(in-package :z3-sets)

(solver-init)

(solver-push)
(z3-assert (x (:set :int))
           (= x (set.insert 1 2 3 (as set.empty (:set :int)))))
(check-sat)
(get-model)
(solver-pop)

(solver-push)
;; We use CVC5's set operation names here, as Z3 does not expose set
;; operations via its SMT-LIB2 interface.
(z3-assert (x y (:set :int))
           (and (set.member 1 y)
                (= x (set.minus (set.insert 1 2 (as set.empty (:set :int)))
                                (set.singleton 1)))))

(check-sat)
(get-model)
(solver-pop)

(solver-push)

(z3-assert (x :bool y (:set :int) z :bool w (:set :int))
           (and (= x (set.member 1 (set.singleton 1)))
                (= y (set.minus (set.insert 1 2 (as set.empty (:set :int)))
                                     (set.singleton 1)))
                ;; complementing the full set \ 2 produces the same set as y
                (= z (= y (set.complement (set.minus (as set.universe (:set :int)) (set.singleton 2)))))
                (= w (as set.universe (:set :int)))))

;; we represent sets as alists when converting to Lisp. Every set must
;; have a :default key in the alist, typically associated with nil.
(check-sat)
(get-model)
(get-model-as-assignment)
;; Note that we also get an |array-ext| element in our output here.
;; This is an artifact of how Z3's theory of arrays works.
;; See the following link for more information:
;; https://github.com/Z3Prover/z3/discussions/6089

