;; SPDX-FileCopyrightText: Copyright (c) 2025 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-arithmetic
  (:use :cl :z3)
  (:import-from :z3 :expect-error))

(in-package :z3-arithmetic)

(solver-init)

(solver-push)
(z3-assert (x y z :int)
           (= (div x y) z))
(check-sat)
(get-model)
(solver-pop)

(solver-push)
(expect-error
 (z3-assert (x z :int y :real)
            (= (div x y) z)))
;; This would be the right way to do it
(z3-assert (x z :int y :real)
           (= (div x (to_int y)) z))
(check-sat)
(get-model)
(solver-pop)

(solver-push)
(z3-assert (x y z :bool)
           ((_ at-most 2) x y z))
(check-sat)
(get-model)
(solver-pop)

(solver-push)
(z3-assert (x :int y z :real)
           (and (> x 0)
                (> y 1)
                (= z (/ y (to_real x)))))
(check-sat)
(get-model)
(solver-pop)
