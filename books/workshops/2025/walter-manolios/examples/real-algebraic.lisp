;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-real-algebraic
  (:use :cl :z3))

(in-package :z3-real-algebraic)

(solver-init)

(solver-push)
(z3-assert
 (x :real)
 (and (not (= x 0))
      (= (* 20 x) 1)))
(check-sat)
(get-model)
(get-model-as-assignment)
(solver-pop)

(solver-push)
(z3-assert
 (x :real)
 (= (* x x) 2))
(check-sat)
(get-model)
;; Algebraic numbers are turned into Lisp floats by default, potentially
;; causing loss of precision. You can control this with the
;; *ALGEBRAIC-NUMBER-CONVERT-MODE* parameter. See the docstring in
;; (describe '*ALGEBRAIC-NUMBER-CONVERT-MODE*) for more information.
(get-model-as-assignment)
(solver-pop)
