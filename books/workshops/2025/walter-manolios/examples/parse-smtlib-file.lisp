;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-parse-smtlib
  (:use :cl :z3))

(in-package :z3-parse-smtlib)

;; Even though we're not using the solver, we want to initialize the
;; context and attach error handlers.
(solver-init)

(defvar *assertions* (parse-smt2-file "example-smtlib-file.smt2"))

;; parse-smt2-file will produce an ast-vector of the assertions from the smt2 file.
(format t "~a" *assertions*)

;; You can convert it to a list of ASTs using the ast-vector-to-list method.
(format t "~S" (ast-vector-to-list *assertions*))
