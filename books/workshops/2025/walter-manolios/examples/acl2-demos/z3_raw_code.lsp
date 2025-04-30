;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package "ACL2S")
(load "../try-load-quicklisp.lisp")

(pushnew (truename "../../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

;; We need to define these fns in a package that ACL2 knows about so
;; that they can be referenced in defun-bridge.

(defun z3-assert-fn (types query)
  (z3::z3-assert-fn types query))

(defun z3-check-sat-fn ()
  (z3:check-sat))

(defun z3-get-model-as-assignment-fn ()
  (z3:get-model-as-assignment))

(defun z3-solver-init-fn ()
  (z3:solver-init))

(defun z3-solver-push-fn ()
  (z3:solver-push))

(defun z3-solver-pop-fn ()
  (z3:solver-pop))

(defun z3-default-context ()
  z3::*default-context*)

(defun z3-register-tuple-sort-fn (name fields ctx)
  (z3::register-tuple-sort-fn name fields ctx)
  name)

(defun z3-register-enum-sort-fn (name elements ctx)
  (z3::register-enum-sort-fn name elements ctx)
  name)

(defun z3-get-solver-stats-fn ()
  (z3::get-solver-stats))

(defun z3-set-solver (solver)
  (z3::set-solver solver))

(defun z3-make-solver-from-tactic-name (name)
  (z3::make-solver-from-tactic (z3::make-tactic name)))
