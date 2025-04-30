;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3)

;; We create these classes so that we can catch cases where the user
;; doesn't initialize the solver and context before using the
;; interface.
(defclass unset-context (context) ())
(defmethod translate-to-foreign ((v unset-context) (type z3-c-types::Z3_config))
  (error "You need to call (solver-init) before calling other Z3 interface functions!"))
(defmethod print-object ((obj unset-context) stream)
  (print-unreadable-object (obj stream :type t)
                           (format stream "~A" "CONTEXT NOT SET - NEED TO (SOLVER-INIT)")))

(defclass unset-solver (solver) ())
(defmethod translate-to-foreign ((v unset-solver) (type z3-c-types::Z3_solver))
  (error "You need to call (solver-init) before calling other Z3 interface functions!"))
(defmethod z3-object-to-string ((obj unset-solver))
  "SOLVER NOT SET - NEED TO (SOLVER-INIT)")
(defmethod initialize-instance :after ((obj unset-solver) &key) nil)
(defmethod get-context ((v unset-solver))  (error "You need to call (solver-init) before calling other Z3 interface functions!"))

(defparameter *default-context* (make-instance 'unset-context :handle nil))
(defparameter *default-solver* (make-instance 'unset-solver :handle nil :context *default-context*))

(defun set-solver (solver)
  (setf *default-solver* solver))
