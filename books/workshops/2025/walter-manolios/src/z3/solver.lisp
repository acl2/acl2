;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3)

(defun make-simple-solver (&optional context)
  "Create a new incremental solver that will not apply any
logic-specific tactics or change its behavior based on whether it is
used incrementally or not. See `z3-mk-simple-solver` for more
information."
  (let ((ctx (or context (make-instance 'context))))
    (make-instance 'solver
                   :handle (z3-mk-simple-solver ctx)
                   :context ctx)))

(defun make-composite-solver (&optional context)
  "Create a new solver that internally consists of both a
non-incremental and an incremental solver. Which solver is used
depends on whether the composite solver is used in a incremental
way (e.g. `solver-push` or `solver-pop` are used, or the set of
assertions is modified after a call to `check-sat`). See `z3-mk-solver`
for more information."
  (let ((ctx (or context (make-instance 'context))))
    (make-instance 'solver
                   :handle (z3-mk-solver ctx)
                   :context ctx)))

(defun make-solver-for-logic (logic &optional context)
  "Create a new solver that is optimized for the logic with the given
name. Note that this will fail silently if the given logic isn't known
by Z3, creating the same solver as `make-simple-solver` in that case.
See `z3-mk-solver-for-logic` for more information."
  (let ((ctx (or context *default-context*)))
    (make-instance 'solver
                   :handle (z3-mk-solver-for-logic ctx (z3-mk-string-symbol ctx logic))
                   :context ctx)))

(defun make-solver-from-tactic (tactic &optional context)
  "Create a new solver that will operate using the given tactic. The
solver will not be incremental. See `z3-mk-solver-from-tactic` for more
information."
  (let ((ctx (or context *default-context*)))
    (make-instance 'solver
                   :handle (z3-mk-solver-from-tactic ctx tactic)
                   :context ctx)))

(defun make-optimizer (&optional context)
  "Create a solver that is capable of performing optimization."
  (let ((ctx (or context (make-instance 'context))))
    (make-instance 'optimizer
                   :handle (z3-mk-optimize ctx)
                   :context ctx)))

(defgeneric solver-assert (solver stmt)
  (:documentation "Assert a statement in a solver")
  (:method (solver stmt)
           ;; TBD try to convert
           (error "Currently we only support stmt arguments that are ASTs."))
  (:method ((solver solver) (stmt ast))
           (z3-solver-assert (get-context solver) solver stmt))
  (:method ((solver optimizer) (stmt ast))
           (z3-optimize-assert (get-context solver) solver stmt)))

(defgeneric solver-assert-soft (solver stmt weight)
  (:documentation "Assert a statement in a solver")
  (:method (solver stmt weight)
           (error "Currently we only support stmt arguments that are ASTs."))
  (:method ((solver solver) (stmt ast) weight)
           (error "Cannot add a soft assertion to a non-optimizer solver"))
  (:method ((solver optimizer) (stmt ast) weight)
           (z3-optimize-assert-soft (get-context solver)
                                    solver stmt
                                    (if (stringp weight) weight (write-to-string weight))
                                    (z3-mk-string-symbol (get-context solver) ""))))

(defun get-solver-help (&optional solver)
  (let ((slv (or solver *default-solver*)))
    (z3-solver-get-help (get-context slv) slv)))

(defun get-solver-param-descrs (&optional solver)
  (let ((slv (or solver *default-solver*)))
    (make-instance 'param-descrs
                   :handle (z3-solver-get-param-descrs (get-context slv) slv)
                   :context (get-context slv))))

(defgeneric get-solver-stats-fn (slv)
  (:method ((slv solver))
           (make-instance 'statistics
                          :handle (z3-solver-get-statistics (get-context slv) slv)
                          :context (get-context slv)))
  (:method ((slv optimizer))
            (make-instance 'statistics
                           :handle (z3-optimize-get-statistics (get-context slv) slv)
                           :context (get-context slv))))

(defun get-solver-stats (&optional solver)
  "Get statistics from the given solver."
  (get-solver-stats-fn (or solver *default-solver*)))

(defun set-params-fn (params solver)
  (let* ((ctx (get-context solver))
         (param-descrs (get-solver-param-descrs solver)))
    (z3-params-validate ctx params param-descrs)
    (when (equal (z3-get-error-code ctx) :OK)
      (z3-solver-set-params ctx solver params))))

(defmacro set-params (settings &optional solver)
  "Set some parameters on the given solver.
See the output of `get-solver-help` for contain information regarding
the name, meaning, default value, and set of acceptable values for
each available parameter."
  `(let ((slv (or ,solver *default-solver*)))
     (set-params-fn (make-params ,settings) slv)))

#|
;; This is an example of using the z3 bound functions to find a satisfying assignment
(let* ((config (z3-mk-config))
       (c (z3-mk-context config))
       (solver (z3-mk-simple-solver c))
       (x (z3-mk-const c
                       (z3-mk-string-symbol c "X")
                       (z3-mk-bool-sort c)))
       (y (z3-mk-const c
                       (z3-mk-string-symbol c "Y")
                       (z3-mk-bool-sort c)))
       (_ (z3-solver-assert c solver (z3-mk-xor c x y))))
  (list (z3-solver-check c solver)
        (z3-solver-get-model c solver)))
|#
