;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3)

(defun make-tactic (name &optional context)
  "Make an instance of the tactic with the given name. Will signal an
error if the name is incorrect."
  (let ((ctx (or context *default-context*)))
    (make-instance 'tactic
                   :handle (z3-mk-tactic ctx name)
                   :context ctx)))

(defun make-tactic-with-params (tac params &optional context)
  (let ((ctx (or context *default-context*)))
    (make-instance 'tactic
                   :handle (z3-tactic-using-params ctx tac params)
                   :context ctx)))
