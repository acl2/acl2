;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3)

(defun make-config ()
  (make-instance 'config))

(defun del-config (config)
  (z3-c::z3-del-config config))

(defun set-config-param (config id value)
  (z3-c::z3-set-param-value config id value))

(defun reset-global-params ()
  (z3-c::z3-global-param-reset-all))

(defun set-global-param (id value)
  "Set the global parameter with the given id to the given value.
   Prints a warning if no such parameter exists or if the value is of an incorrect type."
  (z3-c::z3-global-param-set id value))

(defun get-global-param (id)
  "Get a string representing the current value of the global parameter with the given id.
   Returns nil and prints a warning if no such parameter exists."
  (with-foreign-pointer (retval 1)
                        (z3-c::z3-global-param-get id retval)
                        (values (foreign-string-to-lisp (mem-ref retval :pointer)))))
