;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3)

(defun guess-param-type (value)
  (match value
         ((type boolean) :bool)
         ((satisfies integerp) :uint)
         ((type real) :double)
         ((or (type string) (type symbol)) :symbol)
         (otherwise (error "Unable to guess the type of the parameter value ~S. Try providing an explicit type for it." value))))

(defun params-set (params name value context &optional ty)
  (let ((ty (if ty ty (guess-param-type value)))
        (name-sym (z3-mk-string-symbol context name)))
    (match ty
           (:bool
            (assert (typep value 'boolean))
            (z3-params-set-bool context params name-sym value))
           (:uint
            (assert (or (zerop value) (plusp value)))
            (z3-params-set-uint context params name-sym value))
           (:double
            (assert (realp value))
            (z3-params-set-double context params name-sym (float value 1.0d0)))
           (:symbol
            (assert (or (stringp value) (symbolp value)))
            (let ((value-as-str (if (stringp value) value (string-downcase (symbol-name value)))))
              (z3-params-set-symbol context params name-sym (z3-mk-string-symbol context value-as-str))))
           (otherwise (error "Unknown parameter type ~S for parameter ~S." ty name)))))

(defun make-params-fn (settings context)
  (let ((params (make-instance 'params :handle (z3-mk-params context) :context context)))
    (z3-params-inc-ref context params)
    (loop for setting in settings
          do (let* ((name (string-downcase (symbol-name (car setting))))
                    (value (second setting))
                    (ty (third setting)))
               (params-set params name value context ty)))
    params))

(defmacro make-params ((&rest settings) &optional context)
  `(let ((ctx (or ,context *default-context*)))
     (make-params-fn ',settings ctx)))
