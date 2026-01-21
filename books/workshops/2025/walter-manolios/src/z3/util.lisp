;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3)

;; Create a C array from the given Common Lisp list.
;; If provided, elt-fn is a function to apply to each element of the
;; Common Lisp list before assigning the result to the appropriate
;; element of the C array.
(defmacro with-foreign-array ((array-var-name array-ty lisp-list &key (elt-fn '#'identity)) &body body)
  `(let ((array-len (length ,lisp-list)))
     (cffi:with-foreign-object
      (,array-var-name ',array-ty array-len)
      (loop for elt in ,lisp-list
            for i upto (1- array-len)
            do (setf (cffi:mem-aref ,array-var-name ',array-ty i) (funcall ,elt-fn elt)))
      ,@body)))

(defmacro with-foreign-arrays (array-specs &body body)
  (if array-specs
      `(with-foreign-array ,(car array-specs)
                           (with-foreign-arrays ,(cdr array-specs) ,@body))
    `(progn ,@body)))

(defun foreign-array-to-list (arr ty len)
  "Convert a foreign array of the given element type and length into a list."
  (loop for i below len
        collect (cffi:mem-aref arr ty i)))

;; Useful for testing.
(defmacro expect-error (&rest forms)
  `(handler-case (progn ,@forms)
     (error (c) (format t "~a~%" c))
     (:no-error (_) (declare (ignore _)) (error "Expected an error but none occurred!"))))

;; Useful for testing.
(defun fresh-env-from-spec-fn (var-specs context)
  (let* ((ctx (or context *default-context*))
         (env (make-instance 'environment-stack))
         (processed-specs (process-var-specs var-specs)))
    (check-processed-var-specs processed-specs)
    (setup-env processed-specs env ctx)
    env))

(defmacro fresh-env-from-spec (var-specs &optional context)
  `(fresh-env-from-spec-fn ',var-specs ,context))
