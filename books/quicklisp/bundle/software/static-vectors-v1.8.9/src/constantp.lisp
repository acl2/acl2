;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-
;;;
;;; --- Checking for compile-time constance and evaluating such forms
;;;

(in-package :static-vectors)

(defun quotedp (form)
  (and (listp form)
       (= 2 (length form))
       (eql 'quote (car form))))

(defun constantp (form &optional env)
  (let ((form (if (symbolp form)
                  (macroexpand form env)
                  form)))
    (or (quotedp form)
        (cl:constantp form))))

(defun eval-constant (form &optional env)
  (declare (ignorable env))
  (cond
    ((quotedp form)
     (second form))
    (t
     #+clozure
     (ccl::eval-constant form)
     #+sbcl
     (sb-int:constant-form-value form env)
     #-(or clozure sbcl)
     (eval form))))

(defun canonicalize-args (env element-type length)
  (let* ((eltype-spec (or (and (constantp element-type)
                               (ignore-errors
                                (upgraded-array-element-type
                                 (eval-constant element-type))))
                          '*))
         (length-spec (if (constantp length env)
                          `,(eval-constant length env)
                          '*))
         (type-decl (if (eql '* eltype-spec)
                        'simple-array
                        `(simple-array ,eltype-spec (,length-spec)))))
    (values (if (eql '* eltype-spec)
                element-type
                `(quote ,eltype-spec))
            (if (eql '* length-spec)
                length
                length-spec)
            type-decl)))
