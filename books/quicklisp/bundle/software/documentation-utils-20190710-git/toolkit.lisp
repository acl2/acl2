#|
 This file is a part of documentation-utils
 (c) 2016 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.documentation-utils)

(defvar *documentation-tests* ())

(defun documentation-test (type)
  (cdr (assoc type *documentation-tests*)))

(defun (setf documentation-test) (test type)
  (if (assoc type *documentation-tests*)
      (setf (cdr (assoc type *documentation-tests*)) test)
      (push (cons type test) *documentation-tests*)))

(defun remove-documentation-test (type)
  (setf *documentation-tests*
        (remove type *documentation-tests* :key #'car)))

(defmacro define-documentation-test (type args &body body)
  `(setf (documentation-test ',type)
         (lambda ,args ,@body)))

(defvar *documentation-translators* ())

(defun documentation-translator (type)
  (or (cdr (assoc type *documentation-translators*))
      (lambda (form)
        `(documentation ',(if (listp form) (first form) form) ',type))))

(defun (setf documentation-translator) (translator type)
  (if (assoc type *documentation-translators*)
      (setf (cdr (assoc type *documentation-translators*)) translator)
      (push (cons type translator) *documentation-translators*)))

(defun remove-documentation-translator (type)
  (setf *documentation-translators*
        (remove type *documentation-translators* :key #'car)))

(defmacro define-documentation-translator (type args &body body)
  `(setf (documentation-translator ',type)
         (lambda ,args ,@body)))

(defmacro define-documentation-alias (alias type)
  `(setf (documentation-translator ',alias)
         (lambda (form) (funcall (documentation-translator ',type) form))))

(defun list-symbols (package &key (internal T))
  (let ((symbs ())
        (package (find-package package)))
    (do-symbols (symb package (sort symbs #'string<))
      (when (and (eql (symbol-package symb) package)
                 (or internal (eql :external (nth-value 1 (find-symbol (string symb) package)))))
        (push symb symbs)))))

(defun check (&key (package *package*) (internal T))
  (loop for (type . test) in (sort (copy-list *documentation-tests*)
                                   #'string< :key #'car)
        for reader = (documentation-translator type)
        do (dolist (symb (list-symbols package :internal internal))
             (when (and (funcall test symb) (not (handler-bind ((warning #'muffle-warning)) (documentation symb type))))
               (warn "No documentation for ~(~a~) ~a." type symb)))))

(defclass documentation-formatter ()
  ())

(defgeneric format-documentation (formatter type var documentation))

(defclass plain-formatter (documentation-formatter)
  ())

(defmethod format-documentation ((formatter plain-formatter) type var documentation)
  (check-type documentation string)
  documentation)

(defun split-body-options (body)
  (values (loop for list = body then rest
                for (key val . rest) = list
                while (and (cdr list) (keywordp key))
                collect key collect val
                finally (setf body list))
          body))

(defun removef (plist &rest keys)
  (loop for (key val) on plist by #'cddr
        for test = (find key keys)
        unless test collect key
        unless test collect val))

(defvar *default-formatter* (make-instance 'plain-formatter))

(defmacro define-docs (&body expressions)
  (multiple-value-bind (options expressions) (split-body-options expressions)
    (let* ((formatter (or (getf options :formatter)
                          *default-formatter*))
           (formatter (apply (etypecase formatter
                               (documentation-formatter #'reinitialize-instance)
                               (symbol #'make-instance))
                             formatter (removef options :formatter))))
      `(progn
         ,@(loop for expr in expressions
                 for length = (length expr)
                 for type = (if (< 2 length) (first expr) 'function)
                 for var = (if (< 2 length) (rest (butlast expr)) (butlast expr))
                 for doc = (car (last expr))
                 collect `(setf ,(funcall (documentation-translator type) var)
                                ,(format-documentation formatter type var doc)))))))

(trivial-indent:define-indentation define-docs (&rest (&whole 2 0 &body)))

(setf (documentation-test 'function) #'fboundp)
(setf (documentation-test 'variable) #'boundp)
(setf (documentation-test 'compiler-macro) #'compiler-macro-function)
(setf (documentation-test 'package) #'find-package)

(define-documentation-test type (symb)
  (find-class symb NIL))

(define-documentation-translator method (expr)
  (destructuring-bind (func &rest quals-specs) expr
    (let* ((qualifiers (butlast quals-specs))
           (specializers (car (last quals-specs)))
           (clean-specs (loop for arg in specializers
                              until (find arg lambda-list-keywords)
                              collect (if (listp arg) (second arg) T))))
      `(documentation (find-method #',func ',qualifiers ',clean-specs) 't))))

(define-documentation-alias defun function)
(define-documentation-alias defmacro function)
(define-documentation-alias defgeneric function)
(define-documentation-alias defmethod method)
(define-documentation-alias defvar variable)
(define-documentation-alias defparameter variable)
(define-documentation-alias defconstant variable)
(define-documentation-alias defclass type)
(define-documentation-alias defstruct type)
(define-documentation-alias define-condition type)
(define-documentation-alias deftype type)
(define-documentation-alias define-method-combination method-combination)
(define-documentation-alias define-compiler-macro compiler-macro)
(define-documentation-alias defpackage package)
