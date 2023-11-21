;;;; -*- Mode: LISP; Syntax: ANSI-Common-lisp; Base: 10; Package: BORDEAUX-THREADS-2 -*-
;;;; The above modeline is required for Genera. Do not change.

(in-package :bordeaux-threads-2)

(defconstant +supports-threads-p+
  #+thread-support t
  #-thread-support nil
  "This should be set to T if the running instance has thread support.")

#+thread-support
(eval-when (:compile-toplevel :load-toplevel :execute)
  (pushnew :bordeaux-threads *features*))

(defun bool (thing) (if thing t nil))

(define-condition bordeaux-threads-error (error) ())

(define-condition abnormal-exit (bordeaux-threads-error)
  ((exit-condition :initarg :condition
                   :reader abnormal-exit-condition))
  (:report (lambda (condition stream)
             (format stream "Thread exited with condition: ~A"
                     (abnormal-exit-condition condition)))))

(define-condition bordeaux-threads-simple-error
    (simple-error bordeaux-threads-error)
  ())

(defun bt-error (msg &rest args)
  (error 'bordeaux-threads-simple-error
         :format-control msg
         :format-arguments args))

(define-condition not-implemented (bordeaux-threads-error)
  ())

(define-condition operation-not-implemented (not-implemented)
  ((operation :initarg :operation :reader operation-not-implemented-operation))
  (:report (lambda (condition stream)
             (format stream "Operation not implemented: ~A"
                     (operation-not-implemented-operation condition)))))

(define-condition keyarg-not-implemented (not-implemented)
  ((operation :initarg :operation :reader keyarg-not-implemented-operation)
   (keyarg :initarg :keyarg :reader keyarg-not-implemented-keyarg))
  (:report (lambda (condition stream)
             (format stream "~A does not implement argument ~S"
                     (keyarg-not-implemented-operation condition)
                     (keyarg-not-implemented-keyarg condition)))))

(defun signal-not-implemented (op &optional keyarg)
  (if keyarg
      (error 'keyarg-not-implemented :operation op :keyarg keyarg)
      (error 'operation-not-implemented :operation op)))

(defparameter *not-implemented* (make-hash-table :test #'equal))

(defun mark-not-implemented (op &rest features)
  (setf (gethash op *not-implemented*) features))

(defun implemented-p (op &optional feature)
  (multiple-value-bind (missing-features found)
      (gethash op *not-implemented*)
    (cond
      ((not found)
       t)
      (t
       (if (null feature)
           (not (null missing-features))
           (find feature missing-features))))))

(defun implemented-p* (op &optional feature)
  (if (implemented-p op feature)
      '(:and)
      '(:or)))

#-sbcl
(define-condition timeout (serious-condition)
  ((length :initform nil
             :initarg :length
             :reader timeout-length))
  (:report (lambda (c s)
             (if (timeout-length c)
                 (format s "A timeout set to ~A seconds occurred."
                         (timeout-length c))
                 (format s "A timeout occurred.")))))
