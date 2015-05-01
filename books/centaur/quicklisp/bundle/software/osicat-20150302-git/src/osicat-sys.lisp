;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; osicat-sys.lisp --- Early Osicat infrastructure.
;;;
;;; Copyright (C) 2007, Luis Oliveira  <loliveira@common-lisp.net>
;;;
;;; Permission is hereby granted, free of charge, to any person
;;; obtaining a copy of this software and associated documentation
;;; files (the "Software"), to deal in the Software without
;;; restriction, including without limitation the rights to use, copy,
;;; modify, merge, publish, distribute, sublicense, and/or sell copies
;;; of the Software, and to permit persons to whom the Software is
;;; furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;; DEALINGS IN THE SOFTWARE.

(in-package #:cl-user)

(defpackage #:osicat-sys
  (:use #:common-lisp #:alexandria #:cffi)
  (:export
   ;; Conditions
   #:bug
   #:system-error
   #:system-error-code
   #:system-error-identifier
   #:system-error-message
   #:unsupported-function
   #:define-unsupported-functions

   ;; Functions
   #:native-namestring

   ;; Type Designators
   #:filename
   #:filename-designator
   #:file-descriptor
   #:file-descriptor-designator

   ;; FFI constants
   #:size-of-char
   #:size-of-int
   #:size-of-long
   #:size-of-long-long
   #:size-of-pointer
   #:size-of-short

   ;; KLUDGE: intern this symbol early because OSICAT-POSIX needs it.
   ;; The OSICAT package re-exports it later.
   #:get-monotonic-time
   ))

(in-package #:osicat-sys)

;;;; Conditions

(define-condition bug (error)
  ((message :reader message :initarg :message))
  (:report (lambda (condition stream)
             (format stream "~A. This seems to be a bug in Osicat. ~
                             Please report on osicat-devel@common-lisp.net."
                     (message condition)))))

(defun bug (control &rest args)
  (error 'bug :message (format nil "~?" control args)))

(define-condition system-error (error)
  ((code :reader system-error-code :initarg :code :type (or null integer)
         :documentation "Numeric error code, or NIL.")
   (identifier :reader system-error-identifier :initarg :identifier
               :type symbol :documentation "Keyword identifier, or NIL.")
   (message :reader system-error-message :initarg :message
            :documentation "Error description."))
  (:default-initargs :code nil
                     :identifier :unknown-error)
  (:documentation "Base class for errors signalled by Osicat."))

(defun system-error (control-string &rest args)
  (error 'system-error :message (format nil "~?" control-string args)))

(define-condition unsupported-function (error)
  ((function :initarg :function :reader uf-function))
  (:report (lambda (condition stream)
             (format stream "The function ~S is not present on this platform."
                     (uf-function condition))))
  (:documentation
   "Condition signalled when an unsupported function is invoked."))

(defmacro unsupported-function (name)
  `(progn
     (defun ,name (&rest args)
       (declare (ignore args))
       (error 'unsupported-posix-function :function ',name))

     ;; signal a compile-time warning as well.
     (define-compiler-macro ,name (&whole form &rest args)
       (declare (ignore args))
       (unless (eq *package* (find-package '#:osicat-tests))
         (warn "The function ~S is not present on this platform." ',name))
       form)))

(defmacro define-unsupported-functions (&body functions)
  `(progn
     ,@(loop for fn in functions collect
             `(unsupported-function ,fn))))

;;;; Type Designators

(defmacro define-designator (name cffi-type &body type-clauses)
  (let ((type `(quote (or ,@(mapcar #'car type-clauses))))
        (ctype (alexandria:format-symbol t "~A-~A" name '#:designator)))
    `(progn
       (deftype ,name () ,type)
       (defun ,name (,name)
         (etypecase ,name
           ,@type-clauses))
       (define-foreign-type ,ctype ()
         ()
         (:simple-parser ,ctype)
         (:actual-type ,cffi-type))
       (defmethod expand-to-foreign (value (type ,ctype))
         `(convert-to-foreign
           (let ((,',name ,value))
             (etypecase ,',name ,@',type-clauses))
           ,',cffi-type)))))

(declaim (inline native-namestring))
(defun native-namestring (pathname)
  (cffi-sys:native-namestring pathname))

;;; NATIVE-NAMESTRING should take care of complaining when FILENAME
;;; is wild but I don't think it does on all Lisps, so let's check it
;;; explicitly.
(define-designator filename :string
  (pathname (when (wild-pathname-p filename)
              (system-error "Pathname is wild: ~S." filename))
            (native-namestring (translate-logical-pathname filename)))
  (string filename))

(define-designator pointer-or-nil :pointer
  (null (null-pointer))
  (foreign-pointer pointer-or-nil))

;;; This can be specialized by, e.g., the IO-STREAMS library.
;;;
;;; Should probably signal an error when a stream has more than one
;;; associated FD.
(defgeneric get-stream-fd (stream)
  (:documentation "Generic function that can be specialized for
different kinds of streams.  Returns the FD of STREAM."))

#+sbcl
(defmethod get-stream-fd ((stream file-stream))
  (sb-sys:fd-stream-fd stream))

(define-designator file-descriptor :int
  (stream (get-stream-fd file-descriptor))
  (integer file-descriptor))

;;;; Sizes of Standard Types

(defconstant size-of-char (foreign-type-size :char))
(defconstant size-of-int (foreign-type-size :int))
(defconstant size-of-long (foreign-type-size :long))
(defconstant size-of-long-long (foreign-type-size :long-long))
(defconstant size-of-pointer (foreign-type-size :pointer))
(defconstant size-of-short (foreign-type-size :short))
