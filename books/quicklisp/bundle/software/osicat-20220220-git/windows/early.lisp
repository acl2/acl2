;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-
;;;
;;; early.lisp --- Early definitions used throughout OSICAT-WINDOWS.
;;;
;;; Copyright (C) 2005-2006, Matthew Backes  <lucca@accela.net>
;;; Copyright (C) 2005-2006, Dan Knapp  <dankna@accela.net>
;;; Copyright (C) 2006-2007, Stelian Ionescu  <stelian.ionescu-zeus@poste.it>
;;; Copyright (C) 2007, Luis Oliveira  <loliveira@common-lisp.net>
;;; Copyright (c) 2021, Eric Timmons   <eric@timmons.dev>
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

(in-package #:osicat-windows)


;;; Early types

(defctype bool (:boolean :uchar))
(defctype wchar :uint16)
(defctype large-integer :int64)
(defctype search-handle :pointer)
(defctype handle :pointer)
(defctype dword :uint32)

;;; We'll define the translators for this later, once we've set up the needed
;;; foreign functions.
(define-foreign-type wide-string ()
  ()
  (:actual-type :pointer))

(define-parse-method wide-string ()
  (make-instance 'wide-string))


(define-foreign-type wide-filename ()
  ()
  (:actual-type :pointer))

(define-parse-method wide-filename ()
  (make-instance 'wide-filename))

;;; Subtypes of WIN32-ERROR correspond to errors detected through the
;;; GetLastError mechanism.  These are defined below.
(define-condition win32-error (system-error)
  ((syscall :initform nil :initarg :syscall :reader win32-error-syscall))
  (:documentation
   "WIN32-ERRORs are signalled whenever GetLastError is set by a call or where
the call signals an error via the return value.")
  (:report (lambda (condition stream)
             (format stream "Error calling ~S~%~%~A"
                     (win32-error-syscall condition)
                     (get-error-message (system-error-code condition))))))

(defun win32-error (&optional (error-code (get-last-error)) syscall)
  (error (make-instance 'win32-error :code error-code :syscall syscall)))

;;; Default ERROR-GENERATOR for ERRNO-WRAPPER.
(defun syscall-signal-win32-error (return-value syscall)
  (declare (ignore return-value))
  (win32-error (get-last-error) syscall))

;;; Error predicate that always returns NIL.  Not actually used
;;; because the WIN32-ERROR-WRAPPER optimizes this call away.
(defun never-fails (&rest args)
  (declare (ignore args))
  nil)

;;; This type is used by DEFWINAPI to automatically check for errors
;;; using the ERROR-PREDICATE function which is passed the foreign
;;; function's return value (after going through RETURN-FILTER).  If
;;; ERROR-PREDICATE returns true, ERROR-GENERATOR is invoked.  See the
;;; ERRNO-WRAPPER parse method and type translation.
(define-foreign-type win32-error-wrapper ()
  ((error-predicate :initarg :error-predicate :reader error-predicate)
   (return-filter :initarg :return-filter :reader return-filter)
   (error-generator :initarg :error-generator :reader error-generator)
   (base-type :initarg :base-type :reader base-type)
   (function-name :initarg :function-name :reader function-name)))

(define-parse-method win32-error-wrapper
    (base-type &key error-predicate (return-filter 'identity)
               (error-generator 'syscall-signal-win32-error)
               function-name)
  ;; pick a default error-predicate
  (unless error-predicate
    (ecase base-type
      ((handle search-handle)
       (setf error-predicate '(lambda (p) (= (pointer-address p) +invalid-handle-value+))))
      (:pointer
       (setf error-predicate 'null-pointer-p))
      ((dword large-integer :int)
       (setf error-predicate 'zerop))
      ((bool :bool)
       (setf error-predicate 'not))))
  (make-instance 'win32-error-wrapper
                 :actual-type base-type
                 :base-type base-type
                 :error-predicate error-predicate
                 :return-filter return-filter
                 :error-generator error-generator
                 :function-name function-name))

;;; This type translator sets up the appropriate calls to
;;; RETURN-FILTER, ERROR-PREDICATE and ERROR-GENERATOR around the
;;; foreign function call.
(defmethod expand-from-foreign (value (type win32-error-wrapper))
  (if (and (eq (return-filter type) 'identity)
           (eq (error-predicate type) 'never-fails))
      value
      `(let ((r (convert-from-foreign ,value ',(base-type type))))
         ,(let ((return-exp (if (eq (return-filter type) 'identity)
                               'r
                               `(,(return-filter type) r))))
            (if (eq (error-predicate type) 'never-fails)
                return-exp
                `(if (,(error-predicate type) r)
                     (,(error-generator type) r ',(function-name type))
                     ,return-exp))))))

(defmacro defrawwinapi (name-and-opts return-type &body params)
  (multiple-value-bind (lisp-name c-name options)
      (cffi::parse-name-and-options name-and-opts)
    `(defcfun (,c-name ,lisp-name :convention :stdcall ,@options) ,return-type
       ,@params)))

(defmacro defwinapi (name-and-opts return-type &body args)
  (multiple-value-bind (lisp-name c-name options)
      (cffi::parse-name-and-options name-and-opts)
    (declare (ignore c-name options))
    `(defrawwinapi ,name-and-opts (win32-error-wrapper ,return-type :function-name ,lisp-name)
       ,@args)))
