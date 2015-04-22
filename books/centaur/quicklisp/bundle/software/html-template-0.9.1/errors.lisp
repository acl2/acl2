;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: HTML-TEMPLATE-LISP; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/html-template/errors.lisp,v 1.8 2007/01/01 23:49:16 edi Exp $

;;; Copyright (c) 2003-2007, Dr. Edmund Weitz. All rights reserved.

;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:

;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.

;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.

;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(in-package #:html-template)

(defstruct syntax-error-location
  "Structure to store parser locations consisting of a stream, a line
number, and a column number."
  line col stream)

(defvar *syntax-error-location* (make-syntax-error-location)
  "Used internally to remember the last position which made sense to
the parser.")

(define-condition template-error (simple-error)
  ()
  (:documentation "All errors signaled by HTML-TEMPLATE are of
this type."))
  
(define-condition template-invocation-error (template-error)
  ()
  (:documentation "Signaled when HTML-TEMPLATE functions are
invoked with wrong arguments."))
  
(define-condition template-missing-value-error (template-error)
  ()
  (:documentation "Signaled when a TMPL_VAR printer is provided
with a NIL value and *CONVERT-NIL-TO-EMPTY-STRING* is false."))
  
(define-condition template-not-a-string-error (template-error)
  ((value :initarg :value
          :reader template-not-a-string-error-value))
  (:documentation "Signaled when a TMPL_VAR printer is provided
with a non-string value."))
  
(define-condition template-syntax-error (template-error)
  ((line :initarg :line
         :reader template-syntax-error-line)
   (col :initarg :col
        :reader template-syntax-error-col)
   (stream :initarg :stream
           :reader template-syntax-error-stream))
  (:default-initargs
      :line (syntax-error-location-line *syntax-error-location*)
      :col (syntax-error-location-col *syntax-error-location*)
      :stream (syntax-error-location-stream *syntax-error-location*))
  (:report (lambda (condition stream)
             (format stream "~?~%[Line ~A, column ~A, stream ~A]"
                     (simple-condition-format-control condition)
                     (simple-condition-format-arguments condition)
                     (template-syntax-error-line condition)
                     (template-syntax-error-col condition)
                     (template-syntax-error-stream condition))))
  (:documentation "Signaled when a syntax error occurs while
parsing a template."))

(defmacro signal-template-invocation-error (format-control &rest format-arguments)
  `(error 'template-invocation-error
          :format-control ,format-control
          :format-arguments (list ,@format-arguments)))

(defmacro signal-template-missing-value-error (format-control &rest format-arguments)
  `(error 'template-missing-value-error
          :format-control ,format-control
          :format-arguments (list ,@format-arguments)))

(defmacro signal-template-syntax-error (format-control &rest format-arguments)
  `(error 'template-syntax-error
          :format-control ,format-control
          :format-arguments (list ,@format-arguments)))

(defmacro with-syntax-error-location ((&rest rest) &body body)
  "This is wrapped around forms in order to remember a meaningful
position within the stream in case an error has to be signaled."
  (declare (ignore rest))
  `(let ((*syntax-error-location* (make-syntax-error-location
                                   :line *current-line*
                                   :col *current-column*
                                   :stream *standard-input*)))
    ,@body))
