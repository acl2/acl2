;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: ODD-STREAMS; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/odd-streams/conditions.lisp,v 1.5 2007/12/31 01:08:45 edi Exp $

;;; Copyright (c) 2008-2010, Dr. Edmund Weitz.  All rights reserved.

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

(in-package :chunga)

(define-condition chunga-condition (condition)
  ()
  (:documentation "Superclass for all conditions related to Chunga."))

(define-condition chunga-error (chunga-condition stream-error)
  ()
  (:documentation "Superclass for all errors related to Chunga.  This
is a subtype of STREAM-ERROR, so STREAM-ERROR-STREAM can be used to
access the offending stream."))

(define-condition chunga-simple-error (chunga-error simple-condition)
  ()
  (:documentation "Like CHUNGA-ERROR but with formatting capabilities."))

(define-condition parameter-error (chunga-simple-error)
  ()
  (:documentation "Signalled if a function was called with
inconsistent or illegal parameters."))

(define-condition syntax-error (chunga-simple-error)
  ()
  (:documentation "Signalled if Chunga encounters wrong or unknown
syntax when reading data."))

(define-condition chunga-warning (chunga-condition warning)
  ()
  (:documentation "Superclass for all warnings related to Chunga."))

(define-condition chunga-simple-warning (chunga-warning simple-condition)
  ()
  (:documentation "Like CHUNGA-WARNING but with formatting capabilities."))

(define-condition input-chunking-unexpected-end-of-file (chunga-error)
  ()
  (:documentation "A condition of this type is signaled if we reach an
unexpected EOF on a chunked stream with input chunking enabled."))

(define-condition input-chunking-body-corrupted (chunga-error)
  ((last-char :initarg :last-char
              :documentation "The \(unexpected) character which was read.")
   (expected-chars :initarg :expected-chars
                   :documentation "The characters which were expected.
A list of characters or one single character."))
  (:report (lambda (condition stream)
             (with-slots (last-char expected-chars)
                 condition
               (format stream "Chunked stream ~S seems to be corrupted.
Read character ~S, but expected ~:[a member of ~S~;~S~]."
                       (stream-error-stream condition)
                       last-char (atom expected-chars) expected-chars))))
  (:documentation "A condition of this type is signaled if an
unexpected character \(octet) is read while reading from a chunked
stream with input chunking enabled."))
