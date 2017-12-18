;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: CHUNGA; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/chunga/streams.lisp,v 1.10 2008/05/24 03:06:22 edi Exp $

;;; Copyright (c) 2006-2010, Dr. Edmund Weitz.  All rights reserved.

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

(defclass chunked-stream (trivial-gray-stream-mixin)
  ((real-stream :initarg :real-stream
                :reader chunked-stream-stream
                :documentation "The actual stream that's used for
input and/or output."))
  (:documentation "Every chunked stream returned by
MAKE-CHUNKED-STREAM is of this type which is a subtype of
STREAM."))

(defclass chunked-input-stream (chunked-stream fundamental-binary-input-stream)
  ((input-chunking-p :initform nil
                     :reader chunked-stream-input-chunking-p
                     :documentation "Whether input chunking is currently enabled.")
   (input-buffer :initform nil
                 :documentation "A vector containing the binary
data from the most recent chunk that was read.")
   (input-index :initform 0
                :accessor chunked-stream-input-index
                :documentation "The current position within INPUT-BUFFER.")
   (input-limit :initform 0
                :accessor chunked-stream-input-limit
                :documentation "Only the content in INPUT-BUFFER
up to INPUT-LIMIT belongs to the current chunk.")
   (chunk-extensions :initform nil
                     :reader chunked-input-stream-extensions
                     :documentation "An alist of attribute/value
pairs corresponding to the optional `chunk extensions' which
might be encountered when reading from a chunked stream.")
   (chunk-trailers :initform nil
                   :reader chunked-input-stream-trailers
                   :documentation "An alist of attribute/value
pairs corresponding to the optional `trailer' HTTP headers which
might be encountered at the end of a chunked stream.")
   (expecting-crlf-p :initform nil
                     :accessor expecting-crlf-p
                     :documentation "Whether we expect to see
CRLF before we can read the next chunk-size header part from the
stream.  \(This will actually be the CRLF from the end of the
last chunk-data part.)"))
  (:documentation "A chunked stream is of this type if its
underlying stream is an input stream. This is a subtype of
CHUNKED-STREAM."))

(defclass chunked-output-stream (chunked-stream fundamental-binary-output-stream)
  ((output-chunking-p :initform nil
                      :reader chunked-stream-output-chunking-p
                      :documentation "Whether output chunking is
currently enabled.")
   (output-buffer :initform (make-array +output-buffer-size+ :element-type '(unsigned-byte 8))
                  :accessor output-buffer
                  :documentation "A vector used to temporarily
store data which will output in one chunk.")
   (output-index :initform 0
                 :accessor output-index
                 :documentation "The current end of OUTPUT-BUFFER."))
  (:documentation "A chunked stream is of this type if its
underlying stream is an output stream. This is a subtype of
CHUNKED-STREAM."))

(defclass chunked-io-stream (chunked-input-stream chunked-output-stream)
  ()
  (:documentation "A chunked stream is of this type if it is both
a CHUNKED-INPUT-STREAM as well as a CHUNKED-OUTPUT-STREAM."))

(defmethod stream-element-type ((stream chunked-stream))
  "Chunked streams are always binary streams.  Wrap them with
flexi streams if you need a character stream."
  '(unsigned-byte 8))

(defmethod open-stream-p ((stream chunked-stream))
  "A chunked stream is open if its underlying stream is open."
  (open-stream-p (chunked-stream-stream stream)))

(defmethod close ((stream chunked-stream) &key abort)
  "If a chunked stream is closed, we close the underlying stream as well."
  (with-slots (real-stream)
      stream
    (cond ((open-stream-p real-stream)
           (close real-stream :abort abort))
          (t nil))))

(defun make-chunked-stream (stream)
  "Creates and returns a chunked stream \(a stream of type
CHUNKED-STREAM) which wraps STREAM.  STREAM must be an open
binary stream."
  (unless (and (streamp stream)
               (open-stream-p stream))
    (error 'parameter-error
           :stream stream
           :format-control "~S should have been an open stream."
           :format-arguments (list stream)))
  (make-instance ;; actual type depends on STREAM
                 (cond ((and (input-stream-p stream)
                             (output-stream-p stream))
                        'chunked-io-stream)
                       ((input-stream-p stream)
                        'chunked-input-stream)
                       ((output-stream-p stream)
                        'chunked-output-stream))
                 :real-stream stream))