;;;
;;; Copyright (c) 2021 Eric Timmons, All Rights Reserved
;;;
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:
;;;
;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.
;;;
;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.
;;;
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
;;;

(in-package #:salza2)

(define-condition stream-closed-error (stream-error)
  ()
  (:documentation "Signaled when attempting to write to a closed COMPRESSING-STREAM.")
  (:report (lambda (condition stream)
             (format stream "Stream ~S is closed" (stream-error-stream condition)))))

(defclass compressing-stream (trivial-gray-streams:fundamental-binary-output-stream)
  ((openp
    :initform t
    :accessor openp)
   (compressor
    :initarg :compressor
    :accessor compressor))
  (:documentation
   "A gray stream that transparently compresses its input and writes the
compressed data to another stream."))

(defun make-compressing-stream (compressor-type stream)
  "Return a COMPRESSING-STREAM that transparently compresses its input and
writes it to STREAM. COMPRESSOR-TYPE is a symbol naming the compressor class to
use.

Closing the returned COMPRESSING-STREAM merely finalizes the compression and
does not close STREAM."
  (make-instance
   'compressing-stream
   :compressor (make-instance
                compressor-type
                :callback (make-stream-output-callback stream))))


(defmethod trivial-gray-streams:stream-write-byte ((stream compressing-stream) byte)
  (unless (openp stream)
    (error 'stream-closed-error :stream stream))
  (compress-octet byte (compressor stream))
  byte)

(defmethod trivial-gray-streams:stream-write-sequence ((stream compressing-stream) sequence start end &key)
  (unless (openp stream)
    (error 'stream-closed-error :stream stream))
  (let ((vector (if (typep sequence 'vector)
                    sequence
                    (coerce sequence 'vector))))
    (compress-octet-vector vector (compressor stream) :start start :end end))
  sequence)

(defmethod trivial-gray-streams:stream-file-position ((stream compressing-stream))
  "Does not keep track of position in the stream."
  nil)

(defmethod (setf trivial-gray-streams:stream-file-position) (newval (stream compressing-stream))
  "Unable to seek within the stream."
  (declare (ignore newval))
  nil)

(defmethod stream-element-type ((stream compressing-stream))
  '(unsigned-byte 8))

(defmethod close ((stream compressing-stream) &key abort)
  (declare (ignore abort))
  (when (openp stream)
    (finish-compression (compressor stream))
    (setf (openp stream) nil)
    t))
