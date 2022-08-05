;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: CHUNGA; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/chunga/output.lisp,v 1.14 2008/05/24 03:06:22 edi Exp $

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

(defmethod chunked-stream-output-chunking-p ((object t))
  "The default method for all objects which are not of type
CHUNKED-OUTPUT-STREAM."
  nil)

(defmethod write-chunk ((stream chunked-output-stream) sequence
                        &key (start 0)
                             (end (length sequence)))
  "Writes the contents of SEQUENCE from START to END to the
underlying stream of STREAM as one chunk."
  (let ((output-stream (chunked-stream-stream stream)))
    ;; chunk size
    (loop for char across (format nil "~X" (- end start))
          do (write-byte (char-code char) output-stream))
    (write-sequence +crlf+ output-stream)
    ;; data
    (write-sequence sequence output-stream :start start :end end)
    (write-sequence +crlf+ output-stream)))

(defmethod flush-buffer ((stream chunked-output-stream))
  "Uses WRITE-CHUNK to empty the output buffer unless it is
already empty."
  (with-slots (output-buffer output-index)
      stream
    (when (plusp output-index)
      (write-chunk stream output-buffer :end output-index)
      (setq output-index 0))))

(defmethod (setf chunked-stream-output-chunking-p) (new-value (stream chunked-output-stream))
  "Switches output chunking for STREAM on or off."
  (unless (eq (not new-value) (not (chunked-stream-output-chunking-p stream)))
    (with-slots (real-stream output-index)
        stream
      (cond (new-value
             ;; get rid of "old" data
             (force-output real-stream)
             ;; initialize output buffer as being empty
             (setq output-index 0))
            (t (flush-buffer stream)
               ;; last chunk to signal end of chunking
               (write-byte #.(char-code #\0) real-stream)
               (write-sequence +crlf+ real-stream)
               (write-sequence +crlf+ real-stream)
               (force-output real-stream)))))
  (setf (slot-value stream 'output-chunking-p) new-value))

(defmethod stream-clear-output ((stream chunked-output-stream))
  "We clear output by resetting the output buffer and clearing
the underlying stream."
  (when (chunked-stream-output-chunking-p stream)
    (setf (slot-value stream 'output-index) 0))
  (clear-output (chunked-stream-stream stream)))

(defmethod stream-finish-output ((stream chunked-output-stream))
  "Flush the output buffer if output chunking is on, then operate
on the underlying stream."
  (when (chunked-stream-output-chunking-p stream)
    (flush-buffer stream))
  (finish-output (chunked-stream-stream stream)))

(defmethod stream-force-output ((stream chunked-output-stream))
  "Flush the output buffer if output chunking is on, then operate
on the underlying stream."
  (when (chunked-stream-output-chunking-p stream)
    (flush-buffer stream))
  (force-output (chunked-stream-stream stream)))

(defmethod stream-write-byte ((stream chunked-output-stream) byte)
  "Writes one byte by simply adding it to the end of the output
buffer \(if output chunking is enabled).  The buffer is flushed
if necessary."
  (unless (chunked-stream-output-chunking-p stream)
    (return-from stream-write-byte
      (write-byte byte (chunked-stream-stream stream))))
  (with-slots (output-index output-buffer)
      stream
    (when (>= output-index +output-buffer-size+)
      (flush-buffer stream))
    (setf (aref output-buffer output-index) byte)
    (incf output-index)
    byte))

(defmethod stream-write-sequence ((stream chunked-output-stream) sequence start end &key)
  "Outputs SEQUENCE by appending it to the output buffer if it's
small enough.  Large sequences are written directly using
WRITE-CHUNK."
  (unless (chunked-stream-output-chunking-p stream)
    (return-from stream-write-sequence
      (write-sequence sequence (chunked-stream-stream stream) :start start :end end)))
  (with-slots (output-buffer output-index)
      stream
    (let ((length (- end start)))
      (cond ((<= length (- +output-buffer-size+ output-index))
             (replace output-buffer sequence :start1 output-index
                      :start2 start :end2 end)
             (incf output-index length))
            (t (flush-buffer stream)
               (write-chunk stream sequence :start start :end end)))))
  sequence)

(defmethod close ((stream chunked-output-stream) &key abort)
  "When a stream is closed and ABORT isn't true we have to make
sure to send the last chunk."
  (unless abort
    (setf (chunked-stream-output-chunking-p stream) nil))
  (call-next-method))
