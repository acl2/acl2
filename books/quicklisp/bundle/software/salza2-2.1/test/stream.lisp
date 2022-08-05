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

(in-package #:salza2-test)

(defparameter *data-size* (* 10 1024))

(define-test compressing-stream
  "Test the compressing stream by round tripping random data through salza2 and
then chipz."
  (let ((data (make-array *data-size* :element-type '(unsigned-byte 8)
                                      :initial-contents (loop :repeat *data-size*
                                                              :collect (random 256))))
        (round-trip-data (make-array *data-size* :element-type '(unsigned-byte 8)
                                                 :initial-element 0))
        compressed-data)
    (setf compressed-data
          (flexi-streams:with-output-to-sequence (wrapped-stream)
            (with-open-stream
                (out-stream (salza2:make-compressing-stream 'salza2:gzip-compressor wrapped-stream))
              (write-sequence data out-stream))))
    (flexi-streams:with-input-from-sequence (wrapped-stream compressed-data)
      (with-open-stream
          (in-stream (chipz:make-decompressing-stream 'chipz:gzip wrapped-stream))
        (read-sequence round-trip-data in-stream)
        (is eql :eof (read-byte in-stream nil :eof))))
    (is equalp data round-trip-data)))

(define-test compressing-stream-closed-error
  (flexi-streams:with-output-to-sequence (wrapped-stream)
    (let ((out-stream (salza2:make-compressing-stream 'salza2:gzip-compressor wrapped-stream)))
      (write-byte 1 out-stream)
      (close out-stream)
      (fail (write-byte 2 out-stream) 'salza2:stream-closed-error))))
