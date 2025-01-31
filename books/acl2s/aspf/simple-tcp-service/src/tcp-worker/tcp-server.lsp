;; SPDX-FileCopyrightText: Copyright (c) 2021 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: BSD-3-Clause
(in-package :server)

;; The handler should signal this to indicate that the server should
;; shutdown.
(define-condition handler-shutdown-request () ())

;; Uncomment this line to enable debug messages
;;(push :lisp-server-debug cl:*features*)

;; Parts of this file adapted from/inspired by
;; https://gist.github.com/traut/648dc0d7b22fdfeae6771a5a4a19f877
;; That code is licensed under the BSD 3-Clause License, as shown
;; below.

; BSD 3-Clause License
; 
; Copyright (c) 2018, Sergey Polzunov
; All rights reserved.
; 
; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are met:
; 
; * Redistributions of source code must retain the above copyright notice, this
;   list of conditions and the following disclaimer.
; 
; * Redistributions in binary form must reproduce the above copyright notice,
;   this list of conditions and the following disclaimer in the documentation
;   and/or other materials provided with the distribution.
; 
; * Neither the name of the copyright holder nor the names of its
;   contributors may be used to endorse or promote products derived from
;   this software without specific prior written permission.
; 
; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
; AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
; DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
; FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
; SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
; CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
; OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(defvar +max-buffer-size+ 32768)

(defun logger (text &rest args)
  "Wrapper around format to simplify logging"
  #+lisp-server-debug
  (apply 'format (append (list t (concatenate 'string text "~%")) args)))

;; Message Protocol
#|
This server sends and recieves messages in the following binary format:
[ 'Q' 'K' |  size   | contents...  ]
[ 2 bytes | 4 bytes | <size> bytes ]

Note that the contents are utf8 encoded.
|#

;; Why QK? This subsequence does not appear in any English word in the
;; dictionary file I looked in.
(define-constant +HEADER-B0+ (char-code #\Q))
(define-constant +HEADER-B1+ (char-code #\K))
(define-constant +OK-STATUS+ (flexi-streams:string-to-octets "OK" :external-format :utf-8) :test #'equalp)
(define-constant +ERROR-STATUS+ (flexi-streams:string-to-octets "ER" :external-format :utf-8) :test #'equalp)

(defun read-u32-big-endian (stream)
  (let ((val 0))
    (setf (ldb (byte 8 24) val) (read-byte stream))
    (setf (ldb (byte 8 16) val) (read-byte stream))
    (setf (ldb (byte 8 8) val) (read-byte stream))
    (setf (ldb (byte 8 0) val) (read-byte stream))
    val))

(defun write-u32-big-endian (val stream)
  (write-sequence (list (ldb (byte 8 24) val)
			(ldb (byte 8 16) val)
			(ldb (byte 8 8) val)
			(ldb (byte 8 0) val))
		  stream))

(defun read-header (stream)
  (assert (= (read-byte stream) +HEADER-B0+))
  (assert (= (read-byte stream) +HEADER-B1+))
  (read-u32-big-endian stream))

(defun read-body (nbytes stream)
  ;; TODO: check that nbytes are actually read
  (let ((buffer (make-array nbytes
                            :element-type '(unsigned-byte 8))))
    (read-sequence buffer stream)
    buffer))

(defun write-header (nbytes stream)
  (write-byte +HEADER-B0+ stream)
  (write-byte +HEADER-B1+ stream)
  (write-u32-big-endian nbytes stream))

(defun write-body (body-string stream)
  (write-sequence (flexi-streams:string-to-octets body-string :external-format :utf-8) stream))

(defun write-message (status body stream)
  "Write a message to the given stream."
  (let ((body-nbytes (flexi-streams:octet-length body :external-format :utf-8)))
    (write-header (+ body-nbytes (length status)) stream)
    (write-sequence status stream)
    (write-body body stream)
    (force-output stream)))

;; Top-level connection handling functions
(defun tcp-handler (stream socket con handler)
  ;; Keep reading data until we get an end-of-file error (i.e. the
  ;; other side closed the connection)
  (handler-case
      (loop
       (usocket:wait-for-input con)
       (logger "Recieved data over socket.")
       (let* ((nbytes (read-header stream))
              (body (read-body nbytes stream))
              (body-string (trim (flexi-streams:octets-to-string body :external-format :utf-8 :end nbytes)))
              (output-with-status
               (handler-case
                   (funcall handler body-string)
                 (handler-shutdown-request (c) (logger "Shutting down service.")
                                           (write-message +OK-STATUS+ "" stream)
                                           (signal c))
                 (error (c) (logger "Error in request handler: ~S" c)
                        (cons +ERROR-STATUS+ (princ-to-string c)))
                 (:no-error (val) (cons +OK-STATUS+ val))))
              (status (car output-with-status))
              (output (cdr output-with-status)))
         (write-message status output stream)))
    (end-of-file () nil)))

(defun run-tcp-server (host handler &key (print-stream *STANDARD-OUTPUT*) (on-socket-listen nil on-socket-listen-p))
  "Run TCP server in a loop, listening to incoming connections.
  This is a single-threaded version."
  ;; TODO: Better approach would be to run tcp-handler in a separate
  ;;       thread every time there is activity on the client socket
  ;; We request a TCP socket on an arbitrary free port.
  (let* ((socket (usocket:socket-listen host 0 :element-type '(unsigned-byte 8)))
         (port (usocket:get-local-port socket)))
    (handler-case
        (unwind-protect
            (progn
              (logger "Listening on port ~a." port)
              ;; We either call the provided on-socket-listen function with the
              ;; port number, if the argument was provided, or print the port
              ;; number out to print-stream. This is important because otherwise
              ;; whatever called us wouldn't know what port to connect to.
              (if on-socket-listen-p
                  (funcall on-socket-listen port)
                (progn
                  ;; Ensure that the printed port number is exactly 5 characters
                  (format print-stream "~5,'0D" port)
                  (force-output print-stream)))
              ;; Keep looping, accepting connections in serial.
              (loop do
                    (let* ((con (usocket:socket-accept socket))
	                   (stream (usocket:socket-stream con)))
                      (logger "Accepted connection.")
                      (tcp-handler stream socket con handler)
                      (close stream)
                      (usocket:socket-close con))))
          (usocket:socket-close socket))
      (handler-shutdown-request (c) (uiop/image:quit 0 t)))))

;;(run-tcp-server "0.0.0.0")
