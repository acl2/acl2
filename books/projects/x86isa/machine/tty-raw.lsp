; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) May - August 2023, Regents of the University of Texas
; Copyright (C) August 2023 - May 2024, Yahya Sohail
; Copyright (C) May 2024 - August 2024, Intel Corporation

; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Yahya Sohail        <yahya.sohail@intel.com>

(in-package "X86ISA")

(defparameter *console-stream* nil)

;; Initially, I just made the *input-buffer* a list and had a separate global
;; for the lock. The issue is that handling it that way makes it so that adding
;; a new item when the list is empty creates a new object. This is bad because
;; while threads share an address space, the binding context is different, so
;; updating the binding of *input-buffer* doesn't update it on all threads.
(defclass input-buffer ()
  ((lock :initform (ccl::make-lock)
         :accessor input-buffer-lock)
   (buffer :initform 'nil
           :accessor input-buffer-buffer)))

;; Perhaps doing this in a more object oriented way, with methods, would be
;; better, but I don't know nearly enough about CLOS to do that

(defparameter *input-buffer* (make-instance 'input-buffer))

(let* ((socket (ccl::make-socket :connect :passive ;; Listen
                                 :local-host "localhost"
                                 :local-port 6444))
       (stream (ccl::accept-connection socket))
       (tty-read-proc (ccl::make-process "tty-read")))
  (setf *console-stream* stream)
  (ccl::process-preset
    tty-read-proc
    (lambda ()
      (loop
        (let* ((c (read-char *console-stream*))
               (byt (char-code c)))
          (ccl::with-lock-grabbed
            ((input-buffer-lock *input-buffer*))
            (setf (input-buffer-buffer *input-buffer*)
                  (nconc (input-buffer-buffer *input-buffer*)
                         (list byt))))))))
  (ccl::process-enable tty-read-proc))

(defun write-tty (c x86)
  (write-char (code-char c) *console-stream*)
  (force-output *console-stream*)
  x86)

(defun read-tty (x86)
  (ccl::with-lock-grabbed
    ((input-buffer-lock *input-buffer*))
    (b* ((buffer (input-buffer-buffer *input-buffer*))
         ((when (null buffer)) (mv nil x86))
         ((list* byt rst) buffer))
        (progn
          (setf (input-buffer-buffer *input-buffer*) rst)
          (mv byt x86)))))
