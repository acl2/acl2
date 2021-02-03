; Standard IO Library
; read-string.lisp
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

(defparameter *read-string-should-check-bad-lisp-object* t)

(defun read-string-fn (str state)
  (with-input-from-string
   (stream str)
   (handler-case
    (progn (unless (live-state-p state)
             (error "read-string requires a live state!"))
           (let ((acc         nil)
                 (*readtable* *acl2-readtable*)
                 (*package*   (find-package (current-package state))))
             (loop do
                   (let* ((eof-marker (cons nil nil))
                          (elem       (read stream nil eof-marker)))
                     (if (eq elem eof-marker)
                         (loop-finish)
                       (push elem acc))))
             (setq acc (nreverse acc))
             (let ((msg (and *read-string-should-check-bad-lisp-object*
                             (bad-lisp-objectp acc))))
               (if msg
                   (mv msg nil state)
                 (mv nil acc state)))))
    (error (condition)
           (return-from read-string-fn
                        (mv (format nil "~A" condition) nil state)))
    ;; Really bad-lisp-objectp shouldn't just stack-overflow on #1=(a . #1#).
    ;; Catching it is tricky...
    ;; "Because such a condition is indicative of a limitation of the
    ;;  implementation or of the image rather than an error in a program,
    ;;  objects of type storage-condition are not of type error."
    (storage-condition (condition)
                       (return-from read-string-fn
                                    (mv (format nil "~A" condition) nil state))))))

