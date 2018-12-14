; Fast print to file
; Copyright (C) 2017 Apple, Inc.
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

(in-package "VL")

(defun vl-print-to-file-and-clear-fn (filename ps state)
  ;; Similar to vl-print-to-file-and-clear's logical definition, but
  ;;  (1) use nreverse to reverse the characters, and
  ;;  (2) avoid the (heavy) overhead of ACL2's princ$ by using write-char/string directly
  (b* ((__function__ 'vl-print-to-file-and-clear)
       ((unless (acl2::live-state-p state))
        (raise "A live state is required")
        (mv ps state))
       (filename (string-fix filename))
       ((mv channel state)
        (open-output-channel! filename :character state))
       ((unless channel)
        (raise "Error opening file ~s0 for writing." filename)
        (mv ps state))
       (rchars (vl-ps->rchars))
       (ps     (vl-ps-update-rchars nil))
       (ps     (vl-ps-update-col 0))
       (rchars (if (true-listp rchars)
                   (nreverse rchars)
                 (cons (cdr (last rchars))
                       (acl2::revappend-without-guard rchars nil))))
       (stream (acl2::get-output-stream-from-channel channel))
       (- (loop for elem in rchars do
                (if (atom elem)
                    (cond ((characterp elem)
                           (write-char elem stream))
                          ((stringp elem) (write-string elem stream)))
                  (write-string (vl-printedlist->string elem)))))
       (state  (close-output-channel channel state)))
    (mv ps state)))
