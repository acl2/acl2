; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
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

(in-package "OSLIB")

(defun file-kind-fn (path follow-symlinks state)
  (unless (live-state-p state)
    (error "file-kind can only be called on a live state."))
  (mv-let (errmsg result)
    (handler-case
     (multiple-value-bind
         (main-kind broken)
         (osicat::file-kind path :follow-symlinks follow-symlinks)
       (cond ((and follow-symlinks broken)
              (assert (eq main-kind :symbolic-link))
              (mv nil :broken-symbolic-link))
             ((file-kind-p main-kind)
              (mv nil

; Work around issue with LispWorks, which returns nil for the application of
; osicat::file-kind to "."  and to "./".

                  (cond ((and (null main-kind)
			      (member path '("." "./") :test 'equal))
			 :DIRECTORY)
			(t main-kind))))
             (t
              (mv (msg "Error in file-kind for ~x0: osicat::file-kind returned ~
                        unexpected value ~s1."
                       path
                       (format nil "~a" main-kind))
                  nil))))
     (error (condition)
            (mv (msg "Error in file-kind: ~s0." (format nil "~a" condition))
                nil)))
    (mv errmsg result state)))

