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

(defun copy-file-fn (from to overwrite state) ;; --> (mv error/nil state)

  (b* (((unless (live-state-p state))
        (error "COPY-FILE can only be called on a live state.")
        (mv "ERROR" state))

       ;; These should never happen due to our guard.
       ((unless (stringp from))
        (error "COPY-FILE called on a non-stringp from?")
        (mv "ERROR" state))
       ((unless (stringp to))
        (error "COPY-FILE called on a non-stringp to?")
        (mv "ERROR" state))
       ((unless (booleanp overwrite))
        (error "COPY-FILE called on a non-boolean overwrite?")
        (mv "ERROR" state))

       ((mv from-err from-kind state) (file-kind from))
       ((mv to-err   to-kind state)   (file-kind to))
       ((when from-err) (mv from-err state))
       ((when to-err)   (mv to-err state))

       ((unless (eq from-kind :regular-file))
        (mv (msg "~s0: can't copy ~s1: ~s2." 'copy-file from
                 (if from-kind
                     "not a regular file"
                   "no such file"))
            state))

       ((unless (or (eq to-kind nil)
                    (eq to-kind :regular-file)))
        (mv (msg "~s0: can't copy ~s1 to ~s2: trying to overwrite ~s3."
                 'copy-file from to to-kind)
            state)))

    (handler-case
      (progn
        (cl-fad::copy-file from to :overwrite overwrite)
        (mv nil state))
      (error (condition)
             (let ((condition-str (format nil "~a" condition)))
               (mv (msg "~s0: error copying ~s1 to ~s2: ~s3."
                        'copy-file from to condition-str)
                   state))))))

