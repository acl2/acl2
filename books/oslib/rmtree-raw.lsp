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

; BOZO could possibly rework this using uiop:delete-empty-directory,
; uiop:delete-file-if-exists, etc., to avoid syscalls.

(defun rmtree-fn (dir state)

  (b* (((unless (live-state-p state))
        (error "RMTREE can only be called on a live state.")
        (mv nil state))

       ((unless (stringp dir))
        (error "RMTREE called on a non-stringp dir?")
        (mv nil state))

       ((mv - file-type)
        (osicat:file-exists-p dir))
       (- (cond ((equal file-type :directory)
                 (osicat:delete-directory-and-files dir
                                                    :if-does-not-exist
                                                    :ignore))
                ((equal file-type :regular-file)
                 (cl:delete-file dir))
                (t nil)))

       ((mv status state)
        (sys-call-status state))

       ((unless (eql status 0))
        (error "error removing ~s0." dir)
        (mv nil state)))

    (mv t state)))

