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
; Supporting author: Eric Smith (eric.smith@kestrel.edu)

;; This book is just a lightweight copy of read-string.lisp, with minimal
;; dependencies.  It loads much faster and uses much less memory.

(in-package "ACL2")
(include-book "tools/include-raw" :dir :system) ; called below
;(local (include-book "oslib/read-acl2-oracle" :dir :system))
(local (include-book "kestrel/utilities/read-acl2-oracle" :dir :system))

; Avoid problems because gcl-cltl1 doesn't know about loop-finish
; cert_param: (ansi-only)

;; Similar to read-string-fn
(defun read-string-light-fn (str state)
  (declare (xargs :guard (stringp str)
                  :stobjs (state))
           (ignore str))
  (prog2$ (er hard? 'read-string-light "Raw lisp definition not installed?")
          (mv-let (err1 errmsg? state)
            (read-acl2-oracle state)
            (mv-let (err2 objects state)
              (read-acl2-oracle state)
              (if (or err1 err2)
                  (mv (msg "Reading oracle failed.") nil state)
                (if errmsg?
                    (mv errmsg? nil state)
                  (mv nil objects state)))))))

(defttag :read-string-light)

; (depends-on "read-string-light-raw.lsp")
(include-raw "read-string-light-raw.lsp")
