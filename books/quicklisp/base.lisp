; ACL2 Quicklisp Interface
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "tools/include-raw" :dir :system)
; cert_param: (uses-quicklisp)
; Matt K. mod, 12/16/2021 (see GitHub Issue #1332):
; cert_param: (non-lispworks)

(make-event
 (mv-let (err override-dir state)
   ;; Most users should never adjust QUICKLISP_ASDF_HOME.  In this case, we
   ;; will install all Quicklisp files into, e.g.,
   ;;     ..../acl2/books/quicklisp/asdf-home/
   ;;
   ;; But if for some reason you want to install the ASDF libraries somewhere
   ;; else, you can set the QUICKLISP_ASDF_HOME environment variable.  This
   ;; must be done:
   ;;
   ;;   1. *before* building the quicklisp books, and
   ;;   2. *forever after* whenever you want to include them
   ;;
   ;; In short, you should not mess around with this unless you have some good
   ;; reason to want the Quicklisp files to live somewhere other than your ACL2
   ;; books directory.
   (getenv$ "QUICKLISP_ASDF_HOME" state)
   (let ((dir (if err
                  (er hard? 'getenv$ "getenv failed")
                (or override-dir (cbd)))))
     (progn$
      (setenv$ "XDG_CONFIG_HOME" (concatenate 'string dir "/asdf-home/config"))
      (setenv$ "XDG_DATA_HOME"   (concatenate 'string dir "/asdf-home/data"))
      (setenv$ "XDG_CACHE_HOME"  (concatenate 'string dir "/asdf-home/cache"))
      (value '(value-triple :invisible)))))
 :check-expansion t)

(defttag :quicklisp)

;; We'll use timestamp.txt as a proxy for whether any Common Lisp libraries
;; have been updated.
; (depends-on "bundle/timestamp.txt")

; (depends-on "bundle/bundle.lisp")
(include-raw "bundle/bundle.lisp" :host-readtable t)

; (depends-on "base-raw.lsp")
(local (include-raw "base-raw.lsp"
                    :host-readtable t
                    :do-not-compile t))



