; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>
(ld "cert.acl2")
(in-package "SV")
(set-deferred-ttag-notes t state)
(include-book "cosims")
(include-book "oslib/top" :dir :system)
(set-fmt-hard-right-margin 200 state)
(set-fmt-soft-right-margin 160 state)
:q

;; (setf *saved-string* "")

;; ; Redefine default-restart to avoid some of the banner nonsense at the start
;; (defun acl2-default-restart ()
;;   (if *acl2-default-restart-complete*
;;       (return-from acl2-default-restart nil))
;;   (setq ccl::*inhibit-greeting* t)
;;   (maybe-load-acl2-init)
;;   (eval `(in-package ,*startup-package-name*))
;;   (eval '(lp))
;;   (setq *acl2-default-restart-complete* t)
;;   nil)

(save-exec "cosim-core"
           "svex cosim framework is built in."
           #+Clozure
           :host-lisp-args
           #+Clozure
           "-Z 256M")
