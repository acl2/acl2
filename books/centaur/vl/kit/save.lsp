; VL Verilog Toolkit
; Copyright (C) 2008-2013 Centaur Technology
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
(ld "cert.acl2")
(in-package "VL")
(include-book "top")
(include-book "oslib/file-types" :dir :system)
(include-book "oslib/top" :dir :system)
(set-deferred-ttag-notes t state)
(set-slow-alist-action :break)
(set-gag-mode :goals)

; Initialize xdoc stuff so all of its books are pre-loaded and we're ready to
; use xdoc commands in the vl shell.
(xdoc::colon-xdoc-init)

:q

;; Set up our program to not print a bunch of ACL2 banners.
(setq *print-startup-banner* nil)

;; Generally unsound hack that practically should be safe, and makes warnings
;; faster.
(setq vl::*vl-enable-unsafe-but-fast-printing* t)

;; Set up our program NOT try to read the any customization files.
(defun initial-customization-filename () :none)

;; the default defs of these screw up the server's scanner thread
(defun acl2::bad-lisp-objectp (x) nil)
(defun acl2::chk-bad-lisp-object (x) nil)

(save-exec "../bin/vl" "VL Verilog Toolkit"
           :inert-args ""
           #+CCL :host-lisp-args #+CCL "-Z 256M"
           :return-from-lp '(vl::vl-main))
