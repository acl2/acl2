; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "progutils")
(include-book "tools/include-raw" :dir :system)
(include-book "std/util/define" :dir :system)
; (depends-on "shell-raw.lsp")

(defconst *vl-shell-help* "
vl shell:  Starts an interactive VL command loop (for experts).

Usage:     vl shell    (there are no options)

VL is built atop the ACL2 theorem prover.  The VL shell gives you access to the
ACL2 command loop, with all of the VL functions already built in.

This is mainly useful for VL developers who want to debug problems or explore
adding new functionality.

")

(define vl-shell ((argv string-listp) &key (state 'state))
  :returns state
  :ignore-ok t
  (progn$ (die "Raw lisp definition not installed?")
          state))


(defttag :vl-shell)
(acl2::include-raw "shell-raw.lsp")

