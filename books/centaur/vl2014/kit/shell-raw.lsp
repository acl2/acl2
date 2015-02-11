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

(in-package "ACL2")

(defun vl2014::vl-shell-fn (argv state)
  (declare (ignore argv))
  (format t "VL 2014 -- VL Verilog Toolkit, 2014 Edition
Copyright (C) 2008-2015 Centaur Technology <http://www.centtech.com>

,-------------------------,
|  VL Interactive Shell   |     This is an interactive ACL2 shell with VL pre-
|     (for experts)       |     loaded.  To learn about ACL2 (and hence how to
|                         |     use this shell) see the ACL2 homepage:
|  Enter (quit) to quit   |      http://www.cs.utexas.edu/users/moore/acl2
`-------------------------'

")

  (f-put-global 'ld-verbose nil state)
  ;; well, this doesn't seem to actually work and get us into an interactive
  ;; LP shell.  But at least we get into a raw-lisp shell, which is probably
  ;; fine for now.
  (lp)
  state)

