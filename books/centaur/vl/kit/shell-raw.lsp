; VL Verilog Toolkit
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

(defun vl::vl-shell-entry-fn (events state)
  (format t "VL Verilog Toolkit
Copyright (C) 2008-2016 Centaur Technology <http://www.centtech.com>

,-------------------------,
|  VL Interactive Shell   |     This is an interactive ACL2 shell with VL pre-
|     (for experts)       |     loaded.  To learn about ACL2 (and hence how to
|                         |     use this shell) see the ACL2 homepage:
|  Enter (quit) to quit   |      http://www.cs.utexas.edu/users/moore/acl2
`-------------------------'

")

  (f-put-global 'ld-verbose nil state)
  (ld events)
  ;; Note: We used to execute (lp) here, but it didn't really do anything.  The
  ;; vl executable ends up at a prompt as long as (vl-main) doesn't directly
  ;; exit.  It's a raw Lisp prompt if we save with :return-from-lp or an ACL2
  ;; prompt if we use :init-forms instead.

  ;; So basically all this function does is provide an entry to LD that can be
  ;; used in logic mode.  We could easily work around this so we don't need raw
  ;; Lisp code at all.  Oh well, someday.
  state)

