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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(define vl-gather-portdecls-with-attribute ((x vl-portdecllist-p)
                                            (att stringp))
  :returns (sub-x vl-portdecllist-p)
  (cond ((atom x)
         nil)
        ((assoc-equal (string-fix att) (vl-portdecl->atts (car x)))
         (cons (vl-portdecl-fix (car x))
               (vl-gather-portdecls-with-attribute (cdr x) att)))
        (t
         (vl-gather-portdecls-with-attribute (cdr x) att))))

(define vl-gather-vardecls-with-attribute ((x vl-vardecllist-p)
                                           (att stringp))
  :returns (sub-x vl-vardecllist-p)
  (cond ((atom x)
         nil)
        ((assoc-equal (string-fix att) (vl-vardecl->atts (car x)))
         (cons (vl-vardecl-fix (car x))
               (vl-gather-vardecls-with-attribute (cdr x) att)))
        (t
         (vl-gather-vardecls-with-attribute (cdr x) att))))
