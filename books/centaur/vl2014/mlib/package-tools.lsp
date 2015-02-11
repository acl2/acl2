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
(include-book "modnamespace")
(local (include-book "../util/arithmetic"))

(defsection package-tools
  :parents (mlib)
  :short "Functions for working with SystemVerilog packages.")

(local (xdoc::set-default-parents package-tools))

(define vl-package-all-names-nrev ((x vl-package-p) nrev)
  :parents (vl-package-all-names)
  (b* (((vl-package x))
       (nrev (vl-fundecllist->names-nrev   x.fundecls   nrev))
       (nrev (vl-taskdecllist->names-nrev  x.taskdecls  nrev))
       (nrev (vl-typedeflist->names-nrev   x.typedefs   nrev))
       (nrev (vl-paramdecllist->names-nrev x.paramdecls nrev))
       (nrev (vl-vardecllist->names-nrev   x.vardecls   nrev)))
    nrev))

(define vl-package-all-names ((x vl-package-p))
  :returns (names string-listp)
  :verify-guards nil
  (mbe :logic
       (b* (((vl-package x)))
         (append (vl-fundecllist->names x.fundecls)
                 (vl-taskdecllist->names x.taskdecls)
                 (vl-typedeflist->names x.typedefs)
                 (vl-paramdecllist->names x.paramdecls)
                 (vl-vardecllist->names x.vardecls)))
       :exec
       (with-local-nrev
         (vl-package-all-names-nrev x nrev)))
  ///
  (defthm vl-package-all-names-nrev-removal
    (equal (vl-package-all-names-nrev x nrev)
           (append nrev (vl-package-all-names x)))
    :hints(("Goal" :in-theory (enable vl-package-all-names-nrev))))

  (verify-guards vl-package-all-names))


