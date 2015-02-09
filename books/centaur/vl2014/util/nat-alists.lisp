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
(include-book "defs")
(local (include-book "arithmetic"))

(defsection vl-nat-values-p

  (defund vl-nat-values-p (x)
    (declare (xargs :guard t))
    (or (atom x)
        (and (consp (car x))
             (natp (cdar x))
             (vl-nat-values-p (cdr x)))))

  (local (in-theory (enable vl-nat-values-p)))

  (defthm vl-nat-values-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-nat-values-p x)
                    t)))

  (defthm vl-nat-values-p-of-cons
    (equal (vl-nat-values-p (cons a x))
           (and (natp (cdr a))
                (vl-nat-values-p x))))

  (defthm vl-nat-values-p-of-hons-shrink-alist
    (implies (and (vl-nat-values-p x)
                  (vl-nat-values-p ans))
             (vl-nat-values-p (hons-shrink-alist x ans)))
    :hints(("Goal" :in-theory (e/d (hons-shrink-alist)
                                   ((force))))))

  (defthm natp-of-cdr-of-hons-assoc-equal-when-vl-nat-values-p
    (implies (vl-nat-values-p x)
             (equal (natp (cdr (hons-assoc-equal a x)))
                    (if (hons-assoc-equal a x)
                        t
                      nil)))))
