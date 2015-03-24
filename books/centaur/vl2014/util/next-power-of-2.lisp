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
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (include-book "arithmetic"))

(defund next-power-of-2 (n)
  ;; Returns the smallest M such that n <= 2^M
  (declare (xargs :guard (posp n)))
  (integer-length (1- n)))

(local (in-theory (enable next-power-of-2)))

(defthm type-of-next-power-of-2
  (natp (next-power-of-2 n))
  :rule-classes :type-prescription)

(defthm lower-bound-of-next-power-of-2
  (implies (force (posp n))
           (<= n (expt 2 (next-power-of-2 n))))
  :rule-classes ((:rewrite) (:linear)))

(defthm upper-bound-of-next-power-of-2
  (implies (force (posp n))
           (< (expt 2 (1- (next-power-of-2 n)))
              n))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal"
          :in-theory (disable bitops::|2^{(integer-length n) - 1} <= n|)
          :use ((:instance bitops::|2^{(integer-length n) - 1} <= n|
                           (bitops::n (- n 1)))))))
