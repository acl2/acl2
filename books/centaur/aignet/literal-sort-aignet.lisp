; Copyright (C) 2020 Centaur Technology
; AIGNET - And-Inverter Graph Networks
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


(in-package "AIGNET")

(include-book "literal-sort")
(include-book "supergate")


(defthm aignet-eval-parity-of-literal-sort-insert
  (equal (aignet-eval-parity (literal-sort-insert x y) invals regvals aignet)
         (aignet-eval-parity (cons x y) invals regvals aignet))
  :hints(("Goal" :in-theory (enable aignet-eval-parity literal-sort-insert )
          :induct (literal-sort-insert x y))))

(defthm aignet-eval-parity-of-literal-sort-insertsort
  (equal (aignet-eval-parity (literal-sort-insertsort x) invals regvals aignet)
         (aignet-eval-parity x invals regvals aignet))
  :hints(("Goal" :in-theory (enable aignet-eval-parity literal-sort-insertsort )
          :induct (literal-sort-insertsort x))))

(defthm aignet-lit-listp-of-literal-sort-insertsort
  (equal (aignet-lit-listp (literal-sort-insertsort lits) aignet)
         (aignet-lit-listp lits aignet)))
