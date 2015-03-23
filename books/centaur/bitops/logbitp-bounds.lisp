; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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
; Original author: Anna Slobodova <anna@centtech.com>
; Minor modifications by: Shilpi Goel <shilpi@centtech.com>

(in-package "BITOPS")
(include-book "xdoc/top" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (in-theory (e/d () (expt floor))))

(defsection bitops/logbitp-bounds
  :parents (bitops)
  :short "A book about @(see logbitp) and @(see expt)."

  :long "<p>This is a fast-loading book that can be used separately from the rest of Bitops.</p>")

;; ======================================================================

(defsection logbitp-bounds

  :parents (bitops/logbitp-bounds logbitp)
  :short "Lemmas about inferring @('logbitp') information from bounds
  expressed using @('expt') and vice versa"

  :long "<ul>

<li>@('  (logbitp n x) => (<= (expt 2 n) x)')</li>

<li>@('  (logbitp n (expt 2 n)) = t')</li>

<li>@('  (<= (expt 2 n) x)') and @('(< x (expt 2 (1+ n)))  =>  (logbitp n
x)') and @(' (not (logbitp (1+ n) x))')</li>

</ul>
"

  (defthm logbitp-to-lower-bound
    (implies (and (logbitp n x)
                  (natp n)
                  (natp x))
             (<= (expt 2 n) x))
    :hints (("Goal" :in-theory (enable logbitp)))
    :rule-classes (:linear :rewrite))

  (defthm expt-2-n-to-logbitp
    (implies (natp n)
             (logbitp n (expt 2 n)))
    :hints (("Goal" :in-theory (enable logbitp))))

  (local
   (defthm lemma-1
     (implies (and (< x (expt 2 (+ 1 n)))
                   (natp n)
                   (natp x))
              (<= (floor x (expt 2 n))
                  1))
     :hints (("Goal" :nonlinearp t))
     :rule-classes :linear))

  (local
   (defthmd lemma-2
     (implies (and (rationalp x)
                   (<= x 1)
                   (< 0 x))
              (not (integerp (* 1/2 x))))
     :hints (("Goal" :nonlinearp t))))

  (defthm bounds-to-logbitp-lemma
    (implies (and (< (expt 2 n) x)
                  (<  x (expt 2 (+ 1 n)))
                  (natp n)
                  (natp x))
             (logbitp n x))
    :hints (("Goal" :in-theory (e/d (logbitp) ())
             :use ((:instance lemma-2
                              (x (floor x (expt 2 n))))))))

  (local
   (defthm floor-of-expt2
     (implies (and (< (expt 2 n) x)
                   (< x (* 2 (expt 2 n)))
                   (natp n)
                   (natp x))
              (equal (floor x (expt 2 n)) 1))))

  (defthm bounds-to-logbitp
    (implies (and (<= (expt 2 n) x)
                  (< x (expt 2 (+ 1 n)))
                  (natp n)
                  (natp x))
             (and (logbitp n x)
                  (not (logbitp (+ 1 n) x))))
    :hints (("Goal" :cases ((equal x (expt 2 n)))))))

;; ======================================================================
