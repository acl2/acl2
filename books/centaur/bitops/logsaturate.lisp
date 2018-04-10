; Centaur Bitops Library
; Copyright (C) 2018 Centaur Technology
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


(in-package "BITOPS")

(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))

(local (in-theory (disable unsigned-byte-p signed-byte-p logmask
                           (tau-system))))


(define logsaturate ((position natp)
                     (x integerp))
  :parents (bitops)
  :short "Leaving the lowest position bits of x intact, reduce it to a position+2-bit
          signed value that is x itself if x was already a position+1-bit signed
          value, and if not, is outside of that range in the same direction as
          x."

:long "<p>This operation is useful for bit-level symbolic execution in some
cases where exact values outside a given range don't really matter but the
direction in which they overflow/underflow that range does matter.</p>

<p>The important properties of this function:</p>
<ul>
<li>Preserves signed values in the range @('-(2^position) <= x < 2^position'),
that is, signed bytes of size position+1 or less:
@(def logsaturate-when-signed-byte-p)</li>
<li>Out of range values are kept out of range in the same direction:
@(def logsaturate-when-greater)
@(def logsaturate-when-less)</li>
<li>The result is a signed integer of size position+2 or less:
@(def logsaturate-size)</li>
<li>The result preserves the value of all bits at position or below:
@(def logsaturate-bits-preserved)</li>
</ul>"
  :returns (val integerp :rule-classes :type-prescription)
  (b* ((position (lnfix position))
       (x (lifix x)))
    (logapp position
            x
            (if (<= 0 x)
                (if (eql 0 (logtail position x)) 0 1)
              (if (eql -1 (logtail position x)) -1 -2))))
  ///
  (local (defthm signed-byte-p-implies-posp
           (implies (signed-byte-p w x)
                    (and  (posp w) (integerp x)))
           :hints(("Goal" :in-theory (enable signed-byte-p)))
           :rule-classes :forward-chaining))

  (local (defthm logtail-when-signed-byte-p-neg
           (implies (and (signed-byte-p (+ 1 (nfix w)) x)
                         (< x 0))
                    (equal (logtail w x) -1))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (defthm logtail-when-signed-byte-p-nonneg
           (implies (and (signed-byte-p (+ 1 (nfix w)) x)
                         (<= 0 x))
                    (equal (logtail w x) 0))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (defthm logapp-when-signed-byte-p-neg
           (implies (and (signed-byte-p (+ 1 (nfix w)) x)
                         (< x 0))
                    (equal (logapp w x -1) x))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                              ihsext-inductions)))))

  (local (in-theory (disable bitops::logapp-of-j-0)))

  (local (defthm logapp-when-signed-byte-p-nonneg
           (implies (and (signed-byte-p (+ 1 (nfix w)) x)
                         (<= 0 x))
                    (equal (logapp w x 0) x))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                              ihsext-inductions)))))

  (defret logsaturate-when-signed-byte-p
    (implies (signed-byte-p (+ 1 (nfix position)) x)
             (equal val x)))

  (local (defthm logapp-nonneg-gte-ash
           (implies (and (<= 0 (ifix x)))
                    (<= (ash x (nfix w)) (logapp w y x)))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                              ihsext-inductions)))))

  (local (defthm logtail-nonzero-when-gte-ash
           (implies (<= (ash 1 (nfix w)) (ifix x))
                    (not (equal 0 (logtail w x))))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                              ihsext-inductions)))))

  (defret logsaturate-when-greater
    (implies (<= (ash 1 (nfix position)) (ifix x))
             (<= (ash 1 (nfix position)) val)))

  (local (defthm neg-ash-1-is-lognot-logmask
           (implies (natp w)
                    (equal (- (ash 1 w))
                           (lognot (logmask w))))
           :hints(("Goal" :in-theory (enable* bitops::minus-to-lognot
                                              logmask))
                  (and stable-under-simplificationp
                       '(:in-theory (enable  bitops::ash-is-expt-*-x)))
                  (and stable-under-simplificationp
                       '(:in-theory (enable bitops::expt-2-is-ash
                                            lognot))))))

  (local (defthm logtail-not-neg1-when-lt-neg-ash
           (implies (< (ifix x) (lognot (logmask w)))
                    (not (equal -1 (logtail w x))))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                              ihsext-inductions)))))

  (local (defthm logapp-minus2-lt-neg-ash
           (< (logapp w y -2) (lognot (logmask w)))
           :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                              ihsext-inductions)))))

  (defret logsaturate-when-less
    (implies (< (ifix x) (- (ash 1 (nfix position))))
             (< val (- (ash 1 (nfix position))))))

  (defret logsaturate-size
    (implies (equal pos (nfix position))
             (signed-byte-p (+ 2 pos) val)))

  (defret logsaturate-bits-preserved
    (implies (< (nfix i) (nfix position))
             (equal (logbitp i val)
                    (logbitp i x)))))

