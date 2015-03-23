; Centaur Bitops Library
; Copyright (C) 2010-2013 Centaur Technology
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

(in-package "BITOPS")
(include-book "xdoc/top" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "ihsext-basics"))
(local (in-theory (enable* arith-equiv-forwarding)))

(defxdoc bitops/defaults
  :parents (bitops)
  :short "(semi-deprecated) Basic theorems about the \"default\" behavior of
bit-vector operations when their inputs are ill-formed (e.g., not integers, not
naturals)."

  :long "<p>We tend not to include this any more, because it should mostly be
subsumed by the @('nat-equiv') and @('int-equiv') congruence reasoning.</p>")

(defsection logbitp-defaults
  :parents (bitops/defaults logbitp)
  :short "Behavior of @(see logbitp) on bad inputs."

  (defthm logbitp-default-1
    (implies (not (natp a))
             (equal (logbitp a x)
                    (logbitp 0 x)))
    :hints(("Goal" :in-theory (enable logbitp**)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm logbitp-default-2
    (implies (not (integerp x))
             (equal (logbitp a x)
                    nil))
    :hints(("Goal" :in-theory (enable logbitp**)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection lognot-default
  :parents (bitops/defaults lognot)
  :short "Behavior of @(see lognot) on bad inputs."

  (defthm lognot-default
    (implies (not (integerp x))
             (equal (lognot x)
                    -1))
    :hints(("Goal" :in-theory (enable lognot**)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))



(defsection logand-defaults
  :parents (bitops/defaults logand)
  :short "Behavior of @(see logand) on bad inputs."

  (defthm logand-default-1
    (implies (not (integerp x))
             (equal (logand x y)
                    (logand 0 y)))
    :hints(("Goal" :in-theory (enable logand**)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm logand-default-2
    (implies (not (integerp y))
             (equal (logand x y)
                    (logand x 0)))
    :hints(("Goal" :in-theory (e/d (logand**))))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection logior-defaults
  :parents (bitops/defaults logior)
  :short "Behavior of @(see logior) on bad inputs."

  (defthm logior-default-1
    (implies (not (integerp x))
             (equal (logior x y)
                    (logior 0 y)))
    :hints(("Goal" :in-theory (enable logior**)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm logior-default-2
    (implies (not (integerp y))
             (equal (logior x y)
                    (logior x 0)))
    :hints(("Goal" :in-theory (enable logior**)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection logcar-default
  :parents (bitops/defaults logcar)
  :short "Behavior of @(see logcar) on bad inputs."

  (defthm logcar-default
    (implies (not (integerp x))
             (equal (logcar x)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection logcdr-default
  :parents (bitops/defaults logcdr)
  :short "Behavior of @(see logcdr) on bad inputs."

  (defthm logcdr-default
    (implies (not (integerp x))
             (equal (logcdr x)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection integer-length-default
  :parents (bitops/defaults integer-length)
  :short "Behavior of @(see integer-length) on bad inputs."

  (defthm integer-length-default
    (implies (not (integerp x))
             (equal (integer-length x)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection ash-defaults
  :parents (bitops/defaults ash)
  :short "Behavior of @(see ash) on bad inputs."

  (defthm ash-default-1
    (implies (not (integerp x))
             (equal (ash x y)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm ash-default-2
    (implies (not (integerp y))
             (equal (ash x y)
                    (ifix x)))
    :hints(("Goal" :in-theory (enable ash**)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection logxor-defaults
  :parents (bitops/defaults logxor)
  :short "Behavior of @(see logxor) on bad inputs."

  (defthm logxor-default-1
    (implies (not (integerp x))
             (equal (logxor x y)
                    (logxor 0 y)))
    :hints(("Goal" :in-theory (enable logxor**)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm logxor-default-2
    (implies (not (integerp y))
             (equal (logxor x y)
                    (logxor x 0)))
    :hints(("Goal" :in-theory (enable logxor**)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))
