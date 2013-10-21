; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
; (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (include-book "ihsext-basics"))
(local (in-theory (disable floor mod logbitp evenp oddp ash)))
(local (in-theory (disable logcons logcar logcdr integer-length)))
(local (in-theory (disable expt logior logand lognot)))

(defxdoc bitops/defaults
  :parents (bitops)
  :short "Basic theorems about the \"default\" behavior of bit operations when
their inputs are ill-formed.")

(local (in-theory (enable* arith-equiv-forwarding)))

(defsection logbitp-defaults
  :parents (bitops/defaults logbitp)

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

  (defthm lognot-default
    (implies (not (integerp x))
             (equal (lognot x)
                    -1))
    :hints(("Goal" :in-theory (enable lognot**)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))



(defsection logand-defaults
  :parents (bitops/defaults logand)

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

  (defthm logcar-default
    (implies (not (integerp x))
             (equal (logcar x)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection logcdr-default
  :parents (bitops/defaults logcdr)

  (defthm logcdr-default
    (implies (not (integerp x))
             (equal (logcdr x)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))



(defsection integer-length-default
  :parents (bitops/defaults integer-length)

  (defthm integer-length-default
    (implies (not (integerp x))
             (equal (integer-length x)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection ash-defaults
  :parents (bitops/defaults ash)

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
