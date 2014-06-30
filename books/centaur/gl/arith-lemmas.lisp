; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

; cert_param: (non-acl2r)

(in-package "GL")
(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))



(local (in-theory (e/d* (acl2::ihsext-redefs
                         acl2::ihsext-inductions))))

(defthmd loghead-of-integer-length-nonneg
  (implies (and (<= (integer-length x) (nfix n))
                (<= 0 (ifix x)))
           (equal (loghead n x)
                  (ifix x))))

(progn ;; integer-length lemmas
  (include-book "ihs/quotient-remainder-lemmas" :dir :system)

  (defthmd integer-length-lte-by-compare-nonneg
    (implies (and (<= 0 (ifix a))
                  (<= (ifix a) (ifix b)))
             (<= (integer-length a) (integer-length b)))
    :hints (("goal" :induct (logxor a b))))

  (defthmd integer-length-lte-by-compare-neg
    (implies (and (<= (ifix a) 0)
                  (<= (ifix b) (ifix a)))
             (<= (integer-length a) (integer-length b)))
    :hints (("goal" :induct (logxor a b))))

  (in-theory (disable (force))))




(progn ;; integer-length, floor/mod/rem/truncate lemmas

  (defthm floor-of-negations
    (equal (floor (- a) (- b))
           (floor a b))
    :hints(("Goal" :in-theory (enable floor))))

  (defthm logext-of-integer-length-bound
    (implies (< (integer-length x) (ifix n))
             (equal (acl2::logext n x)
                    (ifix x))))

  (local (in-theory (disable acl2::mod-minus
                             ACL2::/R-WHEN-ABS-NUMERATOR=1)))

  (defthm mod-of-negatives
    (implies (and (integerp a) (integerp b)
                  (not (equal 0 b)))
             (equal (mod (- a) (- b))
                    (- (mod a b))))
    :hints(("Goal" :in-theory (enable mod))))

  (defthm integer-length-of-mod
    (implies (and (integerp b)
                  (integerp a)
                  (not (equal b 0)))
             (<= (integer-length (mod a b))
                 (integer-length b)))
    :hints (("goal" :in-theory (enable integer-length-lte-by-compare-nonneg
                                       integer-length-lte-by-compare-neg)
             :cases ((< 0 b))))
    :rule-classes :linear)

  (defthm integer-length-of-plus-1
    (implies (integerp x)
             (<= (integer-length (+ 1 x)) (+ 1 (integer-length x)))))

  (defthm integer-length-of-lognot
    (equal (integer-length (lognot x))
           (integer-length x)))

  (defthm integer-length-of-abs
    (implies (integerp x)
             (<= (integer-length (abs x)) (+ 1 (integer-length x))))
    :hints (("goal" :use ((:instance integer-length-of-lognot)
                          (:instance integer-length-of-plus-1
                           (x (+ -1 (- x)))))
             :in-theory (enable lognot))))
  


  (defthm integer-length-of-between-abs-and-minus-abs
    (implies (and (integerp x)
                  (integerp y)
                  (< y (abs x))
                  (< (- (abs x)) y))
             (<= (integer-length y) (integer-length x)))
    :hints (("goal" :use ((:instance integer-length-of-lognot)
                          (:instance integer-length-lte-by-compare-nonneg
                           (a y) (b (abs x)))
                          (:instance integer-length-lte-by-compare-neg
                           (a y) (b (1- (- (abs x)))))
                          (:instance integer-length-lte-by-compare-neg
                           (a y) (b (- (abs x)))))
             :cases ((<= 0 y))
             :do-not-induct t
             :in-theory (e/d (lognot)
                             (integer-length-of-plus-1))))
    :otf-flg t)

  (defthm integer-length-of-rem
    (implies (and (integerp b)
                  (integerp a)
                  (not (equal b 0)))
             (<= (integer-length (rem a b))
                 (integer-length b)))
    :hints (("goal" :in-theory (e/d (integer-length-lte-by-compare-nonneg
                                     integer-length-lte-by-compare-neg)
                                    (acl2::rem-bounds
                                     rem abs))
             :use ((:instance acl2::rem-bounds (x a) (y b)))
             :do-not-induct t
             :cases ((< 0 b))))
    :otf-flg t
    :rule-classes :linear)

  (defthm truncate-is-floor
    (implies (and (integerp a) (integerp b))
             (equal (truncate a b)
                    (if (equal b 0)
                        0
                      (if (acl2::xor (< a 0) (< b 0))
                          (- (floor (abs a) (abs b)))
                        (floor (abs a) (abs b))))))
    :hints(("Goal" :in-theory (enable truncate floor))))

  (defthm rem-is-mod
    (implies (and (integerp a) (integerp b))
             (equal (rem a b)
                    (if (equal b 0)
                        a
                      (if (< a 0)
                          (- (mod (- a) (abs b)))
                        (mod a (abs b))))))
    :hints(("Goal" :in-theory (enable rem mod)))))
