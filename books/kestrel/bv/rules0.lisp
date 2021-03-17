; Mixed bit-vector theorems
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "slice")
(include-book "getbit")
(include-book "bvplus")
(include-book "bvminus")
(include-book "bvmult")
(include-book "bvlt")
(include-book "bitxor")
(include-book "bvcat")
(include-book "bvuminus")
(include-book "unsigned-byte-p")
(include-book "bvor")
(include-book "bvand")
(include-book "kestrel/arithmetic-light/integer-length" :dir :system)
(include-book "kestrel/arithmetic-light/lg" :dir :system)
(include-book "sbvlt")
(include-book "bitand")
(local (include-book "arith")) ;tod0o, for  expt-collect-hack
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;supported operators: bvchop, getbit, slice, bvcat, bvand, bvor, bvxor, bvshr, bvshl, bvplus, bvminus, bvmult, logext

;add bitxor, etc.

;fixme eventually split up this book

(defthm sbp-32-of-one-more
  (implies (and (signed-byte-p 32 x)
                (< x free)
                (signed-byte-p 32 free))
           (signed-byte-p 32 (+ 1 x)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

;use bvminus!
(defthm bvplus-minus-cancel
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (natp size)
                )
           (equal (bvplus size y (bvplus size (- y) x))
                  (bvchop size x)))
    :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-of-bvuminus-same
  (equal (bvplus size (bvuminus size x) x)
         0)
  :hints (("Goal" :in-theory (enable bvplus bvminus bvuminus))))

(defthm bvplus-of-bvuminus-same-alt
  (equal (bvplus size x (bvuminus size x))
         0)
  :hints (("Goal" :use (:instance bvplus-of-bvuminus-same)
           :in-theory (disable bvplus-of-bvuminus-same))))

;bozo, more generally, bvmult-1 just becomes and? huh?
(defthm bvmult-1-becomes-bitand
  (equal (bvmult 1 x y)
         (bitand x y))
  :hints (("Goal"
           :cases ((and (equal 1 (getbit 0 x)) (equal 1 (getbit 0 y)))
                   (and (not (equal 1 (getbit 0 x))) (equal 1 (getbit 0 y)))
                   (and (equal 1 (getbit 0 x)) (not (equal 1 (getbit 0 y)))))
           :use ((:instance bvmult-of-bvchop-arg2 (size 1))
                 (:instance bvmult-of-bvchop-arg2 (size 1) (x y) (y 1))
                 (:instance bvmult-of-bvchop-arg2 (size 1) (x y) (y 0)))
           :in-theory (e/d (bitand bvand ;bvmult
                                   getbit-when-val-is-not-an-integer)
                           (bvmult-of-bvchop-arg2)))))

;bozo, more generally?
(defthm bvplus-1-becomes-bitxor
  (equal (bvplus 1 x y)
         (bitxor x y))
  :hints (("Goal"
           :cases ((and (equal 1 (getbit 0 x)) (equal 1 (getbit 0 y)))
                   (and (not (equal 1 (getbit 0 x))) (equal 1 (getbit 0 y)))
                   (and (equal 1 (getbit 0 x)) (not (equal 1 (getbit 0 y)))))
           :use ((:instance bvplus-of-bvchop-arg1 (size 1))
                 (:instance bvplus-of-bvchop-arg1 (size 1) (x y) (y 1))
                 (:instance bvplus-of-bvchop-arg1 (size 1) (x y) (y 0)))
           :in-theory (e/d (bitand bvand getbit-when-val-is-not-an-integer)
                           (bvplus-of-bvchop-arg1)))))

;yuck! can loop!
(defthmd getbit-0-of-times
   (implies (and (integerp x) (integerp y))
            (equal (getbit 0 (* x y))
                   (getbit 0 (* (getbit 0 x) (getbit 0 y)))))
   :hints (("Goal" :in-theory (e/d (getbit) (bvchop-1-becomes-getbit slice-becomes-getbit)))))

(defthm bvmult-when-size-is-1
  (implies (and (integerp x)
                (integerp y))
           (equal (bvmult 1 x y)
                  (bvand 1 x y)))
  :hints (("Goal"
           :use ((:instance usb1-cases (x (getbit 0 x)))
                 (:instance usb1-cases (x (getbit 0 y)))
                 (:instance getbit-0-of-times))
           :in-theory (enable bvmult bvand bitand))))

;bozo gen
;strength reduction from bvmult to shift, so i guess this is a win? unless we are in an arithmetic context?
(defthm bvmult-of-2
  (implies (natp n)
           (equal (bvmult n 2 x)
                  (bvcat (+ -1 n) x 1 0)))
  :hints (("Goal" :in-theory (e/d (bvmult slice getbit bvcat)
                                  (bvchop-1-becomes-getbit
                                   slice-becomes-getbit
                                   bvchop-of-logtail-becomes-slice
                                   logtail-of-bvchop-becomes-slice)))))

;rename
(defthmd even-when-power-of-2-and-at-least-2
  (implies (and (<= 2 n)
                (power-of-2p n))
           (integerp (binary-* 1/2 n)))
  :hints (("Goal" :in-theory (enable expt-collect-hack natp power-of-2p))))

;need more bitxor cancel rules?

(defthmd bvchop-of-floor-of-expt-of-2
  (implies (and (integerp x) ;would like to drop this..
                (integerp n)
                (natp m))
           (equal (bvchop n (floor x (expt 2 m)))
                  (slice (+ m -1 n) m x)))
  :hints (("Goal" :in-theory (e/d (slice logtail) (;anti-slice
                                                   BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                                   )))))

(defthmd bvchop-of-floor-of-expt-of-2-constant-version
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (integerp x)
                (integerp n)
                (power-of-2p k))
           (equal (bvchop n (floor x k))
                  (slice (+ (lg k) -1 n) (lg k) x)))
  :hints (("Goal" :use (:instance bvchop-of-floor-of-expt-of-2 (m (lg k)))
           :in-theory (e/d (power-of-2p) (bvchop-of-floor-of-expt-of-2)))))

(theory-invariant (incompatible (:rewrite bvchop-of-floor-of-expt-of-2) (:definition slice)))
(theory-invariant (incompatible (:rewrite bvchop-of-floor-of-expt-of-2-constant-version) (:definition slice)))

;drop if we'll always enable bvle?
(defthm bvle-self
  (bvle size x x))
