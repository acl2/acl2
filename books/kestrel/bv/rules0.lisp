; Mixed bit-vector theorems
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
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
;(include-book "bvlt")
(include-book "bitxor")
(include-book "bvcat")
(include-book "bvuminus")
(include-book "unsigned-byte-p")
;(include-book "bvor")
;(include-book "bvand")
;(include-book "kestrel/arithmetic-light/integer-length" :dir :system)
;(include-book "kestrel/arithmetic-light/lg" :dir :system)
;(include-book "sbvlt")
(include-book "bitand")
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;supported operators: bvchop, getbit, slice, bvcat, bvand, bvor, bvxor, bvshr, bvshl, bvplus, bvminus, bvmult, logext

;add bitxor, etc.

;fixme eventually split up this book

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

;; A 1-bit multiply is just an AND.
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

;; A 1-bit sum is just an XOR.
(defthm bvplus-1-becomes-bitxor
  (equal (bvplus 1 x y)
         (bitxor x y))
  :hints (("Goal"
           :cases ((and (equal 1 (getbit 0 x)) (equal 1 (getbit 0 y)))
                   (and (not (equal 1 (getbit 0 x))) (equal 1 (getbit 0 y)))
                   (and (equal 1 (getbit 0 x)) (not (equal 1 (getbit 0 y)))))
           :use ((:instance bvplus-of-bvchop-arg2 (size 1))
                 (:instance bvplus-of-bvchop-arg2 (size 1) (x y) (y 1))
                 (:instance bvplus-of-bvchop-arg2 (size 1) (x y) (y 0)))
           :in-theory (e/d (bitand  getbit-when-val-is-not-an-integer)
                           (bvplus-of-bvchop-arg2)))))

;; ;yuck! can loop!
;; (defthmd getbit-0-of-times
;;    (implies (and (integerp x) (integerp y))
;;             (equal (getbit 0 (* x y))
;;                    (getbit 0 (* (getbit 0 x) (getbit 0 y)))))
;;    :hints (("Goal" :in-theory (e/d (getbit) (bvchop-1-becomes-getbit slice-becomes-getbit)))))

;bozo gen
;strength reduction from bvmult to shift, so i guess this is a win? unless we are in an arithmetic context?
(defthmd bvmult-of-2
  (implies (natp n)
           (equal (bvmult n 2 x)
                  (bvcat (+ -1 n) x 1 0)))
  :hints (("Goal" :in-theory (e/d (bvmult slice getbit bvcat)
                                  (bvchop-1-becomes-getbit
                                   slice-becomes-getbit
                                   bvchop-of-logtail-becomes-slice
                                   logtail-of-bvchop-becomes-slice)))))

;need more bitxor cancel rules?

(theory-invariant (incompatible (:rewrite bvchop-of-floor-of-expt-of-2) (:definition slice)))
(theory-invariant (incompatible (:rewrite bvchop-of-floor-of-expt-of-2-constant-version) (:definition slice)))
