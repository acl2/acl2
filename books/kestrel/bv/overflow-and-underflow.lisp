; Overflow and underflow of signed addition
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logext")
(include-book "sbvlt")
(include-book "bvlt")
(include-book "bvplus")
(include-book "bvminus")
(include-book "rules") ;reduce?
(local (include-book "arith"))
;(local (include-book "arith2"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))

;;;
;;; signed-addition-overflowsp
;;;

;if x is negative, the addition cannot overflow
;if x is positive, the subtraction cannot underflow
;if either is 0, there is no overflow (addition has no effect)

;if one addend is a constant, it's best to make x the constant
(defun signed-addition-overflowsp (size x y)
  (declare (xargs :guard (and (posp size)
                              (unsigned-byte-p size x) ;but interpred as signed
                              (unsigned-byte-p size y) ;but interpred as signed
                              )))
  (and (sbvlt size 0 x)
       ;; if x is positive, the addition might overflow:
       (sbvlt size (bvminus size (- (expt 2 (- size 1)) 1) x) y))) ;implies that y is positive

;testing for overflow is symmetric
;proof splits into many cases...
(defthmd signed-addition-overflowsp-symmetric
  (implies (posp size)
           (equal (signed-addition-overflowsp size x y)
                  (signed-addition-overflowsp size y x)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt getbit-of-plus
                                          logext-cases
                                          bvminus bvuminus
                                          bvchop-when-top-bit-1
                                          getbit-when-val-is-not-an-integer
                                          )
                                  (bvminus-becomes-bvplus-of-bvuminus)))))

(defthmd signed-addition-overflowsp-symmetric-limited
  (implies (and (syntaxp (smaller-termp y x))
                (posp size))
           (equal (signed-addition-overflowsp size x y)
                  (signed-addition-overflowsp size y x)))
  :hints (("Goal" :in-theory (e/d (signed-addition-overflowsp-symmetric)
                                  (signed-addition-overflowsp)))))

(defthm signed-addition-overflowsp-correct
  (implies (and (posp size)
                (unsigned-byte-p size x)
                (unsigned-byte-p size y))
           (iff (signed-addition-overflowsp size x y)
                ;; could also say "not signed-byte-p ..."
                (<= (expt 2 (+ -1 size)) (+ (logext size x) (logext size y)))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt GETBIT-OF-PLUS
                                          logext-cases
                                          bvminus  bvuminus
                                          BVCHOP-WHEN-TOP-BIT-1
                                          GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                          )
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

;todo: more like this
(defthm signed-addition-overflowsp-subst-constant-arg1
  (implies (and (syntaxp (not (quotep x)))
                (equal (bvchop 32 x) free)
                (syntaxp (quotep free)))
           (equal (signed-addition-overflowsp 32 x y)
                  (signed-addition-overflowsp 32 free y))))

;todo: dual for underflow?
(defthm not-signed-addition-overflowsp-when-negative-constant-version
  (implies (and (syntaxp (quotep k))
                (sbvle 32 k 0))
           (not (signed-addition-overflowsp 32 k k))))

;;;
;;; signed-addition-underflowsp
;;;

;if one addend is a constant, it's best to make x the constant
(defun signed-addition-underflowsp (size x y)
  (declare (xargs :guard (and (posp size)
                              (unsigned-byte-p size x) ;but interpred as signed
                              (unsigned-byte-p size y) ;but interpred as signed
                              )))
  (and (sbvlt size x 0)
       ;; if x is negative, the addition might overflow:
       (sbvlt size y (bvminus size (- (expt 2 (- size 1))) x)))) ;implies that y is negative?

;testing for underflow should be symmetric
(defthmd signed-addition-underflowsp-symmetric
  (implies (posp size)
           (iff (signed-addition-underflowsp size x y)
                (signed-addition-underflowsp size y x)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt getbit-of-plus
                                          logext-cases
                                          bvminus bvuminus
                                          bvchop-when-top-bit-1
                                          getbit-when-val-is-not-an-integer
                                          )
                                  (bvminus-becomes-bvplus-of-bvuminus)))))

(defthmd signed-addition-underflowsp-symmetric-limited
  (implies (and (syntaxp (smaller-termp y x))
                (posp size))
           (equal (signed-addition-underflowsp size x y)
                  (signed-addition-underflowsp size y x)))
  :hints (("Goal" :in-theory (e/d (signed-addition-underflowsp-symmetric)
                                  (signed-addition-underflowsp)))))

(defthm signed-addition-underflowsp-correct
  (implies (and (posp size)
                (unsigned-byte-p size x)
                (unsigned-byte-p size y))
           (iff (signed-addition-underflowsp size x y)
                (< (+ (logext size x) (logext size y)) (- (expt 2 (+ -1 size))))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt getbit-of-plus
                                          logext-cases
                                          bvminus bvuminus
                                          bvchop-when-top-bit-1
                                          getbit-when-val-is-not-an-integer)
                                  (bvminus-becomes-bvplus-of-bvuminus)))))

(defthm not-signed-addition-underflowsp-when-signed-addition-overflowsp-cheap
  (implies (and (signed-addition-overflowsp size x y)
                (posp size))
           (not (signed-addition-underflowsp size x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))
