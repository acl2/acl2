; Mixed theorems about bit-vector operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Merge this book into the more basic files.

;; TODO: Generalize some 32s in this book to arbitrary sizes.

(include-book "rules")
(include-book "overflow-and-underflow")
(local (include-book "arith")) ; todo: drop (not easy)
;; (local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable LOGEXT-WHEN-NON-NEGATIVE-BECOMES-BVCHOP))) ;for speed

; move these (but need bitnot):

(defthm getbit-of-+-of-expt-same-arg1
  (implies (and (natp n)
                (integerp x))
           (equal (getbit n (+ (expt 2 n) x))
                  (bitnot (getbit n x))))
  :hints (("Goal" :in-theory (enable getbit-of-+))))

(defthm getbit-of-+-of---of-expt-same-arg2
  (implies (and (natp n)
                (integerp x))
           (equal (getbit n (+ x (- (expt 2 n))))
                  (bitnot (getbit n x))))
  :hints (("Goal" :in-theory (enable getbit-of-+))))

(defthm getbit-of-+-of-expt-same-arg2
  (implies (and (natp n)
                (integerp x))
           (equal (getbit n (+ x (expt 2 n)))
                  (bitnot (getbit n x))))
  :hints (("Goal" :in-theory (enable getbit-of-+))))

;Normal case: no overflow or underflow.  Because of symmetry, we can reorder
;the arguments to signed-addition-overflowsp and signed-addition-underflowsp if
;we'd like.
;; Slow proof!
(defthmd sbvlt-add-to-both-sides-normal-case
  (implies (and (not (signed-addition-overflowsp size k x))
                (not (signed-addition-overflowsp size k y))
                (not (signed-addition-underflowsp size k x))
                (not (signed-addition-underflowsp size k y))
                (posp size))
           (equal (sbvlt size (bvplus size k x) (bvplus size k y))
                  (sbvlt size x y)))
  :hints (("Goal" :in-theory (e/d (bvplus
                                   bvchop-of-sum-cases
                                   sbvlt
                                   bvlt
                                   getbit-of-+
                                   logext-cases
                                   bvminus
                                   bvchop-when-top-bit-1

                                   bvuminus
                                   <-of-0-and-logext-alt
                                   *-of-expt-of-one-less)
                                  (bvminus-becomes-bvplus-of-bvuminus
                                   ;; disables for speed:
                                   bvchop-identity
                                   expt-type-even-exponent-1
                                   expt-type-even-exponent-2
                                   expt-type-odd-exponent-negative-base
                                   <=-of-bvchop-same-linear-2
                                   expt-type-small-base-negative-exponent
                                   )))))

;todo: add more versions
(defthmd sbvlt-add-to-both-sides-normal-case-alt
  (implies (and (not (signed-addition-overflowsp size k x))
                (not (signed-addition-overflowsp size k y))
                (not (signed-addition-underflowsp size k x))
                (not (signed-addition-underflowsp size k y))
                (posp size))
           (equal (sbvlt size (bvplus size x k) (bvplus size y k))
                  (sbvlt size x y)))
  :hints (("Goal" :in-theory (enable sbvlt-add-to-both-sides-normal-case))))

;if both additions overflow, adding k does not affect the relative positions of x and y
(defthmd sbvlt-add-to-both-sides-both-overflow
  (implies (and (signed-addition-overflowsp size k x)
                (signed-addition-overflowsp size k y)
                (posp size))
           (equal (sbvlt size (bvplus size k x) (bvplus size k y))
                  (sbvlt size x y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt GETBIT-OF-+
                                          logext-cases
                                          logext-of-plus
                                          bvminus
                                          BVCHOP-WHEN-TOP-BIT-1

                                          bvuminus
                                          )
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
;unsigned-byte-p-when-not-bvlt-tighten
                                   ;bvlt-when-unsigned-byte-p-better-non-constant
                                   ;bvlt-tighten-free
                                   bvlt-tighten-when-getbit-0-alt)))))

;if both additions underflow, adding k does not affect the relative positions of x and y
(defthmd sbvlt-add-to-both-sides-both-underflow
  (implies (and (signed-addition-underflowsp size k x)
                (signed-addition-underflowsp size k y)
                (posp size))
           (equal (sbvlt size (bvplus size k x) (bvplus size k y))
                  (sbvlt size x y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt GETBIT-OF-+
                                          logext-cases
                                          bvminus
                                          BVCHOP-WHEN-TOP-BIT-1

                                          bvuminus
                                          )
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   ;unsigned-byte-p-when-not-bvlt-tighten
                                   ;bvlt-when-unsigned-byte-p-better-non-constant
                                   ;bvlt-tighten-free
                                   bvlt-tighten-when-getbit-0-alt)))))

(defthmd sbvlt-add-to-both-only-x-underflows
  (implies (and (signed-addition-underflowsp size k x)
                (not (signed-addition-underflowsp size k y))
                (posp size))
           (not (sbvlt size (bvplus size k x) (bvplus size k y))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt GETBIT-OF-+
                                          logext-cases
                                          logext-of-plus
                                          bvminus
                                          BVCHOP-WHEN-TOP-BIT-1

                                          bvuminus
                                          )
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   ;unsigned-byte-p-when-not-bvlt-tighten
                                   ;bvlt-when-unsigned-byte-p-better-non-constant
                                   ;bvlt-tighten-free
                                   bvlt-tighten-when-getbit-0-alt)))))

(defthmd sbvlt-add-to-both-only-y-underflows
  (implies (and (signed-addition-underflowsp size k y)
                (not (signed-addition-underflowsp size k x))
                (posp size))
           (sbvlt size (bvplus size k x) (bvplus size k y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt GETBIT-OF-+
                                          logext-cases
                                          bvminus
                                          BVCHOP-WHEN-TOP-BIT-1

                                          bvuminus
                                          )
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   ;unsigned-byte-p-when-not-bvlt-tighten
                                   ;bvlt-when-unsigned-byte-p-better-non-constant
                                   ;;bvlt-tighten-free
                                   bvlt-tighten-when-getbit-0-alt)))))

(defthmd sbvlt-add-to-both-only-x-overflows
  (implies (and (signed-addition-overflowsp size k x)
                (not (signed-addition-overflowsp size k y))
                (posp size))
           (sbvlt size (bvplus size k x) (bvplus size k y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt GETBIT-OF-+
                                          logext-cases
                                          bvminus
                                          BVCHOP-WHEN-TOP-BIT-1

                                          bvuminus
                                          )
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   ;unsigned-byte-p-when-not-bvlt-tighten
                                   ;bvlt-when-unsigned-byte-p-better-non-constant
                                   ;bvlt-tighten-free
                                   bvlt-tighten-when-getbit-0-alt)))))

(defthmd sbvlt-add-to-both-only-y-overflows
  (implies (and (signed-addition-overflowsp size k y)
                (not (signed-addition-overflowsp size k x))
                (posp size))
           (not (sbvlt size (bvplus size k x) (bvplus size k y))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt GETBIT-OF-+
                                          logext-cases
                                          bvminus
                                          BVCHOP-WHEN-TOP-BIT-1

                                          bvuminus
                                          )
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   ;unsigned-byte-p-when-not-bvlt-tighten
                                   ;bvlt-when-unsigned-byte-p-better-non-constant
                                   ;bvlt-tighten-free
                                   bvlt-tighten-when-getbit-0-alt)))))

(defthmd sbvlt-add-to-both-sides-gen
  (implies (and (equal (signed-addition-underflowsp size k x)
                       (signed-addition-underflowsp size k y))
                (equal (signed-addition-overflowsp size k x)
                       (signed-addition-overflowsp size k y))
                (posp size))
           (equal (sbvlt size (bvplus size k x) (bvplus size k y))
                  (sbvlt size x y)))
  :hints (("Goal" :in-theory (e/d (sbvlt-add-to-both-sides-both-underflow
                                   sbvlt-add-to-both-sides-both-overflow
                                   sbvlt-add-to-both-sides-normal-case)
                                  (SIGNED-ADDITION-OVERFLOWSP
                                   SIGNED-ADDITION-undERFLOWSP)))))

(defthmd sbvlt-add-to-both-sides-all-cases
  (implies (posp size)
           (equal (sbvlt size (bvplus size k x) (bvplus size k y))
                  (if (signed-addition-overflowsp size k x)
                      (if (signed-addition-overflowsp size k y)
                          (sbvlt size x y)
                        t)
                    (if (signed-addition-overflowsp size k y)
                        nil
                      ;; neither overflows, so check underflow:
                      (if (signed-addition-underflowsp size k x)
                          (if (signed-addition-underflowsp size k y)
                              (sbvlt size x y)
                            nil)
                        (if (signed-addition-underflowsp size k y)
                            t
                          ;; normal case:
                          (sbvlt size x y)))))))
  :hints (("Goal" :in-theory (e/d (sbvlt-add-to-both-sides-both-underflow
                                   sbvlt-add-to-both-sides-both-overflow
                                   sbvlt-add-to-both-sides-normal-case
                                   sbvlt-add-to-both-only-x-overflows
                                   sbvlt-add-to-both-only-y-overflows
                                   sbvlt-add-to-both-only-x-underflows
                                   sbvlt-add-to-both-only-y-underflows
                                   sbvlt-add-to-both-sides-gen)
                                  (signed-addition-overflowsp
                                   signed-addition-underflowsp)))))

(defthm sbvlt-of-bvplus-same-arg2
  (implies (and (not (signed-addition-overflowsp size y x)) ;we put y first in case it's a constant
                (not (signed-addition-underflowsp size y x))
                (posp size))
           (equal (sbvlt size x (bvplus size y x))
                  (sbvlt size 0 y)))
  :hints (("Goal" :use (:instance sbvlt-add-to-both-sides-all-cases
                                  (k x)
                                  (x 0))
           :in-theory (e/d (signed-addition-overflowsp-symmetric-limited
                            signed-addition-underflowsp-symmetric-limited)
                           (signed-addition-overflowsp
                            signed-addition-underflowsp)))))

;just reorders the args to bvplus in the LHS and the over/underflow hyps
(defthm sbvlt-of-bvplus-same-arg1
  (implies (and (not (signed-addition-overflowsp size x y)) ;we put x first in case it's a constant
                (not (signed-addition-underflowsp size x y))
                (posp size))
           (equal (sbvlt size x (bvplus size x y))
                  (sbvlt size 0 y)))
  :hints (("Goal" :use sbvlt-of-bvplus-same-arg2
           :in-theory (e/d (signed-addition-overflowsp-symmetric
                            signed-addition-underflowsp-symmetric)
                           (SIGNED-ADDITION-OVERFLOWSP
                            SIGNED-ADDITION-underFLOWSP)))))

(defthm unsigned-byte-p-of-bvplus-of-bvuminus-one-bigger
  (implies (and (equal sizeplusone (+ 1 size))
                (unsigned-byte-p size x)
                (natp size)
                (unsigned-byte-p size y))
           (equal (unsigned-byte-p size (bvplus sizeplusone (bvuminus sizeplusone x) y))
                  (bvle size x y)))
  :hints (("Goal" ;:cases ((natp size))
           :in-theory (e/d (bvplus bvchop-of-sum-cases
                                          bvuminus
                                          bvchop-of-minus
                                          bvminus
                                          bvlt
                                          expt-of-+)
                                  (bvminus-becomes-bvplus-of-bvuminus
                                   ;;collect-constants-over-<
                                   )))))

(defthm unsigned-byte-p-of-bvplus-of-bvuminus-one-bigger-alt
  (implies (and (equal sizeplusone (+ 1 size))
                (unsigned-byte-p size x)
                (natp size)
                (unsigned-byte-p size y))
           (equal (unsigned-byte-p size (bvplus sizeplusone y (bvuminus sizeplusone x)))
                  (bvle size x y)))
  :hints (("Goal" :use unsigned-byte-p-of-bvplus-of-bvuminus-one-bigger
           :in-theory (disable unsigned-byte-p-of-bvplus-of-bvuminus-one-bigger))))

(defthm unsigned-byte-p-of-bvplus-of-bvuminus-one-bigger-alt-signed
  (implies (and (equal sizeplusone (+ 1 size))
                (posp size)
                (sbvle sizeplusone 0 x) ;x is non-negative
                (sbvle sizeplusone 0 y)) ;y is non-negative
           (equal (unsigned-byte-p size (bvplus sizeplusone y (bvuminus sizeplusone x)))
                  (sbvle sizeplusone x y)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvplus-of-bvuminus-one-bigger-alt
                                  (x (bvchop sizeplusone x))
                                  (y (bvchop sizeplusone y))
                                  )
           :in-theory (e/d (sbvlt-rewrite)
                           (unsigned-byte-p-of-bvplus-of-bvuminus-one-bigger-alt ;todo in dagrulesmore0.lisp
                            ;; UNSIGNED-BYTE-P-OF-BVPLUS-TIGHTEN
                            )))))

;for overflow to happen (bvuminus size k2) must be positive, so k2 must be negative...
;rename
(defthm signed-addition-overflowsp-of-bvuminus-and-bvplus-same
  (implies (not (signed-addition-underflowsp size k2 x)) ;this also works: (sbvlt size (bvuminus size k2) x) ;todo: gen
           (not (signed-addition-overflowsp size (bvuminus size k2) (bvplus size k2 x))))
  :hints (("Goal":in-theory (e/d (signed-addition-overflowsp
                                  bvplus bvchop-of-sum-cases
                                  sbvlt bvlt
                                  getbit-of-+
                                  bvuminus
                                  logext-cases
                                  bvminus
                                  bvchop-when-top-bit-1

                                  )
                                 (bvminus-becomes-bvplus-of-bvuminus
                                  ;;unsigned-byte-p-when-not-bvlt-tighten
                                  ;bvlt-when-unsigned-byte-p-better-non-constant
                                  ;bvlt-tighten-free
                                  bvlt-tighten-when-getbit-0-alt
                                  getbit-when-<-of-bvchop-and-constant-high)))))

;for underflow to happen, (bvuminus 32 k2) must be negative, so k2 must be positive
;rename
(defthm signed-addition-underflowsp-of-bvuminus-and-bvplus-same
  (implies (and (not (signed-addition-overflowsp 32 k2 x))
                (not (equal (bvchop 32 k2) (expt 2 31)))) ;k2 not min int
           (not (signed-addition-underflowsp 32 (bvuminus 32 k2) (bvplus 32 k2 x))))
  :hints (("Goal":in-theory (e/d (signed-addition-underflowsp
                                  bvplus bvchop-of-sum-cases sbvlt bvlt GETBIT-OF-+
                                  bvuminus
                                  logext-cases
                                  bvminus
                                  BVCHOP-WHEN-TOP-BIT-1

                                  )
                                 (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                  ;;unsigned-byte-p-when-not-bvlt-tighten
                                  ;bvlt-when-unsigned-byte-p-better-non-constant
                                  ;bvlt-tighten-free
                                  bvlt-tighten-when-getbit-0-alt)))))

;; k2 + x < k becomes x < k - k2
(defthm sbvlt-of-bvplus-of-constant-and-constant-2
  (implies (and (syntaxp (and (quotep k) (quotep k2)))
                (not (signed-addition-overflowsp 32 k x))
                (not (signed-addition-overflowsp 32 k (bvuminus 32 k2))) ;gets computed
                (not (signed-addition-underflowsp 32 k x))
                (not (signed-addition-underflowsp 32 k (bvuminus 32 k2))) ;gets computed
                (not (signed-addition-overflowsp 32 k2 x))
                (not (signed-addition-underflowsp 32 k2 x))
                (not (equal (bvchop 32 k2) (expt 2 31))) ;gen?
                )
           (equal (sbvlt 32 (bvplus 32 k2 x) k)
                  (sbvlt 32 x (bvplus 32 k (bvuminus 32 k2)))))
  :hints (("Goal" :use (:instance sbvlt-add-to-both-sides-normal-case
                                  (x (bvplus 32 k2 x))
                                  (y k)
                                  (k (bvuminus 32 k2))
                                  (size 32)
                                  )
           :in-theory (e/d (signed-addition-overflowsp-symmetric-limited
                            signed-addition-underflowsp-symmetric-limited)
                           (signed-addition-overflowsp
                            signed-addition-underflowsp)))))

(defthm sbvlt-of-bvplus-of-min-int-when-positive
  (implies (and (sbvle 32 0 k)
                (sbvlt 32 0 x))
           (sbvlt 32
                  (bvplus 32 2147483648 k) ;must negative
                  x                        ;assumed to be non-negative
                  ))
  :hints (("Goal" :in-theory (enable sbvlt bvplus bvchop-of-sum-cases logext-of-plus))))

;gen the size
(defthm getbit-when-bvchop-bound
  (implies (and (< (bvchop 32 x) k)
                (syntaxp (quotep k))
                (<= k 2147483648))
           (equal (getbit 31 x)
                  0))
  :hints (("Goal" :in-theory (enable bvchop-reduce-when-top-bit-known bvcat logapp))))

;gen the size?
(defthm bvchop-tighten-when-bound-cheap
  (implies (< (bvchop 32 x) 2147483648) ;gen the constant?
           (equal (bvchop 32 x)
                  (bvchop 31 x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthmd bvlt-of-min-int-becomes-sbvlt-of-0
  (equal (bvlt 32 x 2147483648)
         (sbvle 32 0 x))
  :hints (("Goal" :in-theory (enable sbvlt bvlt logext))))

(defthm sbvlt-of-bvplus-of-min-int-and-0
  (equal (sbvlt 32 (bvplus 32 2147483648 x) 0)
         (sbvle 32 0 x))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases sbvlt bvlt GETBIT-OF-+
                                          logext-cases
                                          bvminus
                                          BVCHOP-WHEN-TOP-BIT-1

                                          )
                                  (;unsigned-byte-p-when-not-bvlt-tighten
                                   ;bvlt-when-unsigned-byte-p-better-non-constant
                                   ;bvlt-tighten-free
                                   bvlt-tighten-when-getbit-0-alt)))))

;; k < k2 + x becomes k - k2 < x
(defthm sbvlt-of-bvplus-of-constant-and-constant-2b
  (implies (and (syntaxp (and (quotep k) (quotep k2)))
                (not (signed-addition-overflowsp 32 k x))
                (not (signed-addition-overflowsp 32 k (bvuminus 32 k2))) ;gets computed
                (not (signed-addition-underflowsp 32 k x))
                (not (signed-addition-underflowsp 32 k (bvuminus 32 k2))) ;gets computed
                (not (signed-addition-overflowsp 32 k2 x))
                (not (signed-addition-underflowsp 32 k2 x))
                (not (equal (bvchop 32 k2) (expt 2 31))) ;gen?!
                )
           (equal (sbvlt 32 k (bvplus 32 k2 x))
                  (sbvlt 32 (bvplus 32 k (bvuminus 32 k2)) x)))
  :hints (("Goal" :cases ((not (equal (bvchop 32 k2) (expt 2 31))))
           :use (:instance sbvlt-add-to-both-sides-normal-case
                           (x k)
                           (y (bvplus 32 k2 x))
                           (k (bvuminus 32 k2))
                           (size 32)
                           )
           :in-theory (e/d (bvlt-of-min-int-becomes-sbvlt-of-0
                            SIGNED-ADDITION-OVERFLOWSP-symmetric-limited
                            SIGNED-ADDITION-underFLOWSP-symmetric-limited)
                           ( signed-addition-overflowsp
                             signed-addition-underflowsp
                             SBVLT-OF-0-ARG2-POLARITY ;todo: looped
                             )))))

;If k+x<y with k>=0, then x<y (usually).
(defthm sbvlt-when-sbvlt-of-bvplus-of-constant
  (implies (and (sbvlt size (bvplus size k x) y)
                (syntaxp (and (quotep k)
                              (quotep size)))
                (unsigned-byte-p (+ -1 size) k) ;k is non-negative
                (sbvlt size x (- (expt 2 (+ -1 size)) k)) ; x+k doesn't overflow
                (posp size))
           (sbvlt size x y))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases getbit-of-+ bvplus
                                     getbit-when-not-integerp-arg1
                                     sbvlt-rewrite
                                     ;;expt-of-+
                                     ))))

; If x<y-k with k>=0, then x<y (usually).
(defthm sbvlt-when-sbvlt-of-bvminus-of-constant
  (implies (and (sbvlt size x (bvminus size y k)) ;k is a free var
                (syntaxp (and (quotep k)
                              (quotep size)))
                (unsigned-byte-p (+ -1 size) k) ;k is non-negative (this gets evaluated)
                (sbvle size k y) ; y-k doesn't underflow
                (posp size))
           (sbvlt size x y))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases getbit-of-+ bvplus
                                     getbit-when-not-integerp-arg1
                                     sbvlt-rewrite
                                     ;;expt-of-+
                                     bvminus
                                     ))))
