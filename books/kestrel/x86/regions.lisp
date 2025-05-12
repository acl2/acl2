; Disjointness of memory regions
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; See also the function SEPARATE, but this machinery is intended to be more amenable to SMT solving.

;(include-book "projects/x86isa/proofs/utilities/general-memory-utils" :dir :system) ; reduce?  and get rid of ttags
(include-book "kestrel/bv/bvlt-def" :dir :system)
(include-book "kestrel/bv/bvminus" :dir :system) ; todo: reduce
;(include-book "kestrel/bv/sbvlt-def" :dir :system)
;(local (include-book "kestrel/bv/sbvlt" :dir :system))
;(local (include-book "kestrel/bv/sbvlt-rules" :dir :system)) ; for sbvlt-rewrite
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system)) ; may be droppable with more bvminus rules
(local (include-book "kestrel/bv/bvlt" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;; Defines what it means for AD to be in the region of size LEN starting at
;; START-AD.  Note that the region may wrap around the end of the address
;; space, so AD may be in the region even if it is less than START-AD.
;; We put the len argument before start-ad because len often be a small constant.
(defund in-regionp (ad len start-ad)
  (declare (xargs :guard (and (unsigned-byte-p 48 ad)
                              (unsigned-byte-p 48 len) ; can't be 2^48 as the len gets chopped to 48 bits
                              (unsigned-byte-p 48 start-ad))))
  (bvlt 48 (bvminus 48 ad start-ad) len))

;; Nothing is in a region of size 0
(defthm not-in-regionp-of-0
  (not (in-regionp ad 0 start-ad))
  :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix ACL2::BVCHOP-OF-SUM-CASES))))

;; The address at the start of the region is in the region IFF the size is non-zero
(defthm in-regionp-same
  (equal (in-regionp ad size ad)
         (posp (bvchop 48 size)))
  :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

;; The address at the end of the region is in the region IFF the size is non-zero
(defthm in-regionp-same-end
  (equal (in-regionp (bvplus 48 ad (bvplus 48 -1 size)) size ad)
         (posp (bvchop 48 size)))
  :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

(defthm in-regionp-same-end-alt
  (equal (in-regionp (bvplus 48 281474976710655 (bvplus 48 ad size)) size ad)
         (posp (bvchop 48 size)))
  :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

;; note that the region size can't be 2^48
(defthm not-in-regionp-one-past-end
  (not (in-regionp (bvplus 48 ad size) size ad))
  :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

;; if the region size is 2^48-1, being in the region means not being the single address just before the region
(defthm in-regionp-of-2^48-1
  (equal (in-regionp ad (+ -1 (expt 2 48)) start-ad)
         (not (equal (bvchop 48 ad) (bvminus 48 start-ad 1))))
  :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases))))

(defthm in-regionp-monotone
  (implies (and (in-regionp x len1 ad)
                (<= len1 len2)
                (unsigned-byte-p 48 len1)
                (unsigned-byte-p 48 len2))
           (in-regionp x len2 ad))
  :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

(defthm not-in-regionp-too-far
  (implies (and (in-regionp x len ad)
                (bvle 48 len (bvminus 48 y x)) ; y is at least LEN above x
                (bvle 48 (bvminus 48 x ad) (bvminus 48 y ad)) ; x is closer to the start of the region than y
                (unsigned-byte-p 48 len))
           (not (in-regionp y len ad)))
  :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

(defthm in-regionp-of-bvchop-arg1
  (implies (and (<= 48 n)
                (integerp n))
           (equal (in-regionp (bvchop n ad) len start-ad)
                  (in-regionp ad len start-ad)))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-of-bvchop-arg3
  (implies (and (<= 48 n)
                (integerp n))
           (equal (in-regionp ad len (bvchop n start-ad))
                  (in-regionp ad len start-ad)))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-of-+-arg1
  (implies (and (integerp x)
                (integerp y))
           (equal (in-regionp (+ x y) len ad)
                  (in-regionp (bvplus 48 x y) len ad)))
  :hints (("Goal" :in-theory (enable in-regionp bvplus))))

(defthm in-regionp-of-+-arg3
  (implies (and (integerp x)
                (integerp y))
           (equal (in-regionp ad len (+ x y))
                  (in-regionp ad len (bvplus 48 x y))))
  :hints (("Goal" :in-theory (enable in-regionp bvplus))))

(defthm in-regionp-cancel-1-1+
  (equal (in-regionp x len (bvplus 48 x z))
         (in-regionp 0 len z))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-cancel-1+-1
  (equal (in-regionp (bvplus 48 x z) len x)
         (in-regionp z len 0))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-cancel-1+-1+
  (equal (in-regionp (bvplus 48 x y) len (bvplus 48 x z))
         (in-regionp y len z))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-cancel-1-2
  (equal (in-regionp x len2 (bvplus 48 y x))
         (in-regionp 0 len2 y))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-cancel-2-1
  (equal (in-regionp (bvplus 48 y x) len2 x)
         (in-regionp y len2 0))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-cancel-2-1+
  (equal (in-regionp (bvplus 48 y x) len2 (bvplus 48 x z))
         (in-regionp y len2 z))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-cancel-1+-2
  (equal (in-regionp (bvplus 48 x y) len (bvplus 48 z x))
         (in-regionp y len z))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-cancel-2-2
  (equal (in-regionp (bvplus 48 y x) len2 (bvplus 48 z x))
         (in-regionp y len2 z))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-cancel-3-1
  (equal (in-regionp (bvplus 48 y (bvplus 48 z x)) len x)
         (in-regionp (bvplus 48 y z) len 0))
  :hints (("Goal" :in-theory (enable in-regionp))))

;; todo: hints
(defthm in-regionp-cancel-1-3
  (equal (in-regionp x len (bvplus 48 y (bvplus 48 z x)))
         (in-regionp 0 len (bvplus 48 y z)))
  :hints (("Goal" :in-theory (enable in-regionp bvminus bvlt ifix bvplus))))

;; removes the negative part of the range
(defthm in-regionp-when-non-negative-and-negative-range
  (implies (and (syntaxp (quotep k))
                (<= (expt 2 47) (bvchop 48 k)) ; (sbvlt 48 k 0) ; negative
                (unsigned-byte-p 47 x) ; non-negative
                (unsigned-byte-p 48 k) ; drop?
                (unsigned-byte-p 47 len2) ; gen?
                (<= (- (expt 2 48) k) len2) ;move to rhs?
                )
           (equal (in-regionp x len2 k)
                  (in-regionp x (- len2 (- (expt 2 48) k)) 0)))
  :hints (("Goal" :cases ((< (+ 281474976710656 (- k) x) len2))
           :in-theory (enable in-regionp bvplus bvuminus bvlt acl2::bvchop-of-sum-cases unsigned-byte-p
                              ;;acl2::sbvlt-rewrite
                              ))))

;; todo: more cancellation rules

;; todo: more?
(defthm in-regionp-cancel-constants-1+-1+
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (not (equal 0 k1)) ; prevent loops
                )
           (equal (in-regionp (bvplus 48 k1 x) len2 (bvplus 48 k2 y))
                  (in-regionp x len2 (bvplus 48 (bvminus 48 k2 k1) y))))
  :hints (("Goal" :in-theory (enable in-regionp))))

;; which arg do we prefer to make 0?
(defthm in-regionp-cancel-constants-1-1+
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (not (equal 0 k1)) ; prevent loops
                )
           (equal (in-regionp k1 len2 (bvplus 48 k2 y))
                  (in-regionp 0 len2 (bvplus 48 (bvminus 48 k2 k1) y))))
  :hints (("Goal" :in-theory (enable in-regionp))))

;; how do we prefer to handle this?
(defthm in-regionp-cancel-constants-1+-1
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (not (equal 0 k1)) ; prevent loops
                )
           (equal (in-regionp (bvplus 48 k1 x) len2 k2)
                  (in-regionp x len2 (bvminus 48 k2 k1))))
  :hints (("Goal" :in-theory (enable in-regionp))))

;; disabled for the proofs below
(defthmd in-regionp-of-0-arg3
  (equal (in-regionp ad len 0)
         (bvlt 48 ad len))
  :hints (("Goal" :in-theory (enable in-regionp))))

(defthm in-regionp-subst-constant-arg1
  (implies (and (equal k (bvchop 48 ad1))
                (syntaxp (and (quotep k)
                              (not (quotep ad1)))))
           (equal (in-regionp ad1 n2 ad2)
                  (in-regionp k n2 ad2)))
  :hints (("Goal" :in-theory (enable in-regionp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Defines what it means for 2 memory regions to be disjoint.
;; We put the len arguments first because they will often be small constants.
(defund disjoint-regionsp (len1 ad1 len2 ad2)
  (declare (xargs :guard (and (unsigned-byte-p 48 len1) ; can't be 2^48 as the len gets chopped to 48 bits
                              (unsigned-byte-p 48 ad1)
                              (unsigned-byte-p 48 len2) ; can't be 2^48 as the len gets chopped to 48 bits
                              (unsigned-byte-p 48 ad2))))
  (if (or (equal 0 len1)
          (equal 0 len2))
      t
    (and (bvle 48 len1 (bvminus 48 ad2 ad1)) ; the start of region2 is not within region 1  ;; todo: rephrase to use bvlt?
         (bvle 48 len2 (bvminus 48 ad1 ad2)) ; the start of region1 is not within region 2
         )))

;; todo: more sanity check properties

(defthmd disjoint-regionsp-symmetric
  (equal (disjoint-regionsp len1 ad1 len2 ad2)
         (disjoint-regionsp len2 ad2 len1 ad1))
  :hints (("Goal" :in-theory (enable disjoint-regionsp))))

;; Addresses in disjoint regions cannot be equal.
(defthm not-equal-of-bvchop-and-bvchop-when-in-disjoint-regions
  (implies (and (disjoint-regionsp len1 start1 len2 start2)
                (in-regionp ad1 len1 start1)
                (in-regionp ad2 len2 start2))
           (not (equal (bvchop 48 ad1) (bvchop 48 ad2))))
  :hints (("Goal" :in-theory (enable in-regionp disjoint-regionsp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

;; Addresses in disjoint regions cannot be equal.
(defthm not-equal-when-in-disjoint-regions
  (implies (and (disjoint-regionsp len1 start1 len2 start2)
                (in-regionp ad1 len1 start1)
                (in-regionp ad2 len2 start2))
           (not (equal ad1 ad2)))
  :hints (("Goal" :in-theory (enable in-regionp disjoint-regionsp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

(defthm not-equal-when-in-disjoint-regions-alt
  (implies (and (disjoint-regionsp len1 start1 len2 start2)
                (in-regionp ad2 len1 start1)
                (in-regionp ad1 len2 start2))
           (not (equal ad1 ad2)))
  :hints (("Goal" :in-theory (enable in-regionp disjoint-regionsp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

;; If any address is in both, they are not disjoint.
(defthm not-disjoint-regionsp-when-address-in-both
  (implies (and (in-regionp ad len1 start1)
                (in-regionp ad len2 start2))
           (not (disjoint-regionsp len1 start1 len2 start2)))
  :hints (("Goal" :in-theory (enable in-regionp disjoint-regionsp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

;; If they are disjoint, no address is in both.
(defthm not-in-both-when-disjoint
  (implies (disjoint-regionsp len1 start1 len2 start2)
           (not (and (in-regionp ad len1 start1)
                     (in-regionp ad len2 start2))))
  :hints (("Goal" :in-theory (enable in-regionp disjoint-regionsp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

;; If not disjoint, some address is in both (in fact, one of the start addresses will be in the other region):
(defthm not-disjoint
  (implies (not (disjoint-regionsp len1 start1 len2 start2))
           (or (in-regionp start1 len2 start2)
               (in-regionp start2 len1 start1)))
  :hints (("Goal" :in-theory (enable in-regionp disjoint-regionsp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

(defthm disjoint-regionsp-of-+-arg2
  (implies (and (integerp ad1)
                (integerp x))
           (equal (disjoint-regionsp len1 (+ x ad1) len2 ad2)
                  (disjoint-regionsp len1 (bvplus 48 x ad1) len2 ad2)))
  :hints (("Goal" :in-theory (enable disjoint-regionsp
                                     acl2::bvminus-of-+-arg2
                                     acl2::bvminus-of-+-arg3))))

(defthm disjoint-regionsp-of-+-arg4
  (implies (and (integerp ad2)
                (integerp x))
           (equal (disjoint-regionsp len1 ad1 len2 (+ x ad2))
                  (disjoint-regionsp len1 ad1 len2 (bvplus 48 x ad2))))
  :hints (("Goal" :in-theory (enable disjoint-regionsp
                                     acl2::bvminus-of-+-arg2
                                     acl2::bvminus-of-+-arg3))))

;more
(defthm disjoint-regionsp-cancel-1-2
  (equal (disjoint-regionsp len1 x len2 (bvplus 48 y x))
         (disjoint-regionsp len1 0 len2 y))
  :hints (("Goal" :in-theory (enable disjoint-regionsp))))

(defthm disjoint-regionsp-cancel-1-1+
  (equal (disjoint-regionsp len1 x len2 (bvplus 48 x y))
         (disjoint-regionsp len1 0 len2 y))
  :hints (("Goal" :in-theory (enable disjoint-regionsp))))

(defthm disjoint-regionsp-cancel-1+-1
  (equal (disjoint-regionsp len1 (bvplus 48 x z) len2 x)
         (disjoint-regionsp len1 z len2 0))
  :hints (("Goal" :in-theory (enable disjoint-regionsp))))

(defthm disjoint-regionsp-cancel-1+-1+
  (equal (disjoint-regionsp len1 (bvplus 48 x z) len2 (bvplus 48 x y))
         (disjoint-regionsp len1 z len2 y))
  :hints (("Goal" :in-theory (enable disjoint-regionsp))))

(defthm disjoint-regionsp-cancel-1+-2
  (equal (disjoint-regionsp len1 (bvplus 48 x z) len2 (bvplus 48 y x))
         (disjoint-regionsp len1 z len2 y))
  :hints (("Goal" :in-theory (enable disjoint-regionsp))))

(defthm disjoint-regionsp-cancel-2-1+
  (equal (disjoint-regionsp len1 (bvplus 48 z x) len2 (bvplus 48 x y))
         (disjoint-regionsp len1 z len2 y))
  :hints (("Goal" :in-theory (enable disjoint-regionsp))))

(defthm disjoint-regionsp-cancel-2-2
  (equal (disjoint-regionsp len1 (bvplus 48 z x) len2 (bvplus 48 y x))
         (disjoint-regionsp len1 z len2 y))
  :hints (("Goal" :in-theory (enable disjoint-regionsp))))

;; todo: show that this reduces to a more familiar notion in the non-wrap-around case
;; todo: use defun-sk to show correctness

(defthm disjoint-regionsp-of-bvchop-arg2
  (implies (and (<= 48 size)
                (integerp size))
           (equal (disjoint-regionsp len1 (bvchop size ad1) len2 ad2)
                  (disjoint-regionsp len1 ad1 len2 ad2)))
  :hints (("Goal" :in-theory (enable disjoint-regionsp))))

(defthm disjoint-regionsp-of-bvchop-arg4
  (implies (and (<= 48 size)
                (integerp size))
           (equal (disjoint-regionsp len1 ad1 len2 (bvchop size ad2))
                  (disjoint-regionsp len1 ad1 len2 ad2)))
  :hints (("Goal" :in-theory (enable disjoint-regionsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks whether all of the addresses in the first region are in the second region
(defund subregionp (len1 ad1 len2 ad2)
  (declare (xargs :guard (and (unsigned-byte-p 48 len1) ; can't be 2^48 as the len gets chopped to 48 bits
                              (unsigned-byte-p 48 ad1)
                              (unsigned-byte-p 48 len2) ; can't be 2^48 as the len gets chopped to 48 bits
                              (unsigned-byte-p 48 ad2))))
  (if (zp len1)
      t
    ;; both the first and last address of region1 are in region2:
    (and (in-regionp ad1 len2 ad2)
         (bvle 48 len1 len2) ; ensures the difference is not negative
         (bvle 48 (bvminus 48 ad1 ad2) (bvminus 48 len2 len1)))))

;; A region is a subregion of itself
(defthm subregionp-reflexive
  (implies (unsigned-byte-p 48 len)
           (subregionp len ad len ad))
  :hints (("Goal" :in-theory (enable subregionp))))

;; A region of size 0 is a subregion of any region
(defthm subregionp-of-0-arg1
  (subregionp 0 ad len2 ad2)
  :hints (("Goal" :in-theory (enable subregionp))))

;; A region is a subregion or some other region of size 0 only if it iself has size 0.
(defthm subregionp-of-0-arg3
  (equal (subregionp len1 ad1 0 ad2)
         (zp len1))
  :hints (("Goal" :in-theory (enable subregionp))))

;; todo: prove transitive, anti-symm

(defthm in-regionp-when-in-regionp-and-subregionp
  (implies (and (subregionp len1 ad1 len2 ad2)
                (in-regionp ad len1 ad1)
                (unsigned-byte-p 48 len1)
                (unsigned-byte-p 48 len2))
           (in-regionp ad len2 ad2))
  :hints (("Goal" :in-theory (enable in-regionp disjoint-regionsp SUBREGIONP
                                     bvuminus bvplus bvlt
                                     ifix
                                     ACL2::BVLT-OF-0-ARG2
                                     acl2::bvchop-of-sum-cases
                                     zp))))

;; If there's something in R1 that is not in R2, then R1 is not a subregion of R2
;; todo: prove from the above
(defthm not-subregionp-when-in-regionp-and-not-in-regionp
  (implies (and (in-regionp ad len1 ad1)
                (not (in-regionp ad len2 ad2))
                (unsigned-byte-p 48 len1)
                (unsigned-byte-p 48 len2))
           (not (subregionp len1 ad1 len2 ad2)))
  :hints (("Goal" :in-theory (enable in-regionp disjoint-regionsp SUBREGIONP
                                     bvuminus bvplus bvlt
                                     ifix
                                     ACL2::BVLT-OF-0-ARG2
                                     acl2::bvchop-of-sum-cases
                                     zp))))

(defthm subregionp-cancel-1-1
  (implies (syntaxp (not (quotep x)))
           (equal (subregionp len1 x len2 x)
                  (subregionp len1 0 len2 0) ; usually can be evaluated
                  ))
  :hints (("Goal" :in-theory (enable subregionp))))

(defthm subregionp-cancel-1+-1
  (equal (subregionp len1 (bvplus 48 x y) len2 x)
         (subregionp len1 y len2 0))
  :hints (("Goal" :in-theory (enable subregionp))))

(defthm subregionp-cancel-1-1+
  (equal (subregionp len1 x len2 (bvplus 48 x y))
         (subregionp len1 0 len2 y))
  :hints (("Goal" :in-theory (enable subregionp))))

(defthm subregionp-cancel-2-1
  (equal (subregionp len1 (bvplus 48 y x) len2 x)
         (subregionp len1 y len2 0))
  :hints (("Goal" :in-theory (enable subregionp))))

(defthm subregionp-cancel-2-1+
  (equal (subregionp len1 (bvplus 48 y x) len2 (bvplus 48 x z))
         (subregionp len1 y len2 z))
  :hints (("Goal" :in-theory (enable subregionp))))

(defthm subregionp-cancel-1-2
  (equal (subregionp len1 x len2 (bvplus 48 y x))
         (subregionp len1 0 len2 y))
  :hints (("Goal" :in-theory (enable subregionp))))

(defthm subregionp-cancel-1+-2
  (equal (subregionp len1 (bvplus 48 x z) len2 (bvplus 48 y x))
         (subregionp len1 z len2 y))
  :hints (("Goal" :in-theory (enable subregionp))))

(defthm subregionp-cancel-2-2
  (equal (subregionp len1 (bvplus 48 y x) len2 (bvplus 48 z x))
         (subregionp len1 y len2 z))
  :hints (("Goal" :in-theory (enable subregionp))))

;; todo: more cancellation rules, or a general solution?

(defthm subregionp-of-+-arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (subregionp len1 (+ x y) len2 ad2)
                  (subregionp len1 (bvplus 48 x y) len2 ad2)))
  :hints (("Goal" :in-theory (enable subregionp
                                     acl2::bvminus-of-+-arg2))))

(defthm subregionp-of-+-arg4
  (implies (and (integerp x)
                (integerp y))
           (equal (subregionp len1 ad1 len2 (+ x y))
                  (subregionp len1 ad1 len2 (bvplus 48 x y))))
  :hints (("Goal" :in-theory (enable subregionp
                                     acl2::bvminus-of-+-arg3))))

(defthm subregionp-of-bvchop-arg2
  (implies (and (<= 48 size)
                (integerp size))
           (equal (subregionp len1 (bvchop size ad1) len2 ad2)
                  (subregionp len1 ad1 len2 ad2)))
  :hints (("Goal" :in-theory (enable subregionp in-regionp))))

(defthm subregionp-of-bvchop-arg4
  (implies (and (<= 48 size)
                (integerp size))
           (equal (subregionp len1 ad1 len2 (bvchop size ad2))
                  (subregionp len1 ad1 len2 ad2)))
  :hints (("Goal" :in-theory (enable subregionp in-regionp))))

(defthm subregionp-cancel-constants-1+-1
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (not (equal 0 k1)) ; prevent loops
                )
           (equal (subregionp len1 (bvplus 48 k1 x) len2 k2)
                  (subregionp len1 x len2 (bvminus 48 k2 k1))))
  :hints (("Goal" :in-theory (enable subregionp in-regionp))))

(defthm subregionp-cancel-constants-1+-1+
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (not (equal 0 k1)) ; prevent loops
                )
           (equal (subregionp len1 (bvplus 48 k1 x) len2 (bvplus 48 k2 y))
                  (subregionp len1 x len2 (bvplus 48 (bvminus 48 k2 k1) y))))
  :hints (("Goal" :in-theory (enable subregionp in-regionp))))

;; (thm
;;   (equal (sbvlt 48 x 0)
;;          (<= (expt 2 47) (bvchop 48 x)))
;;   :hints (("Goal" :in-theory (e/d (sbvlt) (logext)))))

;; removes the negative part of the range
(defthm subregionp-when-non-negative-and-negative-range
  (implies (and (<= (expt 2 47) (bvchop 48 k)) ; (sbvlt 48 k 0)
                (unsigned-byte-p 48 k) ; drop?
                (unsigned-byte-p 47 x) ; non-negative
                (unsigned-byte-p 47 len1)
                (unsigned-byte-p 47 len2) ; gen?
                (<= (- (expt 2 48) k) len2) ;move to rhs?
                )
           (equal (subregionp len1 x len2 k)
                  (subregionp len1 x (- len2 (- (expt 2 48) k)) 0)))
  :hints (("Goal" :in-theory (enable subregionp in-regionp bvplus bvuminus bvlt acl2::bvchop-of-sum-cases unsigned-byte-p
                                     ;;acl2::sbvlt-rewrite
                                     ))))

;; decrementing both sizes doesn't change the answer, so we can decrement all the way down to 1
(defthm subregionp-reduce-sizes
  (implies (and (< 1 len1) ; prevent loops
                (<= len1 len2)
                (natp len1)
                (natp len2)
                ;(< len1 1000)
                (unsigned-byte-p 48 len2)
                )
           (equal (subregionp len1 x len2 y)
                  (subregionp 1 x (- len2 (- len1 1)) y)))
  :hints (("Goal" :in-theory (enable subregionp in-regionp bvlt bvplus bvuminus acl2::bvchop-of-sum-cases))))

(defthm subregionp-of-1-arg1
  (equal (subregionp 1 x len2 y)
         (in-regionp x len2 y))
  :hints (("Goal" :in-theory (enable subregionp in-regionp bvlt bvplus bvuminus acl2::bvchop-of-sum-cases))))

(defthm subregionp-subst-constant-arg4
  (implies (and (equal k (bvchop 48 ad2))
                (syntaxp (and (quotep k)
                              (not (quotep ad2)))))
           (equal (subregionp n1 ad1 n2 ad2)
                  (subregionp n1 ad1 n2 k)))
  :hints (("Goal" :in-theory (enable subregionp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; R1 is a subregion of R2 iff every address in R1 is in R2.
(defun-sk subregionp-spec (len1 ad1 len2 ad2)
  (forall (ad)
          (implies (in-regionp ad len1 ad1)
                   (in-regionp ad len2 ad2))))
(local (in-theory (disable subregionp-spec)))

(defthm in-regionp-when-in-regionp-and-subregionp-spec
  (implies (and (subregionp-spec len1 ad1 len2 ad2)
                (in-regionp ad len1 ad1))
           (in-regionp ad len2 ad2))
  :hints (("Goal" :use subregionp-spec-necc)))

(defthm not-subregionp-spec-when-in-regionp-and-not-in-regionp
  (implies (and (in-regionp ad len1 ad1) ; ad is a free var
                (not (in-regionp ad len2 ad2)))
           (not (subregionp-spec len1 ad1 len2 ad2)))
  :hints (("Goal" :use in-regionp-when-in-regionp-and-subregionp-spec
           :in-theory (disable in-regionp-when-in-regionp-and-subregionp-spec))))

(defthm subregion-correct-forward
  (implies (and (unsigned-byte-p 48 len1)
                (unsigned-byte-p 48 len2))
           (implies (subregionp len1 ad1 len2 ad2)
                    (subregionp-spec len1 ad1 len2 ad2)))
  :hints (("Goal"
           :use (:instance in-regionp-when-in-regionp-and-subregionp
                           (ad (subregionp-spec-witness len1 ad1 len2 ad2)))
           :in-theory (e/d (subregionp-spec)
                           (in-regionp-when-in-regionp-and-subregionp)))))

(local
  (defthm subregionp-spec-same-ads-forward
    (implies (and (unsigned-byte-p 48 len1)
                  (unsigned-byte-p 48 len2))
             (implies (subregionp-spec len1 ad len2 ad)
                      (<= len1 len2)))
    :hints (("Goal" :use (:instance not-subregionp-spec-when-in-regionp-and-not-in-regionp
                                    (ad (bvplus 48 ad len2))
                                    (ad1 ad)
                                    (ad2 ad))
             :in-theory (e/d (in-regionp bvlt)
                             (not-subregionp-spec-when-in-regionp-and-not-in-regionp))))))

(local
  (defthm subregionp-spec-same-ads-backward
    (implies (and (unsigned-byte-p 48 len1)
                  (unsigned-byte-p 48 len2))
             (implies (<= len1 len2)
                      (subregionp-spec len1 ad len2 ad)))
    :hints (("Goal" :in-theory (enable SUBREGIONP-SPEC)))))

(defthm subregionp-spec-same-ads
  (implies (and (unsigned-byte-p 48 len1)
                (unsigned-byte-p 48 len2))
           (equal (subregionp-spec len1 ad len2 ad)
                  (<= len1 len2))))

;; ;; The bad guy is an address in r1 but not in r2, is there if such an address
;; (defun bad-guy (r1 r2)
;;   (if (zp (len r1))
;;       nil
;;     (if (member-equal (first r1) r2)
;;         (bad-guy (rest r1) (remove1-equal (first r1) r2))
;;       (first r1))))

;; (local (include-book "kestrel/lists-light/remove1-equal" :dir :system))
;; (thm
;;   (implies (and (no-duplicatesp-equal r1)
;;                 (no-duplicatesp-equal r2)
;;                 (< (len r2) (len r1)))
;;            (and (member-equal (bad-guy r1 r2) r1)
;;                 (not (member-equal (bad-guy r1 r2) r2)))))

;; (thm
;;   (implies (and (no-duplicatesp-equal r1)
;;                 (no-duplicatesp-equal r2)
;;                 (< (len r2) (len r1)))
;;            (not (subsetp-equal r1 r2)))
;;   :hints (("Goal" :induct (subsetp-equal r1 r2)
;;            :in-theory (enable subsetp-equal))))



;; ;r2 could overlap both ends of r1 without overlapping the middle, since this is a cyclic space
;; (thm
;;   (implies (and (unsigned-byte-p 48 len1)
;;                 (unsigned-byte-p 48 len2)
;;                 (bvlt 48 len2 len1)
;;                 (< 0 len1))
;;            (not (subregionp-spec len1 ad1 len2 ad2))))

;todo!
;; (defthm subregion-correct-back
;;   (implies (and (unsigned-byte-p 48 len1)
;;                 (unsigned-byte-p 48 len2))
;;            (implies (subregionp-spec len1 ad1 len2 ad2)
;;                     (subregionp len1 ad1 len2 ad2)))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :use ( ;(:instance in-regionp-when-in-regionp-and-subregionp-spec (ad (if (in-regionp ad1 len2 ad2) (bvplus 48 -1 (bvplus 48 len1 ad1)) ad1)))
;;                  )
;;            :in-theory (e/d (subregionp ;in-regionp
;;                             ;; bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt
;;                             )
;;                            ( ;IN-REGIONP-WHEN-IN-REGIONP-AND-SUBREGIONP-SPEC
;;                             )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; It R1 and R2 are disjoint, and R3 is within R1, and R4 is within R2, than R3 and R4 are disjoint.
(defthm disjoint-regionsp-when-disjoint-regionsp-and-subregionp-and-subregionp
  (implies (and (disjoint-regionsp len1 ad1 len2 ad2)
                (subregionp len3 ad3 len1 ad1) ; expand to bv ops?
                (subregionp len4 ad4 len2 ad2) ; expand to bv ops?
                (unsigned-byte-p 48 len1)
                (unsigned-byte-p 48 len2)
                (unsigned-byte-p 48 len3)
                (unsigned-byte-p 48 len4))
           (disjoint-regionsp len3 ad3 len4 ad4))
  :hints (("Goal"
           :in-theory (enable in-regionp disjoint-regionsp subregionp
                              bvuminus bvplus bvlt
                              ifix
                              acl2::bvlt-of-0-arg2
                              acl2::bvchop-of-sum-cases
                              zp))))

(defthm disjoint-regionsp-when-disjoint-regionsp-and-subregionp-and-subregionp-alt
  (implies (and (disjoint-regionsp len2 ad2 len1 ad1)
                (subregionp len3 ad3 len1 ad1) ; expand to bv ops?
                (subregionp len4 ad4 len2 ad2) ; expand to bv ops?
                (unsigned-byte-p 48 len1)
                (unsigned-byte-p 48 len2)
                (unsigned-byte-p 48 len3)
                (unsigned-byte-p 48 len4))
           (disjoint-regionsp len3 ad3 len4 ad4))
  :hints (("Goal" :in-theory (enable disjoint-regionsp-symmetric))))
