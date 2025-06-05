; Disjointness of memory regions
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X") ; todo: pull out of x86

(defmacro make-memory-region-machinery (num-address-bits)
  (declare (xargs :guard (natp num-address-bits)))
  `(progn
    (include-book "kestrel/bv/bvlt-def" :dir :system)
    (include-book "kestrel/bv/bvminus" :dir :system) ; todo: reduce

    (encapsulate ()
       ;; See also the function SEPARATE, but this machinery is intended to be more amenable to SMT solving.

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
       ;; We put the len argument before start-ad because len is often a small constant.
       ;; In the normal case (non-huge, non-zero length), this can be opened up to a nice BV claim.
       (defund in-regionp (ad len start-ad)
         (declare (xargs :guard (and (unsigned-byte-p ,num-address-bits ad)
                                     (natp len) ; note that len >= 2^,num-address-bits covers the whole region
                                     (unsigned-byte-p ,num-address-bits start-ad))))
         (and (natp len) ; len=0 falsifies the bvlt below
              (if (<= (expt 2 ,num-address-bits) len) ; we handle (expt 2 ,num-address-bits) here, since the len gets chopped to ,num-address-bits bits below
                  t ; the region covers the whole address space
                (bvlt ,num-address-bits (bvminus ,num-address-bits ad start-ad) len))))

       ;; Nothing is in a region of size 0
       (defthm not-in-regionp-of-0s
         (not (in-regionp ad 0 start-ad))
         :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix ACL2::BVCHOP-OF-SUM-CASES))))

       ;; The address at the start of the region is in the region IFF the size is non-zero
       (defthm in-regionp-same
         (equal (in-regionp ad len ad)
                (posp len))
         :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

       ;; The address at the end of the region is in the region IFF the size is non-zero
       (defthm in-regionp-same-end
         (equal (in-regionp (bvplus ,num-address-bits ad (bvplus ,num-address-bits -1 len)) len ad)
                (posp len))
         :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

       (defthm in-regionp-same-end-alt
         (equal (in-regionp (bvplus ,num-address-bits ,(+ -1 (expt 2 num-address-bits)) (bvplus ,num-address-bits ad len)) len ad)
                (posp len))
         :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

       ;; note that the region size can't be 2^,num-address-bits
       (defthm not-in-regionp-one-past-end
         (equal (in-regionp (bvplus ,num-address-bits ad len) len ad)
                (and (<= (expt 2 ,num-address-bits) len)
                     (natp len)))
         :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

       ;; if the region size is 2^,num-address-bits-1, being in the region means not being the single address just before the region
       (defthm in-regionp-of-2^num-address-bits-1
         (equal (in-regionp ad (+ -1 (expt 2 ,num-address-bits)) start-ad)
                (not (equal (bvchop ,num-address-bits ad) (bvminus ,num-address-bits start-ad 1))))
         :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases))))

       (defthm in-regionp-monotone
         (implies (and (in-regionp x len1 ad)
                       (<= len1 len2)
                       (unsigned-byte-p ,num-address-bits len1)
                       (unsigned-byte-p ,num-address-bits len2))
                  (in-regionp x len2 ad))
         :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

       (defthm not-in-regionp-too-far
         (implies (and (in-regionp x len ad)
                       (bvle ,num-address-bits len (bvminus ,num-address-bits y x)) ; y is at least LEN above x
                       (bvle ,num-address-bits (bvminus ,num-address-bits x ad) (bvminus ,num-address-bits y ad)) ; x is closer to the start of the region than y
                       (unsigned-byte-p ,num-address-bits len))
                  (not (in-regionp y len ad)))
         :hints (("Goal" :in-theory (enable in-regionp bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

       (defthm in-regionp-of-bvchop-arg1
         (implies (and (<= ,num-address-bits n)
                       (integerp n))
                  (equal (in-regionp (bvchop n ad) len start-ad)
                         (in-regionp ad len start-ad)))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthm in-regionp-of-bvchop-arg3
         (implies (and (<= ,num-address-bits n)
                       (integerp n))
                  (equal (in-regionp ad len (bvchop n start-ad))
                         (in-regionp ad len start-ad)))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthmd in-regionp-of-+-arg1
         (implies (and (integerp x)
                       (integerp y))
                  (equal (in-regionp (+ x y) len ad)
                         (in-regionp (bvplus ,num-address-bits x y) len ad)))
         :hints (("Goal" :in-theory (enable in-regionp bvplus))))

       (theory-invariant (incompatible (:rewrite in-regionp-of-+-arg1) (:definition bvplus)))

       (defthmd in-regionp-of-+-arg3
         (implies (and (integerp x)
                       (integerp y))
                  (equal (in-regionp ad len (+ x y))
                         (in-regionp ad len (bvplus ,num-address-bits x y))))
         :hints (("Goal" :in-theory (enable in-regionp bvplus))))

       (theory-invariant (incompatible (:rewrite in-regionp-of-+-arg3) (:definition bvplus)))

       (defthm in-regionp-cancel-1-1+
         (equal (in-regionp x len (bvplus ,num-address-bits x z))
                (in-regionp 0 len z))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthm in-regionp-cancel-1+-1
         (equal (in-regionp (bvplus ,num-address-bits x z) len x)
                (in-regionp z len 0))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthm in-regionp-cancel-1+-1+
         (equal (in-regionp (bvplus ,num-address-bits x y) len (bvplus ,num-address-bits x z))
                (in-regionp y len z))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthm in-regionp-cancel-1-2
         (equal (in-regionp x len2 (bvplus ,num-address-bits y x))
                (in-regionp 0 len2 y))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthm in-regionp-cancel-2-1
         (equal (in-regionp (bvplus ,num-address-bits y x) len2 x)
                (in-regionp y len2 0))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthm in-regionp-cancel-2-1+
         (equal (in-regionp (bvplus ,num-address-bits y x) len2 (bvplus ,num-address-bits x z))
                (in-regionp y len2 z))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthm in-regionp-cancel-1+-2
         (equal (in-regionp (bvplus ,num-address-bits x y) len (bvplus ,num-address-bits z x))
                (in-regionp y len z))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthm in-regionp-cancel-2-2
         (equal (in-regionp (bvplus ,num-address-bits y x) len2 (bvplus ,num-address-bits z x))
                (in-regionp y len2 z))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthm in-regionp-cancel-3-1
         (equal (in-regionp (bvplus ,num-address-bits y (bvplus ,num-address-bits z x)) len x)
                (in-regionp (bvplus ,num-address-bits y z) len 0))
         :hints (("Goal" :in-theory (enable in-regionp))))

       ;; todo: hints
       (defthm in-regionp-cancel-1-3
         (equal (in-regionp x len (bvplus ,num-address-bits y (bvplus ,num-address-bits z x)))
                (in-regionp 0 len (bvplus ,num-address-bits y z)))
         :hints (("Goal" :in-theory (enable in-regionp bvuminus bvminus bvlt ifix bvplus))))

       ;; removes the negative part of the range
       (defthm in-regionp-when-non-negative-and-negative-range
         (implies (and (syntaxp (quotep k))
                       (<= (expt 2 ,(+ -1 num-address-bits)) (bvchop ,num-address-bits k)) ; (sbvlt ,num-address-bits k 0) ; negative
                       (unsigned-byte-p ,(+ -1 num-address-bits) x) ; non-negative
                       (unsigned-byte-p ,num-address-bits k) ; drop?
                       (unsigned-byte-p ,(+ -1 num-address-bits) len2) ; gen?
                       (<= (- (expt 2 ,num-address-bits) k) len2) ;move to rhs?
                       )
                  (equal (in-regionp x len2 k)
                         (in-regionp x (- len2 (- (expt 2 ,num-address-bits) k)) 0)))
         :hints (("Goal" :cases ((< (+ (expt 2 ,num-address-bits) (- k) x) len2))
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
                  (equal (in-regionp (bvplus ,num-address-bits k1 x) len2 (bvplus ,num-address-bits k2 y))
                         (in-regionp x len2 (bvplus ,num-address-bits (bvminus ,num-address-bits k2 k1) y))))
         :hints (("Goal" :in-theory (enable in-regionp))))

       ;; which arg do we prefer to make 0?
       (defthm in-regionp-cancel-constants-1-1+
         (implies (and (syntaxp (and (quotep k1)
                                     (quotep k2)))
                       (not (equal 0 k1)) ; prevent loops
                       )
                  (equal (in-regionp k1 len2 (bvplus ,num-address-bits k2 y))
                         (in-regionp 0 len2 (bvplus ,num-address-bits (bvminus ,num-address-bits k2 k1) y))))
         :hints (("Goal" :in-theory (enable in-regionp))))

       ;; how do we prefer to handle this?
       (defthm in-regionp-cancel-constants-1+-1
         (implies (and (syntaxp (and (quotep k1)
                                     (quotep k2)))
                       (not (equal 0 k1)) ; prevent loops
                       )
                  (equal (in-regionp (bvplus ,num-address-bits k1 x) len2 k2)
                         (in-regionp x len2 (bvminus ,num-address-bits k2 k1))))
         :hints (("Goal" :in-theory (enable in-regionp))))

       ;; disabled for the proofs below
       (defthmd in-regionp-of-0-arg3
         (equal (in-regionp ad len 0)
                (and (natp len)
                     (or (<= (expt 2 ,num-address-bits) len)
                         (bvlt ,num-address-bits ad len))))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthm in-regionp-subst-constant-arg1
         (implies (and (equal k (bvchop ,num-address-bits ad1))
                       (syntaxp (and (quotep k)
                                     (not (quotep ad1)))))
                  (equal (in-regionp ad1 n2 ad2)
                         (in-regionp k n2 ad2)))
         :hints (("Goal" :in-theory (enable in-regionp))))

       (defthmd in-regionp-opener
         (implies (and (not (zp len))
;                (unsigned-byte-p ,num-address-bits len)
;       (unsigned-byte-p ,num-address-bits ad)
                       (unsigned-byte-p ,num-address-bits start-ad)
                       )
                  (equal (in-regionp ad len start-ad)
                         (or (equal (bvchop ,num-address-bits ad) start-ad)
                             (in-regionp ad (+ -1 len) (+ 1 start-ad)))))
         :hints (("Goal" :in-theory (enable in-regionp bvlt bvplus bvminus bvuminus acl2::bvchop-of-sum-cases))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ;; Defines what it means for 2 memory regions to be disjoint (no address in both regions).
       ;; Region1 has size len1 and starts at ad1.
       ;; Region2 has size len2 and starts at ad2.
       ;; Regions may wrap around the end of the address space back to the start.
       ;; We put the len arguments first because they will often be small constants.
       ;; In the normal case, this can be opened up to a conjunction of nice, BV claims.
       (defund disjoint-regionsp (len1 ad1 len2 ad2)
         (declare (xargs :guard (and (natp len1) ; note that len >= 2^,num-address-bits covers the whole region
                                     (unsigned-byte-p ,num-address-bits ad1)
                                     (natp len2) ; note that len >= 2^,num-address-bits covers the whole region
                                     (unsigned-byte-p ,num-address-bits ad2))))
         (if (or (zp len1)
                 (zp len2))
             t ; one region is empty
           (if (or (<= (expt 2 ,num-address-bits) len1)
                   (<= (expt 2 ,num-address-bits) len2))
               nil ; one region covers the whole space (and the other is not empty)
             ;; Normal case (non-huge, non-empty regions):
             (and (bvle ,num-address-bits len1 (bvminus ,num-address-bits ad2 ad1)) ; the start of region2 is not within region 1  ;; todo: rephrase to use bvlt?
                  (bvle ,num-address-bits len2 (bvminus ,num-address-bits ad1 ad2)) ; the start of region1 is not within region 2
                  ))))

       ;; todo: more sanity check properties

       (defthm disjoint-regionsp-when-not-posp
         (implies (not (posp len1))
                  (disjoint-regionsp len1 ad1 len2 ad2))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

       ;; (defthm disjoint-regionsp-when-zp
       ;;   (implies (and (zp len1)
       ;;                 ;(natp len1) ; drop, have the function nfix
       ;;                 )
       ;;            (disjoint-regionsp len1 ad1 len2 ad2))
       ;;   :hints (("Goal" :in-theory (enable disjoint-regionsp zp))))

       (defthmd disjoint-regionsp-symmetric
         (equal (disjoint-regionsp len1 ad1 len2 ad2)
                (disjoint-regionsp len2 ad2 len1 ad1))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

       ;; Addresses in disjoint regions cannot be equal.
       (defthm not-equal-of-bvchop-and-bvchop-when-in-disjoint-regions
         (implies (and (disjoint-regionsp len1 start1 len2 start2)
                       (in-regionp ad1 len1 start1)
                       (in-regionp ad2 len2 start2))
                  (not (equal (bvchop ,num-address-bits ad1) (bvchop ,num-address-bits ad2))))
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

       (defthm not-in-regionp-when-disjoint-regionsp-1
         (implies (and (disjoint-regionsp len1 start1 len2 start2)
                       (in-regionp ad len1 start1))
                  (not (in-regionp ad len2 start2)))
         :hints (("Goal" :in-theory (enable))))

       (defthm not-in-regionp-when-disjoint-regionsp-2
         (implies (and (disjoint-regionsp len1 start1 len2 start2)
                       (in-regionp ad len2 start2))
                  (not (in-regionp ad len1 start1)))
         :hints (("Goal" :in-theory (enable))))

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

       (defthmd disjoint-regionsp-of-+-arg2
         (implies (and (integerp ad1)
                       (integerp x))
                  (equal (disjoint-regionsp len1 (+ x ad1) len2 ad2)
                         (disjoint-regionsp len1 (bvplus ,num-address-bits x ad1) len2 ad2)))
         :hints (("Goal" :in-theory (enable disjoint-regionsp
                                            acl2::bvminus-of-+-arg2
                                            acl2::bvminus-of-+-arg3))))

       (theory-invariant (incompatible (:rewrite disjoint-regionsp-of-+-arg2) (:definition bvplus)))

       (defthmd disjoint-regionsp-of-+-arg4
         (implies (and (integerp ad2)
                       (integerp x))
                  (equal (disjoint-regionsp len1 ad1 len2 (+ x ad2))
                         (disjoint-regionsp len1 ad1 len2 (bvplus ,num-address-bits x ad2))))
         :hints (("Goal" :in-theory (enable disjoint-regionsp
                                            acl2::bvminus-of-+-arg2
                                            acl2::bvminus-of-+-arg3))))

       (theory-invariant (incompatible (:rewrite disjoint-regionsp-of-+-arg4) (:definition bvplus)))

      ;;more?
       (defthm disjoint-regionsp-cancel-1-2
         (equal (disjoint-regionsp len1 x len2 (bvplus ,num-address-bits y x))
                (disjoint-regionsp len1 0 len2 y))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

      (defthm disjoint-regionsp-cancel-2-1
        (equal (disjoint-regionsp len1 (bvplus ,num-address-bits y x) len2 x)
               (disjoint-regionsp len1 y len2 0))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

       (defthm disjoint-regionsp-cancel-1-1+
         (equal (disjoint-regionsp len1 x len2 (bvplus ,num-address-bits x y))
                (disjoint-regionsp len1 0 len2 y))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

       (defthm disjoint-regionsp-cancel-1+-1
         (equal (disjoint-regionsp len1 (bvplus ,num-address-bits x z) len2 x)
                (disjoint-regionsp len1 z len2 0))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

       (defthm disjoint-regionsp-cancel-1+-1+
         (equal (disjoint-regionsp len1 (bvplus ,num-address-bits x z) len2 (bvplus ,num-address-bits x y))
                (disjoint-regionsp len1 z len2 y))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

       (defthm disjoint-regionsp-cancel-1+-2
         (equal (disjoint-regionsp len1 (bvplus ,num-address-bits x z) len2 (bvplus ,num-address-bits y x))
                (disjoint-regionsp len1 z len2 y))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

       (defthm disjoint-regionsp-cancel-2-1+
         (equal (disjoint-regionsp len1 (bvplus ,num-address-bits z x) len2 (bvplus ,num-address-bits x y))
                (disjoint-regionsp len1 z len2 y))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

       (defthm disjoint-regionsp-cancel-2-2
         (equal (disjoint-regionsp len1 (bvplus ,num-address-bits z x) len2 (bvplus ,num-address-bits y x))
                (disjoint-regionsp len1 z len2 y))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

      ;; todo: more like this?
      (defthm disjoint-regionsp-of-bvplus-of-constant-and-constant
        (implies (syntaxp (and (quotep k1)
                               (quotep k2)))
                 (equal (disjoint-regionsp len1 (bvplus ,num-address-bits k1 x) len2 k2)
                        (disjoint-regionsp len1 x len2 (bvminus ,num-address-bits k2 k1))))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

      (defthm disjoint-regionsp-of-1-and-1
        (equal (disjoint-regionsp 1 x 1 y)
               (not (equal (bvchop ,num-address-bits x)
                           (bvchop ,num-address-bits y))))
        :hints (("Goal" :in-theory (e/d (disjoint-regionsp)
                                        (acl2::bvminus-becomes-bvplus-of-bvuminus)))))

       ;; todo: show that this reduces to a more familiar notion in the non-wrap-around case
       ;; todo: use defun-sk to show correctness

       (defthm disjoint-regionsp-of-bvchop-arg2
         (implies (and (<= ,num-address-bits size)
                       (integerp size))
                  (equal (disjoint-regionsp len1 (bvchop size ad1) len2 ad2)
                         (disjoint-regionsp len1 ad1 len2 ad2)))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

       (defthm disjoint-regionsp-of-bvchop-arg4
         (implies (and (<= ,num-address-bits size)
                       (integerp size))
                  (equal (disjoint-regionsp len1 ad1 len2 (bvchop size ad2))
                         (disjoint-regionsp len1 ad1 len2 ad2)))
         :hints (("Goal" :in-theory (enable disjoint-regionsp))))

       ;; Higher level spec of disjoint-regionsp: Two regions are disjoint if there is
       ;; no address that is in both of them.
       (defun-sk disjoint-regionsp-spec (len1 ad1 len2 ad2)
         (forall (ad)
                 (not (and (in-regionp ad len1 ad1)
                           (in-regionp ad len2 ad2)))))

       (in-theory (disable disjoint-regionsp-spec))

       (defthm disjoint-regionsp-spec-necc-better
         (implies (and (in-regionp ad len1 ad1)
                       (in-regionp ad len2 ad2))
                  (not (disjoint-regionsp-spec len1 ad1 len2 ad2)))
         :hints (("Goal" :use disjoint-regionsp-spec-necc
                  :in-theory (theory 'minimal-theory))))

       (defthm disjoint-regionsp-spec-necc-better-alt
         (implies (and (in-regionp ad len2 ad2)
                       (in-regionp ad len1 ad1))
                  (not (disjoint-regionsp-spec len1 ad1 len2 ad2)))
         :hints (("Goal" :use disjoint-regionsp-spec-necc
                  :in-theory (theory 'minimal-theory))))

       (encapsulate ()
         (local (defthmd disjoint-regionsp-spec-of-bvchop-arg2-fw
                  (implies (disjoint-regionsp-spec len1 (bvchop ,num-address-bits ad1) len2 ad2)
                           (disjoint-regionsp-spec len1 ad1 len2 ad2))
                  :hints (("Goal" :expand (disjoint-regionsp-spec len1 ad1 len2 ad2)
                           :in-theory (enable ;disjoint-regionsp-spec
                                        )))))

         (local (defthmd disjoint-regionsp-spec-of-bvchop-arg2-bk
                  (implies (disjoint-regionsp-spec len1 ad1 len2 ad2)
                           (disjoint-regionsp-spec len1 (bvchop ,num-address-bits ad1) len2 ad2))
                  :hints (("Goal"  :expand (disjoint-regionsp-spec len1 (bvchop ,num-address-bits ad1) len2 ad2)
                           :in-theory (enable ;disjoint-regionsp-spec
                                        )))))

         (defthm disjoint-regionsp-spec-of-bvchop-arg2
           (equal (disjoint-regionsp-spec len1 (bvchop ,num-address-bits ad1) len2 ad2)
                  (disjoint-regionsp-spec len1 ad1 len2 ad2))
           :hints (("Goal" :use (disjoint-regionsp-spec-of-bvchop-arg2-fw
                                  disjoint-regionsp-spec-of-bvchop-arg2-bk)))))

       (encapsulate ()
         (local (defthmd disjoint-regionsp-spec-of-bvchop-arg4-fw
                  (implies (disjoint-regionsp-spec len1 ad1 len2 (bvchop ,num-address-bits ad2))
                           (disjoint-regionsp-spec len1 ad1 len2 ad2))
                  :hints (("Goal"  :expand (disjoint-regionsp-spec len1 ad1 len2 ad2)
                           :in-theory (enable ;disjoint-regionsp-spec
                                        )))))

         (local (defthmd disjoint-regionsp-spec-of-bvchop-arg4-bk
                  (implies (disjoint-regionsp-spec len1 ad1 len2 ad2)
                           (disjoint-regionsp-spec len1 ad1 len2 (bvchop ,num-address-bits ad2)))
                  :hints (("Goal" :expand (disjoint-regionsp-spec len1 ad1 len2 (bvchop ,num-address-bits ad2))
                           :in-theory (enable ;disjoint-regionsp-spec
                                        )))))

         (defthm disjoint-regionsp-spec-of-bvchop-arg4
           (equal (disjoint-regionsp-spec len1 ad1 len2 (bvchop ,num-address-bits ad2))
                  (disjoint-regionsp-spec len1 ad1 len2 ad2))
           :hints (("Goal" :use (disjoint-regionsp-spec-of-bvchop-arg4-fw
                                  disjoint-regionsp-spec-of-bvchop-arg4-bk)))))

       (defthm disjoint-regionsp-spec-of-one-smaller
         (implies (and (not (zp len1))
                       (disjoint-regionsp-spec len1 ad1 len2 ad2)
        ;        (unsigned-byte-p ,num-address-bits len1)
        ;       (unsigned-byte-p ,num-address-bits len2)
                       (unsigned-byte-p ,num-address-bits ad1)
                       (unsigned-byte-p ,num-address-bits ad2))
                  (disjoint-regionsp-spec (+ -1 len1) (bvplus ,num-address-bits 1 ad1) len2 ad2))
         :hints (("Goal" :expand ((disjoint-regionsp-spec (+ -1 len1) (bvplus ,num-address-bits 1 ad1) len2 ad2))
                  :use (:instance disjoint-regionsp-spec-necc-better
                                  (ad (disjoint-regionsp-spec-witness (+ -1 len1) (bvplus ,num-address-bits 1 ad1) len2 ad2)))
                  :in-theory (e/d (in-regionp-opener in-regionp-of-+-arg3)
                                  (disjoint-regionsp-spec-necc-better
                                   disjoint-regionsp-spec-necc-better-alt)))))

       (local (defun indf (n ad) (if (zp n) (list n ad) (indf (+ -1 n) (bvplus ,num-address-bits 1 ad)))))

       (defthmd disjoint-regionsp-opener
         (implies (and (posp len1)
         ;       (unsigned-byte-p ,num-address-bits len1)
         ;      (unsigned-byte-p ,num-address-bits len2)
                       (unsigned-byte-p ,num-address-bits ad1)
;                (unsigned-byte-p ,num-address-bits ad2)
                       )
                  (equal (disjoint-regionsp len1 ad1 len2 ad2)
                         (and (not (in-regionp ad1 len2 ad2))
                              (disjoint-regionsp (+ -1 len1) (+ 1 ad1) len2 ad2))))
         :hints (("Goal" :in-theory (enable disjoint-regionsp in-regionp bvlt bvplus bvminus bvuminus acl2::bvchop-of-sum-cases))))

       (defthm disjoint-regionsp-correct-backward
         (implies (and (disjoint-regionsp-spec len1 ad1 len2 ad2)
                       (unsigned-byte-p ,num-address-bits ad1)
                       (unsigned-byte-p ,num-address-bits ad2))
                  (disjoint-regionsp len1 ad1 len2 ad2))
         :hints (("Goal" :induct (indf len1 ad1)
                  :in-theory (enable disjoint-regionsp-opener
                                     disjoint-regionsp-of-+-arg2
                                     zp natp))))

       (defthm disjoint-regionsp-correct-forward
         (implies (disjoint-regionsp len1 ad1 len2 ad2)
                  (disjoint-regionsp-spec len1 ad1 len2 ad2))
         :hints (("Goal" :in-theory (enable disjoint-regionsp-spec))))

       ;; Shows that the complicated defintion of disjoint-regionsp agrees with the higher-level spec.
       (defthm disjoint-regionsp-correct
         (equal (disjoint-regionsp-spec len1 ad1 len2 ad2)
                (disjoint-regionsp len1 ad1 len2 ad2))
         :hints (("Goal" :use ((:instance disjoint-regionsp-correct-forward (ad1 (bvchop ,num-address-bits ad1)) (ad2 (bvchop ,num-address-bits ad2)))
                               (:instance disjoint-regionsp-correct-backward (ad1 (bvchop ,num-address-bits ad1)) (ad2 (bvchop ,num-address-bits ad2))))
                  :in-theory (disable disjoint-regionsp-correct-forward
                                      disjoint-regionsp-correct-backward))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ;; Checks whether all of the addresses in the first region (of size len1 starting at ad1) are in the second region (of size len2 starting at ad2).
       ;; We put the len args first because they will often be small constants.
       ;; This can be opened to a conjunction of nice BV facts (requires opening in-regionp too).
       (defund subregionp (len1 ad1 len2 ad2)
         (declare (xargs :guard (and (natp len1) ; note that len >= 2^,num-address-bits covers the whole region
                                     (unsigned-byte-p ,num-address-bits ad1)
                                     (natp len2) ; note that len >= 2^,num-address-bits covers the whole region
                                     (unsigned-byte-p ,num-address-bits ad2))))
         (if (zp len1)
             t ; first region is empty
           (if (zp len2)
               nil ; second region is empty (but first is not)
             (if (<= (expt 2 ,num-address-bits) len2)
                 t ; second region is the whole address space
               (if (<= (expt 2 ,num-address-bits) len1)
                   nil ; first region is the whole address space (but second region is not)
                 ;; Normal case (non-huge, non-empty regions):
                 ;; Checks that both the first and last address of region1 are in region2:
                 (and (in-regionp ad1 len2 ad2)
                      (bvle ,num-address-bits len1 len2) ; ensures the difference below is not negative
                      (bvle ,num-address-bits (bvminus ,num-address-bits ad1 ad2) (bvminus ,num-address-bits len2 len1))))))))

       ;; A region is a subregion of itself
       (defthm subregionp-reflexive
         (implies (unsigned-byte-p ,num-address-bits len)
                  (subregionp len ad len ad))
         :hints (("Goal" :in-theory (enable subregionp))))

       ;; A region of size 0 is a subregion of any region
       (defthm subregionp-of-0-arg1
         (subregionp 0 ad len2 ad2)
         :hints (("Goal" :in-theory (enable subregionp))))

       (defthm subregionp-when-zp-arg1
         (implies (zp len1)
                  (subregionp len1 ad1 len2 ad2))
         :hints (("Goal" :in-theory (enable subregionp))))

       ;; A region is a subregion or some other region of size 0 only if it iself has size 0.
       (defthm subregionp-of-0-arg3
         (equal (subregionp len1 ad1 0 ad2)
                (zp len1))
         :hints (("Goal" :in-theory (enable subregionp))))

       ;; todo: prove transitive, anti-symm

       (defthm in-regionp-when-in-regionp-and-subregionp
         (implies (and (subregionp len1 ad1 len2 ad2)
                       (in-regionp ad len1 ad1))
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
                       (not (in-regionp ad len2 ad2)))
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
         (equal (subregionp len1 (bvplus ,num-address-bits x y) len2 x)
                (subregionp len1 y len2 0))
         :hints (("Goal" :in-theory (enable subregionp))))

       (defthm subregionp-cancel-1-1+
         (equal (subregionp len1 x len2 (bvplus ,num-address-bits x y))
                (subregionp len1 0 len2 y))
         :hints (("Goal" :in-theory (enable subregionp))))

       (defthm subregionp-cancel-2-1
         (equal (subregionp len1 (bvplus ,num-address-bits y x) len2 x)
                (subregionp len1 y len2 0))
         :hints (("Goal" :in-theory (enable subregionp))))

       (defthm subregionp-cancel-2-1+
         (equal (subregionp len1 (bvplus ,num-address-bits y x) len2 (bvplus ,num-address-bits x z))
                (subregionp len1 y len2 z))
         :hints (("Goal" :in-theory (enable subregionp))))

       (defthm subregionp-cancel-1-2
         (equal (subregionp len1 x len2 (bvplus ,num-address-bits y x))
                (subregionp len1 0 len2 y))
         :hints (("Goal" :in-theory (enable subregionp))))

       (defthm subregionp-cancel-1+-2
         (equal (subregionp len1 (bvplus ,num-address-bits x z) len2 (bvplus ,num-address-bits y x))
                (subregionp len1 z len2 y))
         :hints (("Goal" :in-theory (enable subregionp))))

       (defthm subregionp-cancel-2-2
         (equal (subregionp len1 (bvplus ,num-address-bits y x) len2 (bvplus ,num-address-bits z x))
                (subregionp len1 y len2 z))
         :hints (("Goal" :in-theory (enable subregionp))))

       ;; todo: more cancellation rules, or a general solution?

       (defthmd subregionp-of-+-arg2
         (implies (and (integerp x)
                       (integerp y))
                  (equal (subregionp len1 (+ x y) len2 ad2)
                         (subregionp len1 (bvplus ,num-address-bits x y) len2 ad2)))
         :hints (("Goal" :in-theory (enable subregionp
                                            in-regionp-of-+-arg1
                                            acl2::bvminus-of-+-arg2))))
       (theory-invariant (incompatible (:rewrite subregionp-of-+-arg2) (:definition bvplus)))

       (defthmd subregionp-of-+-arg4
         (implies (and (integerp x)
                       (integerp y))
                  (equal (subregionp len1 ad1 len2 (+ x y))
                         (subregionp len1 ad1 len2 (bvplus ,num-address-bits x y))))
         :hints (("Goal" :in-theory (enable subregionp
                                            acl2::bvminus-of-+-arg3
                                            in-regionp-of-+-arg3))))
      (theory-invariant (incompatible (:rewrite subregionp-of-+-arg4) (:definition bvplus)))

       (defthm subregionp-of-bvchop-arg2
         (implies (and (<= ,num-address-bits size)
                       (integerp size))
                  (equal (subregionp len1 (bvchop size ad1) len2 ad2)
                         (subregionp len1 ad1 len2 ad2)))
         :hints (("Goal" :in-theory (enable subregionp in-regionp))))

       (defthm subregionp-of-bvchop-arg4
         (implies (and (<= ,num-address-bits size)
                       (integerp size))
                  (equal (subregionp len1 ad1 len2 (bvchop size ad2))
                         (subregionp len1 ad1 len2 ad2)))
         :hints (("Goal" :in-theory (enable subregionp in-regionp))))

       (defthm subregionp-cancel-constants-1+-1
         (implies (and (syntaxp (and (quotep k1)
                                     (quotep k2)))
                       (not (equal 0 k1)) ; prevent loops
                       )
                  (equal (subregionp len1 (bvplus ,num-address-bits k1 x) len2 k2)
                         (subregionp len1 x len2 (bvminus ,num-address-bits k2 k1))))
         :hints (("Goal" :in-theory (enable subregionp in-regionp))))

       (defthm subregionp-cancel-constants-1+-1+
         (implies (and (syntaxp (and (quotep k1)
                                     (quotep k2)))
                       (not (equal 0 k1)) ; prevent loops
                       )
                  (equal (subregionp len1 (bvplus ,num-address-bits k1 x) len2 (bvplus ,num-address-bits k2 y))
                         (subregionp len1 x len2 (bvplus ,num-address-bits (bvminus ,num-address-bits k2 k1) y))))
         :hints (("Goal" :in-theory (enable subregionp in-regionp))))

       ;; (thm
       ;;   (equal (sbvlt ,num-address-bits x 0)
       ;;          (<= (expt 2 ,(+ -1 num-address-bits)) (bvchop ,num-address-bits x)))
       ;;   :hints (("Goal" :in-theory (e/d (sbvlt) (logext)))))

       ;; ;; removes the negative part of the range
       (defthm subregionp-when-non-negative-and-negative-range
         (implies (and (<= (expt 2 ,(+ -1 num-address-bits)) (bvchop ,num-address-bits k)) ; (sbvlt ,num-address-bits k 0)
                       (unsigned-byte-p ,num-address-bits k) ; drop?
                       (unsigned-byte-p ,(+ -1 num-address-bits) x) ; non-negative
                                                                    ;                (unsigned-byte-p ,(+ -1 num-address-bits) len1)
                       (unsigned-byte-p ,(+ -1 num-address-bits) len2) ; gen?
                       (<= (- (expt 2 ,num-address-bits) k) len2) ;move to rhs?
                       )
                  (equal (subregionp len1 x len2 k)
                         (subregionp len1 x (- len2 (- (expt 2 ,num-address-bits) k)) 0)))
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
                       (unsigned-byte-p ,num-address-bits len2)
                       )
                  (equal (subregionp len1 x len2 y)
                         (subregionp 1 x (- len2 (- len1 1)) y)))
         :hints (("Goal" :in-theory (enable subregionp in-regionp bvlt bvplus bvuminus acl2::bvchop-of-sum-cases))))

       (defthm subregionp-of-1-arg1
         (equal (subregionp 1 x len2 y)
                (and (natp len2)
                     (or (<= (expt 2 ,num-address-bits) len2)
                         (in-regionp x len2 y))))
         :hints (("Goal" :in-theory (enable subregionp in-regionp bvlt bvplus bvuminus acl2::bvchop-of-sum-cases))))

       (defthm subregionp-subst-constant-arg4
         (implies (and (equal k (bvchop ,num-address-bits ad2))
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

       (encapsulate ()
         (local
           (defthmd subregionp-spec-of-bvchop-arg2-fw
             (implies (subregionp-spec len1 (bvchop ,num-address-bits ad1) len2 ad2)
                      (subregionp-spec len1 ad1 len2 ad2))
             :hints (("Goal" :expand (subregionp-spec len1 ad1 len2 ad2)))))

         (local
           (defthmd subregionp-spec-of-bvchop-arg2-bk
             (implies (subregionp-spec len1 ad1 len2 ad2)
                      (subregionp-spec len1 (bvchop ,num-address-bits ad1) len2 ad2))
             :hints (("Goal" :expand (subregionp-spec len1 (bvchop ,num-address-bits ad1) len2 ad2)))))

         (defthm subregionp-spec-of-bvchop-arg2
           (equal (subregionp-spec len1 (bvchop ,num-address-bits ad1) len2 ad2)
                  (subregionp-spec len1 ad1 len2 ad2))
           :hints (("Goal" :use (subregionp-spec-of-bvchop-arg2-fw
                                  subregionp-spec-of-bvchop-arg2-bk)))))

       (encapsulate ()
         (local
           (defthmd subregionp-spec-of-bvchop-arg4-fw
             (implies (subregionp-spec len1 ad1 len2 (bvchop ,num-address-bits ad2))
                      (subregionp-spec len1 ad1 len2 ad2))
             :hints (("Goal" :expand (subregionp-spec len1 ad1 len2 ad2)))))

         (local
           (defthmd subregionp-spec-of-bvchop-arg4-bk
             (implies (subregionp-spec len1 ad1 len2 ad2)
                      (subregionp-spec len1 ad1 len2 (bvchop ,num-address-bits ad2)))
             :hints (("Goal" :expand (subregionp-spec len1 ad1 len2 (bvchop ,num-address-bits ad2))))))

         (defthm subregionp-spec-of-bvchop-arg4
           (equal (subregionp-spec len1 ad1 len2 (bvchop ,num-address-bits ad2))
                  (subregionp-spec len1 ad1 len2 ad2))
           :hints (("Goal" :use (subregionp-spec-of-bvchop-arg4-fw
                                  subregionp-spec-of-bvchop-arg4-bk)))))

       (local
         (defthm subregionp-correct-forward
           (implies (subregionp len1 ad1 len2 ad2)
                    (subregionp-spec len1 ad1 len2 ad2))
           :hints (("Goal"
                    :use (:instance in-regionp-when-in-regionp-and-subregionp
                                    (ad (subregionp-spec-witness len1 ad1 len2 ad2)))
                    :in-theory (e/d (subregionp-spec)
                                    (in-regionp-when-in-regionp-and-subregionp))))))

       (local
         (defthm subregionp-spec-same-ads-forward
           (implies (and; (unsigned-byte-p ,num-address-bits len1)
                      (natp len1)
                      (unsigned-byte-p ,num-address-bits len2)
                      )
                    (implies (subregionp-spec len1 ad len2 ad)
                             (<= len1 len2)))
           :hints (("Goal" :use (:instance not-subregionp-spec-when-in-regionp-and-not-in-regionp
                                           (ad (bvplus ,num-address-bits ad len2))
                                           (ad1 ad)
                                           (ad2 ad))
                    :in-theory (e/d (in-regionp bvlt)
                                    (not-subregionp-spec-when-in-regionp-and-not-in-regionp))))))

       (local
         (defthm subregionp-spec-same-ads-backward
           (implies (and (unsigned-byte-p ,num-address-bits len1)
                         (unsigned-byte-p ,num-address-bits len2)
                         )
                    (implies (<= len1 len2)
                             (subregionp-spec len1 ad len2 ad)))
           :hints (("Goal" :in-theory (enable SUBREGIONP-SPEC)))))

       (defthm subregionp-spec-same-ads
         (implies (and (unsigned-byte-p ,num-address-bits len1)
                       (unsigned-byte-p ,num-address-bits len2))
                  (equal (subregionp-spec len1 ad len2 ad)
                         (<= len1 len2))))

;todo: make some stuff here local:
;todo: move some of this up:

       (defthmd subregionp-opener
         (implies (and ;(unsigned-byte-p ,num-address-bits len1)
                    ;(unsigned-byte-p ,num-address-bits len2)
                    (integerp ad1)
                    (not (zp len1)))
                  (equal (subregionp len1 ad1 len2 ad2)
                         (and (in-regionp ad1 len2 ad2)
                              (subregionp (+ -1 len1) (+ 1 ad1) len2 ad2))))
         :hints (("Goal" :in-theory (enable subregionp in-regionp bvlt bvplus bvminus bvuminus acl2::bvchop-of-sum-cases))))

       ;; The bad guy is an address in r1 but not in r2, is there if such an address
       (local
         (defund bad-guy (len1 ad1 len2 ad2)
           (if (zp len1)
               nil
             (if (in-regionp ad1 len2 ad2)
                 ;; keep looking:
                 (bad-guy (+ -1 len1) (bvplus ,num-address-bits 1 ad1) len2 ad2)
               ;; we found a bad guy:
               ad1))))

       (local
         (defthm unsigned-byte-p-of-bad-guy
           (implies (and (bad-guy len1 ad1 len2 ad2)
                         (unsigned-byte-p ,num-address-bits ad1))
                    (unsigned-byte-p ,num-address-bits (bad-guy len1 ad1 len2 ad2)))
           :hints (("Goal" :in-theory (enable bad-guy)))))

       (local
         (defthm in-regionp-of-bad-guy
           (implies (and (bad-guy len1 ad1 len2 ad2)
                         ;(integerp ad1)
                         (unsigned-byte-p ,num-address-bits ad1)
                         (unsigned-byte-p ,num-address-bits ad2)
                         ;(unsigned-byte-p ,num-address-bits len1)
                         (natp len1)
                         )
                    (in-regionp (bad-guy len1 ad1 len2 ad2) len1 ad1))
           :hints (("Goal" :in-theory (enable in-regionp-opener bad-guy in-regionp-of-+-arg3)))))

       (local
         (defthm subregionp-when-in-regionp-of-bad-guy
           (implies (and (in-regionp (bad-guy len1 ad1 len2 ad2) len2 ad2)
                         ;(unsigned-byte-p ,num-address-bits len1)
                         (natp len1)
;                (unsigned-byte-p ,num-address-bits len2)
                         (integerp ad1))
                    (subregionp len1 ad1 len2 ad2))
           :hints (("Goal" :in-theory (enable subregionp-opener bad-guy subregionp-of-+-arg2)))))

       (local
         (defthm subregionp-when-not-bad-guy
           (implies (and (not (bad-guy len1 ad1 len2 ad2))
        ;        (unsigned-byte-p ,num-address-bits len1)
        ;       (unsigned-byte-p ,num-address-bits len2)
                         (integerp ad1))
                    (subregionp len1 ad1 len2 ad2))
           :hints (("Goal" :in-theory (enable subregionp-opener bad-guy subregionp-of-+-arg2)))))

;drop some hyps?
       (defthmd subregionp-correct-back
         (implies (and (natp len1) ;(unsigned-byte-p ,num-address-bits len1)
                                   ; (unsigned-byte-p ,num-address-bits len2)
                       (unsigned-byte-p ,num-address-bits ad1)
                       (unsigned-byte-p ,num-address-bits ad2))
                  (implies (subregionp-spec len1 ad1 len2 ad2)
                           (subregionp len1 ad1 len2 ad2)))
         :hints (("Goal"
                  :cases ((bad-guy len1 ad1 len2 ad2))
                  :in-theory (enable subregionp-opener))))

       ;; Our subregionp function matches the spec
       (defthm subregionp-correct
         (equal (subregionp-spec len1 ad1 len2 ad2)
                (subregionp len1 ad1 len2 ad2))
         :hints (("Goal" :use (:instance subregionp-correct-back (ad1 (bvchop ,num-address-bits ad1)) (ad2 (bvchop ,num-address-bits ad2))))))

;todo: show that a larger region can't be a subregion of a smaller region

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ;; It R1 and R2 are disjoint, and R3 is within R1, and R4 is within R2, than R3 and R4 are disjoint.
       (defthm disjoint-regionsp-when-disjoint-regionsp-and-subregionp-and-subregionp
         (implies (and (disjoint-regionsp len1 ad1 len2 ad2)
                       (subregionp len3 ad3 len1 ad1) ; expand to bv ops?
                       (subregionp len4 ad4 len2 ad2) ; expand to bv ops?
                       )
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
                       )
                  (disjoint-regionsp len3 ad3 len4 ad4))
         :hints (("Goal" :in-theory (enable disjoint-regionsp-symmetric)))))))
