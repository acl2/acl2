; Disjointness of memory regions
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X") ; todo: pull out of x86

;; This book includes machinery for reasoning about memory addresses and memory
;; regions.  Memory regions can wrap around the end of the address space back
;; to the beginning, but the user of this library rarely if ever has to think
;; about that.  For example, the cancellation rules apply regardless of whether
;; the region wraps around.

;; These functions can be opened up to expose BV functions for SMT solvers like
;; STP.  In many cases (when the lengths of regions are known), the results of
;; opening up these functions are conjunctions of BV terms.  Having
;; conjunctions instead of disjunctions is important if we want to use the
;; opened up functions as assumptions.

(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))
(include-book "kestrel/utilities/pack" :dir :system)

;todo
(local (in-theory (disable string-append-lst
                           string-append
                           character-listp
                           string-listp
                           )))

;; todo: slow
;; todo: allow the package to be an option
(defun make-memory-region-machinery-fn (num-address-bits)
  (declare (xargs :guard (natp num-address-bits)))
  (let* ((in-regionp-name (acl2::pack-in-package "X" 'in-region num-address-bits 'p))
         (subregionp-name (acl2::pack-in-package "X" 'subregion num-address-bits 'p))
         (subregionp-spec-name (acl2::pack-in-package "X" subregionp-name '-spec))
         (disjoint-regionsp-name (acl2::pack-in-package "X" 'disjoint-regions num-address-bits 'p))
         (disjoint-regionsp-spec-name (acl2::pack-in-package "X" disjoint-regionsp-name '-spec)))
    `(progn
       (include-book "kestrel/bv/bvlt-def" :dir :system)
       (include-book "kestrel/bv/logext-def" :dir :system)
       (include-book "kestrel/bv/bvminus" :dir :system) ; todo: reduce

       (encapsulate ()

         ;(include-book "kestrel/bv/sbvlt-def" :dir :system)
         ;(local (include-book "kestrel/bv/sbvlt" :dir :system))
         ;(local (include-book "kestrel/bv/sbvlt-rules" :dir :system)) ; for sbvlt-rewrite
         (local (include-book "kestrel/arithmetic-light/minus" :dir :system))
         (local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system)) ; may be droppable with more bvminus rules
         (local (include-book "kestrel/bv/bvlt" :dir :system))
         (local (include-book "kestrel/bv/bvplus" :dir :system))
         (local (include-book "kestrel/bv/logext" :dir :system))
         (local (include-book "kestrel/bv/rules" :dir :system)) ; for bvplus-of-logext rules
         (local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

         ;; Defines what it means for AD to be in the region of size LEN starting at
         ;; START-AD.  Note that the region may wrap around the end of the address
         ;; space, so AD may be in the region even if it is less than START-AD.
         ;; We put the len argument before start-ad because len is often a small constant.
         ;; In the normal case (non-huge, non-zero length), this can be opened up to a nice BV claim.
         (defund ,in-regionp-name (ad len start-ad)
           (declare (xargs :guard (and (unsigned-byte-p ,num-address-bits ad)
                                       (natp len) ; note that len >= 2^,num-address-bits covers the whole region
                                       (unsigned-byte-p ,num-address-bits start-ad))))
           (and (natp len) ; len=0 falsifies the bvlt below
                (if (<= (expt 2 ,num-address-bits) len) ; we handle (expt 2 ,num-address-bits) here, since the len gets chopped to ,num-address-bits bits below
                    t ; the region covers the whole address space
                  (bvlt ,num-address-bits (bvminus ,num-address-bits ad start-ad) len))))

         ;; Nothing is in a region of size 0
         (defthm ,(acl2::pack-in-package "X" 'not- in-regionp-name '-of-0-arg2)
           (not (,in-regionp-name ad 0 start-ad))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvuminus bvplus ifix ACL2::BVCHOP-OF-SUM-CASES))))

         ;; The address at the start of the region is in the region IFF the size is non-zero
         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-same)
           (equal (,in-regionp-name ad len ad)
                  (posp len))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         ;; The address at the end of the region is in the region IFF the size is non-zero
         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-same-end)
           (equal (,in-regionp-name (bvplus ,num-address-bits ad (bvplus ,num-address-bits -1 len)) len ad)
                  (posp len))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-same-end-alt)
           (equal (,in-regionp-name (bvplus ,num-address-bits ,(+ -1 (expt 2 num-address-bits)) (bvplus ,num-address-bits ad len)) len ad)
                  (posp len))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         ;; note that the region size can't be 2^,num-address-bits
         (defthm ,(acl2::pack-in-package "X" 'not- in-regionp-name '-one-past-end)
           (equal (,in-regionp-name (bvplus ,num-address-bits ad len) len ad)
                  (and (<= (expt 2 ,num-address-bits) len)
                       (natp len)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         ;; if the region size is 2^,num-address-bits-1, being in the region means not being the single address just before the region
         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-of-2^num-address-bits-1)
           (equal (,in-regionp-name ad (+ -1 (expt 2 ,num-address-bits)) start-ad)
                  (not (equal (bvchop ,num-address-bits ad) (bvminus ,num-address-bits start-ad 1))))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-monotone)
           (implies (and (,in-regionp-name x len1 ad)
                         (<= len1 len2)
                         (unsigned-byte-p ,num-address-bits len1)
                         (unsigned-byte-p ,num-address-bits len2))
                    (,in-regionp-name x len2 ad))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         (defthm ,(acl2::pack-in-package "X" 'not- in-regionp-name '-too-far)
           (implies (and (,in-regionp-name x len ad)
                         (bvle ,num-address-bits len (bvminus ,num-address-bits y x)) ; y is at least LEN above x
                         (bvle ,num-address-bits (bvminus ,num-address-bits x ad) (bvminus ,num-address-bits y ad)) ; x is closer to the start of the region than y
                         (unsigned-byte-p ,num-address-bits len))
                    (not (,in-regionp-name y len ad)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-of-bvchop-arg1)
           (implies (and (<= ,num-address-bits n)
                         (integerp n))
                    (equal (,in-regionp-name (bvchop n ad) len start-ad)
                           (,in-regionp-name ad len start-ad)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-of-bvplus-tighten-arg1)
           (implies (and (< ,num-address-bits n)
                         (integerp n))
                    (equal (,in-regionp-name (bvplus n ad1 ad2) len start-ad)
                           (,in-regionp-name (bvplus ,num-address-bits ad1 ad2) len start-ad)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-of-logext-arg1)
           (implies (and (<= ,num-address-bits n)
                         (integerp n))
                    (equal (,in-regionp-name (logext n ad) len start-ad)
                           (,in-regionp-name ad len start-ad)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-of-bvchop-arg3)
           (implies (and (<= ,num-address-bits n)
                         (integerp n))
                    (equal (,in-regionp-name ad len (bvchop n start-ad))
                           (,in-regionp-name ad len start-ad)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-of-bvplus-tighten-arg3)
           (implies (and (< ,num-address-bits n)
                         (integerp n))
                    (equal (,in-regionp-name ad len (bvplus n offset start-ad))
                           (,in-regionp-name ad len (bvplus ,num-address-bits offset start-ad))))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-of-logext-arg3)
           (implies (and (<= ,num-address-bits n)
                         (integerp n))
                    (equal (,in-regionp-name ad len (logext n start-ad))
                           (,in-regionp-name ad len start-ad)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthmd ,(acl2::pack-in-package "X" in-regionp-name '-of-+-arg1)
           (implies (and (integerp x)
                         (integerp y))
                    (equal (,in-regionp-name (+ x y) len ad)
                           (,in-regionp-name (bvplus ,num-address-bits x y) len ad)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvplus ifix))))

         (theory-invariant (incompatible (:rewrite ,(acl2::pack-in-package "X" in-regionp-name '-of-+-arg1)) (:definition bvplus)))

         (defthmd ,(acl2::pack-in-package "X" in-regionp-name '-of-+-arg3)
           (implies (and (integerp x)
                         (integerp y))
                    (equal (,in-regionp-name ad len (+ x y))
                           (,in-regionp-name ad len (bvplus ,num-address-bits x y))))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvplus ifix))))

         (theory-invariant (incompatible (:rewrite ,(acl2::pack-in-package "X" in-regionp-name '-of-+-arg3)) (:definition bvplus)))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-1-1+)
           (equal (,in-regionp-name x len (bvplus ,num-address-bits x z))
                  (,in-regionp-name 0 len z))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-1+-1)
           (equal (,in-regionp-name (bvplus ,num-address-bits x z) len x)
                  (,in-regionp-name z len 0))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-1+-1+)
           (equal (,in-regionp-name (bvplus ,num-address-bits x y) len (bvplus ,num-address-bits x z))
                  (,in-regionp-name y len z))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-1-2)
           (equal (,in-regionp-name x len2 (bvplus ,num-address-bits y x))
                  (,in-regionp-name 0 len2 y))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-2-1)
           (equal (,in-regionp-name (bvplus ,num-address-bits y x) len2 x)
                  (,in-regionp-name y len2 0))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-2-1+)
           (equal (,in-regionp-name (bvplus ,num-address-bits y x) len2 (bvplus ,num-address-bits x z))
                  (,in-regionp-name y len2 z))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-1+-2)
           (equal (,in-regionp-name (bvplus ,num-address-bits x y) len (bvplus ,num-address-bits z x))
                  (,in-regionp-name y len z))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-2-2)
           (equal (,in-regionp-name (bvplus ,num-address-bits y x) len2 (bvplus ,num-address-bits z x))
                  (,in-regionp-name y len2 z))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-3-1)
           (equal (,in-regionp-name (bvplus ,num-address-bits y (bvplus ,num-address-bits z x)) len x)
                  (,in-regionp-name (bvplus ,num-address-bits y z) len 0))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         ;; todo: hints
         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-1-3)
           (equal (,in-regionp-name x len (bvplus ,num-address-bits y (bvplus ,num-address-bits z x)))
                  (,in-regionp-name 0 len (bvplus ,num-address-bits y z)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvuminus bvminus bvlt ifix bvplus))))

         ;; removes the negative part of the range
         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-when-non-negative-and-negative-range)
           (implies (and (syntaxp (quotep k))
                         (<= (expt 2 ,(+ -1 num-address-bits)) (bvchop ,num-address-bits k)) ; (sbvlt ,num-address-bits k 0) ; negative
                         (unsigned-byte-p ,(+ -1 num-address-bits) x) ; non-negative
                         (unsigned-byte-p ,num-address-bits k) ; drop?
                         (unsigned-byte-p ,(+ -1 num-address-bits) len2) ; gen?
                         (<= (- (expt 2 ,num-address-bits) k) len2) ;move to rhs?
                         )
                    (equal (,in-regionp-name x len2 k)
                           (,in-regionp-name x (- len2 (- (expt 2 ,num-address-bits) k)) 0)))
           :hints (("Goal" :cases ((< (+ (expt 2 ,num-address-bits) (- k) x) len2))
                    :in-theory (enable ,in-regionp-name bvplus bvuminus bvlt acl2::bvchop-of-sum-cases unsigned-byte-p
                                       ;;acl2::sbvlt-rewrite
                                       ))))

         ;; todo: more cancellation rules

         ;; todo: more?
         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-constants-1+-1+)
           (implies (and (syntaxp (and (quotep k1)
                                       (quotep k2)))
                         (not (equal 0 k1)) ; prevent loops
                         )
                    (equal (,in-regionp-name (bvplus ,num-address-bits k1 x) len2 (bvplus ,num-address-bits k2 y))
                           (,in-regionp-name x len2 (bvplus ,num-address-bits (bvminus ,num-address-bits k2 k1) y))))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         ;; which arg do we prefer to make 0?
         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-constants-1-1+)
           (implies (and (syntaxp (and (quotep k1)
                                       (quotep k2)))
                         (not (equal 0 k1)) ; prevent loops
                         )
                    (equal (,in-regionp-name k1 len2 (bvplus ,num-address-bits k2 y))
                           (,in-regionp-name 0 len2 (bvplus ,num-address-bits (bvminus ,num-address-bits k2 k1) y))))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         ;; how do we prefer to handle this?
         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-cancel-constants-1+-1)
           (implies (and (syntaxp (and (quotep k1)
                                       (quotep k2)))
                         (not (equal 0 k1)) ; prevent loops
                         )
                    (equal (,in-regionp-name (bvplus ,num-address-bits k1 x) len2 k2)
                           (,in-regionp-name x len2 (bvminus ,num-address-bits k2 k1))))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         ;; disabled for the proofs below
         (defthmd ,(acl2::pack-in-package "X" in-regionp-name '-of-0-arg3)
           (equal (,in-regionp-name ad len 0)
                  (and (natp len)
                       (or (<= (expt 2 ,num-address-bits) len)
                           (bvlt ,num-address-bits ad len))))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-subst-constant-arg1)
           (implies (and (equal k (bvchop ,num-address-bits ad1))
                         (syntaxp (and (quotep k)
                                       (not (quotep ad1)))))
                    (equal (,in-regionp-name ad1 n2 ad2)
                           (,in-regionp-name k n2 ad2)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name))))

         (defthmd ,(acl2::pack-in-package "X" in-regionp-name '-opener)
           (implies (and (not (zp len))
;                (unsigned-byte-p ,num-address-bits len)
;       (unsigned-byte-p ,num-address-bits ad)
                         (unsigned-byte-p ,num-address-bits start-ad)
                         )
                    (equal (,in-regionp-name ad len start-ad)
                           (or (equal (bvchop ,num-address-bits ad) start-ad)
                               (,in-regionp-name ad (+ -1 len) (+ 1 start-ad)))))
           :hints (("Goal" :in-theory (enable ,in-regionp-name bvlt bvplus bvminus bvuminus acl2::bvchop-of-sum-cases))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

         ;; Defines what it means for 2 memory regions to be disjoint (no address in both regions).
         ;; Region1 has size len1 and starts at ad1.
         ;; Region2 has size len2 and starts at ad2.
         ;; Regions may wrap around the end of the address space back to the start.
         ;; We put the len arguments first because they will often be small constants.
         ;; In the normal case, this can be opened up to a conjunction of nice, BV claims.
         ;; See also the function SEPARATE, but this machinery is intended to be more amenable to SMT solving.
         (defund ,disjoint-regionsp-name (len1 ad1 len2 ad2)
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

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-when-not-posp)
           (implies (not (posp len1))
                    (,disjoint-regionsp-name len1 ad1 len2 ad2))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         ;; (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-when-zp)
         ;;   (implies (and (zp len1)
         ;;                 ;(natp len1) ; drop, have the function nfix
         ;;                 )
         ;;            (,disjoint-regionsp-name len1 ad1 len2 ad2))
         ;;   :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name zp))))

         (defthmd ,(acl2::pack-in-package "X" disjoint-regionsp-name '-symmetric)
           (equal (,disjoint-regionsp-name len1 ad1 len2 ad2)
                  (,disjoint-regionsp-name len2 ad2 len1 ad1))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         ;; Addresses in disjoint regions cannot be equal.
         (defthm ,(acl2::pack-in-package "X" 'not-equal-of-bvchop-and-bvchop-when- disjoint-regionsp-name)
           (implies (and (,disjoint-regionsp-name len1 start1 len2 start2)
                         (,in-regionp-name ad1 len1 start1)
                         (,in-regionp-name ad2 len2 start2))
                    (not (equal (bvchop ,num-address-bits ad1) (bvchop ,num-address-bits ad2))))
           :hints (("Goal" :in-theory (enable ,in-regionp-name ,disjoint-regionsp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         ;; Addresses in disjoint regions cannot be equal.
         (defthm ,(acl2::pack-in-package "X" 'not-equal-when- disjoint-regionsp-name)
           (implies (and (,disjoint-regionsp-name len1 start1 len2 start2)
                         (,in-regionp-name ad1 len1 start1)
                         (,in-regionp-name ad2 len2 start2))
                    (not (equal ad1 ad2)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name ,disjoint-regionsp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         (defthm ,(acl2::pack-in-package "X" 'not-equal-when- disjoint-regionsp-name '-alt)
           (implies (and (,disjoint-regionsp-name len1 start1 len2 start2)
                         (,in-regionp-name ad2 len1 start1)
                         (,in-regionp-name ad1 len2 start2))
                    (not (equal ad1 ad2)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name ,disjoint-regionsp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         ;; If any address is in both, they are not disjoint.
         (defthm ,(acl2::pack-in-package "X" 'not- disjoint-regionsp-name '-when-address-in-both)
           (implies (and (,in-regionp-name ad len1 start1)
                         (,in-regionp-name ad len2 start2))
                    (not (,disjoint-regionsp-name len1 start1 len2 start2)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name ,disjoint-regionsp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         (defthm ,(acl2::pack-in-package "X" 'not- in-regionp-name '-when- disjoint-regionsp-name '-one)
           (implies (and (,disjoint-regionsp-name len1 start1 len2 start2)
                         (,in-regionp-name ad len1 start1))
                    (not (,in-regionp-name ad len2 start2)))
           :hints (("Goal" :in-theory (enable))))

         (defthm ,(acl2::pack-in-package "X" 'not- in-regionp-name '-when- disjoint-regionsp-name '-two)
           (implies (and (,disjoint-regionsp-name len1 start1 len2 start2)
                         (,in-regionp-name ad len2 start2))
                    (not (,in-regionp-name ad len1 start1)))
           :hints (("Goal" :in-theory (enable))))

         ;; If they are disjoint, no address is in both.
         (defthm ,(acl2::pack-in-package "X" 'not-in-both-when- disjoint-regionsp-name)
           (implies (,disjoint-regionsp-name len1 start1 len2 start2)
                    (not (and (,in-regionp-name ad len1 start1)
                              (,in-regionp-name ad len2 start2))))
           :hints (("Goal" :in-theory (enable ,in-regionp-name ,disjoint-regionsp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         ;; If not disjoint, some address is in both (in fact, one of the start addresses will be in the other region):
         (defthm ,(acl2::pack-in-package "X" 'in-one-when-not- disjoint-regionsp-name)
           (implies (not (,disjoint-regionsp-name len1 start1 len2 start2))
                    (or (,in-regionp-name start1 len2 start2)
                        (,in-regionp-name start2 len1 start1)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name ,disjoint-regionsp-name bvuminus bvplus ifix acl2::bvchop-of-sum-cases zp bvlt))))

         (defthmd ,(acl2::pack-in-package "X" disjoint-regionsp-name '-of-+-arg2)
           (implies (and (integerp ad1)
                         (integerp x))
                    (equal (,disjoint-regionsp-name len1 (+ x ad1) len2 ad2)
                           (,disjoint-regionsp-name len1 (bvplus ,num-address-bits x ad1) len2 ad2)))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name
                                              acl2::bvminus-of-+-arg2
                                              acl2::bvminus-of-+-arg3))))

         (theory-invariant (incompatible (:rewrite ,(acl2::pack-in-package "X" disjoint-regionsp-name '-of-+-arg2)) (:definition bvplus)))

         (defthmd ,(acl2::pack-in-package "X" disjoint-regionsp-name '-of-+-arg4)
           (implies (and (integerp ad2)
                         (integerp x))
                    (equal (,disjoint-regionsp-name len1 ad1 len2 (+ x ad2))
                           (,disjoint-regionsp-name len1 ad1 len2 (bvplus ,num-address-bits x ad2))))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name
                                              acl2::bvminus-of-+-arg2
                                              acl2::bvminus-of-+-arg3))))

         (theory-invariant (incompatible (:rewrite ,(acl2::pack-in-package "X" disjoint-regionsp-name '-of-+-arg4)) (:definition bvplus)))

         ;; todo: more, or make a general cancellation rule (add the negation of the term to be cancelled):

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-cancel-1-1+)
           (equal (,disjoint-regionsp-name len1 x len2 (bvplus ,num-address-bits x y))
                  (,disjoint-regionsp-name len1 0 len2 y))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-cancel-1+-1)
           (equal (,disjoint-regionsp-name len1 (bvplus ,num-address-bits x z) len2 x)
                  (,disjoint-regionsp-name len1 z len2 0))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-cancel-1+-1+)
           (equal (,disjoint-regionsp-name len1 (bvplus ,num-address-bits x z) len2 (bvplus ,num-address-bits x y))
                  (,disjoint-regionsp-name len1 z len2 y))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-cancel-1-2)
           (equal (,disjoint-regionsp-name len1 x len2 (bvplus ,num-address-bits y x))
                  (,disjoint-regionsp-name len1 0 len2 y))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-cancel-2-1)
           (equal (,disjoint-regionsp-name len1 (bvplus ,num-address-bits y x) len2 x)
                  (,disjoint-regionsp-name len1 y len2 0))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-cancel-1+-2)
           (equal (,disjoint-regionsp-name len1 (bvplus ,num-address-bits x z) len2 (bvplus ,num-address-bits y x))
                  (,disjoint-regionsp-name len1 z len2 y))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-cancel-2-1+)
           (equal (,disjoint-regionsp-name len1 (bvplus ,num-address-bits z x) len2 (bvplus ,num-address-bits x y))
                  (,disjoint-regionsp-name len1 z len2 y))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-cancel-2-2)
           (equal (,disjoint-regionsp-name len1 (bvplus ,num-address-bits z x) len2 (bvplus ,num-address-bits y x))
                  (,disjoint-regionsp-name len1 z len2 y))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         ;; todo: more like this?
         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-of-bvplus-of-constant-and-constant)
           (implies (syntaxp (and (quotep k1)
                                  (quotep k2)))
                    (equal (,disjoint-regionsp-name len1 (bvplus ,num-address-bits k1 x) len2 k2)
                           (,disjoint-regionsp-name len1 x len2 (bvminus ,num-address-bits k2 k1))))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-of-1-and-1)
           (equal (,disjoint-regionsp-name 1 x 1 y)
                  (not (equal (bvchop ,num-address-bits x)
                              (bvchop ,num-address-bits y))))
           :hints (("Goal" :in-theory (e/d (,disjoint-regionsp-name)
                                           (acl2::bvminus-becomes-bvplus-of-bvuminus)))))

         ;; todo: show that this reduces to a more familiar notion in the non-wrap-around case
         ;; todo: use defun-sk to show correctness

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-of-bvchop-arg2)
           (implies (and (<= ,num-address-bits size)
                         (integerp size))
                    (equal (,disjoint-regionsp-name len1 (bvchop size ad1) len2 ad2)
                           (,disjoint-regionsp-name len1 ad1 len2 ad2)))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-of-bvchop-arg4)
           (implies (and (<= ,num-address-bits size)
                         (integerp size))
                    (equal (,disjoint-regionsp-name len1 ad1 len2 (bvchop size ad2))
                           (,disjoint-regionsp-name len1 ad1 len2 ad2)))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name))))

         ;; Higher level spec of disjoint-regionsp: Two regions are disjoint if there is
         ;; no address that is in both of them.
         (defun-sk ,disjoint-regionsp-spec-name (len1 ad1 len2 ad2)
           (forall (ad)
                   (not (and (,in-regionp-name ad len1 ad1)
                             (,in-regionp-name ad len2 ad2)))))

         (in-theory (disable ,disjoint-regionsp-spec-name))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-necc-better)
           (implies (and (,in-regionp-name ad len1 ad1)
                         (,in-regionp-name ad len2 ad2))
                    (not (,disjoint-regionsp-spec-name len1 ad1 len2 ad2)))
           :hints (("Goal" :use ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-necc)
                    :in-theory (theory 'minimal-theory))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-necc-better-alt)
           (implies (and (,in-regionp-name ad len2 ad2)
                         (,in-regionp-name ad len1 ad1))
                    (not (,disjoint-regionsp-spec-name len1 ad1 len2 ad2)))
           :hints (("Goal" :use ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-necc)
                    :in-theory (theory 'minimal-theory))))

         (encapsulate ()
           (local (defthmd ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-bvchop-arg2-fw)
                    (implies (,disjoint-regionsp-spec-name len1 (bvchop ,num-address-bits ad1) len2 ad2)
                             (,disjoint-regionsp-spec-name len1 ad1 len2 ad2))
                    :hints (("Goal" :expand (,disjoint-regionsp-spec-name len1 ad1 len2 ad2)))))

           (local (defthmd ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-bvchop-arg2-bk)
                    (implies (,disjoint-regionsp-spec-name len1 ad1 len2 ad2)
                             (,disjoint-regionsp-spec-name len1 (bvchop ,num-address-bits ad1) len2 ad2))
                    :hints (("Goal" :expand (,disjoint-regionsp-spec-name len1 (bvchop ,num-address-bits ad1) len2 ad2)))))

           (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-bvchop-arg2)
             (equal (,disjoint-regionsp-spec-name len1 (bvchop ,num-address-bits ad1) len2 ad2)
                    (,disjoint-regionsp-spec-name len1 ad1 len2 ad2))
             :hints (("Goal" :use (,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-bvchop-arg2-fw)
                                   ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-bvchop-arg2-bk))))))

         (encapsulate ()
           (local (defthmd ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-bvchop-arg4-fw)
                    (implies (,disjoint-regionsp-spec-name len1 ad1 len2 (bvchop ,num-address-bits ad2))
                             (,disjoint-regionsp-spec-name len1 ad1 len2 ad2))
                    :hints (("Goal" :expand (,disjoint-regionsp-spec-name len1 ad1 len2 ad2)))))

           (local (defthmd ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-bvchop-arg4-bk)
                    (implies (,disjoint-regionsp-spec-name len1 ad1 len2 ad2)
                             (,disjoint-regionsp-spec-name len1 ad1 len2 (bvchop ,num-address-bits ad2)))
                    :hints (("Goal" :expand (,disjoint-regionsp-spec-name len1 ad1 len2 (bvchop ,num-address-bits ad2))))))

           (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-bvchop-arg4)
             (equal (,disjoint-regionsp-spec-name len1 ad1 len2 (bvchop ,num-address-bits ad2))
                    (,disjoint-regionsp-spec-name len1 ad1 len2 ad2))
             :hints (("Goal" :use (,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-bvchop-arg4-fw)
                                   ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-bvchop-arg4-bk))))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-of-one-smaller)
           (implies (and (not (zp len1))
                         (,disjoint-regionsp-spec-name len1 ad1 len2 ad2)
                         ;; (unsigned-byte-p ,num-address-bits len1)
                         ;; (unsigned-byte-p ,num-address-bits len2)
                         (unsigned-byte-p ,num-address-bits ad1)
                         (unsigned-byte-p ,num-address-bits ad2))
                    (,disjoint-regionsp-spec-name (+ -1 len1) (bvplus ,num-address-bits 1 ad1) len2 ad2))
           :hints (("Goal" :expand ((,disjoint-regionsp-spec-name (+ -1 len1) (bvplus ,num-address-bits 1 ad1) len2 ad2))
                    :use (:instance ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-necc-better)
                                    (ad (,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-witness) (+ -1 len1) (bvplus ,num-address-bits 1 ad1) len2 ad2)))
                    :in-theory (e/d (,(acl2::pack-in-package "X" in-regionp-name '-opener)
                                     ,(acl2::pack-in-package "X" in-regionp-name '-of-+-arg3))
                                    (,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-necc-better)
                                     ,(acl2::pack-in-package "X" disjoint-regionsp-spec-name '-necc-better-alt))))))

         (local (defun indf (n ad) (if (zp n) (list n ad) (indf (+ -1 n) (bvplus ,num-address-bits 1 ad)))))

         (defthmd ,(acl2::pack-in-package "X" disjoint-regionsp-name '-opener)
           (implies (and (posp len1)
                         ;; (unsigned-byte-p ,num-address-bits len1)
                         ;; (unsigned-byte-p ,num-address-bits len2)
                         (unsigned-byte-p ,num-address-bits ad1)
                         ;; (unsigned-byte-p ,num-address-bits ad2)
                         )
                    (equal (,disjoint-regionsp-name len1 ad1 len2 ad2)
                           (and (not (,in-regionp-name ad1 len2 ad2))
                                (,disjoint-regionsp-name (+ -1 len1) (+ 1 ad1) len2 ad2))))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-name ,in-regionp-name bvlt bvplus bvminus bvuminus acl2::bvchop-of-sum-cases))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-correct-backward)
           (implies (and (,disjoint-regionsp-spec-name len1 ad1 len2 ad2)
                         (unsigned-byte-p ,num-address-bits ad1)
                         (unsigned-byte-p ,num-address-bits ad2))
                    (,disjoint-regionsp-name len1 ad1 len2 ad2))
           :hints (("Goal" :induct (indf len1 ad1)
                    :in-theory (enable ,(acl2::pack-in-package "X" disjoint-regionsp-name '-opener)
                                       ,(acl2::pack-in-package "X" disjoint-regionsp-name '-of-+-arg2)
                                       zp natp))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-correct-forward)
           (implies (,disjoint-regionsp-name len1 ad1 len2 ad2)
                    (,disjoint-regionsp-spec-name len1 ad1 len2 ad2))
           :hints (("Goal" :in-theory (enable ,disjoint-regionsp-spec-name))))

         ;; Shows that the complicated defintion of disjoint-regionsp agrees with the higher-level spec.
         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-correct)
           (equal (,disjoint-regionsp-spec-name len1 ad1 len2 ad2)
                  (,disjoint-regionsp-name len1 ad1 len2 ad2))
           :hints (("Goal" :use ((:instance ,(acl2::pack-in-package "X" disjoint-regionsp-name '-correct-forward) (ad1 (bvchop ,num-address-bits ad1)) (ad2 (bvchop ,num-address-bits ad2)))
                                 (:instance ,(acl2::pack-in-package "X" disjoint-regionsp-name '-correct-backward) (ad1 (bvchop ,num-address-bits ad1)) (ad2 (bvchop ,num-address-bits ad2))))
                    :in-theory (disable ,(acl2::pack-in-package "X" disjoint-regionsp-name '-correct-forward)
                                        ,(acl2::pack-in-package "X" disjoint-regionsp-name '-correct-backward)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

         ;; Checks whether all of the addresses in the first region (of size len1 starting at ad1) are in the second region (of size len2 starting at ad2).
         ;; We put the len args first because they will often be small constants.
         ;; This can be opened to a conjunction of nice BV facts (requires opening ,in-regionp-name too).
         (defund ,subregionp-name (len1 ad1 len2 ad2)
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
                   (and (,in-regionp-name ad1 len2 ad2)
                        (bvle ,num-address-bits len1 len2) ; ensures the difference below is not negative
                        (bvle ,num-address-bits (bvminus ,num-address-bits ad1 ad2) (bvminus ,num-address-bits len2 len1))))))))

         ;; A region is a subregion of itself
         (defthm ,(acl2::pack-in-package "X" subregionp-name '-reflexive)
           (implies (unsigned-byte-p ,num-address-bits len)
                    (,subregionp-name len ad len ad))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-same-ads-same-lens)
           (,subregionp-name len ad len ad)
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         ;; A region of size 0 is a subregion of any region
         (defthm ,(acl2::pack-in-package "X" subregionp-name '-of-0-arg1)
           (,subregionp-name 0 ad len2 ad2)
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-when-zp-arg1)
           (implies (zp len1)
                    (,subregionp-name len1 ad1 len2 ad2))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         ;; A region is a subregion or some other region of size 0 only if it iself has size 0.
         (defthm ,(acl2::pack-in-package "X" subregionp-name '-of-0-arg3)
           (equal (,subregionp-name len1 ad1 0 ad2)
                  (zp len1))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         ;; todo: prove transitive, anti-symm

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-when- in-regionp-name '-and- subregionp-name)
           (implies (and (,subregionp-name len1 ad1 len2 ad2)
                         (,in-regionp-name ad len1 ad1))
                    (,in-regionp-name ad len2 ad2))
           :hints (("Goal" :in-theory (enable ,in-regionp-name ,disjoint-regionsp-name ,SUBREGIONP-NAME
                                              bvuminus bvplus bvlt
                                              ifix
                                              ACL2::BVLT-OF-0-ARG2
                                              acl2::bvchop-of-sum-cases
                                              zp))))

         ;; If there's something in R1 that is not in R2, then R1 is not a subregion of R2
         ;; todo: prove from the above
         (defthm ,(acl2::pack-in-package "X" 'not- subregionp-name '-when- in-regionp-name '-and-not- in-regionp-name)
           (implies (and (,in-regionp-name ad len1 ad1)
                         (not (,in-regionp-name ad len2 ad2)))
                    (not (,subregionp-name len1 ad1 len2 ad2)))
           :hints (("Goal" :in-theory (enable ,in-regionp-name ,disjoint-regionsp-name ,SUBREGIONP-NAME
                                              bvuminus bvplus bvlt
                                              ifix
                                              ACL2::BVLT-OF-0-ARG2
                                              acl2::bvchop-of-sum-cases
                                              zp))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-cancel-1-1)
           (implies (syntaxp (not (quotep x)))
                    (equal (,subregionp-name len1 x len2 x)
                           (,subregionp-name len1 0 len2 0) ; usually can be evaluated
                           ))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-cancel-1+-1)
           (equal (,subregionp-name len1 (bvplus ,num-address-bits x y) len2 x)
                  (,subregionp-name len1 y len2 0))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-cancel-1-1+)
           (equal (,subregionp-name len1 x len2 (bvplus ,num-address-bits x y))
                  (,subregionp-name len1 0 len2 y))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-cancel-2-1)
           (equal (,subregionp-name len1 (bvplus ,num-address-bits y x) len2 x)
                  (,subregionp-name len1 y len2 0))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-cancel-2-1+)
           (equal (,subregionp-name len1 (bvplus ,num-address-bits y x) len2 (bvplus ,num-address-bits x z))
                  (,subregionp-name len1 y len2 z))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-cancel-1-2)
           (equal (,subregionp-name len1 x len2 (bvplus ,num-address-bits y x))
                  (,subregionp-name len1 0 len2 y))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-cancel-1+-2)
           (equal (,subregionp-name len1 (bvplus ,num-address-bits x z) len2 (bvplus ,num-address-bits y x))
                  (,subregionp-name len1 z len2 y))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-cancel-2-2)
           (equal (,subregionp-name len1 (bvplus ,num-address-bits y x) len2 (bvplus ,num-address-bits z x))
                  (,subregionp-name len1 y len2 z))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

         ;; todo: more cancellation rules, or a general solution?

         (defthmd ,(acl2::pack-in-package "X" subregionp-name '-of-+-arg2)
           (implies (and (integerp x)
                         (integerp y))
                    (equal (,subregionp-name len1 (+ x y) len2 ad2)
                           (,subregionp-name len1 (bvplus ,num-address-bits x y) len2 ad2)))
           :hints (("Goal" :in-theory (enable ,subregionp-name
                                              ,(acl2::pack-in-package "X" in-regionp-name '-of-+-arg1)
                                              acl2::bvminus-of-+-arg2))))
         (theory-invariant (incompatible (:rewrite ,(acl2::pack-in-package "X" subregionp-name '-of-+-arg2)) (:definition bvplus)))

         (defthmd ,(acl2::pack-in-package "X" subregionp-name '-of-+-arg4)
           (implies (and (integerp x)
                         (integerp y))
                    (equal (,subregionp-name len1 ad1 len2 (+ x y))
                           (,subregionp-name len1 ad1 len2 (bvplus ,num-address-bits x y))))
           :hints (("Goal" :in-theory (enable ,subregionp-name
                                              acl2::bvminus-of-+-arg3
                                              ,(acl2::pack-in-package "X" in-regionp-name '-of-+-arg3)))))
         (theory-invariant (incompatible (:rewrite ,(acl2::pack-in-package "X" subregionp-name '-of-+-arg4)) (:definition bvplus)))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-of-bvchop-arg2)
           (implies (and (<= ,num-address-bits size)
                         (integerp size))
                    (equal (,subregionp-name len1 (bvchop size ad1) len2 ad2)
                           (,subregionp-name len1 ad1 len2 ad2)))
           :hints (("Goal" :in-theory (enable ,subregionp-name ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-of-bvchop-arg4)
           (implies (and (<= ,num-address-bits size)
                         (integerp size))
                    (equal (,subregionp-name len1 ad1 len2 (bvchop size ad2))
                           (,subregionp-name len1 ad1 len2 ad2)))
           :hints (("Goal" :in-theory (enable ,subregionp-name ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-cancel-constants-1+-1)
           (implies (and (syntaxp (and (quotep k1)
                                       (quotep k2)))
                         (not (equal 0 k1)) ; prevent loops
                         )
                    (equal (,subregionp-name len1 (bvplus ,num-address-bits k1 x) len2 k2)
                           (,subregionp-name len1 x len2 (bvminus ,num-address-bits k2 k1))))
           :hints (("Goal" :in-theory (enable ,subregionp-name ,in-regionp-name))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-cancel-constants-1+-1+)
           (implies (and (syntaxp (and (quotep k1)
                                       (quotep k2)))
                         (not (equal 0 k1)) ; prevent loops
                         )
                    (equal (,subregionp-name len1 (bvplus ,num-address-bits k1 x) len2 (bvplus ,num-address-bits k2 y))
                           (,subregionp-name len1 x len2 (bvplus ,num-address-bits (bvminus ,num-address-bits k2 k1) y))))
           :hints (("Goal" :in-theory (enable ,subregionp-name ,in-regionp-name))))

         ;; (thm
         ;;   (equal (sbvlt ,num-address-bits x 0)
         ;;          (<= (expt 2 ,(+ -1 num-address-bits)) (bvchop ,num-address-bits x)))
         ;;   :hints (("Goal" :in-theory (e/d (sbvlt) (logext)))))

         ;; ;; removes the negative part of the range
         (defthm ,(acl2::pack-in-package "X" subregionp-name '-when-non-negative-and-negative-range)
           (implies (and (<= (expt 2 ,(+ -1 num-address-bits)) (bvchop ,num-address-bits k)) ; (sbvlt ,num-address-bits k 0)
                         (unsigned-byte-p ,num-address-bits k) ; drop?
                         (unsigned-byte-p ,(+ -1 num-address-bits) x) ; non-negative
                                                                      ;                (unsigned-byte-p ,(+ -1 num-address-bits) len1)
                         (unsigned-byte-p ,(+ -1 num-address-bits) len2) ; gen?
                         (<= (- (expt 2 ,num-address-bits) k) len2) ;move to rhs?
                         )
                    (equal (,subregionp-name len1 x len2 k)
                           (,subregionp-name len1 x (- len2 (- (expt 2 ,num-address-bits) k)) 0)))
           :hints (("Goal" :in-theory (enable ,subregionp-name ,in-regionp-name bvplus bvuminus bvlt acl2::bvchop-of-sum-cases unsigned-byte-p
                                              ;;acl2::sbvlt-rewrite
                                              ))))

         ;; decrementing both sizes doesn't change the answer, so we can decrement all the way down to 1
         (defthm ,(acl2::pack-in-package "X" subregionp-name '-reduce-sizes)
           (implies (and (< 1 len1) ; prevent loops
                         (<= len1 len2)
                         (natp len1)
                         (natp len2)
                         ;(< len1 1000)
                         (unsigned-byte-p ,num-address-bits len2)
                         )
                    (equal (,subregionp-name len1 x len2 y)
                           (,subregionp-name 1 x (- len2 (- len1 1)) y)))
           :hints (("Goal" :in-theory (enable ,subregionp-name ,in-regionp-name bvlt bvplus bvuminus acl2::bvchop-of-sum-cases))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-of-1-arg1)
           (equal (,subregionp-name 1 x len2 y)
                  (and (natp len2)
                       (or (<= (expt 2 ,num-address-bits) len2)
                           (,in-regionp-name x len2 y))))
           :hints (("Goal" :in-theory (enable ,subregionp-name ,in-regionp-name bvlt bvplus bvuminus acl2::bvchop-of-sum-cases))))

         (defthm ,(acl2::pack-in-package "X" subregionp-name '-subst-constant-arg4)
           (implies (and (equal k (bvchop ,num-address-bits ad2))
                         (syntaxp (and (quotep k)
                                       (not (quotep ad2)))))
                    (equal (,subregionp-name n1 ad1 n2 ad2)
                           (,subregionp-name n1 ad1 n2 k)))
           :hints (("Goal" :in-theory (enable ,subregionp-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

         ;; R1 is a subregion of R2 iff every address in R1 is in R2.
         (defun-sk ,subregionp-spec-name (len1 ad1 len2 ad2)
           (forall (ad)
                   (implies (,in-regionp-name ad len1 ad1)
                            (,in-regionp-name ad len2 ad2))))
         (local (in-theory (disable ,subregionp-spec-name)))

         (defthm ,(acl2::pack-in-package "X" in-regionp-name '-when- in-regionp-name '-and- subregionp-spec-name)
           (implies (and (,subregionp-spec-name len1 ad1 len2 ad2)
                         (,in-regionp-name ad len1 ad1))
                    (,in-regionp-name ad len2 ad2))
           :hints (("Goal" :use ,(acl2::pack-in-package "X" subregionp-spec-name '-necc))))

         (defthm ,(acl2::pack-in-package "X" 'not- subregionp-spec-name '-when- in-regionp-name '-and-not- in-regionp-name)
           (implies (and (,in-regionp-name ad len1 ad1) ; ad is a free var
                         (not (,in-regionp-name ad len2 ad2)))
                    (not (,subregionp-spec-name len1 ad1 len2 ad2)))
           :hints (("Goal" :use ,(acl2::pack-in-package "X" in-regionp-name '-when- in-regionp-name '-and- subregionp-spec-name)
                    :in-theory (disable ,(acl2::pack-in-package "X" in-regionp-name '-when- in-regionp-name '-and- subregionp-spec-name)))))

         (encapsulate ()
           (local
             (defthmd ,(acl2::pack-in-package "X" subregionp-spec-name '-of-bvchop-arg2-fw)
               (implies (,subregionp-spec-name len1 (bvchop ,num-address-bits ad1) len2 ad2)
                        (,subregionp-spec-name len1 ad1 len2 ad2))
               :hints (("Goal" :expand (,subregionp-spec-name len1 ad1 len2 ad2)))))

           (local
             (defthmd ,(acl2::pack-in-package "X" subregionp-spec-name '-of-bvchop-arg2-bk)
               (implies (,subregionp-spec-name len1 ad1 len2 ad2)
                        (,subregionp-spec-name len1 (bvchop ,num-address-bits ad1) len2 ad2))
               :hints (("Goal" :expand (,subregionp-spec-name len1 (bvchop ,num-address-bits ad1) len2 ad2)))))

           (defthm ,(acl2::pack-in-package "X" subregionp-spec-name '-of-bvchop-arg2)
             (equal (,subregionp-spec-name len1 (bvchop ,num-address-bits ad1) len2 ad2)
                    (,subregionp-spec-name len1 ad1 len2 ad2))
             :hints (("Goal" :use (,(acl2::pack-in-package "X" subregionp-spec-name '-of-bvchop-arg2-fw)
                                   ,(acl2::pack-in-package "X" subregionp-spec-name '-of-bvchop-arg2-bk))))))

         (encapsulate ()
           (local
             (defthmd ,(acl2::pack-in-package "X" subregionp-spec-name '-of-bvchop-arg4-fw)
               (implies (,subregionp-spec-name len1 ad1 len2 (bvchop ,num-address-bits ad2))
                        (,subregionp-spec-name len1 ad1 len2 ad2))
               :hints (("Goal" :expand (,subregionp-spec-name len1 ad1 len2 ad2)))))

           (local
             (defthmd ,(acl2::pack-in-package "X" subregionp-spec-name '-of-bvchop-arg4-bk)
               (implies (,subregionp-spec-name len1 ad1 len2 ad2)
                        (,subregionp-spec-name len1 ad1 len2 (bvchop ,num-address-bits ad2)))
               :hints (("Goal" :expand (,subregionp-spec-name len1 ad1 len2 (bvchop ,num-address-bits ad2))))))

           (defthm ,(acl2::pack-in-package "X" subregionp-spec-name '-of-bvchop-arg4)
             (equal (,subregionp-spec-name len1 ad1 len2 (bvchop ,num-address-bits ad2))
                    (,subregionp-spec-name len1 ad1 len2 ad2))
             :hints (("Goal" :use (,(acl2::pack-in-package "X" subregionp-spec-name '-of-bvchop-arg4-fw)
                                   ,(acl2::pack-in-package "X" subregionp-spec-name '-of-bvchop-arg4-bk))))))

         (local
           (defthm ,(acl2::pack-in-package "X" subregionp-name '-correct-forward)
             (implies (,subregionp-name len1 ad1 len2 ad2)
                      (,subregionp-spec-name len1 ad1 len2 ad2))
             :hints (("Goal"
                      :use (:instance ,(acl2::pack-in-package "X" in-regionp-name '-when- in-regionp-name '-and- subregionp-name)
                                      (ad (,(acl2::pack-in-package "X" subregionp-spec-name '-witness) len1 ad1 len2 ad2)))
                      :in-theory (e/d (,subregionp-spec-name)
                                      (,(acl2::pack-in-package "X" in-regionp-name '-when- in-regionp-name '-and- subregionp-name)))))))

         (local
           (defthm ,(acl2::pack-in-package "X" subregionp-spec-name '-same-ads-forward)
             (implies (and; (unsigned-byte-p ,num-address-bits len1)
                        (natp len1)
                        (unsigned-byte-p ,num-address-bits len2)
                        )
                      (implies (,subregionp-spec-name len1 ad len2 ad)
                               (<= len1 len2)))
             :hints (("Goal" :use (:instance ,(acl2::pack-in-package "X" 'not- subregionp-spec-name '-when- in-regionp-name '-and-not- in-regionp-name)
                                             (ad (bvplus ,num-address-bits ad len2))
                                             (ad1 ad)
                                             (ad2 ad))
                      :in-theory (e/d (,in-regionp-name bvlt)
                                      (,(acl2::pack-in-package "X" 'not- subregionp-spec-name '-when- in-regionp-name '-and-not- in-regionp-name)))))))

         (local
           (defthm ,(acl2::pack-in-package "X" subregionp-spec-name '-same-ads-backward)
             (implies (and (unsigned-byte-p ,num-address-bits len1)
                           (unsigned-byte-p ,num-address-bits len2)
                           )
                      (implies (<= len1 len2)
                               (,subregionp-spec-name len1 ad len2 ad)))
             :hints (("Goal" :in-theory (enable ,SUBREGIONP-SPEC-NAME)))))

         ;; do we really want this to be about the spec?
         (defthm ,(acl2::pack-in-package "X" subregionp-spec-name '-same-ads)
           (implies (and (unsigned-byte-p ,num-address-bits len1)
                         (unsigned-byte-p ,num-address-bits len2))
                    (equal (,subregionp-spec-name len1 ad len2 ad)
                           (<= len1 len2))))



;todo: make some stuff here local:
;todo: move some of this up:

         (defthmd ,(acl2::pack-in-package "X" subregionp-name '-opener)
           (implies (and ;(unsigned-byte-p ,num-address-bits len1)
                      ;(unsigned-byte-p ,num-address-bits len2)
                      (integerp ad1)
                      (not (zp len1)))
                    (equal (,subregionp-name len1 ad1 len2 ad2)
                           (and (,in-regionp-name ad1 len2 ad2)
                                (,subregionp-name (+ -1 len1) (+ 1 ad1) len2 ad2))))
           :hints (("Goal" ;; :in-theory (enable ,subregionp-name ,in-regionp-name bvlt bvplus bvminus bvuminus acl2::bvchop-of-sum-cases
                           ;;                    ifix natp)
                    :in-theory '((:compound-recognizer booleanp-compound-recognizer)
                                 (:compound-recognizer acl2::natp-compound-recognizer)
                                 (:compound-recognizer acl2::zp-compound-recognizer)
                                 (:definition bvle)
                                 (:definition bvlt)
                                 (:definition bvplus)
                                 (:definition bvuminus)
                                 (:definition fix)
                                 (:definition ifix)
                                 (:definition ,in-regionp-name)
                                 (:definition natp)
                                 (:definition not)
                                 (:definition ,subregionp-name)
                                 (:definition synp)
                                 (:executable-counterpart <)
                                 (:executable-counterpart binary-+)
                                 (:executable-counterpart bvchop)
                                 (:executable-counterpart equal)
                                 (:executable-counterpart expt)
                                 (:executable-counterpart integerp)
                                 (:executable-counterpart natp)
                                 (:executable-counterpart not)
                                 (:executable-counterpart tau-system)
                                 (:executable-counterpart unary--)
                                 (:executable-counterpart unsigned-byte-p)
                                 (:executable-counterpart zp)
                                 ;; (:fake-rune-for-linear nil)
                                 ;; (:fake-rune-for-linear-equalities nil)
                                 ;; (:fake-rune-for-type-set nil)
                                 (:linear acl2::bvchop-upper-bound-linear-strong)
                                 (:rewrite acl2::<-of-+-of---and-0-arg1)
                                 (:rewrite acl2::<-of-+-of---and-0-arg2)
                                 (:rewrite acl2::<-of-bvchop-when-<-of-bvchop-bigger)
                                 (:rewrite associativity-of-+)
                                 (:rewrite acl2::bvchop-bound-2)
                                 (:rewrite acl2::bvchop-bound-other)
                                 (:rewrite acl2::bvchop-chop-leading-constant)
                                 (:rewrite acl2::bvchop-identity)
                                 (:rewrite acl2::bvchop-of-minus)
                                 (:rewrite acl2::bvchop-of-sum-cases)
                                 (:rewrite acl2::bvchop-sum-drop-bvchop)
                                 (:rewrite acl2::bvminus-becomes-bvplus-of-bvuminus)
                                 (:rewrite acl2::commutativity-2-of-+)
                                 (:rewrite commutativity-of-+)
                                 (:rewrite acl2::distributivity-of-minus-over-+)
                                 (:rewrite acl2::equal-of-booleans-cheap)
                                 (:rewrite acl2::fold-consts-in-+)
                                 (:rewrite inverse-of-+)
                                 (:rewrite unicity-of-0)
                                 (:rewrite acl2::unsigned-byte-p-from-bound)
                                 (:rewrite acl2::unsigned-byte-p-from-bounds)
                                 (:rewrite acl2::unsigned-byte-p-of-+-of--1)
                                 (:rewrite acl2::unsigned-byte-p-of-if)
                                 (:rewrite acl2::usb-plus-from-bounds)
                                 (:rewrite acl2::zp-open)
                                 (:type-prescription acl2::natp-of-bvchop-type))
                    )))

         ;; The bad guy is an address in r1 but not in r2, is there if such an address
         (local
           (defund bad-guy (len1 ad1 len2 ad2)
             (if (zp len1)
                 nil
               (if (,in-regionp-name ad1 len2 ad2)
                   ;; keep looking:
                   (bad-guy (+ -1 len1) (bvplus ,num-address-bits 1 ad1) len2 ad2)
                 ;; we found a bad guy:
                 ad1))))

         (local
           (defthm ,(acl2::pack-in-package "X" 'unsigned-byte-p-of-bad-guy)
             (implies (and (bad-guy len1 ad1 len2 ad2)
                           (unsigned-byte-p ,num-address-bits ad1))
                      (unsigned-byte-p ,num-address-bits (bad-guy len1 ad1 len2 ad2)))
             :hints (("Goal" :in-theory (enable bad-guy)))))

         (local
           (defthm ,(acl2::pack-in-package "X" in-regionp-name '-of-bad-guy)
             (implies (and (bad-guy len1 ad1 len2 ad2)
                           ;(integerp ad1)
                           (unsigned-byte-p ,num-address-bits ad1)
                           (unsigned-byte-p ,num-address-bits ad2)
                           ;(unsigned-byte-p ,num-address-bits len1)
                           (natp len1)
                           )
                      (,in-regionp-name (bad-guy len1 ad1 len2 ad2) len1 ad1))
             :hints (("Goal" :in-theory (enable ,(acl2::pack-in-package "X" in-regionp-name '-opener)
                                                bad-guy
                                                ,(acl2::pack-in-package "X" in-regionp-name '-of-+-arg3))))))

         (local
           (defthm ,(acl2::pack-in-package "X" subregionp-name '-when- in-regionp-name '-of-bad-guy)
             (implies (and (,in-regionp-name (bad-guy len1 ad1 len2 ad2) len2 ad2)
                           ;; (unsigned-byte-p ,num-address-bits len1)
                           (natp len1)
                           ;; (unsigned-byte-p ,num-address-bits len2)
                           (integerp ad1))
                      (,subregionp-name len1 ad1 len2 ad2))
             :hints (("Goal" :in-theory (enable ,(acl2::pack-in-package "X" subregionp-name '-opener)
                                                bad-guy
                                                ,(acl2::pack-in-package "X" subregionp-name '-of-+-arg2))))))

         (local
           (defthm ,(acl2::pack-in-package "X" subregionp-name '-when-not-bad-guy)
             (implies (and (not (bad-guy len1 ad1 len2 ad2))
                           ;; (unsigned-byte-p ,num-address-bits len1)
                           ;; (unsigned-byte-p ,num-address-bits len2)
                           (integerp ad1))
                      (,subregionp-name len1 ad1 len2 ad2))
             :hints (("Goal" :in-theory (enable ,(acl2::pack-in-package "X" subregionp-name '-opener)
                                                bad-guy
                                                ,(acl2::pack-in-package "X" subregionp-name '-of-+-arg2))))))

         ;;drop some hyps?
         (defthmd ,(acl2::pack-in-package "X" subregionp-name '-correct-back)
           (implies (and (natp len1)
                         ;; (unsigned-byte-p ,num-address-bits len1)
                         ;; (unsigned-byte-p ,num-address-bits len2)
                         (unsigned-byte-p ,num-address-bits ad1)
                         (unsigned-byte-p ,num-address-bits ad2))
                    (implies (,subregionp-spec-name len1 ad1 len2 ad2)
                             (,subregionp-name len1 ad1 len2 ad2)))
           :hints (("Goal"
                    :cases ((bad-guy len1 ad1 len2 ad2))
                    :in-theory (enable ,(acl2::pack-in-package "X" subregionp-name '-opener)))))

         ;; Our subregionp function matches the spec
         (defthm ,(acl2::pack-in-package "X" subregionp-name '-correct)
           (equal (,subregionp-spec-name len1 ad1 len2 ad2)
                  (,subregionp-name len1 ad1 len2 ad2))
           :hints (("Goal" :use (:instance ,(acl2::pack-in-package "X" subregionp-name '-correct-back)
                                           (ad1 (bvchop ,num-address-bits ad1))
                                           (ad2 (bvchop ,num-address-bits ad2))))))

;todo: show that a larger region can't be a subregion of a smaller region

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

         ;; It R1 and R2 are disjoint, and R3 is within R1, and R4 is within R2, than R3 and R4 are disjoint.
         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-when- disjoint-regionsp-name '-and- subregionp-name '-and- subregionp-name)
           (implies (and (,disjoint-regionsp-name len1 ad1 len2 ad2)
                         (,subregionp-name len3 ad3 len1 ad1) ; expand to bv ops?
                         (,subregionp-name len4 ad4 len2 ad2) ; expand to bv ops?
                         )
                    (,disjoint-regionsp-name len3 ad3 len4 ad4))
           :hints (("Goal"
                    :in-theory (enable ,in-regionp-name ,disjoint-regionsp-name ,subregionp-name
                                       bvuminus bvplus bvlt
                                       ifix
                                       acl2::bvlt-of-0-arg2
                                       acl2::bvchop-of-sum-cases
                                       zp))))

         (defthm ,(acl2::pack-in-package "X" disjoint-regionsp-name '-when- disjoint-regionsp-name '-and- subregionp-name '-and- subregionp-name '-alt)
           (implies (and (,disjoint-regionsp-name len2 ad2 len1 ad1)
                         (,subregionp-name len3 ad3 len1 ad1) ; expand to bv ops?
                         (,subregionp-name len4 ad4 len2 ad2) ; expand to bv ops?
                         )
                    (,disjoint-regionsp-name len3 ad3 len4 ad4))
           :hints (("Goal" :in-theory (enable ,(acl2::pack-in-package "X" disjoint-regionsp-name '-symmetric)))))))))

(defmacro make-memory-region-machinery (num-address-bits)
  (make-memory-region-machinery-fn num-address-bits))
