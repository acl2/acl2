; Axe-specific rules
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "A") ; or use ARM package for consistency with other rules?

(include-book "run-until-return")
(include-book "run-until-return-with-tracing")
(include-book "../axe-syntax-functions")
(include-book "../known-booleans")

;; These are all disabled, because they are for Axe, not the ACL2 rewriter.

(defthmd run-until-return-aux-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (< call-stack-height 0))
           (equal (run-until-return-aux call-stack-height arm)
                  arm)))

(defthmd run-until-return-aux-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (not (< call-stack-height 0)))
           (equal (run-until-return-aux call-stack-height arm)
                  ;; todo: decoding is done here twice (in update-call-stack-height and step):
                  (run-until-return-aux (update-call-stack-height call-stack-height arm) (step arm)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd run-until-return-or-reach-pc-aux-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (or (< call-stack-height 0)
                    (memberp (reg *pc* arm) ; (pc arm)
                             stop-pcs)))
           (equal (run-until-return-or-reach-pc-aux call-stack-height stop-pcs arm)
                  arm)))

(defthmd run-until-return-or-reach-pc-aux-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (not (or (< call-stack-height 0)
                         (memberp (reg *pc* arm) ; (pc arm)
                                  stop-pcs))))
           (equal (run-until-return-or-reach-pc-aux call-stack-height stop-pcs arm)
                  ;; todo: decoding is done here twice (in update-call-stack-height and step):
                  (run-until-return-or-reach-pc-aux (update-call-stack-height call-stack-height arm) stop-pcs (step arm)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd run-until-return-with-tracing-aux-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (< call-stack-height 0))
           (equal (run-until-return-with-tracing-aux call-stack-height arm trace)
                  arm)))

(defthmd run-until-return-with-tracing-aux-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (not (< call-stack-height 0)))
           (equal (run-until-return-with-tracing-aux call-stack-height arm trace)
                  ;; todo: decoding is done here twice (in update-call-stack-height and step):
                  (run-until-return-with-tracing-aux (update-call-stack-height call-stack-height arm) (step arm) (append trace (list (reg *pc* arm)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd run-until-return-with-tracing-or-reach-pc-aux-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (or (< call-stack-height 0)
                    (memberp (reg *pc* arm) ; (pc arm)
                             stop-pcs)))
           (equal (run-until-return-with-tracing-or-reach-pc-aux call-stack-height stop-pcs arm trace)
                  arm)))

(defthmd run-until-return-with-tracing-or-reach-pc-aux-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (not (or (< call-stack-height 0)
                         (memberp (reg *pc* arm) ; (pc arm)
                                  stop-pcs))))
           (equal (run-until-return-with-tracing-or-reach-pc-aux call-stack-height stop-pcs arm trace)
                  ;; todo: decoding is done here twice (in update-call-stack-height and step):
                  (run-until-return-with-tracing-or-reach-pc-aux (update-call-stack-height call-stack-height arm) stop-pcs (step arm) (append trace (list (reg *pc* arm)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-known-boolean armp)
(add-known-boolean arm::conditionpassed) ; not sure if needed

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Good for subregions of corresponding, larger disjoint regions.
(defthm read-of-write-when-disjoint-regions32p-gen-smt
  (implies (and (disjoint-regions32p len1 start1 len2 start2) ; free vars

                ;; opened form of (subregion32p n1 ad1 len1 start1):
                (not (zp len1))
                (< len1 4294967296 ;(expt 2 32)
                   )
                (axe-smt (bvlt 32 (bvminus 32 ad1 start1) len1)) ; (in-region32p ad1 len1 start1)
                (bvle 32 n1 len1)
                (axe-smt (bvle 32 (bvminus 32 ad1 start1) (bvminus 32 len1 n1)))

                ;; opened form of (subregion32p n2 ad2 len2 start2):
                (not (zp len2))
                (< len2 4294967296 ;(expt 2 32)
                   )
                (axe-smt (bvlt 32 (bvminus 32 ad2 start2) len2)) ; (in-region32p ad2 len2 start2)
                (bvle 32 n2 len2)
                (axe-smt (bvle 32 (bvminus 32 ad2 start2) (bvminus 32 len2 n2)))

                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p 32 n1)
                (unsigned-byte-p 32 n2))
           (equal (read n1 ad1 (write n2 ad2 val x86))
                  (read n1 ad1 x86)))
  :hints (("Goal" :use arm::read-of-write-when-disjoint-regions32p-gen
                  :in-theory (e/d (subregion32p in-region32p) (arm::read-of-write-when-disjoint-regions32p-gen)))))

;; This -alt version has the disjoint-regions32p hyp reordered
(defthm read-of-write-when-disjoint-regions32p-gen-smt-alt
  (implies (and (disjoint-regions32p len2 start2 len1 start1) ; free vars

                ;; opened form of (subregion32p n1 ad1 len1 start1):
                (not (zp len1))
                (< len1 4294967296 ;(expt 2 32)
                   )
                (axe-smt (bvlt 32 (bvminus 32 ad1 start1) len1)) ; (in-region32p ad1 len1 start1)
                (bvle 32 n1 len1)
                (axe-smt (bvle 32 (bvminus 32 ad1 start1) (bvminus 32 len1 n1)))

                ;; opened form of (subregion32p n2 ad2 len2 start2):
                (not (zp len2))
                (< len2 4294967296 ;(expt 2 32)
                   )
                (axe-smt (bvlt 32 (bvminus 32 ad2 start2) len2)) ; (in-region32p ad2 len2 start2)
                (bvle 32 n2 len2)
                (axe-smt (bvle 32 (bvminus 32 ad2 start2) (bvminus 32 len2 n2)))

                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p 32 n1)
                (unsigned-byte-p 32 n2))
           (equal (read n1 ad1 (write n2 ad2 val x86))
                  (read n1 ad1 x86)))
  :hints (("Goal" :use arm::read-of-write-when-disjoint-regions32p-gen-alt
                  :in-theory (e/d (subregion32p in-region32p) (arm::read-of-write-when-disjoint-regions32p-gen-alt)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-when-equal-of-read-bytes-smt
  (implies (and (equal bytes (read-bytes n2 ad2 arm)) ; lots of free vars here ; note that refine-assumptions... puts the constant first
                ;(subregion32p n1 ad1 n2 ad2)

                ;; opened form of (subregion32p n1 ad1 n2 ad2):
                (not (zp n2))
                (< n2 4294967296 ;(expt 2 32)
                   )
                (axe-smt (bvlt 32 (bvminus 32 ad1 ad2) n2)) ; (in-region32p ad1 n2 ad2)
                (bvle 32 n1 n2)
                (axe-smt (bvle 32 (bvminus 32 ad1 ad2) (bvminus 32 n2 n1)))


                ;; (syntaxp (quotep bytes)) ; maybe uncomment
                ;; (unsigned-byte-p 32 n1)
                (natp n1)
                (< n1 (expt 2 32)) ; allow equal?
                (unsigned-byte-p 32 n2) ; allow 2^32?
                (unsigned-byte-p 32 n1) ; todo
                (integerp ad1) ; todo
                (integerp ad2) ; todo
                (unsigned-byte-p 32 ad1) ; drop?
                (unsigned-byte-p 32 ad2) ; drop?
                )
           (equal (read n1 ad1 arm)
                  (bv-list-read-chunk-little 8 n1 (bvminus 32 ad1 ad2) bytes)))
  :hints (("Goal" :use (:instance arm::read-when-equal-of-read-bytes
                                  (arm::bytes bytes)
                                  (arm::n2 n2)
                                  (arm::n1 n1)
                                  (arm::ad2 ad2)
                                  (arm::ad1 ad1)
                                  )
           :in-theory (e/d (arm::subregion32p in-region32p) (arm::read-when-equal-of-read-bytes)))))

;; commutes the equal
(defthm read-when-equal-of-read-bytes-smt-alt
  (implies (and (equal (read-bytes n2 ad2 arm) bytes) ; lots of free vars here ; note that refine-assumptions... puts the constant first
                ;(subregion32p n1 ad1 n2 ad2)

                ;; opened form of (subregion32p n1 ad1 n2 ad2):
                (not (zp n2))
                (< n2 4294967296 ;(expt 2 32)
                   )
                (axe-smt (bvlt 32 (bvminus 32 ad1 ad2) n2)) ; (in-region32p ad1 n2 ad2)
                (bvle 32 n1 n2)
                (axe-smt (bvle 32 (bvminus 32 ad1 ad2) (bvminus 32 n2 n1)))


                ;; (syntaxp (quotep bytes)) ; maybe uncomment
                ;; (unsigned-byte-p 32 n1)
                (natp n1)
                (< n1 (expt 2 32)) ; allow equal?
                (unsigned-byte-p 32 n2) ; allow 2^32?
                (unsigned-byte-p 32 n1) ; todo
                (integerp ad1) ; todo
                (integerp ad2) ; todo
                (unsigned-byte-p 32 ad1) ; drop?
                (unsigned-byte-p 32 ad2) ; drop?
                )
           (equal (read n1 ad1 arm)
                  (bv-list-read-chunk-little 8 n1 (bvminus 32 ad1 ad2) bytes)))
  :hints (("Goal" :use read-when-equal-of-read-bytes-smt
           :in-theory (disable read-when-equal-of-read-bytes-smt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-constant-opener cmp-sign)
(def-constant-opener cmp-zero)
(def-constant-opener cmp-carry)
(def-constant-opener cmp-overflow)
(def-constant-opener arm::addwithcarry)
(def-constant-opener arm::sint)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; useful when an address is forcibly 4-byte aligned but is already so aligned
;move
;gen
(defthm bvcat-of-slice-of-0-when-low-bits-0
  (implies (equal 0 (bvchop 2 x))
           (equal (bvcat 30 (slice 31 2 x) 2 0)
                  (bvchop 32 x))))
