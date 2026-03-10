; Rules about the ARM model
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "pseudocode")
(include-book "instructions")
(include-book "kestrel/utilities/def-constant-opener" :dir :system)

(defthm conditionpassed-of-set-reg
  (equal (conditionpassed cond (set-reg n val arm))
         (conditionpassed cond arm))
  :hints (("Goal" :in-theory (enable conditionpassed))))

(defthm conditionpassed-of-write
  (equal (conditionpassed cond (write n addr val arm))
         (conditionpassed cond arm))
  :hints (("Goal" :in-theory (enable conditionpassed))))

;; Here we recharacterize conditionpassed.  This scheme can result in fewer
;; branches during symbolic execution compared to just opening everything up
;; (consider the complex conditions like gt-condition).

(defund eq-condition (z) (declare (xargs :guard (bitp z))) (== z 1))
(defund ne-condition (z) (declare (xargs :guard (bitp z))) (not (== z 1))) ; or do (== z 0)

(defund cs-condition (c) (declare (xargs :guard (bitp c))) (== c 1))
(defund cc-condition (c) (declare (xargs :guard (bitp c))) (== c 0))

(defund mi-condition (n) (declare (xargs :guard (bitp n))) (== n 1))
(defund pl-condition (n) (declare (xargs :guard (bitp n))) (== n 0))

(defund vs-condition (v) (declare (xargs :guard (bitp v))) (== v 1))
(defund vc-condition (v) (declare (xargs :guard (bitp v))) (== v 0))

(defund hi-condition (c z) (declare (xargs :guard (and (bitp c) (bitp z)))) (and (== c 1) (== z 0)))
(defund ls-condition (c z) (declare (xargs :guard (and (bitp c) (bitp z)))) (not (and (== c 1) (== z 0))))

(defund ge-condition (n v) (declare (xargs :guard (and (bitp n) (bitp v)))) (== n v))
(defund lt-condition (n v) (declare (xargs :guard (and (bitp n) (bitp v)))) (not (== n v)))

(defund gt-condition (n v z) (declare (xargs :guard (and (bitp n) (bitp v) (bitp z)))) (and (== n v) (== z 0)))
(defund le-condition (n v z) (declare (xargs :guard (and (bitp n) (bitp v) (bitp z)))) (not (and (== n v) (== z 0))))

(defthm conditionpassed-of-0 (equal (conditionpassed 0 arm) (eq-condition (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed eq-condition))))
(defthm conditionpassed-of-1 (equal (conditionpassed 1 arm) (ne-condition (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed ne-condition))))

(defthm conditionpassed-of-2 (equal (conditionpassed 2 arm) (cs-condition (apsr.c arm))) :hints (("Goal" :in-theory (enable conditionpassed cs-condition))))
(defthm conditionpassed-of-3 (equal (conditionpassed 3 arm) (cc-condition (apsr.c arm))) :hints (("Goal" :in-theory (enable conditionpassed cc-condition))))

(defthm conditionpassed-of-4 (equal (conditionpassed 4 arm) (mi-condition (apsr.n arm))) :hints (("Goal" :in-theory (enable conditionpassed mi-condition))))
(defthm conditionpassed-of-5 (equal (conditionpassed 5 arm) (pl-condition (apsr.n arm))) :hints (("Goal" :in-theory (enable conditionpassed pl-condition))))

(defthm conditionpassed-of-6 (equal (conditionpassed 6 arm) (vs-condition (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed vs-condition))))
(defthm conditionpassed-of-7 (equal (conditionpassed 7 arm) (vc-condition (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed vc-condition))))

(defthm conditionpassed-of-8 (equal (conditionpassed 8 arm) (hi-condition (apsr.c arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed hi-condition))))
(defthm conditionpassed-of-9 (equal (conditionpassed 9 arm) (ls-condition (apsr.c arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed ls-condition))))

(defthm conditionpassed-of-10 (equal (conditionpassed 10 arm) (ge-condition (apsr.n arm) (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed ge-condition))))
(defthm conditionpassed-of-11 (equal (conditionpassed 11 arm) (lt-condition (apsr.n arm) (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed lt-condition))))

(defthm conditionpassed-of-12 (equal (conditionpassed 12 arm) (gt-condition (apsr.n arm) (apsr.v arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed gt-condition))))
(defthm conditionpassed-of-13 (equal (conditionpassed 13 arm) (le-condition (apsr.n arm) (apsr.v arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed le-condition))))

(defthm conditionpassed-of-14 (equal (conditionpassed 14 arm) t) :hints (("Goal" :in-theory (enable conditionpassed))))
(defthm conditionpassed-of-15 (equal (conditionpassed 15 arm) t) :hints (("Goal" :in-theory (enable conditionpassed))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd cmn-zero-elim
  (implies (and (unsigned-byte-p 32 x)
                ;; (unsigned-byte-p 32 y)
                )
           (equal (cmn-zero x y)
                  (bool-to-bit (equal x (bvuminus 32 y)))))
  :hints (("Goal" :in-theory (enable cmn-zero bvplus bvuminus acl2::bvchop-of-sum-cases bool-to-bit))))

(defthmd cmp-zero-elim
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cmp-zero x y)
                  (bool-to-bit (equal x y))))
  :hints (("Goal" :in-theory (enable cmp-zero acl2::bvnot-becomes-bvminus-of-bvuminus-and-1 bool-to-bit))))

(defthmd cmn-carry-elim
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cmn-carry x y)
                  (bool-to-bit (bvle 33 (expt 2 32) (bvplus 33 x y)))))
  :hints (("Goal" :in-theory (enable cmn-carry
                                     mv-nth-1-of-addwithcarry
                                     bvnot bvplus bvlt lognot acl2::getbit-of-+))))

(defthmd cmp-carry-elim
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cmp-carry x y)
                  (bool-to-bit (not (bvlt 32 x y)))))
  :hints (("Goal" :in-theory (enable cmp-carry mv-nth-1-of-addwithcarry
                                     bvnot bvplus bvlt lognot acl2::getbit-of-+))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm eq-condition-of-cmn-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (eq-condition (cmn-zero x y))
                  (equal x (bvuminus 32 y))))
  :hints (("Goal" :in-theory (enable eq-condition
                                     cmn-zero-elim))))

(defthm ne-condition-of-cmn-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ne-condition (cmn-zero x y))
                  (not (equal x (bvuminus 32 y)))))
  :hints (("Goal" :in-theory (enable ne-condition
                                     cmn-zero-elim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm eq-condition-of-cmp-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (eq-condition (cmp-zero x y))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable eq-condition
                                     cmp-zero-elim))))

(defthm ne-condition-of-cmp-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ne-condition (cmp-zero x y))
                  (not (equal x y))))
  :hints (("Goal" :in-theory (enable ne-condition
                                     cmp-zero-elim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::def-constant-opener arm::eq-condition)
(acl2::def-constant-opener arm::ne-condition)
(acl2::def-constant-opener arm::cs-condition)
(acl2::def-constant-opener arm::cc-condition)
(acl2::def-constant-opener arm::mi-condition)
(acl2::def-constant-opener arm::pl-condition)
(acl2::def-constant-opener arm::vs-condition)
(acl2::def-constant-opener arm::vc-condition)
(acl2::def-constant-opener arm::hi-condition)
(acl2::def-constant-opener arm::ls-condition)
(acl2::def-constant-opener arm::ge-condition)
(acl2::def-constant-opener arm::lt-condition)
(acl2::def-constant-opener arm::gt-condition)
(acl2::def-constant-opener arm::le-condition)
