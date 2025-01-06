; Supporting material for x86 code proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;; unlike most books, this one is in the X86ISA package

(include-book "projects/x86isa/machine/state" :dir :system) ; for canonical-address-p
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

;see xr-xw-inter-field but that has a case-split
(defthm xr-of-xw-diff
  (implies (not (equal fld1 fld2))
           (equal (xr fld2 i2 (xw fld1 i1 v x86))
                  (xr fld2 i2 x86))))

(defthm unsigned-byte-p-of-xr-of-mem
  (implies (and (<= 8 size)
                (x86p x86))
           (equal (unsigned-byte-p size (xr :mem i x86))
                  (natp size)))
  :hints (("Goal" :use (:instance X86ISA::ELEM-P-OF-XR-MEM (x86$a x86))
           :in-theory (disable X86ISA::ELEM-P-OF-XR-MEM))))

(defthm integerp-of-xr-mem
  (implies (x86p x86)
           (integerp (xr :mem acl2::i x86)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance x86isa::unsigned-byte-p-of-xr-of-mem (size 8))
           :in-theory (disable x86isa::unsigned-byte-p-of-xr-of-mem))))

(defthm unsigned-byte-p-of-memi
  (implies (and (<= 8 size)
                (x86p x86))
           (equal (unsigned-byte-p size (memi i x86))
                  (natp size)))
  :hints (("Goal" :in-theory (enable memi))))

(defthm integerp-of-memi
  (implies (x86p x86)
           (integerp (memi i x86)))
  :hints (("Goal" :in-theory (enable memi))))

(defthm x86isa::xr-of-if
  (equal (XR fld index (IF test state1 state2))
         (if test
             (XR fld index state1)
           (XR fld index state2))))

(defthm x86isa::xr-of-if-special-case-for-ms
  (equal (XR :ms nil (IF test state1 state2))
         (if test
             (XR :ms nil state1)
           (XR :ms nil state2))))

(defthm x86isa::xr-of-if-special-case-for-fault
  (equal (xr :fault nil (if test state1 state2))
         (if test
             (xr :fault nil state1)
           (xr :fault nil state2))))

(defthm integerp-of-xr-of-rsp
  (implies (x86p x86)
           (integerp (xr :rgf *rsp* x86))))

(defthm app-view-of-xw
  (implies (not (equal fld :app-view))
           (equal (app-view (xw fld index value x86))
                  (app-view x86))))
