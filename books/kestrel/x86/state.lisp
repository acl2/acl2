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

(include-book "projects/x86isa/machine/state" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

;see xr-xw-inter-field but that has a case-split
(defthm xr-of-xw-diff
  (implies (not (equal fld1 fld2))
           (equal (xr fld2 i2 (xw fld1 i1 v x86))
                  (xr fld2 i2 x86))))

(defthm unsigned-byte-p-of-xr-of-mem
  (implies (<= 8 size)
           (equal (unsigned-byte-p size (xr :mem i x86))
                  (natp size)))
  :hints (("Goal" :use (:instance X86ISA::ELEM-P-OF-XR-MEM (x86$a x86))
           :in-theory (disable X86ISA::ELEM-P-OF-XR-MEM))))

(defthm integerp-of-xr-mem
  (integerp (xr :mem acl2::i x86))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance x86isa::unsigned-byte-p-of-xr-of-mem (size 8))
           :in-theory (disable x86isa::unsigned-byte-p-of-xr-of-mem))))

(defthm unsigned-byte-p-of-memi
  (implies (<= 8 size)
           (equal (unsigned-byte-p size (memi i x86))
                  (natp size)))
  :hints (("Goal" :in-theory (enable memi))))

(defthm integerp-of-memi
  (integerp (memi i x86))
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

;; For Axe, since ACL2 will use the :type-prescription rule
(defthmd x86isa::integerp-of-xr-rgf
  (integerp (xr :rgf index x86)))

(defthm x86isa::integerp-of-xr-rgf-type
  (integerp (xr :rgf index x86))
  :rule-classes :type-prescription
  :hints (("Goal" :use (:instance x86isa::elem-p-of-xr-rgf (x86isa::x86$a x86))
           :in-theory (e/d (xr) (x86isa::elem-p-of-xr-rgf)))))


(defthm app-view-of-xw
  (implies (not (equal fld :app-view))
           (equal (app-view (xw fld index value x86))
                  (app-view x86))))

(defthm memi-of-xw
  (implies (not (equal :mem fld))
           (equal (memi i (xw fld index val x86))
                  (memi i x86)))
  :hints (("Goal" :in-theory (enable memi))))

;; each of the 2 branches in the RHS has a clear RIP
(defthm xw-rip-of-if-arg3
  (equal (xw :rip nil (if test rip1 rip2) x86)
         (if test
             (xw :rip nil rip1 x86)
           (xw :rip nil rip2 x86))))

;gen?
(defthm fix-of-xr-rgf-4
  (equal (fix (xr ':rgf '4 x86))
         (xr ':rgf '4 x86)))

(defthm x86p-of-!memi
  (implies (and (x86p x86)
                ;;(INTEGERP ADDR)
                ;;(UNSIGNED-BYTE-P 8 VAL)
                )
           (x86p (!memi addr val x86)))
  :hints (("Goal" :in-theory (enable !memi))))

;gen
(defthm xr-app-view-of-!memi
  (equal (xr :app-view nil (!memi addr val x86))
         (xr :app-view nil x86))
  :hints (("Goal" :in-theory (enable !memi))))

(defthm app-view-of-!memi
  (equal (app-view (!memi addr val x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable !memi))))

(defthm memi-of-!memi-diff
  (implies (and (unsigned-byte-p 48 addr)
                (unsigned-byte-p 48 addr2)
                (not (equal addr addr2)))
           (equal (memi addr (!memi addr2 val x86))
                  (memi addr x86)))
  :hints (("Goal" :in-theory (enable memi))))

(defthm memi-of-!memi-both
  (implies (and (unsigned-byte-p 48 addr)
                (unsigned-byte-p 48 addr2))
           (equal (memi addr (!memi addr2 val x86))
                  (if (equal addr addr2)
                      (acl2::loghead 8 val)
                    (memi addr x86))))
  :hints (("Goal" :in-theory (enable memi))))

;rename
(defthm memi-of-!memi
  (implies t; (unsigned-byte-p 48 addr)
           (equal (memi addr (!memi addr val x86))
                  (acl2::loghead 8 val)))
  :hints (("Goal" :in-theory (enable memi))))

(defthm !memi-of-!memi-same
  (equal (!memi addr val (!memi addr val2 x86))
         (!memi addr val x86)))

;crosses abstraction layers?
(defthm memi-of-xw-same
  (implies t; (unsigned-byte-p 48 addr)
           (equal (memi addr (xw :mem addr val x86))
                  (acl2::loghead 8 val)))
  :hints (("Goal" :in-theory (enable memi))))

;crosses abstraction layers?
(defthm memi-of-xw-irrel
  (implies (not (equal fld :mem))
           (equal (memi addr (xw fld index val x86))
                  (memi addr x86)))
  :hints (("Goal" :in-theory (e/d (memi)
                                  (;x86isa::memi-is-n08p ;does forcing
                                   )))))

;why?
;; use def-constant-opener?
(acl2::defopeners xr :hyps ((syntaxp (quotep rstobj2::fld))
                            (syntaxp (quotep rstobj2::index))
                            (syntaxp (quotep X86ISA::X86$A))))

;why?
;(acl2::defopeners x86p :hyps ((syntaxp (quotep x86))))

;; (include-book "projects/x86isa/tools/execution/init-state" :dir :system)
;; ;; Intialize the x86 state and set up 64-bit execution.  Returns (mv error-flag x86)
;; (defun init-x86-state-64 (status start-addr halt-addr gprs ctrs msrs flags mem x86)
;;   (declare (xargs :stobjs x86
;;                   :guard (and (canonical-address-p start-addr)
;;                               (canonical-address-p halt-addr)
;;                               (rgfi-alistp gprs)
;;                               (ctri-alistp ctrs)
;;                               (msri-alistp msrs)
;;                               (n64p flags)
;;                               (n64p-byte-alistp mem))))
;;   (b* (((mv flg x86)
;;         (init-x86-state STATUS START-ADDR HALT-ADDR GPRS CTRS MSRS FLAGS MEM X86))
;;        ((when flg) (mv t x86))
;;        ;; The following two updates to X86 make 64-BIT-MODEP true.
;;        ;; The resulting state does not necessarily satisfy
;;        ;; expected invariants of the processor state,
;;        ;; but it suffices for the proof to go through.
;;        ;; set IA32_EFER.LMA to 1:
;;        (ia32_efer (n12 (msri *ia32_efer-idx* x86)))
;;        (ia32_efer (n64 (!ia32_efer-slice :ia32_efer-lma 1 ia32_efer)))
;;        (x86 (!msri *ia32_efer-idx* ia32_efer x86))
;;        ;; set CS.L to 1 (TODO: Improve this?):
;;        (x86 (!seg-hiddeni *cs* (expt 2 105) x86))
;;        )
;;     (mv nil x86)))
