; An evaluator for x86 code lifting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../evaluator-basic")

(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ;for canonical-address-p$inline
(include-book "projects/x86isa/machine/register-readers-and-writers" :dir :system) ; for reg-index$inline
(include-book "projects/x86isa/machine/prefix-modrm-sib-decoding" :dir :system) ; for X86ISA::X86-DECODE-SIB-P

(defund x86isa::n03$inline-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::n03$inline (ifix x)))

(defthm n03$inline-unguarded-correct
  (equal (x86isa::n03$inline-unguarded x)
         (x86isa::n03$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n03$inline-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::n06$inline-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::n06$inline (ifix x)))

(defthm n06$inline-unguarded-correct
  (equal (x86isa::n06$inline-unguarded x)
         (x86isa::n06$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n06$inline-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::n08$inline-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::n08$inline (ifix x)))

(defthm n08$inline-unguarded-correct
  (equal (x86isa::n08$inline-unguarded x)
         (x86isa::n08$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n08$inline-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::n32$inline-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::n32$inline (ifix x)))

(defthm n32$inline-unguarded-correct
  (equal (x86isa::n32$inline-unguarded x)
         (x86isa::n32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n32$inline-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::n64$inline-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::n64$inline (ifix x)))

(defthm n64$inline-unguarded-correct
  (equal (x86isa::n64$inline-unguarded x)
         (x86isa::n64$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n64$inline-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::4bits-fix-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::4bits-fix (loghead 4 (ifix x))))

(defthm 4bits-fix-unguarded-correct
  (equal (x86isa::4bits-fix-unguarded x)
         (x86isa::4bits-fix x))
  :hints (("Goal" :in-theory (enable x86isa::4bits-fix-unguarded X86ISA::4BITS-FIX))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::8bits-fix-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::8bits-fix (loghead 8 (ifix x))))

(defthm 8bits-fix-unguarded-correct
  (equal (x86isa::8bits-fix-unguarded x)
         (x86isa::8bits-fix x))
  :hints (("Goal" :in-theory (enable x86isa::8bits-fix-unguarded X86ISA::8BITS-FIX))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::prefixes-fix$inline-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::prefixes-fix$inline (acl2::loghead$inline 52 (ifix x))))

(defthm prefixes-fix$inline-unguarded-correct
  (equal (x86isa::prefixes-fix$inline-unguarded x)
         (x86isa::prefixes-fix$inline x))
  :hints (("Goal" :in-theory (enable x86isa::prefixes-fix$inline-unguarded x86isa::prefixes-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund loghead$inline-unguarded (n x)
  (declare (xargs :guard t))
  (loghead$inline (nfix n) (ifix x)))

(defthm loghead$inline-unguarded-correct
  (equal (loghead$inline-unguarded n x)
         (loghead$inline n x))
  :hints (("Goal" :in-theory (enable loghead$inline-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund logbitp-unguarded (i j)
  (declare (xargs :guard t))
  (logbitp (nfix i) (ifix j)))

(defthm logbitp-unguarded-correct
  (equal (logbitp-unguarded i j)
         (logbitp i j))
  :hints (("Goal" :in-theory (enable logbitp-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun binary-logand-unguarded (i j)
  (declare (xargs :guard t))
  (binary-logand (ifix i) (ifix j)))

(defthm binary-logand-unguarded-correct
  (equal (binary-logand-unguarded i j)
         (binary-logand i j))
  :hints (("Goal" :in-theory (enable binary-logand-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun binary-logior-unguarded (i j)
  (declare (xargs :guard t))
  (binary-logior (ifix i) (ifix j)))

(defthm binary-logior-unguarded-correct
  (equal (binary-logior-unguarded i j)
         (binary-logior i j))
  :hints (("Goal" :in-theory (enable binary-logior-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::reg-index$inline-unguarded (reg rex-byte index)
  (declare (xargs :guard t))
  (if (logbitp-unguarded index rex-byte)
      (logior 8 (x86isa::n03$inline-unguarded reg))
    (x86isa::n03$inline-unguarded reg)))

(defthm reg-index$inline-unguarded-correct
  (equal (x86isa::reg-index$inline-unguarded reg rex-byte index)
         (x86isa::reg-index$inline reg rex-byte index))
  :hints (("Goal" :in-theory (enable x86isa::reg-index$inline-unguarded x86isa::reg-index$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::PREFIXES->OPR-unguarded (x)
  (declare (xargs :guard t ))
  (X86ISA::PREFIXES->OPR (X86ISA::PREFIXES-FIX$inline-unguarded X)))

(defthm X86ISA::PREFIXES->OPR-unguarded-correct
  (equal (X86ISA::PREFIXES->OPR-unguarded x)
         (X86ISA::PREFIXES->OPR x))
  :hints (("Goal" :in-theory (enable X86ISA::PREFIXES->OPR-unguarded X86ISA::PREFIXES->OPR))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::PREFIXES->NXT-unguarded (x)
  (declare (xargs :guard t ))
  (X86ISA::PREFIXES->NXT (X86ISA::PREFIXES-FIX$inline-unguarded X)))

(defthm X86ISA::PREFIXES->NXT-unguarded-correct
  (equal (X86ISA::PREFIXES->NXT-unguarded x)
         (X86ISA::PREFIXES->NXT x))
  :hints (("Goal" :in-theory (enable X86ISA::PREFIXES->NXT-unguarded X86ISA::PREFIXES->NXT))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::PREFIXES->NUM-unguarded (x)
  (declare (xargs :guard t ))
  (X86ISA::PREFIXES->NUM (X86ISA::PREFIXES-FIX$inline-unguarded X)))

(defthm X86ISA::PREFIXES->NUM-unguarded-correct
  (equal (X86ISA::PREFIXES->NUM-unguarded x)
         (X86ISA::PREFIXES->NUM x))
  :hints (("Goal" :in-theory (enable X86ISA::PREFIXES->NUM-unguarded X86ISA::PREFIXES->NUM))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::PREFIXES->LCK-unguarded (x)
  (declare (xargs :guard t ))
  (X86ISA::PREFIXES->LCK (X86ISA::PREFIXES-FIX$inline-unguarded X)))

(defthm X86ISA::PREFIXES->LCK-unguarded-correct
  (equal (X86ISA::PREFIXES->LCK-unguarded x)
         (X86ISA::PREFIXES->LCK x))
  :hints (("Goal" :in-theory (enable X86ISA::PREFIXES->LCK-unguarded X86ISA::PREFIXES->LCK))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::PREFIXES->ADR-unguarded (x)
  (declare (xargs :guard t ))
  (X86ISA::PREFIXES->ADR (X86ISA::PREFIXES-FIX$inline-unguarded X)))

(defthm X86ISA::PREFIXES->ADR-unguarded-correct
  (equal (X86ISA::PREFIXES->ADR-unguarded x)
         (X86ISA::PREFIXES->ADR x))
  :hints (("Goal" :in-theory (enable X86ISA::PREFIXES->ADR-unguarded X86ISA::PREFIXES->ADR))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::PREFIXES->SEG-unguarded (x)
  (declare (xargs :guard t ))
  (X86ISA::PREFIXES->SEG (X86ISA::PREFIXES-FIX$inline-unguarded X)))

(defthm X86ISA::PREFIXES->SEG-unguarded-correct
  (equal (X86ISA::PREFIXES->SEG-unguarded x)
         (X86ISA::PREFIXES->SEG x))
  :hints (("Goal" :in-theory (enable X86ISA::PREFIXES->SEG-unguarded X86ISA::PREFIXES->SEG))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::PREFIXES->REP-unguarded (x)
  (declare (xargs :guard t ))
  (X86ISA::PREFIXES->REP (X86ISA::PREFIXES-FIX$inline-unguarded X)))

(defthm X86ISA::PREFIXES->REP-unguarded-correct
  (equal (X86ISA::PREFIXES->REP-unguarded x)
         (X86ISA::PREFIXES->REP x))
  :hints (("Goal" :in-theory (enable X86ISA::PREFIXES->REP-unguarded X86ISA::PREFIXES->REP))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::!PREFIXES->NUM-unguarded (num x)
  (declare (xargs :guard t))
  (X86ISA::!PREFIXES->NUM (x86isa::4bits-fix-unguarded num)
                          (X86ISA::PREFIXES-FIX$inline-unguarded X)))

(defthm X86ISA::!PREFIXES->num-unguarded-correct
  (equal (X86ISA::!PREFIXES->num-unguarded num x)
         (X86ISA::!PREFIXES->num num x))
  :hints (("Goal" :in-theory (enable X86ISA::!PREFIXES->num-unguarded X86ISA::!PREFIXES->num))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::!PREFIXES->NXT-unguarded (nxt x)
  (declare (xargs :guard t))
  (X86ISA::!PREFIXES->NXT (x86isa::8bits-fix-unguarded nxt)
                          (X86ISA::PREFIXES-FIX$inline-unguarded X)))

(defthm X86ISA::!PREFIXES->nxt-unguarded-correct
  (equal (X86ISA::!PREFIXES->nxt-unguarded nxt x)
         (X86ISA::!PREFIXES->nxt nxt x))
  :hints (("Goal" :in-theory (enable X86ISA::!PREFIXES->nxt-unguarded X86ISA::!PREFIXES->nxt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bitops::part-select-width-low$inline-unguarded (x width low)
  (declare (xargs :guard t))
  (loghead$inline-unguarded width (logtail-unguarded low x)))

(defthm bitops::part-select-width-low$inline-unguarded-correct
  (equal (bitops::part-select-width-low$inline-unguarded x width low)
         (bitops::part-select-width-low$inline x width low))
  :hints (("Goal" :in-theory (enable bitops::part-select-width-low$inline-unguarded bitops::part-select-width-low$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zip-unguarded (x)
  (declare (xargs :guard t))
  (zip (ifix x)))

(defthm zip-unguarded-correct
  (equal (zip-unguarded x)
         (zip x))
  :hints (("Goal" :in-theory (enable zip-unguarded zip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::MODR/M-FIX$inline-unguarded (x)
  (declare (xargs :guard t))
  (loghead$inline-unguarded 8 (ifix x)))

(defthm X86ISA::MODR/M-FIX$inline-unguarded-correct
  (equal (X86ISA::MODR/M-FIX$inline-unguarded x)
         (X86ISA::MODR/M-FIX$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::MODR/M-FIX$inline-unguarded X86ISA::MODR/M-FIX$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::MODR/M->R/M$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::MODR/M->R/M$inline (X86ISA::MODR/M-FIX$inline-unguarded X)))

(defthm X86ISA::MODR/M->r/m-unguarded-correct
  (equal (X86ISA::MODR/M->r/m$inline-unguarded x)
         (X86ISA::MODR/M->r/m$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::MODR/M->r/m$inline-unguarded X86ISA::MODR/M->r/m$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::MODR/M->reg$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::MODR/M->reg$inline (X86ISA::MODR/M-FIX$inline-unguarded X)))

(defthm X86ISA::MODR/M->reg-unguarded-correct
  (equal (X86ISA::MODR/M->reg$inline-unguarded x)
         (X86ISA::MODR/M->reg$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::MODR/M->reg$inline-unguarded X86ISA::MODR/M->reg$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::MODR/M->mod$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::MODR/M->mod$inline (X86ISA::MODR/M-FIX$inline-unguarded X)))

(defthm X86ISA::MODR/M->mod-unguarded-correct
  (equal (X86ISA::MODR/M->mod$inline-unguarded x)
         (X86ISA::MODR/M->mod$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::MODR/M->mod$inline-unguarded X86ISA::MODR/M->mod$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::rflagsbits-FIX$inline-unguarded (x)
  (declare (xargs :guard t))
  (loghead$inline-unguarded 32 (ifix x)))

(defthm X86ISA::rflagsbits-FIX$inline-unguarded-correct
  (equal (X86ISA::rflagsbits-FIX$inline-unguarded x)
         (X86ISA::rflagsbits-FIX$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits-FIX$inline-unguarded X86ISA::rflagsbits-FIX$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::rflagsbits->cf$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->cf$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->cf-unguarded-correct
  (equal (X86ISA::rflagsbits->cf$inline-unguarded x)
         (X86ISA::rflagsbits->cf$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->cf$inline-unguarded X86ISA::rflagsbits->cf$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::rflagsbits->pf$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->pf$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->pf-unguarded-correct
  (equal (X86ISA::rflagsbits->pf$inline-unguarded x)
         (X86ISA::rflagsbits->pf$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->pf$inline-unguarded X86ISA::rflagsbits->pf$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::rflagsbits->af$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->af$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->af-unguarded-correct
  (equal (X86ISA::rflagsbits->af$inline-unguarded x)
         (X86ISA::rflagsbits->af$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->af$inline-unguarded X86ISA::rflagsbits->af$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::rflagsbits->of$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->of$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->of-unguarded-correct
  (equal (X86ISA::rflagsbits->of$inline-unguarded x)
         (X86ISA::rflagsbits->of$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->of$inline-unguarded X86ISA::rflagsbits->of$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::rflagsbits->sf$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->sf$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->sf-unguarded-correct
  (equal (X86ISA::rflagsbits->sf$inline-unguarded x)
         (X86ISA::rflagsbits->sf$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->sf$inline-unguarded X86ISA::rflagsbits->sf$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::rflagsbits->zf$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->zf$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->zf-unguarded-correct
  (equal (X86ISA::rflagsbits->zf$inline-unguarded x)
         (X86ISA::rflagsbits->zf$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->zf$inline-unguarded X86ISA::rflagsbits->zf$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::!rflagsbits->af$inline-unguarded (af x)
  (declare (xargs :guard t))
  (X86ISA::!rflagsbits->af$inline (bfix$inline af) (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::!rflagsbits->af-unguarded-correct
  (equal (X86ISA::!rflagsbits->af$inline-unguarded af x)
         (X86ISA::!rflagsbits->af$inline af x))
  :hints (("Goal" :in-theory (enable X86ISA::!rflagsbits->af$inline-unguarded X86ISA::!rflagsbits->af$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::n08-to-i08$inline-unguarded (x)
  (declare (xargs :guard t))
  (logext-unguarded 8 x))

(defthm x86isa::n08-to-i08$inline-unguarded-correct
  (equal (x86isa::n08-to-i08$inline-unguarded x)
         (x86isa::n08-to-i08$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n08-to-i08$inline-unguarded x86isa::n08-to-i08$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::n32-to-i32$inline-unguarded (x)
  (declare (xargs :guard t))
  (logext-unguarded 32 x))

(defthm x86isa::n32-to-i32$inline-unguarded-correct
  (equal (x86isa::n32-to-i32$inline-unguarded x)
         (x86isa::n32-to-i32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n32-to-i32$inline-unguarded x86isa::n32-to-i32$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::n64-to-i64$inline-unguarded (x)
  (declare (xargs :guard t))
  (logext-unguarded 64 x))

(defthm x86isa::n64-to-i64$inline-unguarded-correct
  (equal (x86isa::n64-to-i64$inline-unguarded x)
         (x86isa::n64-to-i64$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n64-to-i64$inline-unguarded x86isa::n64-to-i64$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun evenp-unguarded (x)
  (declare (xargs :guard t ))
  (INTEGERP (binary-*-unguarded X (unary-/-unguarded 2))))

(defthm evenp-unguarded-correct
  (equal (evenp-unguarded x)
         (evenp x))
  :hints (("Goal" :in-theory (enable evenp-unguarded evenp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun logcount-unguarded (x)
  (declare (xargs :guard t ))
  (logcount (ifix x)))

(defthm logcount-unguarded-correct
  (equal (logcount-unguarded x)
         (logcount x))
  :hints (("Goal" :in-theory (enable logcount-unguarded logcount))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ash-unguarded (i c)
  (declare (xargs :guard t ))
  (ash (ifix i) (ifix c)))

(defthm ash-unguarded-correct
  (equal (ash-unguarded i c)
         (ash i c))
  :hints (("Goal" :in-theory (enable ash-unguarded ash))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::PF-SPEC8$inline-unguarded (result)
  (declare (xargs :guard t))
  (BOOL->BIT (NOT (LOGBITP 0 (LOGCOUNT (ifix result))))))

(defthm PF-SPEC8$inline-unguarded-correct
  (equal (x86isa::PF-SPEC8$inline-unguarded x)
         (x86isa::PF-SPEC8$inline x))
  :hints (("Goal" :in-theory (enable x86isa::PF-SPEC8$inline-unguarded x86isa::PF-SPEC8$inline ifix LOGCOUNT))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::SF-SPEC8$inline-unguarded (result)
  (declare (xargs :guard t))
  (ACL2::PART-SELECT (ifix RESULT) :LOW 7 :WIDTH 1))

(local (include-book "kestrel/bv/logapp" :dir :system)) ; for loghead-becomes-bvchop
(defthm sf-spec8$inline-unguarded-correct
  (equal (x86isa::sf-spec8$inline-unguarded x)
         (x86isa::sf-spec8$inline x))
  :hints (("Goal" :in-theory (enable x86isa::sf-spec8$inline-unguarded x86isa::sf-spec8$inline))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::CF-SPEC32$inline-unguarded (raw-result)
  (declare (xargs :guard t))
  (BOOL->BIT (NOT (UNSIGNED-BYTE-P 32 RAW-RESULT))))

(defthm CF-SPEC32$inline-unguarded-correct
  (equal (x86isa::CF-SPEC32$inline-unguarded x)
         (x86isa::CF-SPEC32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::CF-SPEC32$inline-unguarded x86isa::CF-SPEC32$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::PF-SPEC32$inline-unguarded (result)
  (declare (xargs :guard t))
  (BOOL->BIT (NOT (LOGBITP 0 (LOGCOUNT (acl2::loghead$inline-unguarded 8 result))))))

(defthm PF-SPEC32$inline-unguarded-correct
  (equal (x86isa::PF-SPEC32$inline-unguarded x)
         (x86isa::PF-SPEC32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::PF-SPEC32$inline-unguarded x86isa::PF-SPEC32$inline))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::SF-SPEC32$inline-unguarded (result)
  (declare (xargs :guard t))
  (ACL2::PART-SELECT (acl2::loghead$inline-unguarded 32 RESULT) :LOW 31 :WIDTH 1))

;(local (include-book "kestrel/bv/logapp" :dir :system)) ; for loghead-becomes-bvchop
(defthm sf-spec32$inline-unguarded-correct
  (equal (x86isa::sf-spec32$inline-unguarded x)
         (x86isa::sf-spec32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::sf-spec32$inline-unguarded x86isa::sf-spec32$inline))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::OF-SPEC32$inline-unguarded (signed-raw-result)
  (declare (xargs :guard t))
  (BOOL->BIT (NOT (SIGNED-BYTE-P 32 SIGNED-RAW-RESULT))))

(defthm OF-SPEC32$inline-unguarded-correct
  (equal (x86isa::OF-SPEC32$inline-unguarded x)
         (x86isa::OF-SPEC32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::OF-SPEC32$inline-unguarded x86isa::OF-SPEC32$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::zf-spec$inline-unguarded (result)
  (declare (xargs :guard t))
  (IF (EQUAL RESULT 0) 1 0))

(defthm zf-spec$inline-unguarded-correct
  (equal (x86isa::zf-spec$inline-unguarded x)
         (x86isa::zf-spec$inline x))
  :hints (("Goal" :in-theory (enable x86isa::zf-spec$inline-unguarded x86isa::zf-spec$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun X86ISA::X86-DECODE-SIB-P-unguarded (modr/m 16-BIT-ADDRESSP)
  (declare (xargs :guard t))
  (AND (NOT 16-BIT-ADDRESSP)
       (B* ((R/M (X86ISA::MODR/M->R/M$inline-unguarded MODR/M))
            (MOD (X86ISA::MODR/M->MOD$inline-unguarded MODR/M)))
         (AND (INT= R/M 4)
              (NOT (INT= MOD 3))))))

(defthm X86-DECODE-SIB-P-unguarded-correct
  (equal (x86isa::X86-DECODE-SIB-P-unguarded modr/m 16-BIT-ADDRESSP)
         (x86isa::X86-DECODE-SIB-P modr/m 16-BIT-ADDRESSP))
  :hints (("Goal" :in-theory (enable x86isa::X86-DECODE-SIB-P-unguarded x86isa::X86-DECODE-SIB-P))))

(defconst *axe-evaluator-x86-fns-and-aliases*
  (append '(x86isa::canonical-address-p$inline ; unguarded
            ;; todo: X86ISA::PREFIXES->OPR$INLINE, logbitp
            (lookup lookup-equal-unguarded)
            (x86isa::n03$inline x86isa::n03$inline-unguarded)
            (x86isa::n06$inline x86isa::n06$inline-unguarded)
            (x86isa::n08$inline x86isa::n08$inline-unguarded)
            (x86isa::n32$inline x86isa::n32$inline-unguarded)
            (x86isa::n64$inline x86isa::n64$inline-unguarded)
            (X86ISA::N08-TO-I08$inline X86ISA::N08-TO-I08$inline-unguarded)
            (X86ISA::N32-TO-I32$inline X86ISA::N32-TO-I32$inline-unguarded)
            (X86ISA::N64-TO-I64$inline X86ISA::N64-TO-I64$inline-unguarded)
            (x86isa::4bits-fix x86isa::4bits-fix-unguarded)
            (x86isa::8bits-fix x86isa::8bits-fix-unguarded)
            (loghead$inline loghead$inline-unguarded)
            (x86isa::prefixes-fix$inline x86isa::prefixes-fix$inline-unguarded)
            (x86isa::prefixes->opr$inline x86isa::prefixes->opr-unguarded)
            (x86isa::prefixes->rep$inline x86isa::prefixes->rep-unguarded)
            (x86isa::prefixes->nxt$inline x86isa::prefixes->nxt-unguarded)
            (x86isa::prefixes->num$inline x86isa::prefixes->num-unguarded)
            (x86isa::prefixes->lck$inline x86isa::prefixes->lck-unguarded)
            (x86isa::prefixes->adr$inline x86isa::prefixes->adr-unguarded)
            (x86isa::prefixes->seg$inline x86isa::prefixes->seg-unguarded)
            (x86isa::reg-index$inline x86isa::reg-index$inline-unguarded)
            (x86isa::!prefixes->num$inline x86isa::!prefixes->num-unguarded)
            (x86isa::!prefixes->nxt$inline x86isa::!prefixes->nxt-unguarded)
            power-of-2p
            logmaskp
            bfix$inline
            BOOL->BIT$INLINE
            (evenp evenp-unguarded)
            (logcount logcount-unguarded)
            (zip zip-unguarded)
            (ash ash-unguarded)
            (logbitp logbitp-unguarded)
            (binary-logand binary-logand-unguarded)
            (binary-logior binary-logior-unguarded)
            (nonnegative-integer-quotient nonnegative-integer-quotient-unguarded)
            (x86isa::modr/m-fix$inline x86isa::modr/m-fix$inline-unguarded)
            (X86ISA::MODR/M->R/M$inline X86ISA::MODR/M->R/M$inline-unguarded)
            (X86ISA::MODR/M->Reg$inline X86ISA::MODR/M->reg$inline-unguarded)
            (X86ISA::MODR/M->mod$inline X86ISA::MODR/M->mod$inline-unguarded)
            (X86ISA::rflagsbits-FIX$inline X86ISA::rflagsbits-FIX$inline-unguarded)
            (X86ISA::rflagsbits->af$inline X86ISA::rflagsbits->af$inline-unguarded)
            (X86ISA::rflagsbits->cf$inline X86ISA::rflagsbits->cf$inline-unguarded)
            (X86ISA::rflagsbits->pf$inline X86ISA::rflagsbits->pf$inline-unguarded)
            (X86ISA::rflagsbits->sf$inline X86ISA::rflagsbits->sf$inline-unguarded)
            (X86ISA::rflagsbits->of$inline X86ISA::rflagsbits->of$inline-unguarded)
            (X86ISA::rflagsbits->zf$inline X86ISA::rflagsbits->zf$inline-unguarded)
            (X86ISA::!rflagsbits->af$inline X86ISA::!rflagsbits->af$inline-unguarded)
            (x86isa::PF-SPEC8$inline x86isa::PF-SPEC8$inline-unguarded)
            (x86isa::SF-SPEC8$inline x86isa::SF-SPEC8$inline-unguarded)
            (x86isa::CF-SPEC32$inline x86isa::CF-SPEC32$inline-unguarded)
            (x86isa::OF-SPEC32$inline x86isa::OF-SPEC32$inline-unguarded)
            (x86isa::PF-SPEC32$inline x86isa::PF-SPEC32$inline-unguarded)
            (x86isa::SF-SPEC32$inline x86isa::SF-SPEC32$inline-unguarded)
            (x86isa::ZF-SPEC$inline x86isa::ZF-SPEC$inline-unguarded)
            (x86isa::X86-DECODE-SIB-P x86isa::X86-DECODE-SIB-P-unguarded)
            )
          *axe-evaluator-basic-fns-and-aliases*))

;; Makes the evaluator (also checks that each alias given is equivalent to its function):
(make-evaluator-simple x86 *axe-evaluator-x86-fns-and-aliases*)
