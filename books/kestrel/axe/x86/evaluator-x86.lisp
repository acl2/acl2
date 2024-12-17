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

(in-package "ACL2") ; change to X package?

(include-book "../evaluator-basic")
(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ;for canonical-address-p$inline
(include-book "projects/x86isa/machine/register-readers-and-writers" :dir :system) ; for reg-index$inline, has ttag :UNDEF-FLG
(include-book "projects/x86isa/machine/prefix-modrm-sib-decoding" :dir :system) ; for x86isa::x86-decode-sib-p, 64-bit-mode-one-byte-opcode-modr/m-p, x86isa::get-one-byte-prefix-array-code-unguarded, etc.
(include-book "projects/x86isa/machine/decoding-and-spec-utils" :dir :system) ; for x86isa::check-instruction-length$inline, has ttag :OTHER-NON-DET
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)
(include-book "kestrel/x86/rflags-spec-sub" :dir :system)
(local (include-book "kestrel/bv/bitops" :dir :system))
(local (include-book "kestrel/bv/logapp" :dir :system)) ; for loghead-becomes-bvchop

;; We avoid evaluating the undef-XXX functions, which have raw lisp code, since
;; that might defeat the purpose of having their values be undefined.

(local
  (in-theory (disable rational-listp
                      integer-listp
                      assoc-equal
                      min
                      max
                      integer-range-p
                      signed-byte-p
                      x86isa::canonical-address-p$inline
                      bvle)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund integer-range-p-unguarded (lower upper x)
  (declare (xargs :guard t))
  (and (integerp x)
       (not (<-unguarded x lower))
       (<-unguarded x upper)))

(defthm integer-range-p-unguarded-correct
  (equal (integer-range-p-unguarded lower upper x)
         (integer-range-p lower upper x))
  :hints (("Goal" :in-theory (enable integer-range-p-unguarded
                                     integer-range-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defund x86isa::2bits-fix-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::2bits-fix (loghead 2 (ifix x))))

(defthm 2bits-fix-unguarded-correct
  (equal (x86isa::2bits-fix-unguarded x)
         (x86isa::2bits-fix x))
  :hints (("Goal" :in-theory (enable x86isa::2bits-fix-unguarded X86ISA::2BITS-FIX))))

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

(defund x86isa::10bits-fix-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::10bits-fix (loghead 10 (ifix x))))

(defthm 10bits-fix-unguarded-correct
  (equal (x86isa::10bits-fix-unguarded x)
         (x86isa::10bits-fix x))
  :hints (("Goal" :in-theory (enable x86isa::10bits-fix-unguarded X86ISA::10BITS-FIX))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::prefixes-fix$inline-unguarded (x)
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

(defund binary-logand-unguarded (i j)
  (declare (xargs :guard t))
  (binary-logand (ifix i) (ifix j)))

(defthm binary-logand-unguarded-correct
  (equal (binary-logand-unguarded i j)
         (binary-logand i j))
  :hints (("Goal" :in-theory (enable binary-logand-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund binary-logior-unguarded (i j)
  (declare (xargs :guard t))
  (binary-logior (ifix i) (ifix j)))

(defthm binary-logior-unguarded-correct
  (equal (binary-logior-unguarded i j)
         (binary-logior i j))
  :hints (("Goal" :in-theory (enable binary-logior-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::reg-index$inline-unguarded (reg rex-byte index)
  (declare (xargs :guard t))
  (if (logbitp-unguarded index rex-byte)
      (logior 8 (x86isa::n03$inline-unguarded reg))
    (x86isa::n03$inline-unguarded reg)))

(defthm reg-index$inline-unguarded-correct
  (equal (x86isa::reg-index$inline-unguarded reg rex-byte index)
         (x86isa::reg-index$inline reg rex-byte index))
  :hints (("Goal" :in-theory (enable x86isa::reg-index$inline-unguarded x86isa::reg-index$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::PREFIXES->OPR-unguarded (x)
  (declare (xargs :guard t ))
  (X86ISA::PREFIXES->OPR (X86ISA::PREFIXES-FIX$inline-unguarded X)))

(defthm X86ISA::PREFIXES->OPR-unguarded-correct
  (equal (X86ISA::PREFIXES->OPR-unguarded x)
         (X86ISA::PREFIXES->OPR x))
  :hints (("Goal" :in-theory (enable x86isa::prefixes->opr-unguarded x86isa::prefixes->opr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::prefixes->nxt-unguarded (x)
  (declare (xargs :guard t ))
  (x86isa::prefixes->nxt (x86isa::prefixes-fix$inline-unguarded x)))

(defthm x86isa::prefixes->nxt-unguarded-correct
  (equal (x86isa::prefixes->nxt-unguarded x)
         (x86isa::prefixes->nxt x))
  :hints (("Goal" :in-theory (enable x86isa::prefixes->nxt-unguarded x86isa::prefixes->nxt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::prefixes->num-unguarded (x)
  (declare (xargs :guard t ))
  (x86isa::prefixes->num (x86isa::prefixes-fix$inline-unguarded x)))

(defthm x86isa::prefixes->num-unguarded-correct
  (equal (x86isa::prefixes->num-unguarded x)
         (x86isa::prefixes->num x))
  :hints (("Goal" :in-theory (enable x86isa::prefixes->num-unguarded x86isa::prefixes->num))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::prefixes->lck-unguarded (x)
  (declare (xargs :guard t ))
  (x86isa::prefixes->lck (x86isa::prefixes-fix$inline-unguarded x)))

(defthm x86isa::prefixes->lck-unguarded-correct
  (equal (x86isa::prefixes->lck-unguarded x)
         (x86isa::prefixes->lck x))
  :hints (("Goal" :in-theory (enable x86isa::prefixes->lck-unguarded x86isa::prefixes->lck))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::prefixes->adr-unguarded (x)
  (declare (xargs :guard t ))
  (x86isa::prefixes->adr (x86isa::prefixes-fix$inline-unguarded x)))

(defthm x86isa::prefixes->adr-unguarded-correct
  (equal (x86isa::prefixes->adr-unguarded x)
         (x86isa::prefixes->adr x))
  :hints (("Goal" :in-theory (enable x86isa::prefixes->adr-unguarded x86isa::prefixes->adr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::prefixes->seg-unguarded (x)
  (declare (xargs :guard t ))
  (x86isa::prefixes->seg (x86isa::prefixes-fix$inline-unguarded x)))

(defthm x86isa::prefixes->seg-unguarded-correct
  (equal (x86isa::prefixes->seg-unguarded x)
         (x86isa::prefixes->seg x))
  :hints (("Goal" :in-theory (enable x86isa::prefixes->seg-unguarded x86isa::prefixes->seg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::prefixes->rep-unguarded (x)
  (declare (xargs :guard t ))
  (x86isa::prefixes->rep (x86isa::prefixes-fix$inline-unguarded x)))

(defthm x86isa::prefixes->rep-unguarded-correct
  (equal (x86isa::prefixes->rep-unguarded x)
         (x86isa::prefixes->rep x))
  :hints (("Goal" :in-theory (enable x86isa::prefixes->rep-unguarded x86isa::prefixes->rep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::!prefixes->num-unguarded (num x)
  (declare (xargs :guard t))
  (x86isa::!prefixes->num (x86isa::4bits-fix-unguarded num)
                          (x86isa::prefixes-fix$inline-unguarded x)))

(defthm x86isa::!prefixes->num-unguarded-correct
  (equal (x86isa::!prefixes->num-unguarded num x)
         (x86isa::!prefixes->num num x))
  :hints (("Goal" :in-theory (enable x86isa::!prefixes->num-unguarded x86isa::!prefixes->num))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::!prefixes->nxt-unguarded (nxt x)
  (declare (xargs :guard t))
  (x86isa::!prefixes->nxt (x86isa::8bits-fix-unguarded nxt)
                          (x86isa::prefixes-fix$inline-unguarded x)))

(defthm x86isa::!prefixes->nxt-unguarded-correct
  (equal (x86isa::!prefixes->nxt-unguarded nxt x)
         (x86isa::!prefixes->nxt nxt x))
  :hints (("Goal" :in-theory (enable x86isa::!prefixes->nxt-unguarded x86isa::!prefixes->nxt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::!prefixes->opr-unguarded (opr x)
  (declare (xargs :guard t))
  (x86isa::!prefixes->opr (x86isa::8bits-fix-unguarded opr)
                          (x86isa::prefixes-fix$inline-unguarded x)))

(defthm x86isa::!prefixes->opr-unguarded-correct
  (equal (x86isa::!prefixes->opr-unguarded opr x)
         (x86isa::!prefixes->opr opr x))
  :hints (("Goal" :in-theory (enable x86isa::!prefixes->opr-unguarded x86isa::!prefixes->opr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::!prefixes->rep-unguarded (rep x)
  (declare (xargs :guard t))
  (x86isa::!prefixes->rep (x86isa::8bits-fix-unguarded rep)
                          (x86isa::prefixes-fix$inline-unguarded x)))

(defthm x86isa::!prefixes->rep-unguarded-correct
  (equal (x86isa::!prefixes->rep-unguarded rep x)
         (x86isa::!prefixes->rep rep x))
  :hints (("Goal" :in-theory (enable x86isa::!prefixes->rep x86isa::!prefixes->rep-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bitops::part-select-width-low$inline-unguarded (x width low)
  (declare (xargs :guard t))
  (loghead$inline-unguarded width (logtail$inline-unguarded low x)))

(defthm bitops::part-select-width-low$inline-unguarded-correct
  (equal (bitops::part-select-width-low$inline-unguarded x width low)
         (bitops::part-select-width-low$inline x width low))
  :hints (("Goal" :in-theory (enable bitops::part-select-width-low$inline-unguarded bitops::part-select-width-low$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund zip-unguarded (x)
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

(defthm x86isa::modr/m-fix$inline-unguarded-correct
  (equal (x86isa::modr/m-fix$inline-unguarded x)
         (x86isa::modr/m-fix$inline x))
  :hints (("Goal" :in-theory (enable x86isa::modr/m-fix$inline-unguarded x86isa::modr/m-fix$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::modr/m->r/m$inline-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::modr/m->r/m$inline (x86isa::modr/m-fix$inline-unguarded x)))

(defthm x86isa::modr/m->r/m-unguarded-correct
  (equal (x86isa::modr/m->r/m$inline-unguarded x)
         (x86isa::modr/m->r/m$inline x))
  :hints (("Goal" :in-theory (enable x86isa::modr/m->r/m$inline-unguarded x86isa::modr/m->r/m$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::modr/m->reg$inline-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::modr/m->reg$inline (x86isa::modr/m-fix$inline-unguarded x)))

(defthm x86isa::modr/m->reg-unguarded-correct
  (equal (x86isa::modr/m->reg$inline-unguarded x)
         (x86isa::modr/m->reg$inline x))
  :hints (("Goal" :in-theory (enable x86isa::modr/m->reg$inline-unguarded x86isa::modr/m->reg$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::modr/m->mod$inline-unguarded (x)
  (declare (xargs :guard t))
  (x86isa::modr/m->mod$inline (x86isa::modr/m-fix$inline-unguarded x)))

(defthm x86isa::modr/m->mod-unguarded-correct
  (equal (x86isa::modr/m->mod$inline-unguarded x)
         (x86isa::modr/m->mod$inline x))
  :hints (("Goal" :in-theory (enable x86isa::modr/m->mod$inline-unguarded x86isa::modr/m->mod$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::rflagsbits-FIX$inline-unguarded (x)
  (declare (xargs :guard t))
  (loghead$inline-unguarded 32 (ifix x)))

(defthm x86isa::rflagsbits-fix$inline-unguarded-correct
  (equal (x86isa::rflagsbits-fix$inline-unguarded x)
         (x86isa::rflagsbits-fix$inline x))
  :hints (("Goal" :in-theory (enable x86isa::rflagsbits-fix$inline-unguarded x86isa::rflagsbits-fix$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::rflagsbits->cf$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->cf$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->cf-unguarded-correct
  (equal (X86ISA::rflagsbits->cf$inline-unguarded x)
         (X86ISA::rflagsbits->cf$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->cf$inline-unguarded X86ISA::rflagsbits->cf$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::rflagsbits->pf$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->pf$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->pf-unguarded-correct
  (equal (X86ISA::rflagsbits->pf$inline-unguarded x)
         (X86ISA::rflagsbits->pf$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->pf$inline-unguarded X86ISA::rflagsbits->pf$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::rflagsbits->af$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->af$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->af-unguarded-correct
  (equal (X86ISA::rflagsbits->af$inline-unguarded x)
         (X86ISA::rflagsbits->af$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->af$inline-unguarded X86ISA::rflagsbits->af$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::rflagsbits->of$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->of$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->of-unguarded-correct
  (equal (X86ISA::rflagsbits->of$inline-unguarded x)
         (X86ISA::rflagsbits->of$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->of$inline-unguarded X86ISA::rflagsbits->of$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::rflagsbits->sf$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->sf$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->sf-unguarded-correct
  (equal (X86ISA::rflagsbits->sf$inline-unguarded x)
         (X86ISA::rflagsbits->sf$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->sf$inline-unguarded X86ISA::rflagsbits->sf$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::rflagsbits->zf$inline-unguarded (x)
  (declare (xargs :guard t))
  (X86ISA::rflagsbits->zf$inline (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::rflagsbits->zf-unguarded-correct
  (equal (X86ISA::rflagsbits->zf$inline-unguarded x)
         (X86ISA::rflagsbits->zf$inline x))
  :hints (("Goal" :in-theory (enable X86ISA::rflagsbits->zf$inline-unguarded X86ISA::rflagsbits->zf$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund X86ISA::!rflagsbits->af$inline-unguarded (af x)
  (declare (xargs :guard t))
  (X86ISA::!rflagsbits->af$inline (bfix$inline af) (X86ISA::rflagsbits-FIX$inline-unguarded X)))

(defthm X86ISA::!rflagsbits->af-unguarded-correct
  (equal (X86ISA::!rflagsbits->af$inline-unguarded af x)
         (X86ISA::!rflagsbits->af$inline af x))
  :hints (("Goal" :in-theory (enable X86ISA::!rflagsbits->af$inline-unguarded X86ISA::!rflagsbits->af$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::n08-to-i08$inline-unguarded (x)
  (declare (xargs :guard t))
  (logext-unguarded 8 x))

(defthm x86isa::n08-to-i08$inline-unguarded-correct
  (equal (x86isa::n08-to-i08$inline-unguarded x)
         (x86isa::n08-to-i08$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n08-to-i08$inline-unguarded x86isa::n08-to-i08$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::n32-to-i32$inline-unguarded (x)
  (declare (xargs :guard t))
  (logext-unguarded 32 x))

(defthm x86isa::n32-to-i32$inline-unguarded-correct
  (equal (x86isa::n32-to-i32$inline-unguarded x)
         (x86isa::n32-to-i32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n32-to-i32$inline-unguarded x86isa::n32-to-i32$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::n64-to-i64$inline-unguarded (x)
  (declare (xargs :guard t))
  (logext-unguarded 64 x))

(defthm x86isa::n64-to-i64$inline-unguarded-correct
  (equal (x86isa::n64-to-i64$inline-unguarded x)
         (x86isa::n64-to-i64$inline x))
  :hints (("Goal" :in-theory (enable x86isa::n64-to-i64$inline-unguarded x86isa::n64-to-i64$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund evenp-unguarded (x)
  (declare (xargs :guard t ))
  (INTEGERP (binary-*-unguarded X (unary-/-unguarded 2))))

(defthm evenp-unguarded-correct
  (equal (evenp-unguarded x)
         (evenp x))
  :hints (("Goal" :in-theory (enable evenp-unguarded evenp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund logcount-unguarded (x)
  (declare (xargs :guard t ))
  (logcount (ifix x)))

(defthm logcount-unguarded-correct
  (equal (logcount-unguarded x)
         (logcount x))
  :hints (("Goal" :in-theory (enable logcount-unguarded logcount))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund ash-unguarded (i c)
  (declare (xargs :guard t ))
  (ash (ifix i) (ifix c)))

(defthm ash-unguarded-correct
  (equal (ash-unguarded i c)
         (ash i c))
  :hints (("Goal" :in-theory (enable ash-unguarded ash))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::pf-spec8$inline-unguarded (result)
  (declare (xargs :guard t))
  (bool->bit (not (logbitp 0 (logcount (ifix result))))))

(defthm pf-spec8$inline-unguarded-correct
  (equal (x86isa::pf-spec8$inline-unguarded x)
         (x86isa::pf-spec8$inline x))
  :hints (("Goal" :in-theory (enable x86isa::pf-spec8$inline-unguarded x86isa::pf-spec8$inline ifix logcount))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::cf-spec32$inline-unguarded (raw-result)
  (declare (xargs :guard t))
  (bool->bit (not (unsigned-byte-p 32 raw-result))))

(defthm cf-spec32$inline-unguarded-correct
  (equal (x86isa::cf-spec32$inline-unguarded x)
         (x86isa::cf-spec32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::cf-spec32$inline-unguarded x86isa::cf-spec32$inline))))

(defund x86isa::cf-spec64$inline-unguarded (raw-result)
  (declare (xargs :guard t))
  (bool->bit (not (unsigned-byte-p 64 raw-result))))

(defthm cf-spec64$inline-unguarded-correct
  (equal (x86isa::cf-spec64$inline-unguarded x)
         (x86isa::cf-spec64$inline x))
  :hints (("Goal" :in-theory (enable x86isa::cf-spec64$inline-unguarded x86isa::cf-spec64$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::pf-spec32$inline-unguarded (result)
  (declare (xargs :guard t))
  (bool->bit (not (logbitp 0 (logcount (acl2::loghead$inline-unguarded 8 result))))))

(defthm pf-spec32$inline-unguarded-correct
  (equal (x86isa::pf-spec32$inline-unguarded x)
         (x86isa::pf-spec32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::pf-spec32$inline-unguarded x86isa::pf-spec32$inline))))

(defund x86isa::pf-spec64$inline-unguarded (result)
  (declare (xargs :guard t))
  (bool->bit (not (logbitp 0 (logcount (acl2::loghead$inline-unguarded 8 result))))))

(defthm pf-spec64$inline-unguarded-correct
  (equal (x86isa::pf-spec64$inline-unguarded x)
         (x86isa::pf-spec64$inline x))
  :hints (("Goal" :in-theory (enable x86isa::pf-spec64$inline-unguarded x86isa::pf-spec64$inline))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sf-spec8$inline-unguarded (result)
  (declare (xargs :guard t))
  (acl2::part-select (ifix result) :low 7 :width 1))

(defthm sf-spec8$inline-unguarded-correct
  (equal (x86isa::sf-spec8$inline-unguarded x)
         (x86isa::sf-spec8$inline x))
  :hints (("Goal" :in-theory (enable x86isa::sf-spec8$inline-unguarded x86isa::sf-spec8$inline))))

(defund x86isa::sf-spec16$inline-unguarded (result)
  (declare (xargs :guard t))
  (acl2::part-select (ifix result) :low 15 :width 1))

(defthm sf-spec16$inline-unguarded-correct
  (equal (x86isa::sf-spec16$inline-unguarded x)
         (x86isa::sf-spec16$inline x))
  :hints (("Goal" :in-theory (enable x86isa::sf-spec16$inline-unguarded x86isa::sf-spec16$inline))))

(defund x86isa::sf-spec32$inline-unguarded (result)
  (declare (xargs :guard t))
  (acl2::part-select (acl2::loghead$inline-unguarded 32 result) :low 31 :width 1))

(defthm sf-spec32$inline-unguarded-correct
  (equal (x86isa::sf-spec32$inline-unguarded x)
         (x86isa::sf-spec32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::sf-spec32$inline-unguarded x86isa::sf-spec32$inline))))

(defund x86isa::sf-spec64$inline-unguarded (result)
  (declare (xargs :guard t))
  (acl2::part-select (acl2::loghead$inline-unguarded 64 result) :low 63 :width 1))

(defthm sf-spec64$inline-unguarded-correct
  (equal (x86isa::sf-spec64$inline-unguarded x)
         (x86isa::sf-spec64$inline x))
  :hints (("Goal" :in-theory (enable x86isa::sf-spec64$inline-unguarded x86isa::sf-spec64$inline))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::of-spec32$inline-unguarded (signed-raw-result)
  (declare (xargs :guard t))
  (bool->bit (not (signed-byte-p 32 signed-raw-result))))

(defthm of-spec32$inline-unguarded-correct
  (equal (x86isa::of-spec32$inline-unguarded x)
         (x86isa::of-spec32$inline x))
  :hints (("Goal" :in-theory (enable x86isa::of-spec32$inline-unguarded x86isa::of-spec32$inline))))

(defund x86isa::of-spec64$inline-unguarded (signed-raw-result)
  (declare (xargs :guard t))
  (bool->bit (not (signed-byte-p 64 signed-raw-result))))

(defthm of-spec64$inline-unguarded-correct
  (equal (x86isa::of-spec64$inline-unguarded x)
         (x86isa::of-spec64$inline x))
  :hints (("Goal" :in-theory (enable x86isa::of-spec64$inline-unguarded x86isa::of-spec64$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::zf-spec$inline-unguarded (result)
  (declare (xargs :guard t))
  (if (equal result 0) 1 0))

(defthm zf-spec$inline-unguarded-correct
  (equal (x86isa::zf-spec$inline-unguarded x)
         (x86isa::zf-spec$inline x))
  :hints (("Goal" :in-theory (enable x86isa::zf-spec$inline-unguarded x86isa::zf-spec$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::x86-decode-sib-p-unguarded (modr/m 16-bit-addressp)
  (declare (xargs :guard t))
  (and (not 16-bit-addressp)
       (b* ((r/m (x86isa::modr/m->r/m$inline-unguarded modr/m))
            (mod (x86isa::modr/m->mod$inline-unguarded modr/m)))
         (and (int= r/m 4)
              (not (int= mod 3))))))

(defthm x86-decode-sib-p-unguarded-correct
  (equal (x86isa::x86-decode-sib-p-unguarded modr/m 16-bit-addressp)
         (x86isa::x86-decode-sib-p modr/m 16-bit-addressp))
  :hints (("Goal" :in-theory (enable x86isa::x86-decode-sib-p-unguarded x86isa::x86-decode-sib-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sib-fix$inline-unguarded (x)
  (declare (xargs :guard t))
  (loghead 8 (ifix x)))

(defthm x86-sib-fix$inline-unguarded-correct
  (equal (x86isa::sib-fix$inline-unguarded x)
         (x86isa::sib-fix$inline x))
  :hints (("Goal" :in-theory (enable x86isa::sib-fix$inline-unguarded x86isa::sib-fix$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sib->scale$inline-unguarded (x)
  (declare (xargs :guard t))
  (slice 7 6 (ifix x)))

(defthm x86isa::sib->scale$inline-unguarded-correct
  (equal (x86isa::sib->scale$inline-unguarded x)
         (x86isa::sib->scale$inline x))
  :hints (("Goal" :in-theory (enable x86isa::sib->scale$inline-unguarded
                                     x86isa::sib->scale$inline
                                     x86isa::sib-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sib->index$inline-unguarded (x)
  (declare (xargs :guard t))
  (slice 5 3 (ifix x)))

(defthm x86isa::sib->index$inline-unguarded-correct
  (equal (x86isa::sib->index$inline-unguarded x)
         (x86isa::sib->index$inline x))
  :hints (("Goal" :in-theory (enable x86isa::sib->index$inline-unguarded
                                     x86isa::sib->index$inline
                                     x86isa::sib-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sib->base$inline-unguarded (x)
  (declare (xargs :guard t))
  (slice 2 0 (ifix x)))

(defthm x86isa::sib->base$inline-unguarded-correct
  (equal (x86isa::sib->base$inline-unguarded x)
         (x86isa::sib->base$inline x))
  :hints (("Goal" :in-theory (enable x86isa::sib->base$inline-unguarded
                                     x86isa::sib->base$inline
                                     x86isa::sib-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund acl2::assoc-keyword-unguarded (key l)
  (declare (xargs :guard t))
  (cond ((atom l) nil)
        ((equal key (car l)) l)
        (t (assoc-keyword-unguarded key (acl2::cdr-unguarded (acl2::cdr-unguarded l))))))

(defthm assoc-keyword-unguarded-correct
  (equal (acl2::assoc-keyword-unguarded key l)
         (assoc-keyword key l))
  :hints (("Goal" :in-theory (enable acl2::assoc-keyword-unguarded))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund acl2::header-unguarded (name l)
  (declare (xargs :guard t))
  (if (or (array1p name l)
          (array2p name l))
      (header name l)
    ;; todo: make an assoc-eq-unguarded:
    (acl2::assoc-equal-unguarded :header l)))

(defthm header-unguarded-correct
  (equal (acl2::header-unguarded name l)
         (acl2::header name l))
  :hints (("Goal" :in-theory (enable acl2::header-unguarded acl2::header))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund acl2::default-unguarded (name l)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable dimensions default)))))
  (if (or (array1p name l)
          (array2p name l))
      ;; normal case:
      (cadr (assoc-keyword :default (cdr (header name l))))
    (acl2::car-unguarded (acl2::cdr-unguarded (acl2::assoc-keyword-unguarded :default (acl2::cdr-unguarded (acl2::header-unguarded name l)))))))

(defthm default-unguarded-correct
  (equal (acl2::default-unguarded name l)
         (acl2::default name l))
  :hints (("Goal" :in-theory (enable acl2::default-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I hope this is still fast in the normal case.
;; TOOD: For some reason, I am seeing slow array warnings.
(defund acl2::aref1-unguarded (name l n)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable array1p header dimensions default)))))
  (if (and (symbolp name)
           (array1p name l)
           (natp n)
           (let ((dims (dimensions name l)))
             (and (consp dims)
                  (let ((len (car dims)))
                    (and (natp len)
                         (< n len))))))
      ;; hope this is fast:
      (aref1 name l n)
    (let ((x (and (not (eq n :header))
                  (acl2::assoc-equal-unguarded n l))))
      (cond ((null x) (acl2::default-unguarded name l))
            (t (acl2::cdr-unguarded x))))))

(defthm aref1-unguarded-correct
  (equal (acl2::aref1-unguarded name l n)
         (acl2::aref1 name l n))
  :hints (("Goal" :in-theory (enable acl2::aref1-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::32-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded (opcode)
  (declare (xargs :guard t))
  (acl2::aref1-unguarded 'x86isa::32-bit-mode-one-byte-has-modr/m
                         x86isa::*32-bit-mode-one-byte-has-modr/m-ar*
                         opcode))

(defthm x86isa::32-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded-correct
  (equal (x86isa::32-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded opcode)
         (x86isa::32-bit-mode-one-byte-opcode-modr/m-p$inline opcode))
  :hints (("Goal" :in-theory (e/d (x86isa::32-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded
                                   x86isa::32-bit-mode-one-byte-opcode-modr/m-p$inline)
                                  (aref1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded (opcode)
  (declare (xargs :guard t))
  (acl2::aref1-unguarded 'x86isa::64-bit-mode-one-byte-has-modr/m
                         x86isa::*64-bit-mode-one-byte-has-modr/m-ar*
                         opcode))

(defthm x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded-correct
  (equal (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded opcode)
         (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline opcode))
  :hints (("Goal" :in-theory (e/d (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded
                                   x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline)
                                  (aref1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::one-byte-opcode-modr/m-p$inline-unguarded (proc-mode opcode)
  (declare (xargs :guard t))
  (if (equal proc-mode 0)
      (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded opcode)
    (x86isa::32-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded opcode)))

(defthm x86isa::one-byte-opcode-modr/m-p$inline-unguarded-correct
  (equal (x86isa::one-byte-opcode-modr/m-p$inline-unguarded proc-mode opcode)
         (x86isa::one-byte-opcode-modr/m-p$inline proc-mode opcode))
  :hints (("Goal" :in-theory (enable x86isa::one-byte-opcode-modr/m-p$inline-unguarded
                                     x86isa::one-byte-opcode-modr/m-p$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::64-bit-mode-two-byte-opcode-modr/m-p-unguarded (x86isa::mandatory-prefix x86isa::opcode)
  (declare (xargs :guard t))
  (case x86isa::mandatory-prefix
    (102 (acl2::aref1-unguarded 'x86isa::64-bit-mode-two-byte-66-has-modr/m
                x86isa::*64-bit-mode-two-byte-66-has-modr/m-ar*
                x86isa::opcode))
    (243 (acl2::aref1-unguarded 'x86isa::64-bit-mode-two-byte-f3-has-modr/m
                x86isa::*64-bit-mode-two-byte-f3-has-modr/m-ar*
                x86isa::opcode))
    (242 (acl2::aref1-unguarded 'x86isa::64-bit-mode-two-byte-f2-has-modr/m
                x86isa::*64-bit-mode-two-byte-f2-has-modr/m-ar*
                x86isa::opcode))
    (t
     (acl2::aref1-unguarded
      'x86isa::64-bit-mode-two-byte-no-prefix-has-modr/m
      x86isa::*64-bit-mode-two-byte-no-prefix-has-modr/m-ar*
      x86isa::opcode))))

(defthm x86isa::64-bit-mode-two-byte-opcode-modr/m-p-unguarded-correct
  (equal (x86isa::64-bit-mode-two-byte-opcode-modr/m-p-unguarded x86isa::mandatory-prefix x86isa::opcode)
         (x86isa::64-bit-mode-two-byte-opcode-modr/m-p x86isa::mandatory-prefix x86isa::opcode))
  :hints (("Goal" :in-theory (e/d (x86isa::64-bit-mode-two-byte-opcode-modr/m-p-unguarded
                                   x86isa::64-bit-mode-two-byte-opcode-modr/m-p)
                                  (aref1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::32-bit-mode-two-byte-opcode-modr/m-p-unguarded (x86isa::mandatory-prefix x86isa::opcode)
  (declare (xargs :guard t))
  (case x86isa::mandatory-prefix
    (102 (acl2::aref1-unguarded 'x86isa::32-bit-mode-two-byte-66-has-modr/m
                x86isa::*32-bit-mode-two-byte-66-has-modr/m-ar*
                x86isa::opcode))
    (243 (acl2::aref1-unguarded 'x86isa::32-bit-mode-two-byte-f3-has-modr/m
                x86isa::*32-bit-mode-two-byte-f3-has-modr/m-ar*
                x86isa::opcode))
    (242 (acl2::aref1-unguarded 'x86isa::32-bit-mode-two-byte-f2-has-modr/m
                x86isa::*32-bit-mode-two-byte-f2-has-modr/m-ar*
                x86isa::opcode))
    (t
     (acl2::aref1-unguarded
      'x86isa::32-bit-mode-two-byte-no-prefix-has-modr/m
      x86isa::*32-bit-mode-two-byte-no-prefix-has-modr/m-ar*
      x86isa::opcode))))

(defthm x86isa::32-bit-mode-two-byte-opcode-modr/m-p-unguarded-correct
  (equal (x86isa::32-bit-mode-two-byte-opcode-modr/m-p-unguarded x86isa::mandatory-prefix x86isa::opcode)
         (x86isa::32-bit-mode-two-byte-opcode-modr/m-p x86isa::mandatory-prefix x86isa::opcode))
  :hints (("Goal" :in-theory (e/d (x86isa::32-bit-mode-two-byte-opcode-modr/m-p-unguarded
                                   x86isa::32-bit-mode-two-byte-opcode-modr/m-p)
                                  (aref1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::two-byte-opcode-modr/m-p$inline-unguarded (proc-mode x86isa::mandatory-prefix x86isa::opcode)
  (declare (xargs :guard t))
  (cond ((equal proc-mode 0)
         (x86isa::64-bit-mode-two-byte-opcode-modr/m-p-unguarded
          x86isa::mandatory-prefix
          x86isa::opcode))
        (t (x86isa::32-bit-mode-two-byte-opcode-modr/m-p-unguarded
            x86isa::mandatory-prefix
            x86isa::opcode))))

(defthm x86isa::two-byte-opcode-modr/m-p$inline-unguarded-correct
  (equal (x86isa::two-byte-opcode-modr/m-p$inline-unguarded proc-mode x86isa::mandatory-prefix x86isa::opcode)
         (x86isa::two-byte-opcode-modr/m-p$inline proc-mode x86isa::mandatory-prefix x86isa::opcode))
  :hints (("Goal" :in-theory (enable x86isa::two-byte-opcode-modr/m-p$inline-unguarded
                                     x86isa::two-byte-opcode-modr/m-p$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::check-instruction-length$inline-unguarded (start-rip temp-rip delta-rip)
  (declare (xargs :guard t))
  (b* ((start-rip (ifix start-rip))
       (temp-rip (ifix temp-rip))
       (delta-rip (nfix delta-rip))
       (end-rip
        (+ temp-rip
           delta-rip))
       (length
        (- end-rip
           start-rip)))
    (and (> length 15) length)))

(defthm x86isa::check-instruction-length$inline-unguarded-correct
  (equal (x86isa::check-instruction-length$inline-unguarded start-rip temp-rip delta-rip)
         (x86isa::check-instruction-length$inline start-rip temp-rip delta-rip))
  :hints (("Goal" :in-theory (enable x86isa::check-instruction-length$inline-unguarded
                                     x86isa::check-instruction-length$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::add-af-spec32$inline-unguarded (dst src)
  (declare (xargs :guard t))
  (x86isa::add-af-spec32$inline (bvchop 32 (ifix dst)) (bvchop 32 (ifix src))))

(defthm x86isa::add-af-spec32$inline-unguarded-correct
  (equal (x86isa::add-af-spec32$inline-unguarded dst src)
         (x86isa::add-af-spec32$inline dst src))
  :hints (("Goal" :in-theory (enable x86isa::add-af-spec32$inline-unguarded
                                     x86isa::add-af-spec32$inline))))

(defund x86isa::add-af-spec64$inline-unguarded (dst src)
  (declare (xargs :guard t))
  (x86isa::add-af-spec64$inline (bvchop 64 (ifix dst)) (bvchop 64 (ifix src))))

(defthm x86isa::add-af-spec64$inline-unguarded-correct
  (equal (x86isa::add-af-spec64$inline-unguarded dst src)
         (x86isa::add-af-spec64$inline dst src))
  :hints (("Goal" :in-theory (enable x86isa::add-af-spec64$inline-unguarded
                                     x86isa::add-af-spec64$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sub-af-spec32$inline-unguarded (dst src)
  (declare (xargs :guard t))
  (x86isa::sub-af-spec32$inline (bvchop 32 (ifix dst)) (bvchop 32 (ifix src))))

(defthm x86isa::sub-af-spec32$inline-unguarded-correct
  (equal (x86isa::sub-af-spec32$inline-unguarded dst src)
         (x86isa::sub-af-spec32$inline dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-af-spec32$inline-unguarded
                                     x86isa::sub-af-spec32$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sub-cf-spec32-unguarded (dst src)
  (declare (xargs :guard t))
  (bool->bit (<-unguarded dst src)))

(defthm x86isa::sub-cf-spec32-unguarded-correct
  (equal (x86isa::sub-cf-spec32-unguarded dst src)
         (x86isa::sub-cf-spec32 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec32-unguarded
                                     x86isa::sub-cf-spec32))))

(defund x86isa::sub-cf-spec64-unguarded (dst src)
  (declare (xargs :guard t))
  (bool->bit (<-unguarded dst src)))

(defthm x86isa::sub-cf-spec64-unguarded-correct
  (equal (x86isa::sub-cf-spec64-unguarded dst src)
         (x86isa::sub-cf-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec64-unguarded
                                     x86isa::sub-cf-spec64))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sub-sf-spec32-unguarded (dst src)
  (declare (xargs :guard t))
  (x86isa::sub-sf-spec32 (bvchop 32 (ifix dst)) (bvchop 32 (ifix src))))

(defthm x86isa::sub-sf-spec32-unguarded-correct
  (equal (x86isa::sub-sf-spec32-unguarded dst src)
         (x86isa::sub-sf-spec32 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-sf-spec32-unguarded
                                     x86isa::sub-sf-spec32))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sub-of-spec32-unguarded (dst src)
  (declare (xargs :guard t))
  (x86isa::sub-of-spec32 (bvchop 32 (ifix dst)) (bvchop 32 (ifix src))))

(defthm x86isa::sub-of-spec32-unguarded-correct
  (equal (x86isa::sub-of-spec32-unguarded dst src)
         (x86isa::sub-of-spec32 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-of-spec32-unguarded
                                     x86isa::sub-of-spec32))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sub-pf-spec32-unguarded (dst src)
  (declare (xargs :guard t))
  (x86isa::sub-pf-spec32 (bvchop 32 (ifix dst)) (bvchop 32 (ifix src))))

(defthm x86isa::sub-pf-spec32-unguarded-correct
  (equal (x86isa::sub-pf-spec32-unguarded dst src)
         (x86isa::sub-pf-spec32 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-pf-spec32-unguarded
                                     x86isa::sub-pf-spec32))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::sub-zf-spec32-unguarded (dst src)
  (declare (xargs :guard t))
  (bool->bit (equal src dst)))

(defthm x86isa::sub-zf-spec32-unguarded-correct
  (equal (x86isa::sub-zf-spec32-unguarded dst src)
         (x86isa::sub-zf-spec32 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec32-unguarded
                                     x86isa::sub-zf-spec32))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund x86isa::get-one-byte-prefix-array-code-unguarded (byte)
  (declare (xargs :guard t))
  (aref1-unguarded 'x86isa::one-byte-prefixes-group-code-info
                   x86isa::*one-byte-prefixes-group-code-info-ar*
                   (bvchop-unguarded 8 byte) ; how fast is stuff like this?  make a separate version that is usually applied to something that needs no chopping?
                   ))

(defthm x86isa::get-one-byte-prefix-array-code-unguarded-correct
  (equal (x86isa::get-one-byte-prefix-array-code-unguarded byte)
         (x86isa::get-one-byte-prefix-array-code byte))
  :hints (("Goal" :in-theory (enable x86isa::get-one-byte-prefix-array-code-unguarded
                                     x86isa::get-one-byte-prefix-array-code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun x86isa::64-bit-compute-mandatory-prefix-for-two-byte-opcode$inline-unguarded (x86isa::opcode x86isa::prefixes)
  (declare (xargs :guard t ))
  (let ((x86isa::rep-pfx (the (unsigned-byte 8)
                           (x86isa::prefixes->rep-unguarded x86isa::prefixes))))
    (if (not (eql x86isa::rep-pfx 0))
        (if (or (and (equal x86isa::rep-pfx 243)
                     (aref1-unguarded 'x86isa::64-bit-mode-two-byte-f3-ok
                                      x86isa::*64-bit-mode-two-byte-f3-ok-ar*
                                      x86isa::opcode))
                (and (equal x86isa::rep-pfx 242)
                     (aref1-unguarded 'x86isa::64-bit-mode-two-byte-f2-ok
                                      x86isa::*64-bit-mode-two-byte-f2-ok-ar*
                                      x86isa::opcode)))
            x86isa::rep-pfx
          0)
      (let ((x86isa::opr-pfx (the (unsigned-byte 8)
                               (x86isa::prefixes->opr-unguarded x86isa::prefixes))))
        (if (not (eql x86isa::opr-pfx 0))
            (if (aref1-unguarded 'x86isa::64-bit-mode-two-byte-66-ok
                                 x86isa::*64-bit-mode-two-byte-66-ok-ar*
                                 x86isa::opcode)
                x86isa::opr-pfx
              0)
          0)))))

(defthm 64-bit-compute-mandatory-prefix-for-two-byte-opcode-unguarded-correct
  (equal (x86isa::64-bit-compute-mandatory-prefix-for-two-byte-opcode$inline-unguarded x86isa::opcode x86isa::prefixes)
         (x86isa::64-bit-compute-mandatory-prefix-for-two-byte-opcode$inline x86isa::opcode x86isa::prefixes))
  :hints (("Goal" :in-theory (enable x86isa::64-bit-compute-mandatory-prefix-for-two-byte-opcode))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bv-array-read-chunk-little-unguarded (element-count element-size array-len index array)
  (declare (xargs :guard t))
  (if (zp-unguarded element-count)
      0
    (bvcat-unguarded (binary-*-unguarded element-size (binary-+-unguarded -1 element-count))
                     (bv-array-read-chunk-little-unguarded (binary-+-unguarded -1 element-count) element-size array-len (binary-+-unguarded 1 index) array)
                     element-size
                     (bv-array-read-unguarded element-size array-len index array))))

(defthm bv-array-read-chunk-little-unguarded-correct
  (equal (bv-array-read-chunk-little-unguarded element-count element-size array-len index array)
         (bv-array-read-chunk-little element-count element-size array-len index array))
  :hints (("Goal" :in-theory (enable bv-array-read-chunk-little-unguarded
                                     bv-array-read-chunk-little))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *axe-evaluator-x86-fns-and-aliases*
  (append '(implies ; push back to basic evaluator?
            (integer-range-p integer-range-p-unguarded)
            x86isa::canonical-address-p$inline ; unguarded
            (bitops::part-select-width-low$inline bitops::part-select-width-low$inline-unguarded)
            (lookup lookup-equal-unguarded)
            (x86isa::n03$inline x86isa::n03$inline-unguarded) ; other sizes?
            (x86isa::n06$inline x86isa::n06$inline-unguarded)
            (x86isa::n08$inline x86isa::n08$inline-unguarded)
            (x86isa::n32$inline x86isa::n32$inline-unguarded)
            (x86isa::n64$inline x86isa::n64$inline-unguarded)
            (x86isa::n08-to-i08$inline x86isa::n08-to-i08$inline-unguarded) ; other sizes?
            (x86isa::n32-to-i32$inline x86isa::n32-to-i32$inline-unguarded)
            (x86isa::n64-to-i64$inline x86isa::n64-to-i64$inline-unguarded)
            (x86isa::2bits-fix x86isa::2bits-fix-unguarded)
            (x86isa::4bits-fix x86isa::4bits-fix-unguarded)
            (x86isa::8bits-fix x86isa::8bits-fix-unguarded)
            (x86isa::10bits-fix x86isa::10bits-fix-unguarded)
            (loghead$inline loghead$inline-unguarded)
            (logapp logapp-unguarded) ; for flags
            (acl2::packbv acl2::packbv-unguarded)
            (bv-array-read-chunk-little bv-array-read-chunk-little-unguarded)
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
            (x86isa::!prefixes->opr$inline x86isa::!prefixes->opr-unguarded)
            (x86isa::!prefixes->rep$inline x86isa::!prefixes->rep-unguarded)
            (x86isa::get-one-byte-prefix-array-code x86isa::get-one-byte-prefix-array-code-unguarded)
            power-of-2p
            logmaskp
            bfix$inline
            bool->bit$inline
            (evenp evenp-unguarded)
            (logcount logcount-unguarded)
            (logtail$inline logtail$inline-unguarded)
            (zip zip-unguarded)
            (ash ash-unguarded)
            (acl2::firstn acl2::firstn-unguarded)
            (logbitp logbitp-unguarded)
            (binary-logand binary-logand-unguarded)
            (binary-logior binary-logior-unguarded)
            (nonnegative-integer-quotient nonnegative-integer-quotient-unguarded)
            (x86isa::modr/m-fix$inline x86isa::modr/m-fix$inline-unguarded)
            (x86isa::modr/m->r/m$inline x86isa::modr/m->r/m$inline-unguarded)
            (x86isa::modr/m->reg$inline x86isa::modr/m->reg$inline-unguarded)
            (x86isa::modr/m->mod$inline x86isa::modr/m->mod$inline-unguarded)
            (x86isa::rflagsbits-fix$inline x86isa::rflagsbits-fix$inline-unguarded)
            (x86isa::rflagsbits->af$inline x86isa::rflagsbits->af$inline-unguarded)
            (x86isa::rflagsbits->cf$inline x86isa::rflagsbits->cf$inline-unguarded)
            (x86isa::rflagsbits->pf$inline x86isa::rflagsbits->pf$inline-unguarded)
            (x86isa::rflagsbits->sf$inline x86isa::rflagsbits->sf$inline-unguarded)
            (x86isa::rflagsbits->of$inline x86isa::rflagsbits->of$inline-unguarded)
            (x86isa::rflagsbits->zf$inline x86isa::rflagsbits->zf$inline-unguarded)
            (x86isa::!rflagsbits->af$inline x86isa::!rflagsbits->af$inline-unguarded)
            (x86isa::add-af-spec32$inline x86isa::add-af-spec32$inline-unguarded)
            (x86isa::add-af-spec64$inline x86isa::add-af-spec64$inline-unguarded)
            (x86isa::sub-af-spec32$inline x86isa::sub-af-spec32$inline-unguarded)
            (x86isa::sub-cf-spec32 x86isa::sub-cf-spec32-unguarded)
            (x86isa::sub-cf-spec64 x86isa::sub-cf-spec64-unguarded)
            (x86isa::sub-of-spec32 x86isa::sub-of-spec32-unguarded)
            (x86isa::sub-pf-spec32 x86isa::sub-pf-spec32-unguarded)
            (x86isa::sub-sf-spec32 x86isa::sub-sf-spec32-unguarded)
            (x86isa::sub-zf-spec32 x86isa::sub-zf-spec32-unguarded)
            (x86isa::pf-spec8$inline x86isa::pf-spec8$inline-unguarded)
            (x86isa::sf-spec8$inline x86isa::sf-spec8$inline-unguarded)
            (x86isa::sf-spec16$inline x86isa::sf-spec16$inline-unguarded)
            (x86isa::sf-spec32$inline x86isa::sf-spec32$inline-unguarded)
            (x86isa::sf-spec64$inline x86isa::sf-spec64$inline-unguarded)
            (x86isa::cf-spec32$inline x86isa::cf-spec32$inline-unguarded)
            (x86isa::cf-spec64$inline x86isa::cf-spec64$inline-unguarded)
            (x86isa::of-spec32$inline x86isa::of-spec32$inline-unguarded)
            (x86isa::of-spec64$inline x86isa::of-spec64$inline-unguarded)
            (x86isa::pf-spec32$inline x86isa::pf-spec32$inline-unguarded)
            (x86isa::pf-spec64$inline x86isa::pf-spec64$inline-unguarded)
            (x86isa::sf-spec32$inline x86isa::sf-spec32$inline-unguarded)
            (x86isa::sf-spec64$inline x86isa::sf-spec64$inline-unguarded)
            (x86isa::zf-spec$inline x86isa::zf-spec$inline-unguarded)
            (x86isa::x86-decode-sib-p x86isa::x86-decode-sib-p-unguarded)
            (x86isa::sib-fix$inline x86isa::sib-fix$inline-unguarded)
            (x86isa::sib->base$inline x86isa::sib->base$inline-unguarded)
            (x86isa::sib->index$inline x86isa::sib->index$inline-unguarded)
            (x86isa::sib->scale$inline x86isa::sib->scale$inline-unguarded)
            (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded)
            (x86isa::32-bit-mode-one-byte-opcode-modr/m-p$inline x86isa::32-bit-mode-one-byte-opcode-modr/m-p$inline-unguarded)
            (x86isa::one-byte-opcode-modr/m-p$inline x86isa::one-byte-opcode-modr/m-p$inline-unguarded)
            (x86isa::64-bit-mode-two-byte-opcode-modr/m-p x86isa::64-bit-mode-two-byte-opcode-modr/m-p-unguarded)
            (x86isa::check-instruction-length$inline x86isa::check-instruction-length$inline-unguarded)
            (x86isa::two-byte-opcode-modr/m-p$inline x86isa::two-byte-opcode-modr/m-p$inline-unguarded)
            (acl2::aref1 acl2::aref1-unguarded)
            (acl2::negated-elems-listp acl2::negated-elems-listp-unguarded)
            (x86isa::64-bit-compute-mandatory-prefix-for-two-byte-opcode$inline x86isa::64-bit-compute-mandatory-prefix-for-two-byte-opcode$inline-unguarded)
            )
          *axe-evaluator-basic-fns-and-aliases*))

;; Makes the evaluator (also checks that each alias given is equivalent to its function):
(make-evaluator-simple x86 *axe-evaluator-x86-fns-and-aliases*)
