; Rules (theorems) relied upon by the Formal Unit Tester
;
; Copyright (C) 2016-2023 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: IN-PROGRESS

(include-book "kestrel/x86/portcullis" :dir :system)
(include-book "kestrel/axe/known-booleans" :dir :system)
(include-book "projects/x86isa/utils/fp-structures" :dir :system)
(include-book "projects/x86isa/machine/instructions/fp/cmp-spec" :dir :system)
(include-book "kestrel/bv/bvchop" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(local (include-book "kestrel/bv/logapp" :dir :system)) ; for ACL2::LOGHEAD-BECOMES-BVCHOP
(local (include-book "kestrel/bv/logtail" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
;(include-book "kestrel/x86/rflags-spec-sub" :dir :system)
;(include-book "kestrel/x86/read-and-write" :dir :system)
;(include-book "kestrel/x86/register-readers-and-writers64" :dir :system)

(in-theory (disable acl2::loghead))

(local (in-theory (enable ACL2::LOGTAIL-OF-BVCHOP)))

;; Recognize a NaN
(defund is-nan (val)
  (declare (xargs :guard t))
  (or (equal 'x86isa::snan val)
      (equal 'x86isa::qnan val)
      ;; a special type of qnan:
      (equal 'x86isa::indef val)))

(acl2::add-known-boolean is-nan)

;; Only needed for Axe.
(defthmd booleanp-of-is-nan
  (booleanp (is-nan val)))

;; May be brittle.  introduce nicer versions of each subexpression?
;; TODO: Have the model just use is-nan?
(defthmd is-nan-intro
  (equal (if (equal 'x86isa::snan val) t (if (equal 'x86isa::qnan val) t (equal 'x86isa::indef val)))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

(theory-invariant (incompatible (:rewrite is-nan-intro) (:definition is-nan)))

(defthm if-of-equal-of-indef-and-is-nan
  (equal (if (equal 'x86isa::indef val) t (is-nan val))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

(defthm if-of-equal-of-qnan-and-is-nan
  (equal (if (equal 'x86isa::qnan val) t (is-nan val))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

(defthm if-of-equal-of-snan-and-is-nan
  (equal (if (equal 'x86isa::snan val) t (is-nan val))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: more
(defthm mxcsrbits->im-of-loghead-32
  (equal (x86isa::mxcsrbits->im (acl2::loghead 32 mxcsr))
         (x86isa::mxcsrbits->im mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->im x86isa::mxcsrbits-fix))))

(defthm mxcsrbits->dm-of-loghead-32
  (equal (x86isa::mxcsrbits->dm (acl2::loghead 32 mxcsr))
         (x86isa::mxcsrbits->dm mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->dm x86isa::mxcsrbits-fix))))

(defthm mxcsrbits->daz-of-loghead-32
  (equal (x86isa::mxcsrbits->daz (acl2::loghead 32 mxcsr))
         (x86isa::mxcsrbits->daz mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->daz x86isa::mxcsrbits-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm mxcsrbits->daz-of-bvchop-32
  (equal (x86isa::mxcsrbits->daz (acl2::bvchop 32 mxcsr))
         (x86isa::mxcsrbits->daz mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->daz x86isa::mxcsrbits-fix))))

(defthm mxcsrbits->daz-of-ifix
  (equal (x86isa::mxcsrbits->daz (ifix mxcsr))
         (x86isa::mxcsrbits->daz mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->daz x86isa::mxcsrbits-fix))))

(defthm mxcsrbits->dm-of-bvchop-32
  (equal (x86isa::mxcsrbits->dm (acl2::bvchop 32 mxcsr))
         (x86isa::mxcsrbits->dm mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->dm x86isa::mxcsrbits-fix))))

(defthm mxcsrbits->dm-of-ifix
  (equal (x86isa::mxcsrbits->dm (ifix mxcsr))
         (x86isa::mxcsrbits->dm mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->dm x86isa::mxcsrbits-fix))))

(defthm mxcsrbits->im-of-bvchop-32
  (equal (x86isa::mxcsrbits->im (acl2::bvchop 32 mxcsr))
         (x86isa::mxcsrbits->im mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->im x86isa::mxcsrbits-fix))))

(defthm mxcsrbits->im-of-ifix
  (equal (x86isa::mxcsrbits->im (ifix mxcsr))
         (x86isa::mxcsrbits->im mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->im x86isa::mxcsrbits-fix))))

;slow?
(defthm not-mv-nth-0-of-sse-cmp
  (implies (and (equal (x86isa::mxcsrbits->daz$inline mxcsr) 0)
                (equal (x86isa::mxcsrbits->dm$inline mxcsr) 1)
                (equal (x86isa::mxcsrbits->im$inline mxcsr) 1))
           (not (mv-nth 0 (x86isa::sse-cmp operation op1 op2 mxcsr exp-width frac-width))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (x86isa::sse-cmp x86isa::sse-cmp-special x86isa::sse-daz
                                                   x86isa::denormal-exception
                                                   is-nan)
                                  (acl2::loghead-becomes-bvchop)))))

;gen?
(defthm mxcsrbits->daz-of-mv-nth-2-of-sse-cmp
  (equal (x86isa::mxcsrbits->daz (mv-nth 2 (x86isa::sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
         (x86isa::mxcsrbits->daz mxcsr))
  :hints (("Goal" :in-theory (e/d (x86isa::sse-cmp x86isa::sse-cmp-special x86isa::denormal-exception)
                                  (acl2::loghead-becomes-bvchop)))))

;gen?
(defthm mxcsrbits->dm-of-mv-nth-2-of-sse-cmp
  (equal (x86isa::mxcsrbits->dm (mv-nth 2 (x86isa::sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
         (x86isa::mxcsrbits->dm mxcsr))
    :hints (("Goal" :in-theory (e/d (x86isa::sse-cmp x86isa::sse-cmp-special x86isa::denormal-exception)
                                  (acl2::loghead-becomes-bvchop)))))

(defthm mxcsrbits->im-of-mv-nth-2-of-sse-cmp
  (equal (x86isa::mxcsrbits->im (mv-nth 2 (x86isa::sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
         (x86isa::mxcsrbits->im mxcsr))
  :hints (("Goal" :in-theory (e/d (x86isa::sse-cmp x86isa::sse-cmp-special x86isa::denormal-exception)
                                  (acl2::loghead-becomes-bvchop)))))

(defthm integerp-of-mv-nth-2-of-sse-cmp
  (integerp (mv-nth 2 (x86isa::sse-cmp operation op1 op2 mxcsr exp-width frac-width))))

;gen
(defthm fp-decode-of-bvchop-arg1-32
  (equal (x86isa::fp-decode (bvchop 32 x) 8 23)
         (x86isa::fp-decode x 8 23))
  :hints (("Goal" :in-theory (enable x86isa::fp-decode))))

(defthm sse-cmp-of-bvchop-arg2-32
  (equal (x86isa::sse-cmp operation (bvchop 32 op1) op2 mxcsr 8 23)
         (x86isa::sse-cmp operation op1 op2 mxcsr 8 23))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp))))

(defthm sse-cmp-of-bvchop-arg3-32
  (equal (x86isa::sse-cmp operation op1 (bvchop 32 op2) mxcsr 8 23)
         (x86isa::sse-cmp operation op1 op2 mxcsr 8 23))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp))))

(defthm sse-cmp-of-bvchop-arg4-32
  (equal (x86isa::sse-cmp operation op1 op2 (bvchop 32 mxcsr) 8 23)
         (x86isa::sse-cmp operation op1 op2 mxcsr 8 23))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp))))

;gen
(defthm unsigned-byte-p-of-mv-nth-1-of-sse-cmp-special-32
  (implies t ; (unsigned-byte-p 32 mxcsr)
           (unsigned-byte-p 32 (mv-nth 1 (x86isa::sse-cmp-special KIND1 SIGN1 KIND2 SIGN2 8 23 OPERATION))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp-special))))

;gen
(defthm unsigned-byte-p-of-mv-nth-1-of-sse-cmp-32
  (implies (unsigned-byte-p 32 mxcsr)
           (unsigned-byte-p 32 (mv-nth 1 (x86isa::sse-cmp operation op1 op2 mxcsr 8 23))))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp))))

(defthm mv-nth-1-of-SSE-CMP-of-SSE-CMP
  (equal (MV-NTH '1 (X86ISA::SSE-CMP operationa op1a op2a (MV-NTH '2 (X86ISA::SSE-CMP operationb op1b op2b mxcsr exp-widthb frac-widthb)) exp-widtha frac-widtha))
         (MV-NTH '1 (X86ISA::SSE-CMP operationa op1a op2a mxcsr exp-widtha frac-widtha)))
  :hints (("Goal" :in-theory (enable X86ISA::SSE-CMP))))

;; compare op with itself
(defthm sse-cmp-of-op-ucomi-same
  (implies (and (equal (x86isa::mxcsrbits->daz$inline mxcsr) 0)
                (equal (x86isa::mxcsrbits->im$inline mxcsr) 1)
                (equal (x86isa::mxcsrbits->dm$inline mxcsr) 1))
           (equal (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op op mxcsr exp-width frac-width))
                  (if (equal (mv-nth 0 (x86isa::fp-decode op exp-width frac-width)) 'x86isa::snan)
                      7
                    (if (equal (mv-nth 0 (x86isa::fp-decode op exp-width frac-width)) 'x86isa::qnan)
                        7
                      (if (equal (mv-nth 0 (x86isa::fp-decode op exp-width frac-width)) 'x86isa::indef)
                          7
                        4)))))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp
                                     x86isa::sse-cmp-special
                                     X86ISA::SSE-DAZ ;todo
                                     ))))

;; introduces X86ISA::SSE-CMP-BASE (rename?)
;; the mxcsr will often not be constant
(acl2::defopeners x86isa::sse-cmp :hyps ((syntaxp (and (quotep x86isa::operation)
                                                       (quotep x86isa::op1)
                                                       (quotep x86isa::op2)
                                                       (quotep x86isa::exp-width)
                                                       (quotep x86isa::frac-width)))))
