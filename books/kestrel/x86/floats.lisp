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
(include-book "kestrel/axe/axe-syntax" :dir :system) ; todo: split out such rules
(include-book "kestrel/axe/axe-syntax-functions" :dir :system) ; todo: split out such rules
(include-book "projects/x86isa/utils/fp-structures" :dir :system)
(include-book "projects/x86isa/machine/instructions/fp/cmp-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/fp/mxcsr" :dir :system)
(include-book "projects/x86isa/machine/state" :dir :system) ; for xr
(include-book "kestrel/bv/bvchop" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
;(include-book "kestrel/x86/rflags-spec-sub" :dir :system)
;(include-book "kestrel/x86/read-and-write" :dir :system)
;(include-book "kestrel/x86/register-readers-and-writers64" :dir :system)
(include-book "projects/x86isa/machine/instructions/fp/add-mul-spec" :dir :system) ; for dazify
(local (include-book "kestrel/bv/logapp" :dir :system)) ; for ACL2::LOGHEAD-BECOMES-BVCHOP
(local (include-book "kestrel/bv/logtail" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

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

(defthm fp-decode-of-bvchop-arg1
  (implies (and (< (+ exp-width frac-width) size)
                (posp frac-width)
                (natp exp-width)
                (natp size))
           (equal (x86isa::fp-decode (bvchop size x) exp-width frac-width)
                  (x86isa::fp-decode x exp-width frac-width)))
  :hints (("Goal" :in-theory (enable x86isa::fp-decode))))

(defthm sse-cmp-of-bvchop-arg2
  (implies (and (< (+ exp-width frac-width) size)
                (posp frac-width)
                (natp exp-width)
                (natp size))
           (equal (x86isa::sse-cmp operation (bvchop size op1) op2 mxcsr exp-width frac-width)
                  (x86isa::sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp))))

(defthm sse-cmp-of-bvchop-arg3
  (implies (and (< (+ exp-width frac-width) size)
                (posp frac-width)
                (natp exp-width)
                (natp size))
           (equal (x86isa::sse-cmp operation op1 (bvchop size op2) mxcsr exp-width frac-width)
                  (x86isa::sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp))))

(defthm sse-cmp-of-bvchop-arg4
  (implies (and (<= 32 size)
                (natp size))
           (equal (x86isa::sse-cmp operation op1 op2 (bvchop size mxcsr) exp-width frac-width)
                  (x86isa::sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp))))

;move
(defthm ash-of-1-becomes-expt2
  (implies (natp c)
           (equal (ash 1 c)
                  (expt 2 c)))
  :hints (("Goal" :in-theory (enable ash))))

(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/lg" :dir :system))

(defthm unsigned-byte-p-when-quotep-arg2
  (implies (and (syntaxp (quotep k))
                (natp k))
           (equal (unsigned-byte-p size k)
                  (and (natp size)
                       (<= (integer-length k) size))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p integer-length))))

(local (in-theory (disable expt)))

;gen?
(defthm unsigned-byte-p-of-mv-nth-1-of-sse-cmp-special
  (implies (and (< (+ exp-width frac-width) size)
                (<= 3 size)
                (posp frac-width)
                (natp exp-width)
                (natp size))
           (unsigned-byte-p size (mv-nth 1 (x86isa::sse-cmp-special kind1 sign1 kind2 sign2 exp-width frac-width operation))))
  :hints (("Goal" :in-theory (e/d (x86isa::sse-cmp-special) (expt)))))

;gen
(defthm unsigned-byte-p-of-mv-nth-1-of-sse-cmp-32
  (implies (and (< (+ exp-width frac-width) 32)
                (posp frac-width)
                (natp exp-width)
                (unsigned-byte-p 32 mxcsr))
           (unsigned-byte-p 32 (mv-nth 1 (x86isa::sse-cmp operation op1 op2 mxcsr exp-width frac-width))))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp))))

;also prove for op8?
(defthm unsigned-byte-p-of-mv-nth-1-of-sse-cmp-of-OP-UCOMI
  (implies (and (<= 3 size)
                (natp size))
           (unsigned-byte-p size (mv-nth 1 (x86isa::sse-cmp x86isa::*OP-UCOMI* op1 op2 mxcsr exp-width frac-width))))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp sse-cmp-special))))

(defthm mv-nth-1-of-sse-cmp-of-mv-nth-2-of-sse-cmp
  (equal (mv-nth 1 (x86isa::sse-cmp operationa op1a op2a (mv-nth 2 (x86isa::sse-cmp operationb op1b op2b mxcsr exp-widthb frac-widthb)) exp-widtha frac-widtha))
         (mv-nth 1 (x86isa::sse-cmp operationa op1a op2a mxcsr exp-widtha frac-widtha)))
  :hints (("Goal" :in-theory (enable x86isa::sse-cmp))))

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

;; todo: move some of these:

;drop!
(include-book "kestrel/booleans/boolif" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
;drop!
(defthm boolif-of-myif-arg1-true
  (equal (boolif (myif test x1 x2) y z)
         (boolif (boolif test x1 x2) y z))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm not-denormal-exception-when-nan
  (implies (or (equal kind1 'x86isa::snan)
               (equal kind1 'x86isa::qnan)
               (equal kind1 'x86isa::indef)
               (equal kind2 'x86isa::snan)
               (equal kind2 'x86isa::qnan)
               (equal kind2 'x86isa::indef))
           (not (x86isa::denormal-exception kind1 kind2)))
  :hints (("Goal" :in-theory (enable x86isa::denormal-exception))))

;;(defstub stub (x y) t)
;; (thm
;;   (implies (and (equal (x86isa::mxcsrbits->daz$inline mxcsr) 0)
;;                 (equal (x86isa::mxcsrbits->im$inline mxcsr) 1)
;;                 (equal (x86isa::mxcsrbits->dm$inline mxcsr) 1))
;;            (equal (EQUAL '0 (MV-NTH '1 (SSE-CMP '9 op1 op2 mxcsr '8 '23)))
;;                   (stub x y)))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (enable SSE-CMP
;;                                      SSE-CMP-SPECIAL))))

;; essentialy, this puts in < instead of > -- todo make better named normal forms for such things
;non-axe
(defthmd equal-of-0-and-mv-nth-1-of-sse-cmp-of-ucomi
  (implies (and (equal (x86isa::mxcsrbits->daz$inline mxcsr) 0)
                (equal (x86isa::mxcsrbits->im$inline mxcsr) 1)
                (equal (x86isa::mxcsrbits->dm$inline mxcsr) 1))
           (equal (equal 0 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 1 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :hints (("Goal" :in-theory (enable sse-cmp sse-cmp-special))))

;; this puts the syntactically smaller op first
(defthmd equal-of-0-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe
  (implies (and (axe-syntaxp (acl2::heavier-dag-term op1 op2))
                (equal (x86isa::mxcsrbits->daz$inline mxcsr) 0)
                (equal (x86isa::mxcsrbits->im$inline mxcsr) 1)
                (equal (x86isa::mxcsrbits->dm$inline mxcsr) 1))
           (equal (equal 0 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 1 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :hints (("Goal" :in-theory (enable sse-cmp sse-cmp-special))))

;; this puts the syntactically smaller op first
(defthmd equal-of-1-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder
  (implies (and (axe-syntaxp (acl2::smaller-termp op1 op2))
                (equal (x86isa::mxcsrbits->daz$inline mxcsr) 0)
                (equal (x86isa::mxcsrbits->im$inline mxcsr) 1)
                (equal (x86isa::mxcsrbits->dm$inline mxcsr) 1))
           (equal (equal 1 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 0 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :hints (("Goal" :in-theory (enable sse-cmp sse-cmp-special))))

;; this puts the syntactically smaller op first
(defthmd equal-of-1-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe
  (implies (and (axe-syntaxp (acl2::heavier-dag-term op1 op2))
                (equal (x86isa::mxcsrbits->daz$inline mxcsr) 0)
                (equal (x86isa::mxcsrbits->im$inline mxcsr) 1)
                (equal (x86isa::mxcsrbits->dm$inline mxcsr) 1))
           (equal (equal 1 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 0 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :hints (("Goal" :use equal-of-1-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder)))

;non-axe
(defthmd equal-of-7-and-mv-nth-1-of-sse-cmp-of-ucomi
  (implies (syntaxp (acl2::smaller-termp op1 op2))
           (equal (equal 7 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 7 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable sse-cmp sse-cmp-special))))

(defthmd equal-of-7-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe
  (implies (axe-syntaxp (acl2::heavier-dag-term op1 op2))
           (equal (equal 7 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 7 (mv-nth 1 (x86isa::sse-cmp x86isa::*op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :hints (("Goal" :use equal-of-7-and-mv-nth-1-of-sse-cmp-of-ucomi
           :in-theory (disable equal-of-7-and-mv-nth-1-of-sse-cmp-of-ucomi))))

;dup??
(defthm sse-daz-of-nil-arg4
  (equal (X86ISA::SSE-DAZ kind exp frac nil)
         (mv kind exp frac))
  :hints (("Goal" :in-theory (enable X86ISA::SSE-DAZ))))

;strengthen?
(defthm not-equal-of-7-and-mv-nth-1-of-sse-cmp
  (implies (and (not (is-nan (mv-nth 0 (fp-decode x exp-width frac-width))))
                (not (is-nan (mv-nth 0 (fp-decode y exp-width frac-width))))
                (equal (x86isa::mxcsrbits->daz$inline mxcsr) 0))
           (not (equal 7 (mv-nth 1 (sse-cmp x86isa::*op-ucomi* y x mxcsr exp-width frac-width)))))
  :hints (("Goal" :in-theory (enable sse-cmp sse-cmp-special is-nan))))

(defthm sse-daz-of-nil
  (equal (X86ISA::SSE-DAZ kind exp frac nil)
         (mv kind exp frac))
  :hints (("Goal" :in-theory (enable X86ISA::SSE-DAZ))))

(defthm X86ISA::MXCSRBITS->IM-of-if
  (equal (X86ISA::MXCSRBITS->IM (if test x86 x86_2))
         (if test (X86ISA::MXCSRBITS->IM x86) (X86ISA::MXCSRBITS->IM x86_2))))

(defthm X86ISA::MXCSRBITS->DM-of-if
  (equal (X86ISA::MXCSRBITS->DM (if test x86 x86_2))
         (if test (X86ISA::MXCSRBITS->DM x86) (X86ISA::MXCSRBITS->DM x86_2))))

(defthm X86ISA::MXCSRBITS->DAZ-of-if
  (equal (X86ISA::MXCSRBITS->DAZ (if test x86 x86_2))
         (if test (X86ISA::MXCSRBITS->DAZ x86) (X86ISA::MXCSRBITS->DAZ x86_2))))

;todo: more like this, or look at how this is proved
(defthm MXCSRBITS->IM-of-!MXCSRBITS->IE
  (equal (X86ISA::MXCSRBITS->IM$INLINE (X86ISA::!MXCSRBITS->IE$INLINE bit mxcsr))
         (X86ISA::MXCSRBITS->IM$INLINE mxcsr)))

(defthm MXCSRBITS->IM-of-!MXCSRBITS->DE
  (equal (X86ISA::MXCSRBITS->IM$INLINE (X86ISA::!MXCSRBITS->DE$INLINE bit mxcsr))
         (X86ISA::MXCSRBITS->IM$INLINE mxcsr)))

(defthm MXCSRBITS->DM-of-!MXCSRBITS->DE
  (equal (X86ISA::MXCSRBITS->DM$INLINE (X86ISA::!MXCSRBITS->DE$INLINE bit mxcsr))
         (X86ISA::MXCSRBITS->DM$INLINE mxcsr)))

(defthm MXCSRBITS->DM-of-!MXCSRBITS->IE
  (equal (X86ISA::MXCSRBITS->DM$INLINE (X86ISA::!MXCSRBITS->IE$INLINE bit mxcsr))
         (X86ISA::MXCSRBITS->DM$INLINE mxcsr)))

(defthm MXCSRBITS->DAZ-of-!MXCSRBITS->IE
  (equal (X86ISA::MXCSRBITS->DAZ$INLINE (X86ISA::!MXCSRBITS->IE$INLINE bit mxcsr))
         (X86ISA::MXCSRBITS->DAZ$INLINE mxcsr)))

(defthm MXCSRBITS->DAZ-of-!MXCSRBITS->DE
  (equal (X86ISA::MXCSRBITS->DAZ$INLINE (X86ISA::!MXCSRBITS->DE$INLINE bit mxcsr))
         (X86ISA::MXCSRBITS->DAZ$INLINE mxcsr)))

(defthm integerp-of-!MXCSRBITS->IE
  (integerp (X86ISA::!MXCSRBITS->IE$INLINE bit mxcsr)))

(defthm unsigned-byte-p-32-of-!MXCSRBITS->IE
  (unsigned-byte-p 32 (X86ISA::!MXCSRBITS->IE$INLINE bit mxcsr)))

(defthm unsigned-byte-p-32-of-!MXCSRBITS->DE
  (unsigned-byte-p 32 (X86ISA::!MXCSRBITS->DE$INLINE bit mxcsr)))

(defthm integerp-of-!MXCSRBITS->DE
  (integerp (X86ISA::!MXCSRBITS->DE$INLINE bit mxcsr)))

(acl2::def-constant-opener X86ISA::FP-DECODE)
(acl2::def-constant-opener X86ISA::FP-TO-RAT)
(acl2::def-constant-opener rtl::bias)
(acl2::def-constant-opener rtl::expw)

;rename
(defthm <-of-fp-to-rat
  (implies (and (natp frac)
                (natp exp)
                (not (equal 0 exp))
                (natp frac-width)
                (equal 8 exp-width) ; todo: gen
                )
           (equal (< (x86isa::fp-to-rat sign exp frac bias exp-width frac-width) 0)
                  (and (not (equal 0 sign))
                       (if (equal 0 exp)
                           (not (equal 0 frac))
                         (<= exp (x86isa::fp-max-finite-exp exp-width))))))
  :hints (("Goal" :in-theory (enable x86isa::fp-to-rat))))

(defthm integerp-of-xr-mxcsr
  (INTEGERP (XR :MXCSR NIL X86)))

(defthm dazify-of-0-arg2
  (equal (rtl::dazify x 0 acl2::f)
         x)
  :hints (("Goal" :in-theory (enable rtl::dazify))))
