; Supporting material for x86 code proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;; unlike most books, this one is in the X86ISA package

;; Supporting material about the x86 model.  Some of this could be moved to the
;; model itself.

(include-book "projects/x86isa/proofs/utilities/app-view/top" :dir :system) ;reduce? needed for the big enable below
(include-book "projects/x86isa/machine/state" :dir :system)
;(include-book "projects/x86isa/machine/state-field-thms" :dir :system)
(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ;for canonical-address-p
(include-book "kestrel/utilities/defopeners" :dir :system)
;(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/utilities/polarity" :dir :system) ; for want-to-weaken
(include-book "kestrel/bv/defs-arith" :dir :system) ;for bvplus
(include-book "kestrel/bv/slice-def" :dir :system)
(include-book "kestrel/bv/defs" :dir :system) ;for bvashr
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "linear-memory") ;drop? but need mv-nth-0-of-rml-size-of-xw-when-app-view
(local (include-book "kestrel/bv/rules10" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/arith" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop, to deal with truncate
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/denominator" :dir :system))
(local (include-book "kestrel/arithmetic-light/numerator" :dir :system))
(local (include-book "kestrel/bv/getbit2" :dir :system))

(defthm unsigned-byte-p-8-of-car-when-byte-listp
  (implies (byte-listp bytes)
           (equal (unsigned-byte-p 8 (car bytes))
                  (consp bytes)))
  :hints (("Goal" :in-theory (enable byte-listp))))

(defthm integerp-of-car-when-byte-listp
  (implies (byte-listp bytes)
           (equal (integerp (car bytes))
                  (consp bytes)))
  :hints (("Goal" :in-theory (enable byte-listp))))

(in-theory (disable GET-PREFIXES-OPENER-LEMMA-ZERO-CNT)) ;for speed

(defthm x86isa::x86p-xw-unforced
  (implies (x86p x86)
           (x86p (xw x86isa::fld x86isa::index value x86))))

(in-theory (disable x86isa::x86p-xw ;does forcing, which causes problems in various places
                    x86isa::x86p-!rip-when-val-is-canonical-address-p ;todo: remove this rule altogether since it is subsumed by x86p-xw
                    ))

(defthm rflags-is-n32p-unforced
  (implies (x86p x86)
           (unsigned-byte-p 32 (xr :rflags i x86)))
  :rule-classes ((:rewrite :corollary (implies (x86p x86)
                                               (unsigned-byte-p 32 (xr :rflags i x86)))
                           :hints (("GOAL" :in-theory (e/d (rflags x86p) nil))))
                 (:type-prescription :corollary (implies (x86p x86)
                                                         (natp (xr :rflags i x86)))
                                     :hints (("GOAL" :in-theory (e/d (rflags x86p) nil))))
                 (:linear :corollary (implies (x86p x86)
                                              (< (xr :rflags i x86) 4294967296))
                          :hints (("GOAL" :in-theory (e/d (rflags x86p) nil))))))

;(in-theory (disable rflags-is-n32p)) ;disable the forced version


;why needed?
;(acl2::defopeners LOAD-PROGRAM-INTO-MEMORY)

;; (acl2::defopeners xr :hyps ((syntaxp (quotep FLD))
;;                             (syntaxp (quotep index))
;;                             (syntaxp (quotep x86))))

;; (defthm xr-xw-intra-simple-field-with-hide
;;   (implies (member fld *x86-simple-fields-as-keywords*)
;;            (equal (xr fld i (hide (xw fld j v x86)))
;;                   v))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm xr-xw-inter-field-with-hide
;;   (implies (case-split (not (equal fld1 fld2)))
;;            (equal (xr fld2 i2 (hide (xw fld1 i1 v x86)))
;;                   (xr fld2 i2 x86)))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;the use of the stobj seems to result in calls to rgfi* being hidden
;; (acl2::defopeners RGFI* :hyps ((syntaxp (quotep i))
;;                                        (syntaxp (quotep x86))))

(acl2::defopeners xr :hyps ((syntaxp (quotep rstobj2::fld))
                            (syntaxp (quotep rstobj2::index))
                            (syntaxp (quotep X86ISA::X86$A))))
;why?
(acl2::defopeners x86p :hyps ((syntaxp (quotep x86))))

;tighten?
(defthm x86isa::signed-byte-p-64-when-canonical-address-p-cheap
  (implies (canonical-address-p x)
           (signed-byte-p 64 x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable signed-byte-p canonical-address-p))))

;; (defthm RGFI*-of-xw-diff
;;   (implies (and (equal :ms fld) ;drop!
;;                 (not (equal :rgf fld)))
;;            (equal (RGFI* 0 (XW fld index value x86))
;;                   (RGFI* 0 x86)))
;;   :hints (("Goal" :in-theory (enable xw !MS* rgfi* !rip*))))

;; (defthm RGFI*-of-xw-same
;;   (equal (RGFI* num (XW :rgf num value x86))
;;          value)
;;   :hints (("Goal" :in-theory (enable xw !RGFI* RGFI*))))
;;; Set up the theory for symbolic execution (work in progress):
;;; Perhaps these should be made into a ruleset.

(in-theory (acl2::enable* x86isa::X86-EFFECTIVE-ADDR-FROM-SIB
                    x86isa::instruction-decoding-and-spec-rules ;this one is a ruleset
                    x86isa::jcc/cmovcc/setcc-spec
                    x86isa::gpr-and-spec-4
                    x86isa::gpr-xor-spec-4
                    x86isa::GPR-ADD-SPEC-4

                    x86isa::one-byte-opcode-execute ;; x86isa::one-byte-opcode-execute
                    ;; !rgfi-size
                    x86isa::x86-operand-to-reg/mem

                    ;;These appear to eventually call xw (via
                    ;;!rgfi), so we'll keep them enabled
                    ;;since xw is our normal form:
                    x86isa::wr08
                    x86isa::wr16
                    x86isa::wr32
                    x86isa::wr64

                    ;;These appear to eventually call xr (via
                    ;;rgfi), so we'll keep them enabled
                    ;;since xw is our normal form:
                    x86isa::rr08
                    x86isa::rr16
                    x86isa::rr32
                    x86isa::rr64

                    x86isa::wml32
                    x86isa::wml64
                    x86isa::riml08
                    x86isa::riml32

                    x86isa::x86-operand-from-modr/m-and-sib-bytes
                    x86isa::riml-size

                    x86isa::check-instruction-length

                    x86isa::select-segment-register

                    x86isa::n08-to-i08
                    x86isa::n16-to-i16
                    x86isa::n32-to-i32
                    x86isa::n64-to-i64
                    x86isa::n128-to-i128

                    x86isa::two-byte-opcode-decode-and-execute
                    x86isa::x86-effective-addr-when-64-bit-modep
                    x86isa::x86-effective-addr-32/64
                    ;; Flags
                    x86isa::write-user-rflags
                    x86isa::zf-spec))

(in-theory (disable x86isa::create-canonical-address-list
                    (:e x86isa::create-canonical-address-list)))

(defthm x86isa::canonical-address-p-foward-to-signed-byte-p
  (implies (canonical-address-p lin-addr)
           (signed-byte-p 48 lin-addr))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable canonical-address-p))))

;; gets rid of the effect of saving and restoring rbp
;; (defthm x86isa::xw-xr-same
;;   (implies (and (equal (xr fld i x86) (xr fld i x86-2))
;;                 (x86p x86))
;;            (equal (xw fld i (xr fld i x86-2) x86)
;;                   x86))
;;   :hints (("Goal" :in-theory (enable ;x86isa::xw-xr
;;                               ))))

(defthm member-p-of-create-canonical-address-list-same
  (implies (canonical-address-p addr)
           (equal (x86isa::member-p addr (x86isa::create-canonical-address-list count addr))
                  (posp count)))
  :hints (("Goal" :in-theory (enable x86isa::create-canonical-address-list))))

;; ;could restrict k and k2 to constants
;; (defthm canonical-address-p-of-+-when-canonical-address-p-of-+
;;   (implies (and (canonical-address-p (+ k2 load-offset))
;;                 (<= k k2)
;;                 (natp k)
;;                 (natp k2)
;;                 (natp load-offset))
;;            (canonical-address-p (+ k load-offset)))
;;   :hints (("Goal" :in-theory (enable canonical-address-p signed-byte-p))))

;; k is between klow and khigh
;; one way to know that something (here, (+ klow load-offset)) is canonical is to know that it's equal to the RIP
;; we could forward-chain from equal rip to canonical (does forward-chaining happen during symsim?)
(defthm canonical-address-p-of-+-when-canonical-address-p-of-+-special
  (implies (and (equal (xr :rip nil x86) (+ klow load-offset)) ;klow is a free var
                (canonical-address-p (+ khigh load-offset))
                (x86p x86) ;implies that the RIP is canonical
                (<= klow k)
                (<= k khigh)
                (natp k)
                (natp klow)
                (natp khigh)
                (integerp load-offset))
           (canonical-address-p (+ k load-offset)))
  :hints (("Goal" :in-theory (enable canonical-address-p signed-byte-p))))


;pretty specific...
;think about possible loops here
(defthm canonical-address-p-of-plus-of-rip
  (implies (and (syntaxp (quotep k))
                (equal (xr :rip nil x86) (+ freek load-offset)) ;freek and load-offset are free vars
                (syntaxp (quotep freek))
                (canonical-address-p (+ (+ k freek) ;gets evaluated
                                        load-offset)))
           (canonical-address-p (+ k (xr :rip nil x86)))))

(defthm x86isa::subset-p-of-singleton-arg1
  (equal (x86isa::subset-p (cons a nil) x)
         (x86isa::member-p a x))
  :hints (("Goal" :in-theory (enable x86isa::subset-p))))

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

(defthm canonical-address-p-of-if
  (equal (canonical-address-p (if test a1 a2))
         (if test
             (canonical-address-p a1)
           (canonical-address-p a2))))

;; splits the simulation!
(defthm x86-fetch-decode-execute-of-set-rip-split
  (equal (x86-fetch-decode-execute (xw :rip nil (if test rip1 rip2) x86))
         (if test
             (x86-fetch-decode-execute (xw :rip nil rip1 x86))
           (x86-fetch-decode-execute (xw :rip nil rip2 x86)))))

;; splits the simulation!
(defthm x86-fetch-decode-execute-of-if
  (equal (x86-fetch-decode-execute (if test x86_1 x86_2))
         (if test
             (x86-fetch-decode-execute x86_1)
           (x86-fetch-decode-execute x86_2))))

(in-theory (disable MEMBER-EQUAL))

;; (defthm !flgi-undefined-of-!flgi-different-concrete-indices
;;   (implies (and (syntaxp (quotep i1))
;;                 (syntaxp (quotep i2))
;;                 (< i1 i2)
;;                 (member i1 *flg-names*)
;;                 (member i2 *flg-names*)
;;                 (x86p x86) ;drop?
;;                 )
;;            (equal (x86isa::!flgi-undefined i2 (!flgi i1 v1 x86))
;;                   (!flgi i1 v1 (x86isa::!flgi-undefined i2 x86))))
;;   :hints (("Goal" :in-theory (enable x86isa::!flgi-undefined))))

; Add untranslate patterns for undefined flags
;copied from !flgi
(make-event
 (cons
  'progn
  (x86isa::x86-fn-untranslate
   '(x86isa::!flgi-undefined)
   '(x86isa::?v x86isa::?x)
   '(0 2 4 6 7 8 9 10 11 12 14 16 17 18 19 20 21)
   '(x86isa::*CF*
     x86isa::*PF*
     x86isa::*AF*
     x86isa::*ZF*
     x86isa::*SF*
     x86isa::*TF*
     x86isa::*IF*
     x86isa::*DF*
     x86isa::*OF*
     x86isa::*IOPL*
     x86isa::*NT*
     x86isa::*RF*
     x86isa::*VM*
     x86isa::*AC*
     x86isa::*VIF*
     x86isa::*VIP*
     x86isa::*ID*))))

(in-theory (disable logcount))
(in-theory (disable x86isa::WRITE-USER-RFLAGS-AND-XW))
(in-theory (disable BYTE-LISTP))
(in-theory (disable x86isa::COMBINE-BYTES))

(defthm canonical-address-p-between
  (implies (and (canonical-address-p low)
                (canonical-address-p high)
                (<= low ad)
                (<= ad high))
           (equal (canonical-address-p ad)
                  (integerp ad)))
  :hints (("Goal" :in-theory (enable canonical-address-p SIGNED-BYTE-P))))

(defun nth-of-create-canonical-address-list-induct (n count addr)
  (if (zp count)
      (list n count addr)
    (nth-of-create-canonical-address-list-induct (+ -1 n) (+ -1 count) (+ 1 addr))))

(defthm nth-of-create-canonical-address-list
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ count -1 addr))
                (natp n)
                (< n count))
           (equal (nth n (x86isa::create-canonical-address-list count addr))
                  (+ n addr)))
  :hints (("Goal" :induct (nth-of-create-canonical-address-list-induct n count addr)
           :in-theory (e/d (x86isa::create-canonical-address-list
                            ;nth ;list::nth-of-cons
                            )
                           (;acl2::nth-of-cdr
                            )))))

;i wonder if not having this but instead considering opening up x86isa::canonical-address-listp could be slowing down acl2.
(defthm canonical-address-listp-of-cons
  (equal (x86isa::canonical-address-listp (cons a x))
         (and (canonical-address-p a)
              (x86isa::canonical-address-listp x))))

(defthm canonical-address-listp-of-nil
  (x86isa::canonical-address-listp nil))

(defthm integerp-of-xr-rgf
  (implies (x86p x86)
           (integerp (xr :rgf i x86))))

;see xr-xw-inter-field but that has a case-split
(defthm xr-of-xw-diff
  (implies (not (equal fld1 fld2))
           (equal (xr fld2 i2 (xw fld1 i1 v x86))
                  (xr fld2 i2 x86))))

;for axe
(defthmd canonical-address-p-becomes-signed-byte-p-when-constant
  (implies (syntaxp (quotep ad))
           (equal (canonical-address-p ad)
                  (signed-byte-p 48 ad)))
  :hints (("Goal" :in-theory (enable canonical-address-p))))

(defthm unsigned-byte-p-of-xr-of-mem
  (implies (and (<= 8 size)
                (x86p x86))
           (equal (unsigned-byte-p size (xr :mem i x86))
                  (natp size))))

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


;; resolve a call to rb on a singleton list when we know the program
;; this rule seems simpler than rb-in-terms-of-nth-and-pos (which is now gone) since it has no extended bind-free hyp.
;; todo: try :match-free :all
;todo: rename
(defthm rb-in-terms-of-nth-and-pos-eric
  (implies (and ;; find that a program is loaded in the initial state:
            (program-at paddr bytes x86-init) ;these are free vars
            ;; try to prove that the same program is loaded in the current state:
            (program-at paddr bytes x86)
            (byte-listp bytes)
            (<= paddr addr)
            (integerp addr)
 ;           (integerp paddr)
            (< addr (+ paddr (len bytes)))
;            (x86isa::member-p addr addresses)
            (canonical-address-p paddr)
            (canonical-address-p (+ -1 (len bytes) paddr))
;(x86isa::canonical-address-listp addresses)
            (app-view x86)
            (X86P X86) ;too bad
            )
           (equal (mv-nth 1 (rb 1 addr r-w-x x86))
                  (nth (- addr paddr)
                       bytes)))
  :hints (("Goal" :do-not-induct t
           :expand ((NTH 0 BYTES))
           :use ((:instance slice-of-combine-bytes
                            (n (- addr paddr))
                            )
                 (:instance x86isa::rb-rb-subset
                           (j 1)
                           (addr-j addr)
                           (r-x-j r-w-x)
                           (val (x86isa::combine-bytes (acl2::list-fix bytes)))
                           (i (len bytes))
                           (addr-i paddr)
                           (r-x-i :x)))
;           :expand (RB-1 1 ADDR R-W-X X86)
           :in-theory (e/d ( ;rb rb-1 program-at rvm08
                            program-at
                            ash
                            ;x86isa::RB-RB-SUBSET
                            natp
                            acl2::mod-becomes-bvchop-8
                            ;;acl2::bvchop
                            ;;ACL2::CAR-BECOMES-NTH-OF-0
                            acl2::bvchop-of-logtail-becomes-slice
                            )
                           (slice-of-combine-bytes)))))

;can this loop?  do we have any rules that backchain from < to signed-byte-p?
(defthm signed-byte-p-when-between-canonical-addresses
  (implies (and (signed-byte-p 48 low)
                (signed-byte-p 48 high)
                (<= low ad)
                (<= ad high))
           (equal (signed-byte-p 48 ad)
                  (integerp ad)))
  :hints
  (("Goal"
    :in-theory (enable canonical-address-p signed-byte-p))))

;; These are for showing that x plus an offset is canonical:

(defthm canonical-address-p-between-special1
  (implies (and (canonical-address-p (+ low-offset x))
                (<= low-offset offset)
                (canonical-address-p (+ high-offset x))
                (<= offset high-offset)
                (integerp low-offset)
                (integerp high-offset)
                (integerp offset))
           (canonical-address-p (+ offset x))))

;case when offset = 0
(defthm canonical-address-p-between-special2
  (implies (and (canonical-address-p (+ low-offset x))
                (<= low-offset 0)
                (canonical-address-p (+ high-offset x))
                (<= 0 high-offset)
                (integerp low-offset)
                (integerp high-offset))
           (equal (canonical-address-p x)
                  (integerp x))))

;case when low-offset = 0
(defthm canonical-address-p-between-special3
  (implies (and (canonical-address-p (+ high-offset x))
                (<= offset high-offset)
                (canonical-address-p x)
                (<= 0 offset)
                (integerp high-offset)
                (integerp offset))
           (canonical-address-p (+ offset x))))

;case when high-offset = 0
(defthm canonical-address-p-between-special4
  (implies (and (canonical-address-p (+ low-offset x))
                (<= low-offset offset)
                (canonical-address-p x)
                (<= offset 0)
                (integerp low-offset)
                (integerp offset))
           (canonical-address-p (+ offset x))))

(defthm integerp-of-xr-of-rsp
  (implies (x86p x86)
           (integerp (xr :rgf *rsp* x86))))

(defthm app-view-of-xw
  (implies (not (equal fld :app-view))
           (equal (app-view (xw fld index value x86))
                  (app-view x86))))

(local (include-book "kestrel/bv/rules3" :dir :system)) ;drop?

;todo: gen the 2
(defthm idiv-64-by-2-no-error
  (equal (mv-nth 0 (x86isa::idiv-spec-64 (acl2::bvsx 128 64 x) 2))
         nil)
  :hints (("Goal" :in-theory (enable x86isa::idiv-spec-64 truncate
                                     ))))

;todo: gen the 2
(defthm idiv-64-by-2-becomes-sbvdiv
  (equal (mv-nth 1 (x86isa::idiv-spec-64 (acl2::bvsx 128 64 x) 2))
         (acl2::sbvdiv 64 x 2))
  :hints (("Goal" :in-theory (enable x86isa::idiv-spec-64 truncate acl2::sbvdiv))))

;todo: gen the 2
(defthm idiv-64-by-2-becomes-sbvrem
  (equal (mv-nth 2 (x86isa::idiv-spec-64 (acl2::bvsx 128 64 x) 2))
         (acl2::sbvrem 64 x 2))
  :hints (("Goal" :in-theory (enable x86isa::idiv-spec-64 truncate acl2::sbvrem))))

;tons of calls of byte-listp were getting memoized, whereas we can just run
;all-unsigned-byte-p.
(defthm byte-listp-becomes-all-unsigned-byte-p
  (equal (byte-listp x)
         (and (acl2::all-unsigned-byte-p 8 x)
              (true-listp x)))
  :hints (("Goal" :in-theory (enable byte-listp))))

;; Avoids the b* at the top level
(defthm x86isa::get-prefixes-does-not-modify-x86-state-in-app-view-new
  (implies (app-view x86)
           (equal (mv-nth 3
                          (get-prefixes x86isa::proc-mode
                                        x86isa::start-rip x86isa::prefixes
                                        x86isa::rex-byte x86isa::cnt x86))
                  x86))
  :hints (("Goal" :use x86isa::get-prefixes-does-not-modify-x86-state-in-app-view)))

(defthm segment-base-and-bounds-of-xw
  (implies (and ;(not (equal :mem fld))
                (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr))
                )
           (equal (segment-base-and-bounds proc-mode seg-reg (xw fld index val x86))
                  (segment-base-and-bounds proc-mode seg-reg x86)))
  :hints (("Goal" :in-theory (e/d (segment-base-and-bounds) (;; X86ISA::SEG-HIDDEN-BASEI-IS-N64P
                                                             ;; X86ISA::SEG-HIDDEN-LIMITI-IS-N32P
                                                             ;; X86ISA::SEG-HIDDEN-ATTRI-IS-N16P
                                                             )))))

(defthm memi-of-xw
  (implies (not (equal :mem fld))
           (equal (memi i (xw fld index val x86))
                  (memi i x86)))
  :hints (("Goal" :in-theory (enable memi))))

(defthm x86isa::logext-48-does-nothing-when-canonical-address-p
  (implies (canonical-address-p x)
           (equal (logext 48 x)
                  x)))

(defthm unsigned-byte-p-of-bfix
  (implies (posp n)
           (unsigned-byte-p n (acl2::bfix x)))
  :hints (("Goal" :in-theory (enable acl2::bfix))))

;; should be cheaper than x86isa::xw-xr-rgf
(defthm xw-rgf-of-xr-rgf-same
  (implies (and (equal (xr :rgf n x86)
                       (xr :rgf n x86-2))
                (natp n)
                (< n 16)
                (x86p x86-2))
           (equal (xw ':rgf n (xr :rgf n x86) x86-2)
                  x86-2))
  :hints (("Goal" :in-theory (enable ;x86isa::xw-xr-rgf
                              ))))

;gen
(defthm weaken-upper-bound-when-top-bit-0
  (implies (and (syntaxp (acl2::want-to-weaken (< x -9223372036854775808)))
                ;; (syntaxp (quotep k))
                ;(< k 0)
                (integerp x)
                (equal (acl2::getbit 63 x) 0))
           (equal (< x -9223372036854775808
                     ) ;gen
                  (< x 0)))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::logtail)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))

;rewrite: (< (BVCHOP 64 Y) 9223372036854775808)
;rewrite: (<= (BVCHOP 64 Y) (BVCHOP 63 Y))

(defthm xw-rip-of-if-arg3
  (equal (XW :RIP NIL (IF test rip1 rip2) x86)
         (if test
             (XW :RIP NIL rip1 x86)
           (XW :RIP NIL rip2 x86))))

; not strictly necessary since not-mv-nth-0-of-rme-size$inline should fire, but this can get rid of irrelevant stuff
(defthm mv-nth-0-of-rme-size-of-xw-when-app-view
  (implies (and (not (equal fld :mem))
                (not (equal fld :app-view))
                (not (equal fld :seg-hidden-attr))
                (not (equal fld :seg-hidden-base))
                (not (equal fld :seg-hidden-limit))
                (not (equal fld :seg-visible))
                (not (equal fld :msr))
                (app-view x86))
           (equal (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (xw fld index val x86) mem-ptr?))
                  (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (e/d (x86isa::rme-size) (ea-to-la$inline
                                                      x86isa::rml-size$inline
                                                      x86isa::ea-to-la-is-i48p-when-no-error)))))

;; TODO: The original rule should be replaced by this one
(DEFTHM X86ISA::PROGRAM-AT-XW-IN-APP-VIEW-better
  (IMPLIES (AND (NOT (EQUAL X86ISA::FLD :MEM))
                (NOT (EQUAL X86ISA::FLD :APP-VIEW))
                (APP-VIEW X86))
           (EQUAL (PROGRAM-AT X86ISA::ADDR X86ISA::BYTES
                              (XW X86ISA::FLD X86ISA::INDEX VALUE X86))
                  (PROGRAM-AT X86ISA::ADDR X86ISA::BYTES X86)))
  :HINTS (("Goal" :IN-THEORY (ACL2::E/D* NIL (RB)))))

(in-theory (disable X86ISA::PROGRAM-AT-XW-IN-APP-VIEW))

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
                      (acl2::bvchop 8 val)
                    (memi addr x86))))
  :hints (("Goal" :in-theory (enable memi))))

(defthm memi-of-xw-same
  (implies (unsigned-byte-p 48 addr)
           (equal (memi addr (xw :mem addr val x86))
                  (acl2::bvchop 8 val)))
  :hints (("Goal" :in-theory (enable memi))))

;gen
(local
 (defthm +-of---of-bvchop-of-bvcat-same
   (equal (+ (- (ACL2::BVCHOP 6 SRC)) (ACL2::BVCAT 1 1 6 SRC))
          (ACL2::BVCAT 1 1 6 0))
   :hints (("Goal" :in-theory (e/d (acl2::bvcat acl2::logapp)
                                   (ACL2::PLUS-BVCAT-WITH-0 ;loop
                                    ACL2::PLUS-BVCAT-WITH-0-ALT
                                    ))))))

;; the normal definition splits with an if!
;; well, this one has an if too, but it's perhaps less bad since the shift amount will often be constant
;;maybe improve bvashr
(defthm SAR-SPEC-32-nice
  (equal (SAR-SPEC-32 DST SRC INPUT-RFLAGS)
         (B* ((DST (MBE :LOGIC (N-SIZE 32 DST)
                        :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 6 SRC)
                        :EXEC SRC))
              (INPUT-RFLAGS
               (MBE :LOGIC (N32 INPUT-RFLAGS)
                    :EXEC INPUT-RFLAGS))
              (RESULT
               (if (<= 32 (ACL2::BVCHOP 6 SRC))
                   (if (EQUAL 1 (ACL2::GETBIT 31 DST))
                       (+ -1 (expt 2 32))
                     0)
                 (acl2::bvashr 32 dst SRC)))
              ((MV (THE (UNSIGNED-BYTE 32)
                        OUTPUT-RFLAGS)
                   (THE (UNSIGNED-BYTE 32)
                        UNDEFINED-FLAGS))
               (CASE
                 SRC
                 (0 (MV INPUT-RFLAGS 0))
                 (1
                  (B*
                      ((CF
                        (MBE
                         :LOGIC (ACL2::PART-SELECT DST
                                                   :LOW 0
                                                   :WIDTH 1)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 1)
                          (LOGAND 1
                                  (THE (UNSIGNED-BYTE 32) DST)))))
                       (PF (GENERAL-PF-SPEC 32 RESULT))
                       (ZF (ZF-SPEC RESULT))
                       (SF
                        (GENERAL-SF-SPEC 32 RESULT))
                       (OF 0)
                       (OUTPUT-RFLAGS
                        (MBE
                         :LOGIC
                         (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                            :CF CF
                                            :PF PF
                                            :ZF ZF
                                            :SF SF
                                            :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF
                              (!RFLAGSBITS->OF
                               OF INPUT-RFLAGS))))))))
                       (UNDEFINED-FLAGS
                        (THE (UNSIGNED-BYTE 32)
                             (!RFLAGSBITS->AF 1 0))))
                    (MV OUTPUT-RFLAGS
                        UNDEFINED-FLAGS)))
                 (OTHERWISE
                  (IF
                   (<= 32 SRC)
                   (B*
                       ((PF (GENERAL-PF-SPEC 32 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF
                         (GENERAL-SF-SPEC 32 RESULT))
                        (OUTPUT-RFLAGS
                         (MBE
                          :LOGIC
                          (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                             :PF PF
                                             :ZF ZF
                                             :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0
                                                    :CF 1
                                                    :AF 1
                                                    :OF 1)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            1
                            (!RFLAGSBITS->AF
                             1 (!RFLAGSBITS->OF 1 0)))))))
                     (MV OUTPUT-RFLAGS
                         UNDEFINED-FLAGS))
                   (B*
                       ((CF
                         (MBE
                          :LOGIC (ACL2::PART-SELECT DST
                                                    :LOW (1- SRC)
                                                    :WIDTH 1)
                          :EXEC
                          (LET*
                           ((SHFT
                             (THE
                              (SIGNED-BYTE 32)
                              (- 1
                                 (THE (UNSIGNED-BYTE 32) SRC)))))
                           (THE
                            (UNSIGNED-BYTE 1)
                            (LOGAND
                             1
                             (THE (UNSIGNED-BYTE 32)
                                  (ASH (THE (UNSIGNED-BYTE 32) DST)
                                       (THE (SIGNED-BYTE 32)
                                            SHFT))))))))
                        (PF (GENERAL-PF-SPEC 32 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF
                         (GENERAL-SF-SPEC 32 RESULT))
                        (OUTPUT-RFLAGS
                         (MBE
                          :LOGIC
                          (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                             :CF CF
                                             :PF PF
                                             :ZF ZF
                                             :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                             PF
                             (!RFLAGSBITS->ZF
                              ZF
                              (!RFLAGSBITS->SF
                               SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE :LOGIC (CHANGE-RFLAGSBITS 0
                                                        :AF 1
                                                        :OF 1)
                              :EXEC (!RFLAGSBITS->AF
                                     1 (!RFLAGSBITS->OF 1 0)))))
                     (MV OUTPUT-RFLAGS
                         UNDEFINED-FLAGS))))))
              (OUTPUT-RFLAGS
               (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                    :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS
               (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                    :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS
               UNDEFINED-FLAGS)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (acl2::bvashr
                                   ;;acl2::bvsx
                                   SAR-SPEC-32 ACL2::BVSHR
                                   ;;ACL2::LOGEXT-CASES
                                   acl2::bvchop-of-logtail-becomes-slice
                                   acl2::<-of-bvchop-and-2
                                   acl2::slice-alt-def
                                   )
                                  ( ;ACL2::BVCAT-EQUAL-REWRITE ACL2::BVCAT-EQUAL-REWRITE-ALT
                                   acl2::BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE
                                   )))))
(DEFthm SAR-SPEC-64-nice
  (equal (SAR-SPEC-64 DST SRC INPUT-RFLAGS)
         (B*
             ((DST (MBE :LOGIC (N-SIZE 64 DST) :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 6 SRC) :EXEC SRC))
              (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                 :EXEC INPUT-RFLAGS))
              (RESULT
               (if (<= 64 (ACL2::BVCHOP 7 SRC))
                   (if (EQUAL 1 (ACL2::GETBIT 63 DST))
                       (+ -1 (expt 2 64))
                     0)
                 (acl2::bvashr 64 dst SRC)))
              ((MV (THE (UNSIGNED-BYTE 32) OUTPUT-RFLAGS)
                   (THE (UNSIGNED-BYTE 32)
                        UNDEFINED-FLAGS))
               (CASE
                 SRC (0 (MV INPUT-RFLAGS 0))
                 (1
                  (B*
                      ((CF
                        (MBE :LOGIC (PART-SELECT DST :LOW 0 :WIDTH 1)
                             :EXEC
                             (THE (UNSIGNED-BYTE 1)
                                  (LOGAND 1 (THE (UNSIGNED-BYTE 64) DST)))))
                       (PF (GENERAL-PF-SPEC 64 RESULT))
                       (ZF (ZF-SPEC RESULT))
                       (SF (GENERAL-SF-SPEC 64 RESULT))
                       (OF 0)
                       (OUTPUT-RFLAGS
                        (MBE
                         :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                   :CF CF
                                                   :PF PF
                                                   :ZF ZF
                                                   :SF SF
                                                   :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF
                              (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
                       (UNDEFINED-FLAGS (THE (UNSIGNED-BYTE 32)
                                             (!RFLAGSBITS->AF 1 0))))
                    (MV OUTPUT-RFLAGS UNDEFINED-FLAGS)))
                 (OTHERWISE
                  (IF
                   (<= 64 SRC)
                   (B*
                       ((PF (GENERAL-PF-SPEC 64 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 64 RESULT))
                        (OUTPUT-RFLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :CF 1 :AF 1 :OF 1)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            1
                            (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))))
                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))
                   (B*
                       ((CF
                         (MBE
                          :LOGIC (PART-SELECT DST :LOW (1- SRC) :WIDTH 1)
                          :EXEC
                          (LET*
                           ((SHFT (THE (SIGNED-BYTE 64)
                                       (- 1 (THE (UNSIGNED-BYTE 64) SRC)))))
                           (THE
                            (UNSIGNED-BYTE 1)
                            (LOGAND
                             1
                             (THE (UNSIGNED-BYTE 64)
                                  (ASH (THE (UNSIGNED-BYTE 64) DST)
                                       (THE (SIGNED-BYTE 64) SHFT))))))))
                        (PF (GENERAL-PF-SPEC 64 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 64 RESULT))
                        (OUTPUT-RFLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :CF CF
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                             PF
                             (!RFLAGSBITS->ZF
                              ZF
                              (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :AF 1 :OF 1)
                          :EXEC (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
              (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                  :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                    :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :otf-flg t
  :hints (("Goal" :expand ()
           :in-theory (e/d (acl2::bvashr ;acl2::bvsx
                            SAR-SPEC-64 ACL2::BVSHR
                                        ;;ACL2::LOGEXT-CASES
                            acl2::bvchop-of-logtail-becomes-slice
                            acl2::<-of-bvchop-and-2
                            acl2::slice-alt-def
                            )
                           ( ;ACL2::BVCAT-EQUAL-REWRITE ACL2::BVCAT-EQUAL-REWRITE-ALT
                            acl2::BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE
                            ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE ;loop
                            ACL2::LOGtail-OF-LOGext ;loop
                            )))))

;move
(defthm bitp-of-sf-spec32
  (acl2::bitp (sf-spec32 result)))

(defthm unsigned-byte-p-1-of-sf-spec32
  (acl2::unsigned-byte-p 1 (sf-spec32 result)))

(defthm unsigned-byte-p-1-of-sub-af-spec32
  (acl2::unsigned-byte-p 1 (sub-af-spec32 dst src)))

(in-theory (disable zf-spec))

;gen?
(defthm integerp-of-xr-rgf-4
  (implies (x86p x86)
           (integerp (xr ':rgf '4 x86))))

;gen?
(defthm fix-of-xr-rgf-4
  (equal (fix (xr ':rgf '4 x86))
         (xr ':rgf '4 x86)))

;gen
(defthm xr-app-view-of-!memi
  (equal (xr :app-view nil (!memi addr val x86))
         (xr :app-view nil x86))
  :hints (("Goal" :in-theory (enable !memi))))

(defthm app-view-of-!memi
  (equal (app-view (!memi addr val x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable !memi))))

(defthm x86p-of-!memi
  (implies (and (x86p x86)
                (INTEGERP ADDR)
                (UNSIGNED-BYTE-P 8 VAL))
           (x86p (!memi addr val x86)))
  :hints (("Goal" :in-theory (enable !memi))))

;rename
(defthm memi-of-!memi
  (implies (unsigned-byte-p 48 addr)
           (equal (memi addr (!memi addr val x86))
                  (acl2::bvchop 8 val)))
  :hints (("Goal" :in-theory (enable memi))))

(defthm !memi-of-!memi-same
  (equal (!memi addr val (!memi addr val2 x86))
         (!memi addr val x86)))

(defthm xw-of-xw-both
  (implies (syntaxp (acl2::smaller-termp addr2 addr))
           (equal (xw :mem addr val (xw :mem addr2 val2 x86))
                  (if (equal addr addr2)
                      (xw :mem addr val x86)
                    (xw :mem addr2 val2 (xw :mem addr val x86)))))
  :hints (("Goal" :in-theory (enable xw))))

(defthm xw-of-xw-diff
  (implies (and (syntaxp (acl2::smaller-termp addr2 addr))
                (not (equal addr addr2)))
           (equal (xw :mem addr val (xw :mem addr2 val2 x86))
                  (xw :mem addr2 val2 (xw :mem addr val x86))))
  :hints (("Goal" :in-theory (enable xw))))

(defthm memi-of-xw-irrel
  (implies (not (equal fld :mem))
           (equal (memi addr (xw fld index val x86))
                  (memi addr x86)))
  :hints (("Goal" :in-theory (e/d (memi)
                                  (;x86isa::memi-is-n08p ;does forcing
                                   )))))
