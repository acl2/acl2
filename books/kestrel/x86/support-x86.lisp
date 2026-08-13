; Supporting material for x86 code proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;; unlike most books, this one is in the X86ISA package

;; Supporting material about the x86 model.  Some of this could be moved to the
;; model itself.

;(include-book "projects/x86isa/proofs/utilities/app-view/top" :dir :system) ;reduce? needed for the big enable below
;(include-book "projects/x86isa/proofs/utilities/general-memory-utils" :dir :system) ; drop?
(include-book "projects/x86isa/proofs/utilities/row-wow-thms" :dir :system) ; for X86ISA::WRITE-USER-RFLAGS-AND-XW
(include-book "projects/x86isa/proofs/utilities/app-view/user-level-memory-utils" :dir :system) ; for rb-rb-subset
;(include-book "projects/x86isa/machine/state" :dir :system)
;(include-book "projects/x86isa/machine/x86" :dir :system) ; for x86-fetch-decode-execute, ONE-BYTE-OPCODE-EXECUTE, etc.
;(include-book "projects/x86isa/machine/get-prefixes" :dir :system)
;(include-book "projects/x86isa/machine/state-field-thms" :dir :system)
;(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ;for canonical-address-p
(include-book "kestrel/utilities/defopeners" :dir :system)
;; todo: ideally, this book should not include non-x86isa books, like these:
(include-book "kestrel/utilities/polarity" :dir :system) ; for want-to-weaken
(include-book "kestrel/utilities/smaller-termp" :dir :system)
;(include-book "kestrel/bv/defs-arith" :dir :system) ;for bvplus
(include-book "kestrel/bv/slice-def" :dir :system)
;(include-book "kestrel/bv/defs" :dir :system) ;for sbvdiv
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "linear-memory") ;drop? but need mv-nth-0-of-rml-size-of-xw-when-app-view
(include-book "canonical")
(include-book "state")
(local (include-book "support-bv"))
(local (include-book "kestrel/bv/rules10" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop, to deal with truncate
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/denominator" :dir :system))
(local (include-book "kestrel/arithmetic-light/numerator" :dir :system))
(local (include-book "kestrel/bv/getbit2" :dir :system))

(in-theory (disable
                    x86isa::write-user-rflags-and-xw
                   ))

;why?
(in-theory (disable x86isa::program-at-xw-in-app-view))

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

;why needed?
;(acl2::defopeners LOAD-PROGRAM-INTO-MEMORY)

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


;; gets rid of the effect of saving and restoring rbp
;; (defthm x86isa::xw-xr-same
;;   (implies (and (equal (xr fld i x86) (xr fld i x86-2))
;;                 (x86p x86))
;;            (equal (xw fld i (xr fld i x86-2) x86)
;;                   x86))
;;   :hints (("Goal" :in-theory (enable ;x86isa::xw-xr
;;                               ))))

;; (defthm member-p-of-create-canonical-address-list-same
;;   (implies (canonical-address-p addr)
;;            (equal (x86isa::member-p addr (x86isa::create-canonical-address-list count addr))
;;                   (posp count)))
;;   :hints (("Goal" :in-theory (enable x86isa::create-canonical-address-list))))

;; ;could restrict k and k2 to constants
;; (defthm canonical-address-p-of-+-when-canonical-address-p-of-+
;;   (implies (and (canonical-address-p (+ k2 load-offset))
;;                 (<= k k2)
;;                 (natp k)
;;                 (natp k2)
;;                 (natp load-offset))
;;            (canonical-address-p (+ k load-offset)))
;;   :hints (("Goal" :in-theory (enable canonical-address-p signed-byte-p))))

(defthm x86isa::subset-p-of-singleton-arg1
  (equal (x86isa::subset-p (cons a nil) x)
         (x86isa::member-p a x))
  :hints (("Goal" :in-theory (enable x86isa::subset-p))))



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
           :in-theory (enable x86isa::create-canonical-address-list canonical-address-p))))

;i wonder if not having this but instead considering opening up x86isa::canonical-address-listp could be slowing down acl2.
(defthm canonical-address-listp-of-cons
  (equal (x86isa::canonical-address-listp (cons a x))
         (and (canonical-address-p a)
              (x86isa::canonical-address-listp x))))

;; or evaulate it, or use a constant opener
(defthm canonical-address-listp-of-nil
  (x86isa::canonical-address-listp nil))

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
                            acl2::mod-becomes-bvchop-when-power-of-2p
                            ;;acl2::bvchop
                            ;;ACL2::CAR-BECOMES-NTH-OF-0
                            acl2::bvchop-of-logtail-becomes-slice
                            )
                           (slice-of-combine-bytes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;tons of calls of byte-listp were getting memoized, whereas we can just run
;all-unsigned-byte-p.
(defthm byte-listp-becomes-all-unsigned-byte-p
  (equal (byte-listp x)
         (and (acl2::all-unsigned-byte-p 8 x)
              (true-listp x)))
  :hints (("Goal" :in-theory (enable byte-listp))))



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
           (equal (xw :rgf n (xr :rgf n x86) x86-2)
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
           (equal (< x -9223372036854775808) ;gen
                  (< x 0)))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::logtail)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))

;; TODO: The original rule should be replaced by this one
(DEFTHM X86ISA::PROGRAM-AT-XW-IN-APP-VIEW-better
  (IMPLIES (AND (NOT (EQUAL X86ISA::FLD :MEM))
                (NOT (EQUAL X86ISA::FLD :APP-VIEW))
                (APP-VIEW X86))
           (EQUAL (PROGRAM-AT X86ISA::ADDR X86ISA::BYTES
                              (XW X86ISA::FLD X86ISA::INDEX VALUE X86))
                  (PROGRAM-AT X86ISA::ADDR X86ISA::BYTES X86)))
  :HINTS (("Goal" :IN-THEORY (ACL2::E/D* (x86isa::program-at-xw-in-app-view) (RB)))))

;gen
(local
 (defthm +-of---of-bvchop-of-bvcat-same
   (equal (+ (- (ACL2::BVCHOP 6 x)) (ACL2::BVCAT 1 1 6 x))
          (ACL2::BVCAT 1 1 6 0))
   :hints (("Goal" :in-theory (enable acl2::bvcat acl2::logapp)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm app-view-of-if
  (equal (app-view (if test x86 x86_2))
         (if test (app-view x86) (app-view x86_2))))

(defthm 64-bit-modep-of-if
  (equal (64-bit-modep (if test x86_1 x86_2))
         (if test (64-bit-modep x86_1)
           (64-bit-modep x86_2))))

(defthm program-at-of-if
  (equal (program-at prog-addr bytes (if test x86 x86_2))
         (if test (program-at prog-addr bytes x86) (program-at prog-addr bytes x86_2))))

(defthm x86p-of-if
  (equal (x86p (if test x86 x86_2))
         (if test (x86p x86) (x86p x86_2))))

(defthm ctri-of-if
  (equal (ctri i (if test x86 x86_2))
         (if test (ctri i x86) (ctri i x86_2))))

;move?
(defthm alignment-checking-enabled-p-of-if
  (equal (alignment-checking-enabled-p (if test x86 x86_2))
         (if test (alignment-checking-enabled-p x86) (alignment-checking-enabled-p x86_2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Most uses of rme-XXX are for 32-bit mode, but this is for 64-bit mode.
;; This version has (canonical-address-p eff-addr) in the conclusion
(defthm x86isa::rme-size-when-64-bit-modep-and-not-fs/gs-strong
  (implies (and (not (equal seg-reg 4))
                (not (equal seg-reg 5))
                (or (not x86isa::check-alignment?)
                    (x86isa::address-aligned-p eff-addr nbytes x86isa::mem-ptr?)))
           (equal (rme-size 0 nbytes eff-addr seg-reg x86isa::r-x x86isa::check-alignment? x86 :mem-ptr? x86isa::mem-ptr?)
                  (if (canonical-address-p eff-addr)
                      (rml-size nbytes eff-addr x86isa::r-x x86)
                    (list (list :non-canonical-address eff-addr) 0 x86)))))

;; Most uses of rme-XXX are for 32-bit mode, but this is for 64-bit mode.
;; This version has (canonical-address-p eff-addr) in the conclusion
(defthm x86isa::wme-size-when-64-bit-modep-and-not-fs/gs-strong
  (implies (and (not (equal seg-reg 4))
                (not (equal seg-reg 5))
                (or (not x86isa::check-alignment?)
                    (x86isa::address-aligned-p
                      eff-addr nbytes x86isa::mem-ptr?)))
           (equal (x86isa::wme-size 0 nbytes eff-addr seg-reg x86isa::val x86isa::check-alignment? x86 :mem-ptr? x86isa::mem-ptr?)
                  (if (canonical-address-p eff-addr)
                      (x86isa::wml-size nbytes eff-addr x86isa::val x86)
                    (list (list :non-canonical-address eff-addr) x86)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm canonical-address-p-of-nth
  (implies (and (x86isa::canonical-address-listp addresses)
                (natp n)
                (< n (len addresses)))
           (canonical-address-p (nth n addresses)))
  :hints (("Goal" :in-theory (e/d (nth) (acl2::nth-of-cdr)))))

(defthm nth-of-pos
  (implies (x86isa::member-p item list)
           (equal (nth (x86isa::pos item list) list)
                  item))
  :hints (("Goal" :in-theory (e/d (nth x86isa::pos) (acl2::nth-of-cdr)))))

;this is the byte-listp in X86ISA
(defthm byte-listp-of-true-list-fix
  (implies (byte-listp bytes)
           (byte-listp (acl2::true-list-fix bytes))))

; better than x86isa::size-of-rb-1
(defthm unsigned-byte-p-of-mv-nth-1-of-rb-1
  (implies (and (<= (* 8 n) m)
                (natp m)
                (x86p x86))
           (unsigned-byte-p m (mv-nth 1 (rb-1 n addr r-x x86))))
  :hints (("Goal" :use (:instance x86isa::size-of-rb-1
                                  (X86ISA::ADDR addr)
                                  (X86ISA::R-X r-x)
                                  (m (* 8 n)))
           :in-theory (e/d (ash rb-1 ifix)
                           (x86isa::size-of-rb-1)))))

(defthm combine-bytes-when-singleton
  (implies (equal 1 (len lst))
           (equal (x86isa::combine-bytes lst)
                  (if (unsigned-byte-p 8 (car lst))
                      (car lst)
                    0))) ;yikes.  combine-bytes should chop its arg?
  :hints (("Goal" :expand (x86isa::combine-bytes lst)
           :in-theory (enable x86isa::combine-bytes))))

;; ;; A version of X86ISA::GET-PREFIXES-OPENER-LEMMA-GROUP-1-PREFIX.
;; ;; simplified hyps should work better with axe
;; (DEFTHM GET-PREFIXES-OPENER-LEMMA-GROUP-1-PREFIX-simple
;;   (IMPLIES
;;    (b* (((MV FLG BYTE X86)
;;          (RME08 PROC-MODE START-RIP *CS* :X X86))
;;         (PREFIX-BYTE-GROUP-CODE
;;          (GET-ONE-BYTE-PREFIX-ARRAY-CODE BYTE)))
;;      (AND (OR (APP-VIEW X86)
;;               (NOT (MARKING-VIEW X86)))
;;           (NOT FLG)
;;           (EQUAL PREFIX-BYTE-GROUP-CODE 1)
;;           (NOT (ZP CNT))
;;           (NOT (MV-NTH 0
;;                        (ADD-TO-*IP PROC-MODE START-RIP 1 X86)))))
;;    (EQUAL
;;     (B* (((MV FLG BYTE X86)
;;           (RME08 PROC-MODE START-RIP *CS* :X X86)))
;;       (GET-PREFIXES PROC-MODE START-RIP PREFIXES CNT X86))
;;     (b* (((MV FLG BYTE X86)
;;           (RME08 PROC-MODE START-RIP *CS* :X X86)))
;;       (LET
;;        ((PREFIXES
;;          (IF (EQUAL BYTE 240)
;;              (!PREFIXES-SLICE
;;               :LCK BYTE
;;               (!PREFIXES-SLICE :LAST-PREFIX 1 PREFIXES))
;;              (!PREFIXES-SLICE
;;               :REP BYTE
;;               (!PREFIXES-SLICE :LAST-PREFIX 2 PREFIXES)))))
;;        (GET-PREFIXES PROC-MODE (1+ START-RIP)
;;                      PREFIXES (1- CNT)
;;                      X86))))))

;; (DEFTHM GET-PREFIXES-OPENER-LEMMA-GROUP-1-PREFIX-simple
;;   (IMPLIES (AND (APP-VIEW X86)
;;                 (64-BIT-MODEP x86)
;;                 (LET* ((FLG (MV-NTH 0 (RME08 START-RIP *CS* :X X86)))
;;                        (PREFIX-BYTE-GROUP-CODE
;;                         (GET-ONE-BYTE-PREFIX-ARRAY-CODE (MV-NTH 1 (RME08 START-RIP *CS* :X X86)))))
;;                       (AND (NOT FLG)
;;                            (EQUAL PREFIX-BYTE-GROUP-CODE 1)))
;;                 (NOT (ZP CNT))
;;                 (CANONICAL-ADDRESS-P (1+ START-RIP))
;;                 )
;;            (EQUAL
;;             (GET-PREFIXES START-RIP PREFIXES CNT X86)
;;             (LET ((PREFIXES
;;                    (IF (EQUAL (MV-NTH 1 (RML08 START-RIP :X X86)) 240)
;;                        (!PREFIXES-SLICE
;;                         :LCK (MV-NTH 1 (RML08 START-RIP :X X86))
;;                         (!PREFIXES-SLICE
;;                          :LAST-PREFIX 1 PREFIXES))
;;                        (!PREFIXES-SLICE
;;                         :REP (MV-NTH 1 (RML08 START-RIP :X X86))
;;                         (!PREFIXES-SLICE
;;                          :LAST-PREFIX 2 PREFIXES)))))
;;                  (GET-PREFIXES (1+ START-RIP)
;;                                PREFIXES (1- CNT)
;;                                X86))))
;;   :hints (("Goal" :expand (GET-PREFIXES START-RIP PREFIXES CNT X86))))

;; ;; A version of X86ISA::GET-PREFIXES-OPENER-LEMMA-GROUP-2-PREFIX.
;; ;; simplified hyps should work better with axe
;; (DEFTHM GET-PREFIXES-OPENER-LEMMA-GROUP-2-PREFIX-simple
;;   (IMPLIES (AND (APP-VIEW X86)
;;                 (64-BIT-MODEP x86)
;;                 (LET* ((FLG (MV-NTH 0 (X86ISA::RME08 START-RIP *CS*
;;                                                   :X X86)))
;;                        (PREFIX-BYTE-GROUP-CODE
;;                         (x86isa::GET-ONE-BYTE-PREFIX-ARRAY-CODE
;;                          (MV-NTH 1 (X86ISA::RME08 START-RIP *CS*
;;                                                   :X X86)))))
;;                       (AND (NOT FLG)
;;                            (EQUAL PREFIX-BYTE-GROUP-CODE 2)))
;;                 (CANONICAL-ADDRESS-P (1+ START-RIP))
;;                 (NOT (ZP CNT)))
;;            (EQUAL
;;             (GET-PREFIXES START-RIP PREFIXES CNT X86)
;;             (GET-PREFIXES
;;                            (1+ START-RIP)
;;                            (X86ISA::!PREFIXES-SLICE
;;                                 :SEG
;;                                 (MV-NTH 1
;;                                         (X86ISA::RME08 START-RIP *CS*
;;                                                        :X X86))
;;                                 (X86ISA::!PREFIXES-SLICE
;;                                      :LAST-PREFIX 3 PREFIXES))
;;                            (1- CNT)
;;                            X86))))

;; ;; a version of x86isa::GET-PREFIXES-OPENER-LEMMA-GROUP-3-PREFIX
;; ;; simplified hyps should work better with axe
;; (DEFTHM GET-PREFIXES-OPENER-LEMMA-GROUP-3-PREFIX-simple
;;   (IMPLIES (AND (APP-VIEW X86)
;;                 (64-BIT-MODEP x86)
;;                 (LET* ((FLG (MV-NTH 0 (X86ISA::RME08 START-RIP *CS*
;;                                                   :X X86)))
;;                        (PREFIX-BYTE-GROUP-CODE
;;                         (x86isa::GET-ONE-BYTE-PREFIX-ARRAY-CODE
;;                          (MV-NTH 1 (X86ISA::RME08 START-RIP *CS*
;;                                                   :X X86)))))
;;                       (AND (NOT FLG)
;;                            (EQUAL PREFIX-BYTE-GROUP-CODE 3)))
;;                 (CANONICAL-ADDRESS-P (1+ START-RIP))
;;                 (NOT (ZP CNT)))
;;            (EQUAL
;;             (GET-PREFIXES START-RIP PREFIXES CNT X86)
;;             (GET-PREFIXES
;;                            (1+ START-RIP)
;;                            (X86ISA::!PREFIXES-SLICE
;;                                 :OPR
;;                                 (MV-NTH 1
;;                                         (X86ISA::RME08 START-RIP *CS*
;;                                                        :X X86))
;;                                 (X86ISA::!PREFIXES-SLICE
;;                                      :LAST-PREFIX 4 PREFIXES))
;;                            (1- CNT)
;;                            X86))))

;; ;; a version of x86isa::GET-PREFIXES-OPENER-LEMMA-GROUP-4-PREFIX
;; ;; simplified hyps should work better with axe
;; (DEFTHM GET-PREFIXES-OPENER-LEMMA-GROUP-4-PREFIX-simple
;;   (IMPLIES (AND (APP-VIEW X86)
;;                 (64-BIT-MODEP x86)
;;                 (LET* ((FLG (MV-NTH 0 (X86ISA::RME08 START-RIP *CS*
;;                                                      :X X86)))
;;                        (PREFIX-BYTE-GROUP-CODE
;;                         (x86isa::GET-ONE-BYTE-PREFIX-ARRAY-CODE
;;                          (MV-NTH 1 (X86ISA::RME08 START-RIP *CS*
;;                                                   :X X86)))))
;;                       (AND (NOT FLG)
;;                            (EQUAL PREFIX-BYTE-GROUP-CODE 4)))
;;                 (CANONICAL-ADDRESS-P (1+ START-RIP))
;;                 (NOT (ZP CNT)))
;;            (EQUAL
;;             (GET-PREFIXES START-RIP PREFIXES CNT X86)
;;             (GET-PREFIXES
;;              (1+ START-RIP)
;;              (X86ISA::!PREFIXES-SLICE
;;               :ADR
;;               (MV-NTH 1
;;                       (X86ISA::RME08 START-RIP *CS*
;;                                      :X X86))
;;               (X86ISA::!PREFIXES-SLICE
;;                :LAST-PREFIX 5 PREFIXES))
;;              (1- CNT)
;;              X86))))


;; We will leave X86-FETCH-DECODE-EXECUTE enabled (the ACL2 rule has
;; binding hyps that Axe doesn't yet handle).  Note that it opens up
;; to a call of ONE-BYTE-OPCODE-EXECUTE.  To prevent a huge case
;; split, we will keep ONE-BYTE-OPCODE-EXECUTE disabled but allow it
;; to open when everything but the RIP arguments is constant (that is,
;; when we managed to resolve the instruction).


;gen the 1?
(defthm unsigned-byte-p-of-bool->bit
  (unsigned-byte-p 1 (acl2::bool->bit x)))

;looped?
(defthmd not-member-p-canonical-address-listp-when-disjoint-p-alt
  (implies (and (x86isa::disjoint-p (x86isa::create-canonical-address-list m addr)
                                    (x86isa::create-canonical-address-list n prog-addr))
                (x86isa::member-p e (x86isa::create-canonical-address-list m addr)))
           (equal (x86isa::member-p e (x86isa::create-canonical-address-list n prog-addr))
                  nil)))

;helps us show that code read from the text section is independent of
;stuff from the stack, given an assumption about a larger region of
;the stack being independent from the text section
(defthm not-memberp-of-+-when-disjoint-from-larger-chunk
  (implies (and (syntaxp (and (quotep stack-slots)
                              (quotep neg-stack-offset)))
                (<= neg-stack-offset (- stack-slots))
                (integerp neg-stack-offset) ;should be negative
                (disjoint-p (x86isa::create-canonical-address-list text-len text-offset)
                            (x86isa::create-canonical-address-list total-stack-slots (+ neg-total-stack-offset (xr ':rgf '4 x86))))
                (syntaxp (and (quotep total-stack-slots)
                              (quotep neg-total-stack-offset)))
                (equal neg-total-stack-offset (- total-stack-slots)) ;could gen but maybe no need to
                ;(<= stack-slots total-stack-slots)
                (<= neg-total-stack-offset neg-stack-offset)
                (canonical-address-p$inline text-offset)
                (canonical-address-p$inline (+ (+ -1 text-len) text-offset))
                (canonical-address-p$inline (+ neg-total-stack-offset (xr ':rgf '4 x86)))
                (canonical-address-p$inline (xr ':rgf '4 x86))
                (natp n)
                (< n text-len)
                (natp text-len)
                (natp stack-slots)
                (posp total-stack-slots)
                )
           (not (x86isa::MEMBER-P (+ n TEXT-OFFSET)
                          ; we take some number of stack items (like 4), starting at some address below the stack pointer (like rsp-24)
                          (CREATE-CANONICAL-ADDRESS-LIST stack-slots (+ neg-stack-offset (XR ':RGF '4 X86))))))
  :hints (("Goal" :use ((:instance x86isa::NOT-MEMBER-P-CANONICAL-ADDRESS-LISTP-WHEN-DISJOINT-P
                                   (e (+ n TEXT-OFFSET))
                                   (n total-stack-slots)
                                   (PROG-ADDR (+ neg-total-stack-offset (XR ':RGF '4 X86)))
                                   (m text-len)
                                   (addr text-offset))
                        (:instance x86isa::NOT-MEMBER-P-OF-SUPERSET-IS-NOT-MEMBER-P-OF-SUBSET
                                   (e (+ n TEXT-OFFSET))
                                   (x (CREATE-CANONICAL-ADDRESS-LIST stack-slots (+ neg-stack-offset (XR :RGF *RSP* X86))))
                                   (y (CREATE-CANONICAL-ADDRESS-LIST total-stack-slots (+ neg-total-stack-offset (XR :RGF *RSP* X86))))))

           :in-theory (e/d (x86isa::DISJOINT-P-COMMUTATIVE
                            ;;NOT-MEMBER-P-OF-SUPERSET-IS-NOT-MEMBER-P-OF-SUBSET
                            )
                           (x86isa::NOT-MEMBER-P-CANONICAL-ADDRESS-LISTP-WHEN-DISJOINT-P
                            x86isa::NOT-MEMBER-P-WHEN-DISJOINT-P)))))

(defthm disjoint-of-CREATE-CANONICAL-ADDRESS-LIST-and-CREATE-CANONICAL-ADDRESS-LIST-stack-and-text
  (implies (and (syntaxp (and (quotep stack-slots)
                              (quotep neg-stack-offset)))
                (<= neg-stack-offset (- stack-slots))
                (integerp neg-stack-offset) ;should be negative
                (disjoint-p (create-canonical-address-list text-len text-offset)
                            (create-canonical-address-list total-stack-slots (+ neg-total-stack-offset (xr ':rgf '4 x86))))
                (syntaxp (and (quotep total-stack-slots)
                              (quotep neg-total-stack-offset)))
                (equal neg-total-stack-offset (- total-stack-slots)) ;could gen but maybe no need to
                (<= neg-total-stack-offset neg-stack-offset)
                (canonical-address-p$inline text-offset)
                (canonical-address-p$inline (+ (+ -1 text-len) text-offset))
                (canonical-address-p$inline (+ neg-total-stack-offset (xr ':rgf '4 x86)))
                (canonical-address-p$inline (xr ':rgf '4 x86))
                (natp n)
                (<= (+ n text-bytes) text-len)
                (natp text-len)
                (natp text-bytes)
                (natp stack-slots)
                (posp total-stack-slots)
                )
           (disjoint-p (CREATE-CANONICAL-ADDRESS-LIST text-bytes (+ n TEXT-OFFSET))
                       ;; we take some number of stack items (like 4), starting at some address below the stack pointer (like rsp-24)
                       (CREATE-CANONICAL-ADDRESS-LIST stack-slots (+ neg-stack-offset (XR ':RGF '4 X86)))))
  :hints (("Goal"
           :in-theory (e/d (x86isa::DISJOINT-P-COMMUTATIVE
                            ;;NOT-MEMBER-P-OF-SUPERSET-IS-NOT-MEMBER-P-OF-SUBSET
                            )
                           (x86isa::NOT-MEMBER-P-CANONICAL-ADDRESS-LISTP-WHEN-DISJOINT-P
                            x86isa::NOT-MEMBER-P-WHEN-DISJOINT-P)))))

;special case for n=0
(defthm disjoint-of-CREATE-CANONICAL-ADDRESS-LIST-and-CREATE-CANONICAL-ADDRESS-LIST-stack-and-text-special
  (implies (and (syntaxp (and (quotep stack-slots)
                              (quotep neg-stack-offset)))
                (<= neg-stack-offset (- stack-slots))
                (integerp neg-stack-offset) ;should be negative
                (disjoint-p (create-canonical-address-list text-len text-offset)
                            (create-canonical-address-list total-stack-slots (+ neg-total-stack-offset (xr ':rgf '4 x86))))
                (syntaxp (and (quotep total-stack-slots)
                              (quotep neg-total-stack-offset)))
                (equal neg-total-stack-offset (- total-stack-slots)) ;could gen but maybe no need to
                (<= neg-total-stack-offset neg-stack-offset)
                (canonical-address-p$inline text-offset)
                (canonical-address-p$inline (+ (+ -1 text-len) text-offset))
                (canonical-address-p$inline (+ neg-total-stack-offset (xr ':rgf '4 x86)))
                (canonical-address-p$inline (xr ':rgf '4 x86))
;                (natp n)
                (<= text-bytes text-len) ;(<= (+ n text-bytes) text-len)
                (natp text-len)
                (natp text-bytes)
                (natp stack-slots)
                (posp total-stack-slots)
                )
           (disjoint-p (CREATE-CANONICAL-ADDRESS-LIST text-bytes TEXT-OFFSET)
                       ;; we take some number of stack items (like 4), starting at some address below the stack pointer (like rsp-24)
                       (CREATE-CANONICAL-ADDRESS-LIST stack-slots (+ neg-stack-offset (XR ':RGF '4 X86)))))
  :hints (("Goal"
           :in-theory (e/d (x86isa::DISJOINT-P-COMMUTATIVE
                            ;;NOT-MEMBER-P-OF-SUPERSET-IS-NOT-MEMBER-P-OF-SUBSET
                            )
                           (x86isa::NOT-MEMBER-P-CANONICAL-ADDRESS-LISTP-WHEN-DISJOINT-P
                            x86isa::NOT-MEMBER-P-WHEN-DISJOINT-P)))))

;dup
;why did this cause loops?
(defthm canonical-address-listp-of-cdr
  (implies (x86isa::canonical-address-listp lst)
           (x86isa::canonical-address-listp (cdr lst))))

;dup
(acl2::defopeners x86isa::COMBINE-BYTES :hyps ((syntaxp (quotep x86isa::bytes))))

;This is kind of a hack.  It's needed because the assumption is not
;obviously a boolean.  TODO: add a backchain limit (or poor man's
;backchain limit)?  TODO: Generalize to any if test?
(defthm if-of-xr-app-view
  (implies (app-view x86)
           (equal (if (app-view x86) tp ep)
                  tp)))


;maybe only needed for PE files?
;helps us show that code read from the text section is independent of stuff
;from the stack (the 32-byte shadow region), given an assumption about a larger
;region of the stack being independent from the text section
(defthm not-memberp-of-+-when-disjoint-from-larger-chunk-pos
  (implies (and (syntaxp (and (quotep stack-slots)
                              (quotep pos-stack-offset)))
                ;; free vars here:
                (disjoint-p (create-canonical-address-list text-len text-offset)
                            (create-canonical-address-list total-stack-slots (xr ':rgf '4 x86)))
                (syntaxp (quotep total-stack-slots))

                (natp pos-stack-offset)
                (natp stack-slots)
                (integerp total-stack-slots)
                (<= (+ stack-slots pos-stack-offset) total-stack-slots)
                (canonical-address-p$inline text-offset)
                (canonical-address-p$inline (+ (+ -1 text-len) text-offset))
                (canonical-address-p$inline (+ (+ -1 total-stack-slots) (xr ':rgf '4 x86)))
                (canonical-address-p$inline (xr ':rgf '4 x86))
                (natp n)
                (< n text-len)
                (natp text-len))
           (not (MEMBER-P (+ n TEXT-OFFSET)
                          ;; we take some number of stack items (like 4), starting at some address above the stack pointer (like rsp+8)
                          (CREATE-CANONICAL-ADDRESS-LIST stack-slots (+ pos-stack-offset (XR ':RGF '4 X86))))))
  :hints (("Goal" :use ((:instance x86isa::NOT-MEMBER-P-CANONICAL-ADDRESS-LISTP-WHEN-DISJOINT-P
                                   (e (+ n TEXT-OFFSET))
                                   (n stack-slots)
                                   (PROG-ADDR (+ pos-stack-offset (XR ':RGF '4 X86)))
                                   (m text-len)
                                   (addr text-offset))
                        (:instance x86isa::DISJOINT-P-SUBSET-P
                                   (a (CREATE-CANONICAL-ADDRESS-LIST TEXT-LEN TEXT-OFFSET))
                                   (b (CREATE-CANONICAL-ADDRESS-LIST
                        STACK-SLOTS
                        (+ POS-STACK-OFFSET (XR :RGF *RSP* X86))))
                                   (x (CREATE-CANONICAL-ADDRESS-LIST TEXT-LEN TEXT-OFFSET))
                                   (y (CREATE-CANONICAL-ADDRESS-LIST TOTAL-STACK-SLOTS (XR :RGF *RSP* X86))))
                        )

           :in-theory (e/d (x86isa::DISJOINT-P-COMMUTATIVE
                            ;;NOT-MEMBER-P-OF-SUPERSET-IS-NOT-MEMBER-P-OF-SUBSET
                            )
                           (x86isa::NOT-MEMBER-P-CANONICAL-ADDRESS-LISTP-WHEN-DISJOINT-P
                            x86isa::NOT-MEMBER-P-WHEN-DISJOINT-P
                            x86isa::DISJOINT-P-SUBSET-P)))))

;tell shilpi
(defthm disjoint-p-two-create-canonical-address-lists-thm-0-gen
  (implies (<= (+ i x) y)
           (disjoint-p (create-canonical-address-list i x)
                       (create-canonical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p create-canonical-address-list)
                                  nil))))

;tell shilpi
(defthm disjoint-p-two-create-canonical-address-lists-thm-1-gen
  (implies (<= (+ j y) x)
           (disjoint-p (create-canonical-address-list i x)
                       (create-canonical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p create-canonical-address-list)
                                  nil))))

(defthm combine-bytes-of-if-when-constants
  (implies (syntaxp (and (quotep tp)
                         (quotep ep)))
           (equal (x86isa::combine-bytes (if test tp ep))
                  (if test
                      (x86isa::combine-bytes tp)
                    (x86isa::combine-bytes ep)))))

(defthm rb-wb-disjoint-eric
  (implies (and (separate r-x n-1 addr-1 w n-2 addr-2)
                (app-view x86))
           (equal (mv-nth 1
                          (rb n-1 addr-1 r-x
                              (mv-nth 1 (wb n-2 addr-2 w val x86))))
                  (mv-nth 1 (rb n-1 addr-1 r-x x86)))))

(defthm rb-of-if-arg2
  (equal (rb n (if test addr1 addr2) rx x86)
         (if test
             (rb n addr1 rx x86)
           (rb n addr2 rx x86))))

;; ;see also !flgi-and-wb-in-app-view (but that seems like a bad rule -- reuse of val -- tell shilpi)
;; (defthm !flgi-of-mv-nth-1-of-wb
;;   (implies (app-view x86)
;;            (equal (!flgi flg val (mv-nth '1 (wb n addr w value x86)))
;;                   (mv-nth '1 (wb n addr w value (!flgi flg val x86)))))
;;   :hints (("Goal" :in-theory (enable !flgi wb))))

(defthm unsigned-byte-p-of-mv-nth-1-of-rvm08
  (implies (and (<= 8 size)
                (app-view x86)
                (canonical-address-p base-addr)
                (x86p x86))
           (equal (unsigned-byte-p size
                                   (mv-nth 1 (rvm08 base-addr x86)))
                  (natp size)))
  :hints (("Goal" :in-theory (enable rvm08 MEMI))))

(defthm address-aligned-p-of-8-and-nil
  (equal (x86isa::address-aligned-p addr 8 nil)
         (equal (acl2::bvchop 3 addr) 0))
  :hints (("Goal" :cases ((integerp addr)) ;because of the force in acl2::logand-with-mask
           :in-theory (enable x86isa::address-aligned-p))))

(defthm address-aligned-p-of-4-and-nil
  (equal (x86isa::address-aligned-p addr 4 nil)
         (equal (acl2::bvchop 2 addr) 0))
  :hints (("Goal" :cases ((integerp addr)) ;because of the force in acl2::logand-with-mask
           :in-theory (enable x86isa::address-aligned-p))))


(defthm x86isa::rflagsbits->of$inline-of-if-safe
  (implies (syntaxp (if (quotep tp)
                        t
                      (quotep ep)))
           (equal (x86isa::rflagsbits->of$inline (if test tp ep))
                  (if test (x86isa::rflagsbits->of$inline tp) (x86isa::rflagsbits->of$inline ep)))))

(defthm x86isa::rflagsbits->sf$inline-of-if-safe
  (implies (syntaxp (if (quotep tp)
                        t
                      (quotep ep)))
           (equal (x86isa::rflagsbits->sf$inline (if test tp ep))
                  (if test (x86isa::rflagsbits->sf$inline tp) (x86isa::rflagsbits->sf$inline ep)))))

(defthm x86isa::rflagsbits->cf$inline-of-if-safe
  (implies (syntaxp (if (quotep tp)
                        t
                      (quotep ep)))
           (equal (x86isa::rflagsbits->cf$inline (if test tp ep))
                  (if test (x86isa::rflagsbits->cf$inline tp) (x86isa::rflagsbits->cf$inline ep)))))

(defthm x86isa::rflagsbits->af$inline-of-if-safe
  (implies (syntaxp (if (quotep tp)
                        t
                      (quotep ep)))
           (equal (x86isa::rflagsbits->af$inline (if test tp ep))
                  (if test (x86isa::rflagsbits->af$inline tp) (x86isa::rflagsbits->af$inline ep)))))

(defthm x86isa::rflagsbits->zf$inline-of-if-safe
  (implies (syntaxp (if (quotep tp)
                        t
                      (quotep ep)))
           (equal (x86isa::rflagsbits->zf$inline (if test tp ep))
                  (if test (x86isa::rflagsbits->zf$inline tp) (x86isa::rflagsbits->zf$inline ep)))))

(defthm x86isa::rflagsbits->pf$inline-of-if-safe
  (implies (syntaxp (if (quotep tp)
                        t
                      (quotep ep)))
           (equal (x86isa::rflagsbits->pf$inline (if test tp ep))
                  (if test (x86isa::rflagsbits->pf$inline tp) (x86isa::rflagsbits->pf$inline ep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm x86isa::rflagsbits->of$inline-of-if
  (equal (rflagsbits->of$inline (if test tp ep))
         (if test (rflagsbits->of$inline tp) (rflagsbits->of$inline ep))))

(defthm x86isa::rflagsbits->sf$inline-of-if
  (equal (rflagsbits->sf$inline (if test tp ep))
                  (if test (rflagsbits->sf$inline tp) (rflagsbits->sf$inline ep))))

(defthm x86isa::rflagsbits->cf$inline-of-if
  (equal (rflagsbits->cf$inline (if test tp ep))
         (if test (rflagsbits->cf$inline tp) (rflagsbits->cf$inline ep))))

(defthm x86isa::rflagsbits->af$inline-of-if
  (equal (rflagsbits->af$inline (if test tp ep))
         (if test (rflagsbits->af$inline tp) (rflagsbits->af$inline ep))))

(defthm x86isa::rflagsbits->zf$inline-of-if
  (equal (rflagsbits->zf$inline (if test tp ep))
         (if test (rflagsbits->zf$inline tp) (rflagsbits->zf$inline ep))))

(defthm x86isa::rflagsbits->pf$inline-of-if
  (equal (rflagsbits->pf$inline (if test tp ep))
         (if test (rflagsbits->pf$inline tp) (rflagsbits->pf$inline ep))))


(defthm unsigned-byte-p-1-of-rflagsbits->cf$inline (unsigned-byte-p 1 (x86isa::rflagsbits->cf$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->res1$inline (unsigned-byte-p 1 (x86isa::rflagsbits->res1$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->pf$inline (unsigned-byte-p 1 (x86isa::rflagsbits->pf$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->ID$inline (unsigned-byte-p 1 (x86isa::rflagsbits->ID$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->VIP$inline (unsigned-byte-p 1 (x86isa::rflagsbits->VIP$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->VIF$inline (unsigned-byte-p 1 (x86isa::rflagsbits->VIF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->AC$inline (unsigned-byte-p 1 (x86isa::rflagsbits->AC$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->VM$inline (unsigned-byte-p 1 (x86isa::rflagsbits->VM$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->RF$inline (unsigned-byte-p 1 (x86isa::rflagsbits->RF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->RES4$inline (unsigned-byte-p 1 (x86isa::rflagsbits->RES4$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->NT$inline (unsigned-byte-p 1 (x86isa::rflagsbits->NT$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->OF$inline (unsigned-byte-p 1 (x86isa::rflagsbits->OF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->DF$inline (unsigned-byte-p 1 (x86isa::rflagsbits->DF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->INTF$inline (unsigned-byte-p 1 (x86isa::rflagsbits->INTF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->TF$inline (unsigned-byte-p 1 (x86isa::rflagsbits->TF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->SF$inline (unsigned-byte-p 1 (x86isa::rflagsbits->SF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->ZF$inline (unsigned-byte-p 1 (x86isa::rflagsbits->ZF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->RES3$inline (unsigned-byte-p 1 (x86isa::rflagsbits->RES3$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->AF$inline (unsigned-byte-p 1 (x86isa::rflagsbits->AF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->RES2$inline (unsigned-byte-p 1 (x86isa::rflagsbits->RES2$inline rflags)))
(defthm unsigned-byte-p-2-of-rflagsbits->iopl$inline (unsigned-byte-p 2 (x86isa::rflagsbits->iopl$inline rflags)))
