; Mixed x86 supporting material
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;todo: use X package

;TODO: Separate out the x86 rules in this file from liter utilities like normal-output-indicatorp

(include-book "projects/x86isa/proofs/utilities/app-view/top" :dir :system)
;(include-book "projects/x86isa/tools/execution/top" :dir :system) ;todo don't even use init-x86-state?
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/utilities/polarity" :dir :system)
(include-book "kestrel/x86/parsers/mach-o-tools" :dir :system)
(include-book "kestrel/bv/rules10" :dir :system)
(include-book "bitops")
;(include-book "kestrel/x86/linear-memory" :dir :system)
(include-book "kestrel/utilities/defconst-computed" :dir :system)
(include-book "kestrel/axe/rules2" :dir :system) ;drop?
;(include-book "axe/bv-rules-axe" :dir :kestrel-acl2)
;(include-book "kestrel/axe/rules1" :dir :system)
;(include-book "kestrel/axe/axe-rules-mixed" :dir :system)
(include-book "run-until-return")
(include-book "kestrel/bv/rules3" :dir :system)
(include-book "kestrel/utilities/mv-nth" :dir :system)
(include-book "kestrel/axe/util2" :dir :system) ;for make-cons-nest
(include-book "support0")
(include-book "support32")
;(include-book "assumptions")
(include-book "read-and-write")
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(local (include-book "kestrel/bv/arith" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;for logand-with-mask
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/bv/idioms" :dir :system))


;; (in-theory (disable acl2::car-to-nth-0))
;; (in-theory (disable acl2::nth-of-cdr)) ;new
;; (in-theory (enable nth))
;; ;(local (in-theory (enable LIST::NTH-OF-CONS)))

;(in-theory (disable ACL2::MEMBER-OF-CONS)) ;potentially bad (matches constants)
(in-theory (disable ACL2::SMALL-INT-HACK)) ;slow
(in-theory (disable ACL2::ZP-WHEN-GT-0)) ;slow
(in-theory (disable ACL2::ZP-WHEN-INTEGERP)) ;slow
(in-theory (disable ACL2::SLICE-TOO-HIGH-IS-0)) ;slow
(in-theory (disable mv-nth))

;; Seems needed because the model adds 7 to rsp-8 and tests whether
;; the result is canonical.  I guess it's testing the highest address
;; of the 8 bit block.
(defthm canonical-address-p-of-minus-1
  (implies (equal 0 (mod x 8))
           (equal (canonical-address-p (+ -1 x))
                  (canonical-address-p (+ -8 x))))
  :hints (("Goal" :in-theory (enable canonical-address-p signed-byte-p ;acl2::mod-=-0
                                     ))))

;; Just a wrapper that is in the x86isa package instead of the ACL2 package.
(defmacro defconst-computed (name form)
  `(acl2::defconst-computed ,name ,form))

;nonsensical
;; (defthm nth-of-mv-nth-1-of-rb-1
;;   (implies (and (not (mv-nth 0 (rb-1 addresses r-w-x x86 nil)))
;;                 (natp n)
;;                 (< n (len addresses))
;;                 (x86isa::canonical-address-listp addresses)
;;                 (app-view x86) ;drop?
;;                 )
;;            (equal (nth n (mv-nth 1 (rb-1 addresses r-w-x x86 nil)))
;;                   (car (mv-nth 1 (rb-1 (list (nth n addresses)) r-w-x x86 nil)))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable ;list::nth-of-cons
;;                        acl2::car-to-nth-0 (:induction nth)))))

(defthm canonical-address-p-of-nth
  (implies (and (x86isa::canonical-address-listp addresses)
                (natp n)
                (< n (len addresses)))
           (canonical-address-p (nth n addresses)))
  :hints (("Goal" :in-theory (e/d (nth) (;acl2::nth-of-cdr
                                         )))))

(defthm nth-of-pos
  (implies (x86isa::member-p item list)
           (equal (nth (x86isa::pos item list) list)
                  item))
  :hints (("Goal" :in-theory (e/d (nth x86isa::pos) (;acl2::nth-of-cdr
                                                     )))))

(defthm byte-listp-of-true-list-fix
  (implies (byte-listp bytes)
           (byte-listp (acl2::true-list-fix bytes))))

;helps in backchaining
(defthm <-when-<=-and-not-equal-cheap
  (implies (and (<= paddr addr)
                (not (equal addr paddr))
                (acl2-numberp addr)
                (acl2-numberp paddr))
           (< paddr addr))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 nil nil))))


 ;try to get my rule to fire:
(in-theory (disable ;rb-in-terms-of-nth-and-pos
                    ;rb-in-terms-of-rb-subset-p
                    ;combine-bytes-rb-in-terms-of-rb-subset-p
            ))






;(in-theory (enable create-canonical-address-list)) ;or rewrite it when the number of addrs is 1

;; (thm
;;  (Implies (and (CANONICAL-ADDRESS-p rip)
;;                (natp len)
;;                (natp k)
;;                (< k len)
;;                (CANONICAL-ADDRESS-p (+ len rip)))
;;           (MEMBER-P (BINARY-+ k RIP) (CREATE-CANONICAL-ADDRESS-LIST len RIP))))

;how does this not already exist?
(defthm len-of-append
  (equal (len (append x y))
         (+ (len x) (len y))))


;; simplify (this is reading the jump offset from the code?):
;; (CANONICAL-ADDRESS-P$INLINE
;;    (BINARY-+
;;     '32
;;     (BINARY-+
;;      (XR ':RIP '0 X86)
;;      (LOGEXT
;;       '32
;;       (COMBINE-BYTES
;;        (MV-NTH
;;          '1
;;          (RB (CREATE-CANONICAL-ADDRESS-LIST '4
;;                                             (BINARY-+ '28 (XR ':RIP '0 X86)))
;;              ':X
;;              X86)))))))

;; ;drop?
;; (defthm hack
;;   (implies (and (DISJOINT-P (CREATE-CANONICAL-ADDRESS-LIST 154 rip)
;;                             (CREATE-CANONICAL-ADDRESS-LIST 24 (+ -24 rsp)))
;;                 (canonical-address-p (+ 153 rip))
;;                 (canonical-address-p rip)
;;                 (CANONICAL-ADDRESS-P (+ -24 RSP)) ;off by 1?
;;                 (CANONICAL-ADDRESS-P RSP))

;;            (DISJOINT-P
;;             (CONS (BINARY-+ '1 rip)
;;                   'NIL)
;;             (CREATE-CANONICAL-ADDRESS-LIST '8
;;                                            (BINARY-+ '-8 rsp)))))

;slow:
(in-theory (disable DEFAULT-CDR
                    ;ACL2::CONSP-OF-ASSOC-EQUAL
                    alistp
                    ;assoc-list
                    ))

;seems bad:
;(in-theory (disable WB-AND-WB-COMBINE-WBS))

;seems needed
(in-theory (enable x86isa::GPR-SUB-SPEC-8$INLINE))

(defthm equal-of-if-constants
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep k3)))
           (equal (equal (if test k1 k2) k3)
                  (if test
                      (equal k1 k3) ;gets computed
                    (equal k2 k3))))) ;gets computed

;perhaps restrict
(defthm mv-nth-of-if
  (equal (mv-nth n (if test l1 l2))
         (if test
             (mv-nth n l1)
           (mv-nth n l2))))

;todo: seems odd that we need this (I saw an access to bit 2)
(defthm getbit-of-sub-af-spec64$inline
  (implies (posp n)
           (equal (acl2::getbit n (x86isa::sub-af-spec64$inline dst src))
                  0))
  :hints (("Goal" :in-theory (enable x86isa::sub-af-spec64$inline bool->bit))))

;why needed?
(defthm getbit-of-pf-spec64$inline
  (implies (posp n)
           (equal (acl2::getbit n (x86isa::pf-spec64$inline result))
                  0))
  :hints (("Goal" :in-theory (enable x86isa::pf-spec64$inline bool->bit))))

;why needed? (TODO: add more)
(defthm getbit-of-pf-spec32
  (implies (posp n)
           (equal (acl2::getbit n (pf-spec32 result))
                  0))
  :hints (("Goal" :in-theory (enable pf-spec32 bool->bit))))

(defthm getbit-of-sf-spec32
  (implies (posp n)
           (equal (acl2::getbit n (x86isa::sf-spec32 result))
                  0))
  :hints (("Goal" :in-theory (enable x86isa::sf-spec32 bool->bit))))

;move
(defthmd bvshl-becomes-*-of-expt
  (implies (and (integerp x)
                (natp shift-amount)
                (integerp width))
           (equal (ACL2::BVSHL width x shift-amount)
                  (acl2::bvchop width (* (expt 2 shift-amount) x))))
  :hints (("Goal" :in-theory (enable acl2::bvshl acl2::bvcat))))

(defthmd rb-split
  (implies (and (posp n)
                (APP-VIEW X86)
                (CANONICAL-ADDRESS-P ADDR)
                (CANONICAL-ADDRESS-P (+ -1 n ADDR))
                (x86p x86) ;too bad
                )
           (equal (mv-nth 1 (rb n addr r-w-x x86))
                  (acl2::bvcat (* 8 (+ -1 n))
                               (mv-nth 1 (rb (+ -1 n) (+ 1 addr) r-w-x x86))
                               8
                               (mv-nth 1 (rb 1 addr r-w-x x86))
                               )))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (rb rb-1 ash ;rvm08
                                      acl2::bvcat-becomes-bvor-of-bvshl acl2::bvor bvshl-becomes-*-of-expt ;acl2::bvshl ; ACL2::BVCAT
                                      acl2::logapp
                                      APP-VIEW
                                      natp
                                      ) (ACL2::BVCAT-EQUAL-REWRITE-ALT
                                         ACL2::BVCAT-EQUAL-REWRITE
                                         X::MV-NTH-1-OF-RB-1-BECOMES-READ
                                         ACL2::BVSHL-REWRITE-WITH-BVCHOP ;looped
                                         )))))

(local (in-theory (enable APP-VIEW)))

;to handle a multi-byte RB by peeling off one known byte at a time
(defthm rb-in-terms-of-nth-and-pos-eric-gen
  (implies (and ;; find that a program is loaded in the initial state:
            (program-at paddr bytes x86-init)
            ;; try to prove that the same program is loaded in the current state:
            (program-at paddr bytes x86)
            (byte-listp bytes)
            (<= paddr addr)
            (integerp addr)
            (< addr (+ paddr (len bytes)))
            (posp n)
            (CANONICAL-ADDRESS-P ADDR)
;            (member-p (first addrs) addresses)
;            (canonical-address-p addr)
;            (x86isa::canonical-address-listp addresses)
 ;           (X86ISA::CANONICAL-ADDRESS-LISTP (CDR ADDRS)) ;why?
            (canonical-address-p paddr)
            (CANONICAL-ADDRESS-P (+ -1 ADDR N))
            ;(<= (+ addr n) (+ paddr (len bytes)))
            (canonical-address-p (+ -1 (len bytes) paddr))

            (app-view x86)
            (app-view x86-init)
            (X86P X86) ;too bad
            )
           (equal (mv-nth 1 (rb n addr r-w-x x86))
                  (acl2::bvcat (* 8 (+ -1 n))
                               (mv-nth 1 (rb (+ -1 n) (+ 1 addr) r-w-x x86))
                               8
                               (nth (- addr paddr)
                                      bytes))))
  :hints (("Goal" :do-not-induct t
           :use (rb-split
                 (:instance x86isa::RB-RB-SUBSET (j 1) (addr-j addr) (r-x-j r-w-x)
                           (val (x86isa::COMBINE-BYTES (ACL2::TRUE-LIST-FIX BYTES)))
                           (i (LEN BYTES))
                           (addr-i paddr)
                           (r-x-i :x)))
;           :expand (RB-1 ADDRS R-W-X X86 NIL)
           :in-theory (e/d (;rb rb-1
                            program-at
                            ash

                            )
                           (;rb-1-when-not-r
                            distributivity ;blocks slice-of-combine-bytes
                            ACL2::BVCAT-EQUAL-REWRITE-ALT
                            ACL2::BVCAT-EQUAL-REWRITE)))))



;; ;(in-theory (disable read64))
;; ;use this?
;; ;TODO: Maybe gen to read n contiguous bytes into a BV of length 8n?
;; ;maybe we don't need this, now that rb is nicer
;; (defthmd introduce-read64
;;   (implies (and (canonical-address-p addr)
;;                 (canonical-address-p (+ 7 addr)))
;;            (equal (mv-nth
;;                     '1
;;                     (rb 8 addr ':r x86))
;;                   (x::read64 addr x86))))


; flag 12 also overwrites flag 13?
;; (defthm getbit-of-xr-flags-of-!flgi-undefined-diff
;;   (implies (and (syntaxp (and (quote m)
;;                               (quote n)))
;;                 (not (equal m n))
;;                 (natp m)
;;                 (< m 32)
;;                 (natp n)
;;                 (member-equal m '(0 2 4 6 7 8 9 10 11 ;12
;;                                     14 16 17 18 19 20 21))
;;                 (member-equal n '(0 2 4 6 7 8 9 10 11 ;12
;;                                     14 16 17 18 19 20 21))
;;                 (x86p x86))
;;            (equal (acl2::getbit m (xr ':rflags '0 (x86isa::!flgi-undefined$inline n x86)))
;;                   (acl2::getbit m (xr ':rflags '0 x86))))
;;   :hints (("Goal" :cases ((< m n))
;;            :in-theory (e/d (x86isa::!flgi-undefined
;;                             LIST::MEMBERP-OF-CONS ;gross? instead, prove integerp from member of constant list of integers..
;;                             !FLGI)
;;                            (member-equal
;;                             ;LIST::MEMBERP-OF-CONS ;yuck: proof is by cases
;;                             acl2::logmask
;;                             bitops::part-select-width-low
;;                             bitops::part-install-width-low)))))

;sign flag
(defthmd sf-spec32-rewrite
  (equal (x86isa::sf-spec32 x)
         (acl2::getbit 31 x))
  :hints (("Goal" :in-theory (enable x86isa::sf-spec32))))

;TODO: need lemmas about logand, ash, etc. in order to prove the
;theorem that justifies the lift (why?)  TODO: try simpify-defun?

;todo: add theory invars since these can loop with the definitions of the bvops
; also add a ruleset for easy disabling of such things

; A copy of rb-nil-lemma, except this is introduced very late and so should
; fire first.
;; (defthm rb-nil-lemma2
;;   (equal (mv-nth 1 (rb nil r-w-x x86))
;;          nil))
;; (in-theory (disable rb-nil-lemma))

(in-theory (disable DEFAULT-<-1))

;(include-book "kestrel/bv/rules3" :dir :system) ;to normalize more
(in-theory (enable acl2::bvplus-of-unary-minus acl2::bvplus-of-unary-minus-arg2))
(in-theory (disable ACL2::BOUND-FROM-NATP-FACT)) ;slow

;see also mv-nth-cons-meta, but axe can't use it
(defthm mv-nth-of-cons
  (implies (and (syntaxp (quotep n))
                (natp n))
           (equal (mv-nth n (cons a b))
                  (if (zp n)
                      a
                    (mv-nth (+ -1 n) b))))
  :hints (("Goal" :in-theory (enable mv-nth))))

;; (defthm rb-of-nil
;;   (equal (rb nil r-w-x x86)
;;          (mv nil nil x86))
;;   :hints (("Goal" :in-theory (enable rb))))



;is there a way to limit this?

;; (defthm true-listp-of-byte-ify
;;   (true-listp (byte-ify n val)))

(defthm combine-bytes-when-singleton
  (implies (equal 1 (len lst))
           (equal (x86isa::combine-bytes lst)
                  (if (unsigned-byte-p 8 (car lst))
                      (car lst)
                    0))) ;yikes.  combine-bytes should chop its arg?
  :hints (("Goal" :expand (x86isa::combine-bytes lst)
           :in-theory (enable x86isa::combine-bytes))))

;move or drop?
(defthm acl2::assoc-equal-of-cons-irrel
  (implies (not (equal acl2::key (car a)))
           (equal (assoc-equal acl2::key (cons a acl2::rst))
                  (assoc-equal acl2::key acl2::rst)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm get-one-byte-prefix-array-code-rewrite-quotep
  (implies (syntaxp (quotep byte))
           (equal (x86isa::get-one-byte-prefix-array-code byte)
                  (acl2::lookup (acl2::bvchop 8 byte)
                                (cdr x86isa::*one-byte-prefixes-group-code-info-ar*))))
  :hints (("Goal" :in-theory (e/d (x86isa::get-one-byte-prefix-array-code aref1 acl2::assoc-equal-of-cons)
                                  (acl2::not-equal-bvchop-when-not-equal-bvchop
                                   acl2::rewrite-bv-equality-when-sizes-dont-match-2)))))

;can loop with CANONICAL-ADDRESS-P-BETWEEN
(defthmd integerp-when-canonical-address-p
  (implies (canonical-address-p x)
           (integerp x)))

(defthm integerp-when-canonical-address-p-cheap
  (implies (and (canonical-address-p free)
                (equal free x))
           (integerp x)))

(defthm 64-bit-mode-one-byte-opcode-modr/m-p-rewrite-quotep
  (implies (and (syntaxp (quotep byte))
                (unsigned-byte-p 8 byte))
           (equal (x86isa::64-bit-mode-one-byte-opcode-modr/m-p byte)
                  (acl2::lookup byte
                                (cdr x86isa::*64-bit-mode-one-byte-has-modr/m-ar*))))
  :hints (("Goal" :in-theory (e/d (x86isa::64-bit-mode-one-byte-opcode-modr/m-p aref1 acl2::assoc-equal-of-cons)
                                  (acl2::not-equal-bvchop-when-not-equal-bvchop)))))

;since axe can eval nth but not mv-nth
(defthm mv-nth-becomes-nth-when-constants
  (implies (and (syntaxp (quotep n))
                (syntaxp (quotep x)))
           (equal (mv-nth n x)
                  (nth n x)))
  :hints (("Goal" :in-theory (enable acl2::mv-nth-becomes-nth))))

(defthm canonical-address-p-of-logext-64
  (implies (canonical-address-p x)
           (canonical-address-p (logext 64 x)))) ;when can we drop the logext completely?

(acl2::defopeners get-prefixes)

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

;todo: make defopeners use the untranslated body
;todo: make defopeners check for redundancy
;todo: make defopeners suppress printing
;todo: use def-constant-opener?
(acl2::defopeners one-byte-opcode-execute :hyps ((syntaxp (and (quotep x86isa::prefixes)
                                                                (quotep x86isa::rex-byte)
                                                                (quotep x86isa::opcode)
                                                                (quotep x86isa::modr/m)
                                                                (quotep x86isa::sib)))))

(in-theory (disable x86isa::one-byte-opcode-execute))

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
                            (x86isa::create-canonical-address-list total-stack-slots (binary-+ neg-total-stack-offset (xr ':rgf '4 x86))))
                (syntaxp (and (quotep total-stack-slots)
                              (quotep neg-total-stack-offset)))
                (equal neg-total-stack-offset (- total-stack-slots)) ;could gen but maybe no need to
                ;(<= stack-slots total-stack-slots)
                (<= neg-total-stack-offset neg-stack-offset)
                (canonical-address-p$inline text-offset)
                (canonical-address-p$inline (binary-+ (+ -1 text-len) text-offset))
                (canonical-address-p$inline (binary-+ neg-total-stack-offset (xr ':rgf '4 x86)))
                (canonical-address-p$inline (xr ':rgf '4 x86))
                (natp n)
                (< n text-len)
                (natp text-len)
                (natp stack-slots)
                (posp total-stack-slots)
                )
           (not (x86isa::MEMBER-P (BINARY-+ n TEXT-OFFSET)
                          ; we take some number of stack items (like 4), starting at some address below the stack pointer (like rsp-24)
                          (CREATE-CANONICAL-ADDRESS-LIST stack-slots (BINARY-+ neg-stack-offset (XR ':RGF '4 X86))))))
  :hints (("Goal" :use ((:instance x86isa::NOT-MEMBER-P-CANONICAL-ADDRESS-LISTP-WHEN-DISJOINT-P
                                   (e (BINARY-+ n TEXT-OFFSET))
                                   (n total-stack-slots)
                                   (PROG-ADDR (BINARY-+ neg-total-stack-offset (XR ':RGF '4 X86)))
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

;this may help that problem where normalizing these constants caused problems
(defthm <-of-logext-and-bvplus-of-constant
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 64 k)
                (EQUAL 1 (ACL2::GETBIT 63 K)) ;(>= k (expt 2 63))
                (signed-byte-p 64 x))
           (equal (< x (LOGEXT 64 (ACL2::BVPLUS 64 k x)))
                  (< x (+ (- (expt 2 64) (acl2::bvchop 64 k)) (- (expt 2 63))))))
  :hints (("Goal" :in-theory (e/d (acl2::bvplus
                                   ACL2::LOGEXT-CASES
                                   acl2::bvcat
                                   ACL2::LOGAPP
                                   ACL2::LOGEXT-OF-PLUS)
                                  (ACL2::BVPLUS-RECOLLAPSE
                                   ACL2::BVCHOP-IDENTITY-CHEAP
                                   ACL2::BVCHOP-IDENTITY
                                   ;ACL2::TRIM-TO-N-BITS-META-RULE-FOR-BVCAT ;looped
                                   ACL2::PLUS-BVCAT-WITH-0 ;looped
                                   ACL2::PLUS-BVCAT-WITH-0-ALT ;looped
                                   ACL2::BVCAT-OF-BVCHOP-LOW ;looped
                                   ACL2::SLICE-OF-BVCHOP-LOW ;looped
                                   ACL2::SLICE-OF-BVCHOP-LOW-GEN ;looped
                                   ACL2::SLICE-OF-BVCHOP-LOW-GEN-BETTER ;looped
                                   ))
           :use (:instance acl2::split-bv
                           (n 64)
                           (m 63)
                           (y (acl2::bvchop 64 k))))))


;add one for the upper bound as well?
(defthm <-when-canonical-address-p
  (implies (and (syntaxp (quotep k))
                (< k (- (expt 2 47)))
                (canonical-address-p x))
           (equal (< x k)
                  nil)))

;;todo #1
;; (CANONICAL-ADDRESS-P$INLINE (LOGEXT '64
;;                                           (ACL2::BVPLUS '64
;;                                                         '18446744073709551604
;;                                                         (XR ':RGF '4 X86))))

(defthm disjoint-of-CREATE-CANONICAL-ADDRESS-LIST-and-CREATE-CANONICAL-ADDRESS-LIST-stack-and-text
  (implies (and (syntaxp (and (quotep stack-slots)
                              (quotep neg-stack-offset)))
                (<= neg-stack-offset (- stack-slots))
                (integerp neg-stack-offset) ;should be negative
                (disjoint-p (create-canonical-address-list text-len text-offset)
                            (create-canonical-address-list total-stack-slots (binary-+ neg-total-stack-offset (xr ':rgf '4 x86))))
                (syntaxp (and (quotep total-stack-slots)
                              (quotep neg-total-stack-offset)))
                (equal neg-total-stack-offset (- total-stack-slots)) ;could gen but maybe no need to
                (<= neg-total-stack-offset neg-stack-offset)
                (canonical-address-p$inline text-offset)
                (canonical-address-p$inline (binary-+ (+ -1 text-len) text-offset))
                (canonical-address-p$inline (binary-+ neg-total-stack-offset (xr ':rgf '4 x86)))
                (canonical-address-p$inline (xr ':rgf '4 x86))
                (natp n)
                (<= (+ n text-bytes) text-len)
                (natp text-len)
                (natp text-bytes)
                (natp stack-slots)
                (posp total-stack-slots)
                )
           (disjoint-p (CREATE-CANONICAL-ADDRESS-LIST text-bytes (BINARY-+ n TEXT-OFFSET))
                       ;; we take some number of stack items (like 4), starting at some address below the stack pointer (like rsp-24)
                       (CREATE-CANONICAL-ADDRESS-LIST stack-slots (BINARY-+ neg-stack-offset (XR ':RGF '4 X86)))))
  :hints (("Goal" :use ()
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
                            (create-canonical-address-list total-stack-slots (binary-+ neg-total-stack-offset (xr ':rgf '4 x86))))
                (syntaxp (and (quotep total-stack-slots)
                              (quotep neg-total-stack-offset)))
                (equal neg-total-stack-offset (- total-stack-slots)) ;could gen but maybe no need to
                (<= neg-total-stack-offset neg-stack-offset)
                (canonical-address-p$inline text-offset)
                (canonical-address-p$inline (binary-+ (+ -1 text-len) text-offset))
                (canonical-address-p$inline (binary-+ neg-total-stack-offset (xr ':rgf '4 x86)))
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
                       (CREATE-CANONICAL-ADDRESS-LIST stack-slots (BINARY-+ neg-stack-offset (XR ':RGF '4 X86)))))
  :hints (("Goal" :use ()
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



;todo: improve axe to handle the form of the original rule
;or now we just expand !flgi-undefined
;; (DEFTHM X86P-OF-!FLGI-UNDEFINED-eric
;;   (IMPLIES (AND (X86P X86)
;;                 (member-equal flg '(0 2 4 6 7 11))
;;                 ;; ((LAMBDA
;;                 ;;   (X L)
;;                 ;;   (RETURN-LAST
;;                 ;;    'ACL2::MBE1-RAW
;;                 ;;    (ACL2::MEMBER-EQL-EXEC X L)
;;                 ;;    (RETURN-LAST 'PROGN
;;                 ;;                 (ACL2::MEMBER-EQL-EXEC$GUARD-CHECK X L)
;;                 ;;                 (MEMBER-EQUAL X L))))
;;                 ;;  FLG '(0 2 4 6 7 11))
;;                 )
;;            (X86P (x86isa::!FLGI-UNDEFINED$INLINE FLG X86)))
;;   :HINTS ((STD::RETURNSPEC-DEFAULT-DEFAULT-HINT
;;            'x86isa::!FLGI-UNDEFINED$INLINE
;;            ID WORLD))
;;   :RULE-CLASSES :REWRITE)

;why did this cause loops?
(defthm <-of-logext-and-+-of-constant
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 64 k)
                (EQUAL 1 (ACL2::GETBIT 63 K)) ;(>= k (expt 2 63))
                (signed-byte-p 64 x))
           (equal (< x (LOGEXT 64 (+ k x)))
                  (< x (+ (- (expt 2 64) k) (- (expt 2 63))))))
  :hints (("Goal" :in-theory (e/d (acl2::bvplus ACL2::LOGEXT-CASES
                                                acl2::bvcat ACL2::LOGAPP
                                                ACL2::LOGEXT-OF-PLUS)
                                  (ACL2::BVPLUS-RECOLLAPSE
                                   ACL2::BVCHOP-IDENTITY-CHEAP
                                   ACL2::BVCHOP-IDENTITY
                                   ;ACL2::TRIM-TO-N-BITS-META-RULE-FOR-BVCAT ;looped
                                   ACL2::PLUS-BVCAT-WITH-0 ;looped
                                   ACL2::PLUS-BVCAT-WITH-0-ALT ;looped
                                   ACL2::BVCAT-OF-BVCHOP-LOW ;looped
                                   ))
           :use (:instance acl2::split-bv
                           (n 64)
                           (m 63)
                           (y k)))))

;todo: fix this rule
;; (defthm signed-byte-p-of-+-between
;;   (implies (and (canonical-address-p (binary-+ big-neg-offset x))
;;                 (<= big-neg-offset small-neg-offset)
;;                 (canonical-address-p x)
;;                 ;(integerp x)
;;                 (integerp small-neg-offset)
;;                 (integerp big-neg-offset)
;;                 (<= 0 small-neg-offset) ;gen? ;TODO: This doesn't make sense
;;                 (signed-byte-p 16 small-neg-offset) ;gen
;;                 )
;;            (signed-byte-p '64 (binary-+ small-neg-offset x)))
;;   :hints (("Goal" :in-theory (enable ;canonical-address-p signed-byte-p
;;                               ))))

;looped with the between lemma?
(defthm <-when-canonical-address-p-impossible
  (implies (and (syntaxp (quotep k))
                (< k (- (expt 2 47)))
                (canonical-address-p x))
           (equal (< x k)
                  nil))
  :hints (("Goal" :use (:instance <-when-canonical-address-p (x (xr ':rgf '4 x86)))
           :in-theory (disable <-when-canonical-address-p))))

; Maybe this is the loop: CANONICAL-ADDRESS-P-BETWEEN backchains from CANONICAL-ADDRESS-P to
; some < claims, but several rules (such as <-WHEN-CANONICAL-ADDRESS-P)
; backchain from < claims to CANONICAL-ADDRESS-P claims.

;; (DEFTHM CANONICAL-ADDRESS-P-OF-+-WHEN-CANONICAL-ADDRESS-P-OF-+-alt
;;   (IMPLIES (AND (CANONICAL-ADDRESS-P (+ K2 LOAD-OFFSET))
;;                 (<= K K2)
;;                 (NATP K)
;;                 (NATP K2)
;;                 (CANONICAL-ADDRESS-P LOAD-OFFSET))
;;            (CANONICAL-ADDRESS-P (+ K LOAD-OFFSET)))
;;   :HINTS
;;   (("Goal"
;;     :IN-THEORY (ENABLE CANONICAL-ADDRESS-P SIGNED-BYTE-P))))


;todo:

;MEMBER-P-CANONICAL-ADDRESS-LISTP is misnamed

;; (thm
;;  (implies (and (<= neg-off 0)
;;                (< (- neg-off) k)
;; ;               (natp k)
;;                (integerp x)
;;                (integerp neg-off)
;;                (integerp k)
;;                (canonical-address-p (+ neg-off x))
;;                (canonical-address-p (+ -1 k neg-off x)))
;;           (member-p x (create-canonical-address-list k (+ neg-off x))))
;; ; :hints (("Goal" :in-theory (enable create-canonical-address-list)))
;;  )


;move hyps to conclusion
;; (thm
;;  (implies (and (<= neg-off 0)
;;                (< (- neg-off) k)
;; ;               (natp k)
;;                (integerp neg-off))
;;           (member-p x (create-canonical-address-list k (+ neg-off x))))
;;  :hints (("Goal" :in-theory (enable create-canonical-address-list))))

 ;todo (I guess this is false - off by 1?):
;; ((173 MEMBER-P 2 164)
;;  (164 CREATE-CANONICAL-ADDRESS-LIST '80 163)
;;  (163 BINARY-+ '-80 2)
;;  (2 XR ':RGF '4 1)
;;  (1 . X86))

;; (DEFTHM !FLGI-of-!FLGI-undefined-DIFFERENT-CONCRETE-INDICES
;;   (IMPLIES (AND (SYNTAXP (QUOTEP I1))
;;                 (SYNTAXP (QUOTEP I2))
;;                 (MEMBER I1 *FLG-NAMES*)
;;                 (MEMBER I2 *FLG-NAMES*)
;;                 (X86P X86)
;;                 (< I1 I2))
;;            (EQUAL (!FLGI I2 V2 (!FLGI-undefined I1 X86))
;;                   (!FLGI-undefined I1 (!FLGI I2 V2 X86))))
;;   :hints (("Goal" :in-theory (enable !FLGI-UNDEFINED))))

;not true, gotta update the undef-flg
;; (DEFTHM !FLGI-of-!FLGI-undefined-same
;;   (IMPLIES (AND (MEMBER I *FLG-NAMES*)
;;                 (X86P X86)
;;                 )
;;            (EQUAL (!FLGI I V (!FLGI-undefined I X86))
;;                   (!FLGI I V X86)))
;;   :hints (("Goal" :in-theory (enable !FLGI-UNDEFINED ;!FLGI
;;                                      ))))

;; (thm
;;  (equal (ACL2::BVPLUS (+ (- LOW) SIZE)
;;                       (EXPT 2 WIDTH)
;;                       (ACL2::REPEATBIT (+ (- LOW) SIZE) 1))

;; (thm
;;  (Implies (and (< n size)
;;                (natp size)
;;                (natp n))
;;           (equal (acl2::bvplus size -1 (expt 2 n))
;;                  (acl2::bvcat (- size n)
;;                               0
;;                               n
;;                               (+ -1 (expt 2 n)))))
;;  :hints (("Goal" :in-theory (e/d (acl2::bvplus ACL2::REPEATBIT)
;;                                  (ACL2::BVPLUS-RECOLLAPSE
;;                                   ACL2::BVCAT-OF-+-LOW ;looped
;;                                   )))))

;; ;a bunch of 0's followed by a bunch of 1's
;; instead, just drop the (expt 2 size)
;; (defthm bvplus-of-expt-and-all-ones
;;  (Implies (and (< n size)
;;                (natp size)
;;                (natp n))
;;           (equal (acl2::bvplus size (expt 2 n) (+ -1 (expt 2 size)))
;;                  (acl2::bvcat (- size n)
;;                               0
;;                               n
;;                               (+ -1 (expt 2 n)))))
;;  :hints (("Goal" :in-theory (e/d (acl2::bvplus ACL2::REPEATBIT)
;;                                  (ACL2::BVPLUS-RECOLLAPSE
;;                                   ACL2::BVCAT-OF-+-LOW ;looped
;;                                   )))))

;helps get rid of irrelevant stuff (even though we expect to not really need this)
(defthm mv-nth-0-of-get-prefixes-of-xw-of-irrel
  (implies (or (eq :rgf field)
               (eq :rip field)
               (eq :undef field)) ;gen
           (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (xw field index value x86)))
                  (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86))))
  :hints (("Goal" :induct (GET-PREFIXES proc-mode START-RIP PREFIXES rex-byte CNT X86)
           :in-theory (e/d ( ;xw
                            add-to-*ip
                            get-prefixes)
                           (acl2::unsigned-byte-p-from-bounds
                            ;acl2::bvchop-identity
                            x86isa::part-install-width-low-becomes-bvcat-32
                            ;for speed:
                            CANONICAL-ADDRESS-P-BETWEEN
                            x86isa::PART-SELECT-WIDTH-LOW-BECOMES-SLICE
                            x86isa::SLICE-OF-PART-INSTALL-WIDTH-LOW
                            MV-NTH-OF-IF
                            x86isa::GET-PREFIXES-OPENER-LEMMA-NO-PREFIX-BYTE
                            )))))

(defthm mv-nth-1-of-get-prefixes-of-xw-of-irrel
  (implies (or (eq :rgf field)
               (eq :rip field)
               (eq :undef field)) ;gen
           (equal (mv-nth 1
                          (get-prefixes proc-mode start-rip prefixes rex-byte
                                        cnt (xw field index value x86)))
                  (mv-nth 1
                          (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86))))
  :hints (("Goal" :induct (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
           :in-theory (e/d (get-prefixes
                            add-to-*ip)
                                  (acl2::unsigned-byte-p-from-bounds
                                   ;acl2::bvchop-identity
                                   x86isa::part-install-width-low-becomes-bvcat-32
                                   combine-bytes-when-singleton ;for speed
                                   x86isa::get-prefixes-opener-lemma-no-prefix-byte ;for speed
                                   x86isa::part-select-width-low-becomes-slice ;for speed
                                   ACL2::ZP-OPEN
                                   MV-NTH-OF-IF
                                   )))))

;; A guess as to how the 32 bytes of shadow space for PE files looks: (TODO: Figure this all out!)
;; Stack layout (stack grows down):
;; ((high addresses))
;; -----
;; (rest of caller's frame)
;; stack arguments
;; 32 bytes of shadow space??
;; return address  <- RSP initially points to this slot
;; --- our theorem fires when the stack contains the stuff above this line
;; saved RBP     <- new RBP
;; rest of callee's frame
;; ----
;; ((low addresses))

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
                (canonical-address-p$inline (binary-+ (+ -1 text-len) text-offset))
                (canonical-address-p$inline (binary-+ (+ -1 total-stack-slots) (xr ':rgf '4 x86)))
                (canonical-address-p$inline (xr ':rgf '4 x86))
                (natp n)
                (< n text-len)
                (natp text-len))
           (not (MEMBER-P (BINARY-+ n TEXT-OFFSET)
                          ;; we take some number of stack items (like 4), starting at some address above the stack pointer (like rsp+8)
                          (CREATE-CANONICAL-ADDRESS-LIST stack-slots (BINARY-+ pos-stack-offset (XR ':RGF '4 X86))))))
  :hints (("Goal" :use ((:instance x86isa::NOT-MEMBER-P-CANONICAL-ADDRESS-LISTP-WHEN-DISJOINT-P
                                   (e (BINARY-+ n TEXT-OFFSET))
                                   (n stack-slots)
                                   (PROG-ADDR (BINARY-+ pos-stack-offset (XR ':RGF '4 X86)))
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


;this version is actually more likely to fire (if the equal is reordered to
;have the constant k3 first)
(defthm equal-of-if-constants-alt
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep k3)))
           (equal (equal k3 (if test k1 k2))
                  (if test
                      (equal k3 k1)
                    (equal k3 k2)))))

;drop?  looped
(defthmd if-x-nil-t
  (equal (if x nil t)
         (not x)))

(defthm if-of-not
  (equal (if (not test) tp ep)
         (if test ep tp)))

(defthm if-of-if-same-arg2
  (equal (if test (if test tp ep) ep2)
         (if test tp ep2)))

;could be bad
(defthmd member-p-of-if-arg1
  (equal (member-p (if test tp ep) lst)
         (if test
             (member-p tp lst)
           (member-p ep lst))))

;could be bad
(defthmd +-of-if-arg1
  (equal (+ (if test x1 x2) y)
         (if test (+ x1 y) (+ x2 y))))

;can blow up (as can all if-lifting rules for non-unary functions)?
(defthmd +-of-if-arg2
  (equal (+ y (if test x1 x2))
         (if test (+ y x1) (+ y x2))))

;could be bad
(defthmd acl2::nth-of-if-arg1
  (equal (nth (if acl2::test a b) x)
         (if acl2::test
             (nth a x)
           (nth b x))))

(defthm cons-of-if-when-constants
  (implies (syntaxp (and (quotep tp)
                         (quotep ep)
                         (quotep x)))
           (equal (cons (if test tp ep) x)
                  (if test
                      (cons tp x)
                    (cons ep x)))))

(defthm combine-bytes-of-if-when-constants
  (implies (syntaxp (and (quotep tp)
                         (quotep ep)))
           (equal (x86isa::combine-bytes (if test tp ep))
                  (if test
                      (x86isa::combine-bytes tp)
                    (x86isa::combine-bytes ep)))))

;TODO: we could just build this kind of thing into axe..
(defthm 64-bit-mode-one-byte-opcode-modr/m-p$inline-of-if-when-constants
  (implies (syntaxp (and (quotep tp)
                         (quotep ep)))
           (equal (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline (if test tp ep))
                  (if test
                      (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline tp)
                    (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline ep)))))

(defthm one-byte-opcode-execute-of-if-arg1
  (equal (one-byte-opcode-execute proc-mode (if test start-rip1 start-rip2) temp-rip prefixes rex-byte opcode modr/m sib x86)
         (if test
             (one-byte-opcode-execute proc-mode start-rip1 temp-rip prefixes rex-byte opcode modr/m sib x86)
           (one-byte-opcode-execute proc-mode start-rip2 temp-rip prefixes rex-byte opcode modr/m sib x86))))

(defthm one-byte-opcode-execute-of-if-arg2
  (equal (one-byte-opcode-execute proc-mode start-rip (if test temp-rip1 temp-rip2) prefixes rex-byte opcode modr/m sib x86)
         (if test
             (one-byte-opcode-execute proc-mode start-rip temp-rip1 prefixes rex-byte opcode modr/m sib x86)
           (one-byte-opcode-execute proc-mode start-rip temp-rip2 prefixes rex-byte opcode modr/m sib x86))))

(defthm one-byte-opcode-execute-of-if-arg6
  (equal (one-byte-opcode-execute proc-mode start-rip temp-rip prefixes rex-byte opcode (if test modr/m1 modr/m2) sib x86)
         (if test
             (one-byte-opcode-execute proc-mode start-rip temp-rip prefixes rex-byte opcode modr/m1 sib x86)
           (one-byte-opcode-execute proc-mode start-rip temp-rip prefixes rex-byte opcode modr/m2 sib x86))))

;once this breaks the symmetry, the two one-byte-opcode-execute terms
;resulting from a branch will be different (and perhaps each then will
;get a nice context computed for it)
(defthm if-of-one-byte-opcode-execute-of-if-arg2
  (equal (if test
             (one-byte-opcode-execute proc-mode start-rip
                                       (if test temp-rip1 temp-rip2) ;same test as above
                                       prefixes rex-byte opcode modr/m sib
                                       x86)
           x)
         (if test
             (one-byte-opcode-execute proc-mode start-rip
                                       temp-rip1
                                       prefixes rex-byte opcode modr/m sib
                                       x86)
           x)))

(defthm if-of-one-byte-opcode-execute-of-if-arg5
  (equal (if test
             (one-byte-opcode-execute proc-mode start-rip
                                       temp-rip
                                       prefixes rex-byte
                                       (if test opcode1 opcode2) ;same test as above
                                       modr/m sib
                                       x86)
           x)
         (if test
             (one-byte-opcode-execute proc-mode start-rip
                                       temp-rip
                                       prefixes rex-byte opcode1 modr/m sib
                                       x86)
           x)))


;;TODO: Maybe we should have axe split the simulation instead of proving all these if lifting rules.

;why is axe reasoning about CHECK-DCL-GUARDIAN? it's mentioned in X86ISA::X86-FETCH-DECODE-EXECUTE

(defthm if-of-if-arg3-same
  (equal (if test x (if test y z))
         (if test x z)))

(defthm <-of-if-arg2
  (implies (syntaxp (and (quotep y)
                         (quotep x1)
                         (quotep x2)))
           (equal (< y (IF test x1 x2))
                  (if test (< y x1) (< y x2)))))

(defthm logext-of-if-arg2
  (implies (syntaxp (and (quotep size)
                         (quotep x1)
                         (quotep x2)))
           (equal (logext size (IF test x1 x2))
                  (if test (logext size x1) (logext size x2)))))

(defthm run-until-rsp-greater-than-of-if-arg2
  (equal (x::run-until-rsp-greater-than target-rsp (if test x86a x86b))
         (if test
             (x::run-until-rsp-greater-than target-rsp x86a)
           (x::run-until-rsp-greater-than target-rsp x86b))))

;; Add aliases in the X86ISA package of some common utilities:

;; (defmacro defconst-computed2 (&rest args) `(acl2::defconst-computed2 ,@args))
;; (defmacro prove-equivalence (&rest args) `(acl2::prove-equivalence ,@args))
;; (defmacro dag-info (&rest args) `(acl2::dag-info ,@args))
;; (defmacro simp-dag (&rest args) `(acl2::simp-dag ,@args))
;; (defmacro make-axe-rules (&rest args) `(acl2::make-axe-rules ,@args))



;; (defthm 64-bit-modep-of-xw
;;   (implies (and (not (equal fld :msr))
;;                 (not (equal fld :seg-hidden)))
;;            (equal (64-bit-modep (xw fld index value x86))
;;                   (64-bit-modep x86)))
;;   :hints (("Goal" :in-theory (enable 64-bit-modep))))

;; (defthm 64-bit-modep-of-mv-nth-1-of-wb
;;   (equal (64-bit-modep (mv-nth 1 (wb n addr w val x86)))
;;          (64-bit-modep x86))
;;   :hints (("Goal" :in-theory (enable 64-bit-modep))))

;; (defthm 64-bit-modep-of-!flgi
;;   (equal (64-bit-modep (!flgi flag val x86))
;;          (64-bit-modep x86))
;;   :hints (("Goal" :in-theory (enable 64-bit-modep))))


;; todo: drop these irrelevant params from separate
(defthm separate-normalize-r-w-x-1
  (implies (not (eq r-w-x-1 :r)) ;not using syntaxp since axe could not handle that
           (equal (separate r-w-x-1 n-1 addr-1 r-w-x-2 n-2 addr-2)
                  (separate :r n-1 addr-1 r-w-x-2 n-2 addr-2)))
  :hints (("Goal" :in-theory (enable separate))))

;; todo: drop these irrelevant params from separate
(defthm separate-normalize-r-w-x-2
  (implies (not (eq r-w-x-2 :r)) ;not using syntaxp since axe could not handle that
           (equal (separate r-w-x-1 n-1 addr-1 r-w-x-2 n-2 addr-2)
                  (separate r-w-x-1 n-1 addr-1 :r n-2 addr-2)))
  :hints (("Goal" :in-theory (enable separate))))

;(in-theory (enable x86-fetch-decode-execute)) ;needed for code proofs (no, use the opener?)

(defthm not-separate-self
  (implies (and (posp n)
                (posp n2))
           (not (separate rwx n addr rwx2 n2 addr)))
  :hints (("Goal" :in-theory (enable separate))))

;gen the 1 here:

(defthm separate-of-plus
  (implies (and (separate :r n text-offset ;n is a free var
                          :r n2+ x)
                (< k n)
                (<= n2 n2+)
                (natp n2+)
                (natp k)
                (natp n))
           (separate :r 1 (+ k text-offset)
                     :r n2 x))
  :hints (("Goal" :in-theory (enable separate))))

;reorders the hyp...
(defthm separate-of-plus-alt
  (implies (and (separate :r n2+ x
                          :r n text-offset ;n is a free var
                          )
                (<= n2 n2+)
                (natp n2+)
                (< k n)
                (natp k)
                (natp n))
           (separate :r 1 (+ k text-offset)
                     :r n2 x))
  :hints (("Goal" :in-theory (enable separate))))


(defthm separate-below-and-above
  (implies (and (<= k1 0)
                (<= k2 (- k1))
                (integerp k1)
                (integerp k2)
                )
           (separate rwx1 k2 (+ k1 x) ;this stuff is below x
                     rwx2 j x)) ;this stuff is above x
  :hints (("Goal" :in-theory (enable separate))))

(defthm separate-below-and-above-alt
  (implies (and (<= k1 0)
                (<= k2 (- k1))
                (integerp k1)
                (integerp k2)
                )
           (separate rwx2 j x
                     rwx1 k2 (+ k1 x)))
  :hints (("Goal" :in-theory (enable separate))))

(defthm separate-below-and-above-offset
  (implies (and (integerp k)
                (integerp k2)
                (<= (+ k n) k2))
           (separate :r n2 (+ k2 x)
                     :r n (+ k x)))
  :hints (("Goal" :in-theory (enable separate))))

(defthm separate-below-and-above-offset-alt
  (implies (and (integerp k)
                (integerp k2)
                (<= (+ k n) k2))
           (separate :r n (+ k x)
                     :r n2 (+ k2 x)))
  :hints (("Goal" :in-theory (enable separate))))

(defthm separate-same-lemma-1
  (implies (and (<= num off2)
                (integerp num)
                (integerp off2))
           (separate :r num x
                     :r num2 (+ off2 x)))
  :hints (("Goal" :in-theory (enable separate))))

(defthm separate-same-lemma-1-alt
  (implies (and (<= num off2)
                (integerp num)
                (integerp off2))
           (separate :r num2 (+ off2 x)
                     :r num x))
  :hints (("Goal" :in-theory (enable separate))))


(in-theory (disable wb))
(in-theory (disable x86isa::WB-BY-WB-1-FOR-APP-VIEW-INDUCTION-RULE))

;; ;tell shilpi
;; (DEFTHM RB-WB-SUBSET-gen
;;   (IMPLIES (AND (APP-VIEW X86)
;;                 (<= (+ ADDR-1 N-1) (+ ADDR-2 N-2)) ;allows = here
;;                 (<= ADDR-2 ADDR-1)
;;                 (CANONICAL-ADDRESS-P ADDR-1)
;;                 (CANONICAL-ADDRESS-P (+ -1 N-1 ADDR-1))
;;                 (CANONICAL-ADDRESS-P ADDR-2)
;;                 (CANONICAL-ADDRESS-P (+ -1 N-2 ADDR-2))
;;                 (UNSIGNED-BYTE-P (ASH N-2 3) VAL)
;;                 (POSP N-1)
;;                 (POSP N-2)
;;                 (X86P X86))
;;            (EQUAL (MV-NTH 1
;;                           (RB N-1 ADDR-1 R-X
;;                               (MV-NTH 1 (WB N-2 ADDR-2 W VAL X86))))
;;                   (PART-SELECT VAL
;;                                :LOW (ASH (- ADDR-1 ADDR-2) 3)
;;                                :WIDTH (ASH N-1 3))))
;;   :hints (("Goal" :cases ((<= (+ ADDR-1 N-1) (+ ADDR-2 N-2))))))

(defthm rb-wb-disjoint-eric
  (implies (and (separate r-x n-1 addr-1 w n-2 addr-2)
                (app-view x86))
           (equal (mv-nth 1
                          (rb n-1 addr-1 r-x
                              (mv-nth 1 (wb n-2 addr-2 w val x86))))
                  (mv-nth 1 (rb n-1 addr-1 r-x x86)))))


;gen?
(defthm separate-lemma-1
  (implies (and (separate :r n text-offset
                          :r big (+ bigneg x))
                (natp n)
                (natp off)
                (<= (+ num off) n)
                (equal big (- bigneg))
                (<= small (- smallneg))
                (<= bigneg smallneg)
                (<= 0 small)
                (<= 0 big)
                (integerp smallneg)
                (integerp bigneg)
                (integerp small)
                (integerp big)
                (integerp text-offset))
           (separate :r num (+ off text-offset)
                     :r small (+ smallneg x)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-lemma-1-alt
  (implies (and (separate :r n text-offset
                          :r big (+ bigneg x))
                (natp n)
                (natp off)
                (<= (+ num off) n)
                (equal big (- bigneg))
                (<= small (- smallneg))
                (<= bigneg smallneg)
                (<= 0 small)
                (<= 0 big)
                (integerp smallneg)
                (integerp bigneg)
                (integerp small)
                (integerp big)
                (integerp text-offset))
           (separate :r small (+ smallneg x)
                     :r num (+ off text-offset)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

;no offset
(defthm separate-lemma-1b
  (implies (and (separate :r n text-offset
                          :r big (+ bigneg x))
                (natp n)
                (<= num n)
                (equal big (- bigneg))
                (<= small (- smallneg))
                (<= bigneg smallneg)
                (<= 0 small)
                (<= 0 big)
                (integerp smallneg)
                (integerp bigneg)
                (integerp small)
                (integerp big)
                (integerp text-offset))
           (separate :r num text-offset
                     :r small (+ smallneg x)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-lemma-1b-alt
  (implies (and (separate :r n text-offset
                          :r big (+ bigneg x))
                (natp n)
                (<= num n)
                (equal big (- bigneg))
                (<= small (- smallneg))
                (<= bigneg smallneg)
                (<= 0 small)
                (<= 0 big)
                (integerp smallneg)
                (integerp bigneg)
                (integerp small)
                (integerp big)
                (integerp text-offset))
           (separate :r small (+ smallneg x)
                     :r num text-offset))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))




(defthm separate-of-if-arg3
  (equal (separate rwx1 n1 (if test addr1a addr1b) rwx2 n2 addr2)
         (if test
             (separate rwx1 n1 addr1a rwx2 n2 addr2)
           (separate rwx1 n1 addr1b rwx2 n2 addr2))))

(defthm separate-of-if-arg6
  (equal (separate rwx1 n1 addr1 rwx2 n2 (if test addr2a addr2b))
         (if test
             (separate rwx1 n1 addr1 rwx2 n2 addr2a)
           (separate rwx1 n1 addr1 rwx2 n2 addr2b))))

(defthm rb-of-if-arg2
  (equal (rb n (if test addr1 addr2) rx x86)
         (if test
             (rb n addr1 rx x86)
           (rb n addr2 rx x86))))

(defthm separate-lemma-2b
  (implies (and (separate :r n text-offset
                          :r big x)
                (natp n)
                (natp off)
                (<= (+ num off) n)
                (integerp text-offset)
                (natp big)
                (natp off2)
                (<= (+ off2 num2) big)
                (natp num2)
                )
           (separate :r num (+ off text-offset)
                     :r num2 (+ off2 x)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-lemma-2b-alt
  (implies (and (separate :r n text-offset
                          :r big x)
                (natp n)
                (natp off)
                (<= (+ num off) n)
                (integerp text-offset)
                (natp big)
                (natp off2)
                (<= (+ off2 num2) big)
                (natp num2)
                )
           (separate :r num2 (+ off2 x)
                     :r num (+ off text-offset)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))


(defthm separate-lemma-3
  (implies (and (separate :r n text-offset
                          :r big x)
                (natp n)
                (<= num n)
                (integerp text-offset)
                (natp big)
                (natp off2)
                (<= (+ off2 num2) big)
                (natp num2)
                )
           (separate :r num text-offset
                     :r num2 (+ off2 x)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-lemma-3-alt
  (implies (and (separate :r n text-offset
                          :r big x)
                (natp n)
                (<= num n)
                (integerp text-offset)
                (natp big)
                (natp off2)
                (<= (+ off2 num2) big)
                (natp num2)
                )
           (separate :r num2 (+ off2 x)
                     :r num text-offset))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))



;; In this series of lemmas, the assumption about separate contains no offsets:
;; todo: these subsume some things above

(defthm separate-from-separate-lemma-1
  (implies (and (separate rwx3 num3 base1
                          rwx4 num4 base2)
                (<= (+ num1 off1) num3)
                (<= (+ num2 off2) num4)
                (natp num1)
                (natp num2)
                (natp off1)
                (natp off2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 (+ off1 base1)
                     rwx2 num2 (+ off2 base2)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-from-separate-lemma-1-alt
  (implies (and (separate rwx4 num4 base2
                          rwx3 num3 base1)
                (<= (+ num1 off1) num3)
                (<= (+ num2 off2) num4)
                (natp num1)
                (natp num2)
                (natp off1)
                (natp off2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 (+ off1 base1)
                     rwx2 num2 (+ off2 base2)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

;off1=0
(defthm separate-from-separate-lemma-1b
  (implies (and (separate rwx3 num3 base1
                          rwx4 num4 base2)
                (<= num1 num3)
                (<= (+ num2 off2) num4)
                (natp num1)
                (natp num2)
                (natp off2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 base1
                     rwx2 num2 (+ off2 base2)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-from-separate-lemma-1b-alt
  (implies (and (separate rwx4 num4 base2
                          rwx3 num3 base1)
                (<= num1 num3)
                (<= (+ num2 off2) num4)
                (natp num1)
                (natp num2)
                (natp off2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 base1
                     rwx2 num2 (+ off2 base2)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

;off2=0
(defthm separate-from-separate-lemma-1c
  (implies (and (separate rwx3 num3 base1
                          rwx4 num4 base2)
                (<= (+ num1 off1) num3)
                (<= num2 num4)
                (natp num1)
                (natp num2)
                (natp off1)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 (+ off1 base1)
                     rwx2 num2 base2))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-from-separate-lemma-1c-alt
  (implies (and (separate rwx4 num4 base2
                          rwx3 num3 base1)
                (<= (+ num1 off1) num3)
                (<= num2 num4)
                (natp num1)
                (natp num2)
                (natp off1)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 (+ off1 base1)
                     rwx2 num2 base2))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

;both off1 and odff2 are 0
(defthm separate-from-separate-lemma-1d
  (implies (and (separate rwx3 num3 base1
                          rwx4 num4 base2)
                (<= num1 num3)
                (<= num2 num4)
                (natp num1)
                (natp num2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 base1
                     rwx2 num2 base2))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-from-separate-lemma-1d-alt
  (implies (and (separate rwx4 num4 base2
                          rwx3 num3 base1)
                (<= num1 num3)
                (<= num2 num4)
                (natp num1)
                (natp num2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 base1
                     rwx2 num2 base2))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

;; ;see also !flgi-and-wb-in-app-view (but that seems like a bad rule -- reuse of val -- tell shilpi)
;; (defthm !flgi-of-mv-nth-1-of-wb
;;   (implies (app-view x86)
;;            (equal (!flgi flg val (mv-nth '1 (wb n addr w value x86)))
;;                   (mv-nth '1 (wb n addr w value (!flgi flg val x86)))))
;;   :hints (("Goal" :in-theory (enable !flgi wb))))

(acl2::defopeners x86-fetch-decode-execute :hyps ((not (ms x86)) (not (x86isa::fault x86))))
(in-theory (disable x86isa::x86-fetch-decode-execute-base)) ;disable because for ACL2 reasoning there is an opener rule

(defthm unsigned-byte-p-of-mv-nth-1-of-rvm08
  (implies (and (<= 8 size)
                (app-view x86)
                (canonical-address-p base-addr)
                (x86p x86))
           (equal (unsigned-byte-p size
                                   (mv-nth 1 (rvm08 base-addr x86)))
                  (natp size)))
  :hints (("Goal" :in-theory (enable rvm08 MEMI))))

(defthm canonical-address-p-of-one-more-when-between
  (implies (and (canonical-address-p base-addr)
                (canonical-address-p (+ -1 base-addr n))
                (< 1 n)
                (integerp n))
           (canonical-address-p (+ 1 base-addr)))
  :hints (("Goal" :in-theory (enable canonical-address-p signed-byte-p))))

;; (defthm n08p-of-g-when-memp-aux
;;   (implies (and (x86isa::memp-aux x)
;;                 (natp i)
;;                 (< I 4503599627370496))
;;            (x86isa::n08p (gz i x)))
;;   :hints (("Goal" :use (:instance x86isa::memp-aux-necc (x86isa::i i))
;;            :in-theory (disable x86isa::memp-aux-necc))))

;; (defthm unsigned-byte-p-of-g-when-memp-aux
;;   (implies (and (x86isa::memp-aux x)
;;                 (natp i)
;;                 (< I 4503599627370496))
;;            (unsigned-byte-p 8 (gz i x)))
;;   :hints (("Goal" :use (:instance n08p-of-g-when-memp-aux)
;;            :in-theory (disable n08p-of-g-when-memp-aux))))

;; (defthm integerp-p-of-g-when-memp-aux
;;   (implies (and (x86isa::memp-aux x)
;;                 (natp i)
;;                 (< I 4503599627370496))
;;            (integerp (gz i x)))
;;   :hints (("Goal" :use (:instance UNSIGNED-BYTE-P-OF-G-WHEN-MEMP-AUX)
;;            :in-theory (disable UNSIGNED-BYTE-P-OF-G-WHEN-MEMP-AUX))))

;; (defthm unsigned-byte-p-of-g-of-nth-31
;;   (implies (and (x86p x86)
;;                 (natp addr)
;;                 (< addr 4503599627370496))
;;            (unsigned-byte-p 8 (gz addr (nth 31 x86))))
;;   :hints (("Goal" :in-theory (enable x86p x86isa::memp))))

;; (defthm integerp-of-g-of-nth-31
;;   (implies (and (x86p x86)
;;                 (natp addr)
;;                 (< addr 4503599627370496))
;;            (integerp (gz addr (nth 31 x86))))
;;   :hints (("Goal" :in-theory (enable x86p x86isa::memp))))

;move
(defthm logext-64-does-nothing-when-canonical-address-p
  (implies (canonical-address-p x)
           (equal (logext 64 x)
                  x)))

;move
(defthm xw-of-rip-and-if
  (equal (xw ':rip '0 (if test pc1 pc2) x86)
         (if test
             (xw ':rip '0 pc1 x86)
           (xw ':rip '0 pc2 x86))))

;move
(defthm if-t-nil
  (equal (if x t nil)
         (acl2::bool-fix x)))

(defthm if-x-x-y
  (implies (booleanp x)
           (equal (if x x y)
                  (if x t y))))

(defthm memberp-of-cons-same
  (acl2::memberp x (cons x y))
  :hints (("Goal" :in-theory (enable acl2::memberp))))

(defthm xr-of-myif
  (equal (xr fld index (acl2::myif test then else))
         (acl2::myif test
                     (xr fld index then)
                     (xr fld index else)))
  :hints (("Goal" :in-theory (enable acl2::myif))))

(in-theory (disable x86isa::rme08))

;; We'll try keeping i48 disabled for now (the x86 books may do the opposite):
(in-theory (disable x86isa::i48$inline))

(defthm canonical-address-p-of-i48
  (canonical-address-p (x86isa::i48 x))
  :hints (("Goal" :in-theory (enable x86isa::i48 canonical-address-p))))

(defthm i48-when-canonical-address-p
  (implies (canonical-address-p x)
           (equal (x86isa::i48 x)
                  x))
  :hints (("Goal" :in-theory (enable x86isa::i48 canonical-address-p))))

;; ;; simplified hyps should work better with axe
;; (DEFTHM GET-PREFIXES-OPENER-LEMMA-GROUP-1-PREFIX-simple-32
;;   (IMPLIES (AND (APP-VIEW X86)
;; ;                (64-BIT-MODEP x86)
;;                 (LET* ((FLG (MV-NTH 0 (RME08 START-RIP *cs* :X X86)))
;;                        (PREFIX-BYTE-GROUP-CODE
;;                         (GET-ONE-BYTE-PREFIX-ARRAY-CODE
;;                          (MV-NTH 1 (RME08 START-RIP *cs* :X X86)))))
;;                       (AND (NOT FLG)
;;                            (EQUAL PREFIX-BYTE-GROUP-CODE 1)))
;;                 (NOT (ZP CNT))
;;                 (CANONICAL-ADDRESS-P (1+ START-RIP))
;;                 (not (MV-NTH 0 (ADD-TO-*IP START-RIP 1 X86))) ;new
;;                 )
;;            (EQUAL
;;             (GET-PREFIXES START-RIP PREFIXES CNT X86)
;;             (LET
;;              ((PREFIXES
;;                (IF (EQUAL (MV-NTH 1 (RME08 START-RIP *cs* :X X86)) 240)
;;                    (!PREFIXES-SLICE
;;                     :LCK (MV-NTH 1 (RME08 START-RIP *cs* :X X86))
;;                     (!PREFIXES-SLICE :LAST-PREFIX 1 PREFIXES))
;;                    (!PREFIXES-SLICE
;;                     :REP (MV-NTH 1 (RME08 START-RIP *cs* :X X86))
;;                     (!PREFIXES-SLICE :LAST-PREFIX 2 PREFIXES)))))
;;              (GET-PREFIXES (1+ START-RIP)
;;                            PREFIXES (1- CNT)
;;                            X86))))
;;   :hints (("Goal" :use (:instance get-prefixes-opener-lemma-group-1-prefix)
;;            :in-theory (disable GET-PREFIXES-OPENER-LEMMA-GROUP-1-PREFIX))))

;; ;; simplified hyps should work better with axe
;; (DEFTHM GET-PREFIXES-OPENER-LEMMA-GROUP-2-PREFIX-simple-32
;;   (IMPLIES (AND (APP-VIEW X86)
;;                 ;;(64-BIT-MODEP x86)
;;                 (LET* ((FLG (MV-NTH 0 (RME08 START-RIP *cs* :X X86)))
;;                        (PREFIX-BYTE-GROUP-CODE
;;                         (GET-ONE-BYTE-PREFIX-ARRAY-CODE
;;                          (MV-NTH 1 (RME08 START-RIP *cs* :X X86)))))
;;                       (AND (NOT FLG)
;;                            (EQUAL PREFIX-BYTE-GROUP-CODE 2)))
;; ;(CANONICAL-ADDRESS-P (1+ START-RIP))
;;                 (NOT (ZP CNT))
;;                 (not (MV-NTH 0 (ADD-TO-*IP START-RIP 1 X86))) ;new
;;                 )
;;            (EQUAL
;;             (GET-PREFIXES START-RIP PREFIXES CNT X86)
;;             (GET-PREFIXES
;;              (1+ START-RIP)
;;              (!PREFIXES-SLICE
;;               :SEG
;;               (MV-NTH 1 (RME08 START-RIP *CS* :X X86))
;;               (!PREFIXES-SLICE :LAST-PREFIX 3 PREFIXES))
;;              (1- CNT)
;;              X86))))

;; ;; simplified hyps should work better with axe
;; (DEFTHM GET-PREFIXES-OPENER-LEMMA-GROUP-3-PREFIX-simple-32
;;   (IMPLIES (AND (APP-VIEW X86)
;;                 ;;(64-BIT-MODEP x86)
;;                 (LET* ((FLG (MV-NTH 0 (RME08 START-RIP *cs* :X X86)))
;;                        (PREFIX-BYTE-GROUP-CODE
;;                         (GET-ONE-BYTE-PREFIX-ARRAY-CODE
;;                          (MV-NTH 1 (RME08 START-RIP *cs* :X X86)))))
;;                       (AND (NOT FLG)
;;                            (EQUAL PREFIX-BYTE-GROUP-CODE 3)))
;;                 ;;(CANONICAL-ADDRESS-P (1+ START-RIP))
;;                 (NOT (ZP CNT))
;;                 (not (MV-NTH 0 (ADD-TO-*IP START-RIP 1 X86))) ;new
;;                 )
;;            (EQUAL
;;             (GET-PREFIXES START-RIP PREFIXES CNT X86)
;;             (GET-PREFIXES
;;              (1+ START-RIP)
;;              (!PREFIXES-SLICE
;;               :OPR
;;               (MV-NTH 1 (RME08 START-RIP *CS* :X X86))
;;               (!PREFIXES-SLICE :LAST-PREFIX 4 PREFIXES))
;;              (1- CNT)
;;              X86))))

;; (DEFTHM GET-PREFIXES-OPENER-LEMMA-GROUP-4-PREFIX-simple-32
;;   (IMPLIES (AND (APP-VIEW X86)
;; ;(64-BIT-MODEP x86)
;;                 (LET* ((FLG (MV-NTH 0 (RME08 START-RIP *cs* :X X86)))
;;                        (PREFIX-BYTE-GROUP-CODE
;;                         (GET-ONE-BYTE-PREFIX-ARRAY-CODE
;;                          (MV-NTH 1 (RME08 START-RIP *cs* :X X86)))))
;;                       (AND (NOT FLG)
;;                            (EQUAL PREFIX-BYTE-GROUP-CODE 4)))
;;                 (CANONICAL-ADDRESS-P (1+ START-RIP))
;;                 (not (MV-NTH 0 (ADD-TO-*IP START-RIP 1 X86))) ;new
;;                 (NOT (ZP CNT)))
;;            (EQUAL
;;             (GET-PREFIXES START-RIP PREFIXES CNT X86)
;;             (GET-PREFIXES
;;              (1+ START-RIP)
;;              (!PREFIXES-SLICE
;;               :ADR
;;               (MV-NTH 1 (RME08 START-RIP *CS* :X X86))
;;               (!PREFIXES-SLICE :LAST-PREFIX 5 PREFIXES))
;;              (1- CNT)
;;              X86))))

(defthm 32-bit-mode-one-byte-opcode-modr/m-p-rewrite-quotep
  (implies (and (syntaxp (quotep byte))
                (unsigned-byte-p 8 byte))
           (equal (32-bit-mode-one-byte-opcode-modr/m-p byte)
                  (acl2::lookup byte
                                (cdr *32-bit-mode-one-byte-has-modr/m-ar*))))
  :hints (("Goal" :in-theory (e/d (32-bit-mode-one-byte-opcode-modr/m-p aref1 acl2::assoc-equal-of-cons)
                                  (acl2::not-equal-bvchop-when-not-equal-bvchop)))))

(defthm if-of-if-of-nil-and-consp
  (implies (consp x)
           (equal (if (if test nil x) tp ep)
                  (if test ep tp))))

(in-theory (enable app-view)) ;for acl2-based lifting

(defthmd acl2::logand-with-mask-alt
  (implies (and (acl2::logmaskp acl2::mask)
                (equal acl2::size (integer-length acl2::mask))
                (force (integerp acl2::i)) ;todo: drop
                )
           (equal (logand acl2::i acl2::mask)
                  (acl2::bvchop acl2::size acl2::i)))
  :hints (("Goal" :use (:instance acl2::logand-with-mask)
           :in-theory (disable acl2::logand-with-mask))))

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

(in-theory (disable acl2::posp-redefinition)) ;yuck
(in-theory (enable posp))

(defthm canonical-address-p-when-unsigned-byte-p
  (implies (unsigned-byte-p 47 ad)
           (canonical-address-p ad))
  :hints (("Goal" :in-theory (enable canonical-address-p))))

(defthm canonical-address-p-of-sum-when-unsigned-byte-p-32
  (implies (and (unsigned-byte-p 32 ad)
                (unsigned-byte-p 32 k) ;gen
                )
           (canonical-address-p (+ k ad))))

;; (defthm +-of-bvplus-of-x-and-minus-x
;;   (implies (unsigned-byte-p 32 x)
;;            (equal (+ (BVPLUS 32 1 x)
;;                      (- x))
;;                   (if (equal x (+ -1 (expt 2 32)))
;;                       (- x)
;;                     1)))
;;   :hints (("Goal" :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases) (ACL2::BVPLUS-RECOLLAPSE)))))

(in-theory (enable x86isa::x86-operation-mode)) ;for non-axe symbolic execution

(acl2::def-constant-opener x86isa::one-byte-opcode-modr/m-p$inline)
(acl2::def-constant-opener x86isa::two-byte-opcode-modr/m-p$inline)

(acl2::def-constant-opener x86isa::rflagsbits->ac$inline)
(acl2::def-constant-opener x86isa::rflagsbits->af$inline)
(acl2::def-constant-opener x86isa::rflagsbits->cf$inline)
(acl2::def-constant-opener x86isa::rflagsbits->of$inline)
(acl2::def-constant-opener x86isa::rflagsbits->pf$inline)
(acl2::def-constant-opener x86isa::rflagsbits->sf$inline)
(acl2::def-constant-opener x86isa::rflagsbits->zf$inline)

(acl2::def-constant-opener X86ISA::RFLAGSBITS-FIX$INLINE)

;pretty gross (due to gross behaviour of bfix)
(defthm RFLAGSBITS-rewrite
  (implies (and (unsigned-byte-p 1 x86isa::cf)
                (unsigned-byte-p 1 X86ISA::RES1)
                (unsigned-byte-p 1 pf)
                (unsigned-byte-p 1 ID)
                (unsigned-byte-p 1 X86ISA::VIP)
                (unsigned-byte-p 1 X86ISA::VIF)
                (unsigned-byte-p 1 X86ISA::AC)
                (unsigned-byte-p 1 X86ISA::VM)
                (unsigned-byte-p 1 X86ISA::RF)
                (unsigned-byte-p 1 X86ISA::RES4)
                (unsigned-byte-p 1 X86ISA::NT)
                (unsigned-byte-p 2 X86ISA::IOPL) ;why?
                (unsigned-byte-p 1 X86ISA::OF)
                (unsigned-byte-p 1 X86ISA::DF)
                (unsigned-byte-p 1 X86ISA::INTF)
                (unsigned-byte-p 1 X86ISA::TF)
                (unsigned-byte-p 1 X86ISA::SF)
                (unsigned-byte-p 1 X86ISA::ZF)
                (unsigned-byte-p 1 X86ISA::RES3)
                (unsigned-byte-p 1 X86ISA::AF)
                (unsigned-byte-p 1 X86ISA::RES2))
           (equal (X86ISA::RFLAGSBITS X86ISA::CF X86ISA::RES1
                                      PF X86ISA::RES2 X86ISA::AF X86ISA::RES3
                                      X86ISA::ZF X86ISA::SF X86ISA::TF
                                      X86ISA::INTF X86ISA::DF X86ISA::OF
                                      X86ISA::IOPL X86ISA::NT X86ISA::RES4
                                      X86ISA::RF X86ISA::VM X86ISA::AC
                                      X86ISA::VIF X86ISA::VIP ID X86ISA::RES5)
                  (acl2::bvcat2 10 X86ISA::RES5
                                1 ID
                                1 X86ISA::VIP
                                1 X86ISA::VIF
                                1 X86ISA::AC
                                1 X86ISA::VM
                                1 X86ISA::RF
                                1 X86ISA::RES4
                                1 X86ISA::NT
                                2 X86ISA::IOPL
                                1 X86ISA::OF
                                1 X86ISA::DF
                                1 X86ISA::INTF
                                1 X86ISA::TF
                                1 X86ISA::SF
                                1 X86ISA::ZF
                                1 X86ISA::RES3
                                1 X86ISA::AF
                                1 X86ISA::RES2
                                1 PF
                                1 X86ISA::RES1
                                1 X86ISA::CF)))
  :hints (("Goal" :in-theory (e/d (X86ISA::RFLAGSBITS
                                   ;;ACL2::BFIX
                                   acl2::bvcat
                                   X86ISA::10BITS-FIX
                                   X86ISA::2BITS-FIX
                                   )
                                  ( ;ACL2::ASSOCIATIVITY-OF-LOGAPP-BETTER
                                   ACL2::LOGAPP-EQUAL-REWRITE
                                   ACL2::LOGAPP-EQUAL-REWRITE-16
                                   ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS
                                   ACL2::BVCHOP-IDENTITY
                                   FTY::LOGAPP-NATP
                                   ACL2::BFIX-WHEN-NOT-1
;ACL2::BVCAT-EQUAL-REWRITE-ALT
                                   ACL2::BVCAT-EQUAL-REWRITE
                                   ACL2::BFIX-WHEN-NOT-BITP)))))

(defthm unsigned-byte-p-1-of-rflagsbits->cf$inline (unsigned-byte-p '1 (x86isa::rflagsbits->cf$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->res1$inline (unsigned-byte-p '1 (x86isa::rflagsbits->res1$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->pf$inline (unsigned-byte-p '1 (x86isa::rflagsbits->pf$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->ID$inline (unsigned-byte-p '1 (x86isa::rflagsbits->ID$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->VIP$inline (unsigned-byte-p '1 (x86isa::rflagsbits->VIP$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->VIF$inline (unsigned-byte-p '1 (x86isa::rflagsbits->VIF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->AC$inline (unsigned-byte-p '1 (x86isa::rflagsbits->AC$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->VM$inline (unsigned-byte-p '1 (x86isa::rflagsbits->VM$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->RF$inline (unsigned-byte-p '1 (x86isa::rflagsbits->RF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->RES4$inline (unsigned-byte-p '1 (x86isa::rflagsbits->RES4$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->NT$inline (unsigned-byte-p '1 (x86isa::rflagsbits->NT$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->OF$inline (unsigned-byte-p '1 (x86isa::rflagsbits->OF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->DF$inline (unsigned-byte-p '1 (x86isa::rflagsbits->DF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->INTF$inline (unsigned-byte-p '1 (x86isa::rflagsbits->INTF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->TF$inline (unsigned-byte-p '1 (x86isa::rflagsbits->TF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->SF$inline (unsigned-byte-p '1 (x86isa::rflagsbits->SF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->ZF$inline (unsigned-byte-p '1 (x86isa::rflagsbits->ZF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->RES3$inline (unsigned-byte-p '1 (x86isa::rflagsbits->RES3$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->AF$inline (unsigned-byte-p '1 (x86isa::rflagsbits->AF$inline rflags)))
(defthm unsigned-byte-p-1-of-rflagsbits->RES2$inline (unsigned-byte-p '1 (x86isa::rflagsbits->RES2$inline rflags)))
(defthm unsigned-byte-p-2-of-rflagsbits->iopl$inline (unsigned-byte-p '2 (x86isa::rflagsbits->iopl$inline rflags)))

(defthm 64-bit-modep-of-set-flag
  (equal (64-bit-modep (x::set-flag flag val x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable x::set-flag))))

(defthm x86p-of-set-flag
  (implies (x86p x86)
           (x86p (x::set-flag flag val x86)))
  :hints (("Goal" :in-theory (enable x::set-flag))))

(defthm alignment-checking-enabled-p-of-set-flag
  (implies (and (member-equal flag x::*flags*) ;drop?
                (not (equal flag :ac)))
           (equal (alignment-checking-enabled-p (x::set-flag flag val x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :in-theory (enable x::set-flag
                                     x86isa::rflagsBits->ac
                                     x86isa::!rflagsBits->cf
                                     x86isa::!rflagsBits->pf
                                     x86isa::!rflagsBits->af
                                     x86isa::!rflagsBits->zf
                                     x86isa::!rflagsBits->sf
                                     x86isa::!rflagsBits->tf
                                     x86isa::!rflagsBits->intf
                                     x86isa::!rflagsBits->df
                                     x86isa::!rflagsBits->of
                                     x86isa::!rflagsBits->iopl
                                     x86isa::!rflagsBits->nt
                                     x86isa::!rflagsBits->rf
                                     x86isa::!rflagsBits->vm
                                     x86isa::!rflagsBits->ac
                                     x86isa::!rflagsBits->vif
                                     x86isa::!rflagsBits->vip
                                     x86isa::!rflagsBits->id))))

;; goes to set-flag instead of exposing details of the flags
(defthm write-user-rflags-rewrite
  (equal (write-user-rflags user-flags-vector undefined-mask x86)
         (b* ((user-flags-vector (n32 user-flags-vector))
              (undefined-mask (n32 undefined-mask))
;             (input-rflags (n32 (rflags x86)))
              (x86 (if (equal (rflagsbits->cf undefined-mask) 1)
                       (xw :undef nil (+ 1 (nfix (xr :undef nil x86)))
                           (x::set-flag :cf (acl2::getbit 0 (create-undef (nfix (xr :undef nil x86)))) x86))
                     (x::set-flag :cf (rflagsbits->cf user-flags-vector) x86)))
              (x86 (if (equal (rflagsbits->pf undefined-mask) 1)
                       (xw :undef nil (+ 1 (nfix (xr :undef nil x86)))
                           (x::set-flag :pf (acl2::getbit 0 (create-undef (nfix (xr :undef nil x86)))) x86))
                     (x::set-flag :pf (rflagsbits->pf user-flags-vector) x86)))
              (x86 (if (equal (rflagsbits->af undefined-mask) 1)
                       (xw :undef nil (+ 1 (nfix (xr :undef nil x86)))
                           (x::set-flag :af (acl2::getbit 0 (create-undef (nfix (xr :undef nil x86)))) x86))
                     (x::set-flag :af (rflagsbits->af user-flags-vector) x86)))
              (x86 (if (equal (rflagsbits->zf undefined-mask) 1)
                       (xw :undef nil (+ 1 (nfix (xr :undef nil x86)))
                           (x::set-flag :zf (acl2::getbit 0 (create-undef (nfix (xr :undef nil x86)))) x86))
                     (x::set-flag :zf (rflagsbits->zf user-flags-vector) x86)))
              (x86 (if (equal (rflagsbits->sf undefined-mask) 1)
                       (xw :undef nil (+ 1 (nfix (xr :undef nil x86)))
                           (x::set-flag :sf (acl2::getbit 0 (create-undef (nfix (xr :undef nil x86)))) x86))
                     (x::set-flag :sf (rflagsbits->sf user-flags-vector) x86)))
              (x86 (if (equal (rflagsbits->of undefined-mask) 1)
                       (xw :undef nil (+ 1 (nfix (xr :undef nil x86)))
                           (x::set-flag :of (acl2::getbit 0 (create-undef (nfix (xr :undef nil x86)))) x86))
                     (x::set-flag :of (rflagsbits->of user-flags-vector) x86))))
           x86))
  :hints (("Goal" :in-theory (enable x::set-flag))))

(defthm program-at-of-set-flag
  (implies (app-view x86)
           (equal (program-at prog-addr x86isa::bytes (x::set-flag flag val x86))
                  (program-at prog-addr x86isa::bytes x86)))
  :hints (("Goal" :in-theory (enable x::set-flag program-at))))

(defthm !rflags-of-write
  (equal (x86isa::!rflags rflags (x::write n base-addr val x86))
         (x::write n base-addr val (x86isa::!rflags rflags x86)))
  :hints (("Goal" :in-theory (enable x86isa::!rflags))))

;apparently the AC flag affects alignment checking
(defthm alignment-checking-enabled-p-of-xw-irrel
  (implies (and (not (member-equal fld '(:ctr :seg-visible)))
                (not (and (equal fld :rflags)
                          (not (equal (x::get-flag :ac x86)
                                      (x86isa::rflagsbits->ac val))))))
           (equal (alignment-checking-enabled-p (xw fld index val x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :in-theory (enable alignment-checking-enabled-p
                                     x86isa::segment-selectorbits->rpl
                                     x86isa::rflags
                                     x86isa::rflagsbits->ac
                                     x86isa::rflagsbits-fix
                                     x::get-flag))))

(defthm x::segment-expand-down-bit-of-set-flag
  (equal (x::segment-expand-down-bit seg-reg (x::set-flag flg val x86))
         (x::segment-expand-down-bit seg-reg x86))
  :hints (("Goal" :in-theory (e/d (x::set-flag)
                                  ()))))
