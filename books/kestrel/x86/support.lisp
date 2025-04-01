; Mixed x86 supporting material
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;todo: use X package

;TODO: Organize this material.

;; This book is for things that mix x86isa notions with our notions.  Pure x86
;; theorems should go in support-x86.lisp.

(include-book "projects/x86isa/proofs/utilities/app-view/user-level-memory-utils" :dir :system)
(include-book "projects/x86isa/machine/prefix-modrm-sib-decoding" :dir :system) ; for get-one-byte-prefix-array-code
(include-book "projects/x86isa/machine/instructions/divide-spec" :dir :system)
(include-book "flags") ; reduce?
;(include-book "projects/x86isa/proofs/utilities/app-view/top" :dir :system)
(in-theory (disable acl2::nth-when-zp)) ; can cause problems
;(include-book "projects/x86isa/tools/execution/top" :dir :system) ;todo don't even use init-x86-state?
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/utilities/polarity" :dir :system)
;(local (include-book "kestrel/bv/rules10" :dir :system))
(include-book "kestrel/utilities/mv-nth" :dir :system)
;(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/bv/bvcat2" :dir :system)
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/sbvrem" :dir :system)
(local (include-book "kestrel/bv/rules3" :dir :system)) ;to normalize more
(local (include-book "linear-memory"))
(local (include-book "kestrel/bv/logand-b" :dir :system))
(local (include-book "kestrel/bv/logior-b" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
;(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop, to deal with truncate
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/denominator" :dir :system))
(local (include-book "kestrel/arithmetic-light/numerator" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;for logand-with-mask
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/bv/idioms" :dir :system))

;; (in-theory (disable acl2::car-to-nth-0))
;; (in-theory (disable acl2::nth-of-cdr)) ;new
;; (in-theory (enable nth))
;; ;(local (in-theory (enable LIST::NTH-OF-CONS)))

;(in-theory (disable ACL2::MEMBER-OF-CONS)) ;potentially bad (matches constants)
(in-theory (disable ACL2::ZP-WHEN-GT-0   ;slow
                    ACL2::ZP-WHEN-INTEGERP ;slow
                    ACL2::SLICE-TOO-HIGH-IS-0 ;slow
                    mv-nth))

(local (in-theory (disable ACL2::SMALL-INT-HACK ;slow
                           )))

;; could expand the bvminus
(defthmd canonical-address-p-becomes-bvlt-of-bvminus
  (implies (signed-byte-p 64 x)
           (equal (canonical-address-p x)
                  (acl2::bvlt 64 (acl2::bvminus 64 x -140737488355328) 281474976710656)))
  :hints (("Goal" :cases ((< x 0))
           :in-theory (enable canonical-address-p acl2::bvlt signed-byte-p
                              acl2::bvchop-when-negative-lemma))))

(defthmd canonical-address-p-becomes-bvlt-of-bvminus-strong
  (equal (canonical-address-p x)
         (and (signed-byte-p 64 x)
              (acl2::bvlt 64 (acl2::bvminus 64 x -140737488355328) 281474976710656)))
  :hints (("Goal" :cases ((< x 0))
           :in-theory (enable canonical-address-p acl2::bvlt signed-byte-p
                              acl2::bvchop-when-negative-lemma))))

;; ;; Just a wrapper that is in the x86isa package instead of the ACL2 package.
;; (defmacro defconst-computed (name form)
;;   `(acl2::defconst-computed ,name ,form))

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
;;  (implies (and (CANONICAL-ADDRESS-p rip)
;;                (natp len)
;;                (natp k)
;;                (< k len)
;;                (CANONICAL-ADDRESS-p (+ len rip)))
;;           (MEMBER-P (BINARY-+ k RIP) (CREATE-CANONICAL-ADDRESS-LIST len RIP))))

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

(defthm equal-of-if-constants
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep k3)))
           (equal (equal (if test k1 k2) k3)
                  (if test
                      (equal k1 k3) ;gets computed
                    (equal k2 k3))))) ;gets computed

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

(local
  (defthmd bvshl-becomes-*-of-expt
    (implies (and (integerp x)
                  (natp shift-amount)
                  (natp width))
             (equal (acl2::bvshl width x shift-amount)
                    (acl2::bvchop width (* (expt 2 shift-amount) x))))
    :hints (("Goal" :in-theory (enable acl2::bvshl acl2::bvcat)))))

;slow?
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
  :hints (("Goal" :in-theory (e/d (rb rb-1 ash ;rvm08
                                      acl2::bvcat-becomes-bvor-of-bvshl acl2::bvor bvshl-becomes-*-of-expt ;acl2::bvshl ; ACL2::BVCAT
                                      acl2::logapp
                                      APP-VIEW
                                      natp
                                      ) (ACL2::BVCAT-EQUAL-REWRITE-ALT
                                         ACL2::BVCAT-EQUAL-REWRITE
                                         ;X::MV-NTH-1-OF-RB-1-BECOMES-READ
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
                            acl2::bvchop-of-logtail-becomes-slice
                            ;;rb-split ; looped
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

;; ;sign flag
;; (defthmd sf-spec32-rewrite
;;   (equal (x86isa::sf-spec32 x)
;;          (acl2::getbit 31 x))
;;   :hints (("Goal" :in-theory (enable x86isa::sf-spec32))))

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

(local (in-theory (enable acl2::bvplus-of-unary-minus acl2::bvplus-of-unary-minus-arg2)))

;; (defthm rb-of-nil
;;   (equal (rb nil r-w-x x86)
;;          (mv nil nil x86))
;;   :hints (("Goal" :in-theory (enable rb))))

;is there a way to limit this?

;; (defthm true-listp-of-byte-ify
;;   (true-listp (byte-ify n val)))

;; ;move or drop?
;; (defthm acl2::assoc-equal-of-cons-irrel
;;   (implies (not (equal acl2::key (car a)))
;;            (equal (assoc-equal acl2::key (cons a acl2::rst))
;;                   (assoc-equal acl2::key acl2::rst)))
;;   :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm get-one-byte-prefix-array-code-rewrite-quotep
  (implies (syntaxp (quotep byte))
           (equal (x86isa::get-one-byte-prefix-array-code byte)
                  (acl2::lookup (acl2::bvchop 8 byte)
                                (cdr x86isa::*one-byte-prefixes-group-code-info-ar*))))
  :hints (("Goal" :in-theory (e/d (x86isa::get-one-byte-prefix-array-code aref1 acl2::assoc-equal-of-cons)
                                  (acl2::not-equal-bvchop-when-not-equal-bvchop
                                   acl2::rewrite-bv-equality-when-sizes-dont-match-2)))))

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

;; Move some of these:

(defthmd split-integer
  (implies (and (integerp x)
                (natp size))
           (equal (+ (acl2::bvchop size x) (* (expt 2 size) (acl2::logtail size x)))
                  x))
  :hints (("Goal" :in-theory (enable acl2::bvchop))))

(defthm logtail-when-signed-byte-p-same
  (implies (signed-byte-p 64 x)
           (equal (logtail 64 x)
                  (if (equal 1 (acl2::getbit 63 x))
                      -1
                    0))))

(defthm logtail-when-signed-byte-p-one-more
  (implies (signed-byte-p 64 x)
           (equal (logtail 63 x)
                  (if (equal 1 (acl2::getbit 63 x))
                      -1
                    0))))

(defthmd bvchop-when-signed-byte-p-one-more-and-negative
  (implies (and (signed-byte-p 64 x)
                (equal 1 (acl2::getbit 63 x)))
           (equal (acl2::bvchop 63 x)
                  (+ x (expt 2 63))))
  :hints (("Goal" :use (:instance split-integer
                                  (size 63)
                                  (x x))
           :in-theory (disable acl2::bvcat-equal-rewrite-alt
                               acl2::bvcat-equal-rewrite))))

(defthmd bvchop-when-signed-byte-p-one-more-and-negative-linear
  (implies (and (signed-byte-p 64 x)
                (equal 1 (acl2::getbit 63 x)))
           (equal (acl2::bvchop 63 x)
                  (+ x (expt 2 63))))
  :rule-classes :linear
  :hints (("Goal" :use (:instance split-integer
                                  (size 63)
                                  (x x))
           :in-theory (disable acl2::bvcat-equal-rewrite-alt
                               acl2::bvcat-equal-rewrite))))

;this may help that problem where normalizing these constants caused problems
(defthm <-of-logext-and-bvplus-of-constant
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 64 k)
                (equal 1 (acl2::getbit 63 k)) ;(>= k (expt 2 63))
                (signed-byte-p 64 x))
           (equal (< x (logext 64 (acl2::bvplus 64 k x)))
                  (< x (+ (- (expt 2 64) (acl2::bvchop 64 k)) (- (expt 2 63))))))
  :hints (("Goal" :in-theory (e/d (acl2::bvplus
                                   acl2::logext-cases
                                   ;acl2::bvcat
                                   ;acl2::logapp
                                   acl2::logext-of-plus
                                   acl2::bvchop-of-sum-cases
                                   acl2::getbit-of-+
                                   acl2::bvchop-when-top-bit-1-cheap
                                   bvchop-when-signed-byte-p-one-more-and-negative-linear)
                                  (
                                   acl2::bvchop-identity-cheap
                                   acl2::bvchop-identity
                                   ;acl2::trim-to-n-bits-meta-rule-for-bvcat ;looped
                                   acl2::bvcat-of-bvchop-low ;looped
                                   acl2::slice-of-bvchop-low ;looped
                                   acl2::slice-of-bvchop-low-gen ;looped
                                   acl2::slice-of-bvchop-low-gen-better ;looped
                                   ))
           :use (:instance acl2::split-bv
                           (n 64)
                           (m 63)
                           (x (acl2::bvchop 64 k))))))







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
                                                ACL2::LOGEXT-OF-PLUS
                                                acl2::getbit)
                                  (ACL2::BVCHOP-IDENTITY-CHEAP
                                   ACL2::BVCHOP-IDENTITY
                                   ;ACL2::TRIM-TO-N-BITS-META-RULE-FOR-BVCAT ;looped
                                   ACL2::BVCAT-OF-BVCHOP-LOW ;looped
                                   ))
           :use (:instance acl2::split-bv
                           (n 64)
                           (m 63)
                           (x k)))))

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
;;  (implies (and (< n size)
;;                (natp size)
;;                (natp n))
;;           (equal (acl2::bvplus size -1 (expt 2 n))
;;                  (acl2::bvcat (- size n)
;;                               0
;;                               n
;;                               (+ -1 (expt 2 n)))))
;;  :hints (("Goal" :in-theory (e/d (acl2::bvplus ACL2::REPEATBIT)
;;                                  (
;;                                   ACL2::BVCAT-OF-+-LOW ;looped
;;                                   )))))

;; ;a bunch of 0's followed by a bunch of 1's
;; instead, just drop the (expt 2 size)
;; (defthm bvplus-of-expt-and-all-ones
;;  (implies (and (< n size)
;;                (natp size)
;;                (natp n))
;;           (equal (acl2::bvplus size (expt 2 n) (+ -1 (expt 2 size)))
;;                  (acl2::bvcat (- size n)
;;                               0
;;                               n
;;                               (+ -1 (expt 2 n)))))
;;  :hints (("Goal" :in-theory (e/d (acl2::bvplus ACL2::REPEATBIT)
;;                                  (
;;                                   ACL2::BVCAT-OF-+-LOW ;looped
;;                                   )))))



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





;; ;drop?
;; (defthm one-byte-opcode-execute-of-if-arg1
;;   (equal (one-byte-opcode-execute proc-mode (if test start-rip1 start-rip2) temp-rip prefixes rex-byte opcode modr/m sib x86)
;;          (if test
;;              (one-byte-opcode-execute proc-mode start-rip1 temp-rip prefixes rex-byte opcode modr/m sib x86)
;;            (one-byte-opcode-execute proc-mode start-rip2 temp-rip prefixes rex-byte opcode modr/m sib x86))))

;; ;drop?
;; (defthm one-byte-opcode-execute-of-if-arg2
;;   (equal (one-byte-opcode-execute proc-mode start-rip (if test temp-rip1 temp-rip2) prefixes rex-byte opcode modr/m sib x86)
;;          (if test
;;              (one-byte-opcode-execute proc-mode start-rip temp-rip1 prefixes rex-byte opcode modr/m sib x86)
;;            (one-byte-opcode-execute proc-mode start-rip temp-rip2 prefixes rex-byte opcode modr/m sib x86))))

;; ;drop?
;; (defthm one-byte-opcode-execute-of-if-arg6
;;   (equal (one-byte-opcode-execute proc-mode start-rip temp-rip prefixes rex-byte opcode (if test modr/m1 modr/m2) sib x86)
;;          (if test
;;              (one-byte-opcode-execute proc-mode start-rip temp-rip prefixes rex-byte opcode modr/m1 sib x86)
;;            (one-byte-opcode-execute proc-mode start-rip temp-rip prefixes rex-byte opcode modr/m2 sib x86))))

;; ;once this breaks the symmetry, the two one-byte-opcode-execute terms
;; ;resulting from a branch will be different (and perhaps each then will
;; ;get a nice context computed for it)
;; ;drop?
;; (defthm if-of-one-byte-opcode-execute-of-if-arg2
;;   (equal (if test
;;              (one-byte-opcode-execute proc-mode start-rip
;;                                        (if test temp-rip1 temp-rip2) ;same test as above
;;                                        prefixes rex-byte opcode modr/m sib
;;                                        x86)
;;            x)
;;          (if test
;;              (one-byte-opcode-execute proc-mode start-rip
;;                                        temp-rip1
;;                                        prefixes rex-byte opcode modr/m sib
;;                                        x86)
;;            x)))

;; ;drop?
;; (defthm if-of-one-byte-opcode-execute-of-if-arg5
;;   (equal (if test
;;              (one-byte-opcode-execute proc-mode start-rip
;;                                        temp-rip
;;                                        prefixes rex-byte
;;                                        (if test opcode1 opcode2) ;same test as above
;;                                        modr/m sib
;;                                        x86)
;;            x)
;;          (if test
;;              (one-byte-opcode-execute proc-mode start-rip
;;                                        temp-rip
;;                                        prefixes rex-byte opcode1 modr/m sib
;;                                        x86)
;;            x)))


;;TODO: Maybe we should have axe split the simulation instead of proving all these if lifting rules.

;why is axe reasoning about CHECK-DCL-GUARDIAN? it's mentioned in X86ISA::X86-FETCH-DECODE-EXECUTE

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

;; Add aliases in the X86ISA package of some common utilities:

;; (defmacro defconst-computed2 (&rest args) `(acl2::defconst-computed2 ,@args))
;; (defmacro prove-equal-with-axe (&rest args) `(acl2::prove-equal-with-axe ,@args))
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
(defthm xw-of-rip-and-if
  (equal (xw ':rip '0 (if test pc1 pc2) x86)
         (if test
             (xw ':rip '0 pc1 x86)
           (xw ':rip '0 pc2 x86))))

(defthm xr-of-myif
  (equal (xr fld index (acl2::myif test then else))
         (acl2::myif test
                     (xr fld index then)
                     (xr fld index else)))
  :hints (("Goal" :in-theory (enable acl2::myif))))

(in-theory (disable x86isa::rme08))

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



(in-theory (disable acl2::posp-redefinition)) ;yuck
(in-theory (enable posp))

;; (defthm +-of-bvplus-of-x-and-minus-x
;;   (implies (unsigned-byte-p 32 x)
;;            (equal (+ (BVPLUS 32 1 x)
;;                      (- x))
;;                   (if (equal x (+ -1 (expt 2 32)))
;;                       (- x)
;;                     1)))
;;   :hints (("Goal" :in-theory (enable bvplus acl2::bvchop-of-sum-cases))))

(in-theory (enable x86isa::x86-operation-mode)) ;for non-axe symbolic execution

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm set-rax-of-if-arg1
;;   (equal (set-rax (if test val1 val2) x86)
;;          (if test (set-rax val1 x86) (set-rax val2 x86))))


;apparently the AC flag affects alignment checking
;todo: avoid get-flag here
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

(defthm alignment-checking-enabled-p-of-set-flag
  (implies (and (member-equal flag x::*flags*) ;drop?
                (not (equal flag :ac)))
           (equal (alignment-checking-enabled-p (x::set-flag flag val x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :in-theory (enable alignment-checking-enabled-p
                                     x::set-flag
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
                                     x86isa::!rflagsBits->id
                                     segment-selectorbits->rpl
                                     cr0bits->am
                                     2bits-fix
                                     acl2::getbit-of-logand))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; goes to set-flag instead of exposing details of the flags
;; todo: avoid IFs on states here
;; TODO: See write-user-rflags-rewrite-better !
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
  :hints (("Goal" :in-theory (enable x::set-flag acl2::getbit write-user-rflags))))

(include-book "readers-and-writers")

;todo: move to a book in the X package
(defthm write-user-rflags-rewrite-better
  (equal (write-user-rflags user-flags-vector undefined-mask x86)
         (b* ((user-flags-vector (n32 user-flags-vector))
              (undefined-mask (n32 undefined-mask))
              (x86 (x::set-flag :cf (if (equal (rflagsbits->cf undefined-mask) 1) (acl2::getbit 0 (create-undef (nfix (x::undef x86)))) (rflagsbits->cf user-flags-vector)) x86)) ; todo: simplify?
              (x86 (x::set-undef (if (equal (rflagsbits->cf undefined-mask) 1) (+ 1 (nfix (undef x86))) (undef x86)) x86))
              (x86 (x::set-flag :pf (if (equal (rflagsbits->pf undefined-mask) 1) (acl2::getbit 0 (create-undef (nfix (x::undef x86)))) (rflagsbits->pf user-flags-vector)) x86))
              (x86 (x::set-undef (if (equal (rflagsbits->pf undefined-mask) 1) (+ 1 (nfix (undef x86))) (undef x86)) x86))
              (x86 (x::set-flag :af (if (equal (rflagsbits->af undefined-mask) 1) (acl2::getbit 0 (create-undef (nfix (x::undef x86)))) (rflagsbits->af user-flags-vector)) x86))
              (x86 (x::set-undef (if (equal (rflagsbits->af undefined-mask) 1) (+ 1 (nfix (undef x86))) (undef x86)) x86))
              (x86 (x::set-flag :zf (if (equal (rflagsbits->zf undefined-mask) 1) (acl2::getbit 0 (create-undef (nfix (x::undef x86)))) (rflagsbits->zf user-flags-vector)) x86))
              (x86 (x::set-undef (if (equal (rflagsbits->zf undefined-mask) 1) (+ 1 (nfix (undef x86))) (undef x86)) x86))
              (x86 (x::set-flag :sf (if (equal (rflagsbits->sf undefined-mask) 1) (acl2::getbit 0 (create-undef (nfix (x::undef x86)))) (rflagsbits->sf user-flags-vector)) x86))
              (x86 (x::set-undef (if (equal (rflagsbits->sf undefined-mask) 1) (+ 1 (nfix (undef x86))) (undef x86)) x86))
              (x86 (x::set-flag :of (if (equal (rflagsbits->of undefined-mask) 1) (acl2::getbit 0 (create-undef (nfix (x::undef x86)))) (rflagsbits->of user-flags-vector)) x86))
              (x86 (x::set-undef (if (equal (rflagsbits->of undefined-mask) 1) (+ 1 (nfix (undef x86))) (undef x86)) x86)))
           x86))
  :hints (("Goal" :in-theory (enable x::set-undef undef))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This could go into a support64 book:

(defthm add-to-*ip-of-*64-bit-mode*
  (equal (x86isa::add-to-*ip *64-bit-mode* x86isa::*ip x86isa::delta x86)
         (let ((sum (+ x86isa::*ip x86isa::delta)))
           (if (canonical-address-p sum)
               (mv nil sum)
             (mv (list :non-canonical-instruction-pointer sum)
                 0))))
  :hints (("Goal" :in-theory (enable x86isa::add-to-*ip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: more
(defthmd n64-becomes-bvchop (equal (x86isa::n64 x) (acl2::bvchop 64 x)))

(local (include-book "kestrel/bv/rules3" :dir :system)) ;drop?

;todo: gen the 2
(defthm idiv-64-by-2-no-error
  (equal (mv-nth 0 (x86isa::idiv-spec-64 (acl2::bvsx 128 64 x) 2))
         nil)
  :hints (("Goal" :in-theory (enable x86isa::idiv-spec-64 truncate))))

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
