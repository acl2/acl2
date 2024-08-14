; Rules (theorems) relied upon by the Formal Unit Tester
;
; Copyright (C) 2016-2023 Kestrel Technology, LLC
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: IN-PROGRESS

;; TODO: Organize this material

;; TODO: Don't even attempt a run if no match is found in the symbol table for the function name?

;; TODO: Somehow distinguish between a run failing to finish and a query failing with a cex -- for now, we just use must-fail.

;(include-book "kestrel/bv/rotate" :dir :system) ;for INTEGERP-OF-LEFTROTATE32
;(include-book "kestrel/bv/intro" :dir :system)
;(include-book "kestrel/axe/rules1" :dir :system)
;(include-book "kestrel/axe/axe-rules-mixed" :dir :system)
(include-book "kestrel/x86/rflags-spec-sub" :dir :system)
(include-book "kestrel/x86/read-and-write" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers64" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
;; todo: reduce:
(local (include-book "kestrel/axe/axe-rules-mixed" :dir :system)) ; drop?
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system)) ; reduce?
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
;; (local (include-book "kestrel/bv/logand-b" :dir :system))
;; (local (include-book "kestrel/bv/logior" :dir :system))
;; (local (include-book "kestrel/bv/logxor-b" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/minus" :dir :system))
;; (local (include-book "kestrel/bv/bvsx-rules" :dir :system))

;(def-constant-opener bool-fix$inline) ; or build into axe?


;; todo: do we want to see myif or if?
;; (defthm rflagsbits->af-of-if
;;   (equal (x86isa::rflagsbits->af$inline (if test tp ep))
;;          (myif test
;;                (x86isa::rflagsbits->af$inline tp)
;;                (x86isa::rflagsbits->af$inline ep))))

(defthm rflagsbits->af-of-myif
  (equal (x86isa::rflagsbits->af$inline (myif test tp ep))
         (myif test
               (x86isa::rflagsbits->af$inline tp)
               (x86isa::rflagsbits->af$inline ep)))
  :hints (("Goal" :in-theory (enable myif))))



(defthm of-spec-of-logext-32
  (equal (of-spec32 (logext 32 x))
         0)
  :hints (("Goal" :in-theory (enable of-spec32))))

(defthm bvchop-of-zf-spec
  (implies (posp size)
           (equal (bvchop size (zf-spec result))
                  (zf-spec result))))

(defthm logext-of-zf-spec
  (implies (and (< 1 size)
                (integerp size))
           (equal (logext size (zf-spec result))
                  (zf-spec result))))

(defthm integerp-of-zf-spec
  (integerp (zf-spec result)))

(defthm sf-spec64-of-bvchop-64
  (equal (sf-spec64 (bvchop 64 x))
         (sf-spec64 x))
  :hints (("Goal" :in-theory (enable sf-spec64))))

(defthm of-spec64-of-logext-64
  (equal (of-spec64 (logext 64 x))
         0)
  :hints (("Goal" :in-theory (enable of-spec64))))

;; ;todo!
;; ;or use a defun-sk to state that all states have the same cpuid
;; (skip-proofs
;;  (defthm feature-flag-sse-of-xw
;;   (equal (x86isa::feature-flag :sse (xw fld index val x86))
;;          (x86isa::feature-flag :sse x86))
;;   :hints (("Goal" :in-theory (enable ctri)))))

;; (skip-proofs
;;  (defthm feature-flag-sse-of-write
;;   (equal (x86isa::feature-flag :sse (write n base-addr val x86))
;;          (x86isa::feature-flag :sse x86))
;;   :hints (("Goal" :in-theory (enable ctri)))))

;; (skip-proofs
;;  (defthm feature-flag-sse-of-set-flag
;;   (equal (x86isa::feature-flag :sse (set-flag flag val x86))
;;          (x86isa::feature-flag :sse x86))
;;   :hints (("Goal" :in-theory (enable ctri)))))

;; (skip-proofs
;;  (defthm feature-flag-sse2-of-xw
;;   (equal (x86isa::feature-flag :sse2 (xw fld index val x86))
;;          (x86isa::feature-flag :sse2 x86))
;;   :hints (("Goal" :in-theory (enable ctri)))))

;; (skip-proofs
;;  (defthm feature-flag-sse2-of-write
;;   (equal (x86isa::feature-flag :sse2 (write n base-addr val x86))
;;          (x86isa::feature-flag :sse2 x86))
;;   :hints (("Goal" :in-theory (enable ctri)))))

;; (skip-proofs
;;  (defthm feature-flag-sse2-of-set-flag
;;   (equal (x86isa::feature-flag :sse2 (set-flag flag val x86))
;;          (x86isa::feature-flag :sse2 x86))
;;   :hints (("Goal" :in-theory (enable ctri)))))

(defthm bvchop-of-sub-zf-spec32
  (implies (and (<= 1 size)
                (integerp size))
           (equal (bvchop size (x86isa::sub-zf-spec32 dst src))
                  (x86isa::sub-zf-spec32 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec32))))

;; we open sub-zf-spec32 here, since it's not being passed to JXXX condition function:
(defthm equal-of-sub-zf-spec32-and-1
  (equal (equal (x86isa::sub-zf-spec32 dst src) 1)
         (equal dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec32
                                     x86isa::zf-spec
                                     acl2::bvchop-of-sum-cases))))

; commuted, only for axe
(defthmd equal-of-1-and-sub-zf-spec32
  (equal (equal 1 (x86isa::sub-zf-spec32 dst src))
         (equal dst src)))

;slow: ACL2::UNSIGNED-BYTE-P-OF-+-OF-MINUS

;; todo: in what other contexts do we need to open this sub-zf-spec32?
;slow?
;; (defthm if-of-sub-zf-spec32-arg2
;;   (equal (if test (x86isa::sub-zf-spec32 dst src) ep)
;;          (if test (if (equal (bvchop 32 dst) (bvchop 32 src)) 1 0) ep))
;;   :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec32
;;                                      x86isa::zf-spec
;;                                      acl2::bvchop-of-sum-cases))))

;todo: gross to have both this and the rule for IF
(defthm myif-of-sub-zf-spec32-arg2
  (equal (myif test (x86isa::sub-zf-spec32 dst src) ep)
         ;;(myif test (if (equal (bvchop 32 dst) (bvchop 32 src)) 1 0) ep)
         (myif test (if (equal dst src) 1 0) ep))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec32
                                     x86isa::zf-spec
                                     acl2::bvchop-of-sum-cases))))

(defthm myif-of-sub-zf-spec32-arg3
  (equal (myif test tp (x86isa::sub-zf-spec32 dst src))
         ;; (myif test tp (if (equal (bvchop 32 dst) (bvchop 32 src)) 1 0))
         (myif test tp (if (equal dst src) 1 0)))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec32
                                     x86isa::zf-spec
                                     acl2::bvchop-of-sum-cases))))


;; (defthm feature-flag-of-if
;;   (equal (x86isa::feature-flag flag (if test x86 x86_2))
;;          (if test (x86isa::feature-flag flag x86) (x86isa::feature-flag flag x86_2))))

;; should not be needed?
(defthm xr-of-!rflags-irrel
  (implies (not (equal fld :rflags))
           (equal (xr fld index (!rflags v x86))
                  (xr fld index x86))))

(defthm !rflags-of-if-arg1
  (equal (x86isa::!rflags (if test v1 v2) x86)
         (if test (x86isa::!rflags v1 x86) (x86isa::!rflags v2 x86))))

(defthm !rflags-of-if-arg2
  (equal (x86isa::!rflags v (if test x86_1 x86_2))
         (if test (x86isa::!rflags v x86_1) (x86isa::!rflags v x86_2))))


;; (defthm x86isa::rflagsbits->pf-of-if
;;   (equal (x86isa::rflagsbits->pf (if test x1 x2))
;;          (if test (x86isa::rflagsbits->pf x1) (x86isa::rflagsbits->pf x2))))

;; (defthm x86isa::rflagsbits->cf-of-if
;;   (equal (x86isa::rflagsbits->cf (if test x1 x2))
;;          (if test (x86isa::rflagsbits->cf x1) (x86isa::rflagsbits->cf x2))))

;; (defthm x86isa::rflagsbits->of-of-if
;;   (equal (x86isa::rflagsbits->of (if test x1 x2))
;;          (if test (x86isa::rflagsbits->of x1) (x86isa::rflagsbits->of x2))))

;; (defthm x86isa::rflagsbits->sf-of-if
;;   (equal (x86isa::rflagsbits->sf (if test x1 x2))
;;          (if test (x86isa::rflagsbits->sf x1) (x86isa::rflagsbits->sf x2))))

;; (defthm x86isa::rflagsbits->zf-of-if
;;   (equal (x86isa::rflagsbits->zf (if test x1 x2))
;;          (if test (x86isa::rflagsbits->zf x1) (x86isa::rflagsbits->zf x2))))

;todo: why is !rflags remaining in some examples like test_popcount_32_one_bit?

;; (thm
;;  (implies (and (PROGRAM-AT (BINARY-+ '304 TEXT-OFFSET) '(0 0 0 0 1 0 0 0 2 0 0 0 3 0 0 0) X86)
;;                (CANONICAL-ADDRESS-P$INLINE (BINARY-+ '319 TEXT-OFFSET))
;;                (bvlt 32 x 4))
;;           (equal (READ '4
;;                        (BINARY-+ '304
;;                                  (BINARY-+ TEXT-OFFSET
;;                                            (BINARY-* '4 (BVCHOP '32 x))))
;;                        X86)
;;                  (bv-array-read 32 4 (BVCHOP '32 x) '(0 1 2 3)))))


;; (thm
;;  (implies (and (PROGRAM-AT (BINARY-+ '304 TEXT-OFFSET) '(0 1 2 3) X86)
;;                (CANONICAL-ADDRESS-P$INLINE (BINARY-+ '319 TEXT-OFFSET))
;;                (bvlt 32 x 4))
;;           (equal (READ '1
;;                        (BINARY-+ '304
;;                                  (BINARY-+ TEXT-OFFSET
;;                                            (BVCHOP '32 x)))
;;                        X86)
;;                  (bv-array-read 32 4 (BVCHOP '32 x) '(0 1 2 3)))))



;; ;arises in array indexing
;; ;perhaps more direct than other rules
;; not right because the values are not offsets...
;; (defthm canonical-address-p-of-+-of-bvmult-64-of-4
;;   (implies (and (syntaxp (quotep k))
;;                 (canonical-address-p k)
;;                 (canonical-address-p free)
;;                 (syntaxp (quotep free))
;;                 (< k free)
;;                 (<= (* 4 (bvchop 62 index)) (- free k)))
;;            (canonical-address-p (+ k (bvmult 64 4 index))))
;;   :hints (("Goal" :in-theory (enable bvmult canonical-address-p))))

;arises in array indexing
;perhaps more direct than other rules
(defthm canonical-address-p-of-+-of-bvmult-64-of-4
  (implies (and (syntaxp (quotep k))
                (canonical-address-p k)
                (< (* 4 (bvchop 62 index)) (- 140737488355328 k)))
           (canonical-address-p (+ k (bvmult 64 4 index))))
  :hints (("Goal" :in-theory (enable bvmult canonical-address-p signed-byte-p))))



;; (thm
;;  (implies (and (canonical-address-p$inline (binary-+ '211 text-offset))
;;                (canonical-address-p$inline text-offset)
;;                (not (< '3 x))
;;                (natp x))
;;           (canonical-address-p$inline (binary-+ '208 (binary-+ x text-offset))))
;; )

;not true?
;; (thm
;;  (equal (GET-PREFIXES X86ISA::PROC-MODE X86ISA::START-RIP X86ISA::PREFIXES X86ISA::REX-BYTE X86ISA::CNT (set-rip rip X86))
;;         (GET-PREFIXES X86ISA::PROC-MODE X86ISA::START-RIP X86ISA::PREFIXES X86ISA::REX-BYTE X86ISA::CNT X86))
;;  :hints (("Goal" :in-theory (enable GET-PREFIXES))))


;gen the (rxp x86)?
(defthm not-equal-of-+-and-+-when-separate
  (implies (and (separate :r text-offset-k text-offset :r rsp-k (+ neg-rsp-k (rsp x86))) ; example: (separate :r 150 text-offset :r 80 (binary-+ -80 (rsp x86)))
                (<= k1 text-offset-k)
                (natp text-offset-k)
                (natp rsp-k)
                (equal neg-rsp-k (- rsp-k))
                (< neg-rsp-k k2)
                (natp k1)
                (< k2 0)
                (integerp k2))
           (not  (equal (+ k1 text-offset)
                        (+ k2 (rsp x86)))))
  :hints (("Goal" :in-theory (enable separate))))

(defthm not-equal-of-+-of-+-and-+-when-separate
  (implies (and (separate :r text-offset-k (+ k1 text-offset) :r rsp-k (+ neg-rsp-k (rsp x86))) ; example: (SEPARATE :R 512 (BINARY-+ 224 TEXT-OFFSET) :R 80 (BINARY-+ -80 (RSP X86)))
                (<= index text-offset-k)
                (natp index)
                (natp text-offset-k)
                (natp rsp-k)
                (equal neg-rsp-k (- rsp-k))
                (< neg-rsp-k k2)
                (natp k1)
                (< k2 0)
                (integerp k2))
           (not (equal (+ k1 (+ index text-offset))
                       (+ k2 (rsp x86)))))
  :hints (("Goal" :in-theory (enable separate))))

(defthm not-equal-of-+-of-+-and-+-when-separate-gen
  (implies (and (separate :r text-offset-k (+ k3 text-offset) :r rsp-k (+ neg-rsp-k (rsp x86))) ; example: (SEPARATE :R 512 (BINARY-+ 224 TEXT-OFFSET) :R 80 (BINARY-+ -80 (RSP X86)))
                (<= k3 (+ k1 index))
                (<= (+ k1 index) (+ k3 text-offset-k))
                (natp index)
                (natp k3)
                (natp text-offset-k)
                (natp rsp-k)
                (equal neg-rsp-k (- rsp-k))
                (< neg-rsp-k k2)
                (natp k1)
                (< k2 0)
                (integerp k2))
           (not (equal (+ k1 (+ index text-offset))
                       (+ k2 (rsp x86)))))
  :hints (("Goal" :in-theory (enable separate))))

;; (thm
;;  (implies (and (syntaxp (and (quotep offset1)
;;                              (quotep offset2)))
;;                (equal offset2 (+ 1 offset1))
;;                (canonical-address-p (+ offset1 addr))
;;                (canonical-address-p (+ 3 offset1 addr)))
;;           (equal (read 1 (+ offset2 addr) (write 4 (+ offset1 addr) val x86))
;;                  (slice 15 8 val)))
;;  :hints (("Goal" :expand ((write 4 (+ addr offset1) val x86)
;;                           (write 3 (+ 1 addr offset1)
;;                                  (logtail 8 val)
;;                                  (write-byte (+ addr offset1) val x86)))
;;           :in-theory (e/d (write bvminus)
;;                           (acl2::logtail-logtail ; todo: does forcing
;;                            )))))

;; (thm
;;  (implies (and (syntaxp (and (quotep offset1)
;;                              (quotep offset2)))
;;                (<= offset1 offset2)
;;                (< offset2 (+ 4 offset1))
;;                (integerp addr)
;;                (integerp offset1)
;;                (integerp offset2)
;;                (signed-byte-p 32 offset1) ; (signed-byte-p 48 offset1)
;;                (signed-byte-p 32 offset2) ; (signed-byte-p 48 offset2)
;;                (canonical-address-p addr)
;;                (canonical-address-p (+ 3 addr)) ; gross?
;;                (canonical-address-p (+ offset1 addr))
;;                (canonical-address-p (+ 3 offset1 addr)))
;;           (equal (read 1 (+ offset2 addr) (write 4 (+ offset1 addr) val x86))
;;                  (slice (+ 7 (* 8 (bvminus 48 offset2 offset1) ;(- offset2 offset1) ;(- (bvchop 48 offset2) (bvchop 48 offset1))
;;                                 ))
;;                         (* 8 (bvminus 48 offset2 offset1) ;(- offset2 offset1) ;(- (bvchop 48 offset2) (bvchop 48 offset1))
;;                            )
;;                         val)))
;;  :otf-flg t
;;  :hints (("Goal" :expand ((write 4 (+ addr offset1) val x86)
;;                           (write 3 (+ 1 addr offset1)
;;                                  (logtail 8 val)
;;                                  x86)
;;                           (write 2 (+ 2 addr offset1)
;;                                  (logtail 16 val)
;;                                  x86))
;;           :in-theory (e/d (write bvminus acl2::bvchop-of-sum-cases
;;                                  ;; equal-of-bvchop-when-signed-byte-p
;;                                  bvchop-when-signed-byte-p-cases-cheap
;;                                  canonical-address-p
;;                                  )
;;                           (acl2::logtail-logtail ; todo: does forcing
;;                            (:e expt) ; prevent out of memory error
;;                            distributivity
;;                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; usually negoffset, n1, n2, and minusn2 are constants
(defthm not-equal-of-+-when-separate
  (implies (and (separate :r n1 text-offset :r n2 (binary-+ minusn2 (rsp x86)))
                (posp n2)
                (integerp negoffset)
                (< negoffset 0)
                (<= (- negoffset) n2)
                (equal minusn2 (- n2))
                (posp n1))
           (not (equal text-offset (+ negoffset (rsp x86)))))
  :hints (("Goal" :in-theory (enable separate))))

(defthm not-equal-of-+-when-separate-alt
  (implies (and (separate :r n1 text-offset :r n2 (binary-+ minusn2 (rsp x86)))
                (posp n2)
                (integerp negoffset)
                (< negoffset 0)
                (<= (- negoffset) n2)
                (equal minusn2 (- n2))
                (posp n1))
           (not (equal (+ negoffset (rsp x86)) text-offset)))
  :hints (("Goal" :in-theory (enable separate))))
