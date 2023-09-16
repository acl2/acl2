; Rules (theorems) relied upon by the Formal Unit Tester
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
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

(include-book "kestrel/axe/bv-rules-axe" :dir :system) ;for trim-does-nothing-dag
;(include-book "kestrel/bv/rotate" :dir :system) ;for INTEGERP-OF-LEFTROTATE32
(include-book "kestrel/bv/intro" :dir :system)
;(include-book "kestrel/axe/rules1" :dir :system)
;(include-book "kestrel/axe/axe-rules-mixed" :dir :system)
(include-book "kestrel/x86/rflags-spec-sub" :dir :system)
(include-book "kestrel/x86/read-and-write" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers64" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/bv/logxor-b" :dir :system))
;(local (include-book "kestrel/alists-light/alistp" :dir :system))

(acl2::def-constant-opener acl2::bool-fix$inline) ; or build into axe?

(defthm /-bound-when-non-negative-and-integer
  (implies (and (natp i)
                (integerp j))
           (<= (- i) (/ i j)))
  :hints (("Goal" :cases ((<= j -1)))))

(defthm truncate-bound-when-non-negative-and-integer-linear
  (implies (and (natp i)
                (integerp j))
           (<= (- i) (truncate i j)))
  :rule-classes :linear
  :hints (("Goal" :cases ((< j 0))
           :in-theory (enable acl2::truncate-becomes-floor-gen))))

(defthm not-sbvlt-of-sbvdiv-and-minus-constant-32-64
  (implies (unsigned-byte-p 31 x)
           (not (sbvlt '64 (acl2::sbvdiv '64 x y) '18446744071562067968)))
  :hints (("Goal" :in-theory (e/d (acl2::sbvdiv sbvlt) (acl2::sbvlt-rewrite)))))

(defthm not-sbvlt-of-constant-and-sbvdiv-32-64
  (implies (unsigned-byte-p 31 x)
           (not (SBVLT '64 '2147483647 (ACL2::SBVDIV '64 x y))))
  :hints (("Goal" :in-theory (e/d (acl2::sbvdiv sbvlt) (acl2::sbvlt-rewrite)))))

(defthm not-bvlt-of-constant-and-bvdiv-64-128
  (implies (unsigned-byte-p 64 x)
           (not (BVLT '128 '18446744073709551615 (ACL2::BVDIV '128 x y))))
  :hints (("Goal" :in-theory (enable ACL2::BVDIV bvlt))))

(defthm not-bvlt-of-constant-and-bvdiv-32-64
  (implies (unsigned-byte-p 32 x)
           (not (bvlt '64 4294967295 (acl2::bvdiv 64 x y))))
  :hints (("Goal" :in-theory (enable acl2::bvdiv bvlt))))

;; todo: do we want to see myif or if?
(defthm rflagsbits->af-of-if
  (equal (x86isa::rflagsbits->af$inline (if test tp ep))
         (myif test
               (x86isa::rflagsbits->af$inline tp)
               (x86isa::rflagsbits->af$inline ep))))

(defthm rflagsbits->af-of-myif
  (equal (x86isa::rflagsbits->af$inline (myif test tp ep))
         (myif test
               (x86isa::rflagsbits->af$inline tp)
               (x86isa::rflagsbits->af$inline ep)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm <-of-*-of-constant-and-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (< 0 k2) ;gen
                (rationalp x)
                (rationalp k1)
                (rationalp k2)
                )
           (equal (< (* k2 x) k1)
                  (and ;(acl2-numberp k1)
                       (< (fix x) (/ k1 k2)))))
  :hints (("Goal" :in-theory (disable inverse-of-*
                                      associativity-of-*)
           :use ((:instance inverse-of-* (x k2))
                 (:instance associativity-of-* (x k2) (y (/ k2)) (z x))))))

;todo: gen
(defthm <-of-15-and-*-of-4
  (implies (natp x)
           (equal (< 15 (* x 4))
                  (< 3 x))))

(defthmd <-of-floor-when-<
  (implies (and (< x y)
                (rationalp x))
           (< (floor x 1) y)))

(defthm <-of-*-when-constant-integers
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (posp k2) ; gen?
                (integerp k1)
                (integerp x))
           (equal (< k1 (* k2 x))
                  (let ((quot (/ k1 k2)))
                    (if (integerp quot)
                        (< quot x)
                      (< (floor quot 1) x)))))
  :hints (("Goal" ;:in-theory (enable <-of-floor-when-<)
           :cases ((<= x (/ K1 k2))))))

;todo: compare to X86ISA::SEPARATE-SMALLER-REGIONS
(defthm separate-when-separate
  (implies (and (separate :r n3 addr3 :r n4 addr4) ; free vars
                (<= addr3 addr1)
                (<= n1 (+ n3 (- addr3 addr1)))
                (<= addr4 addr2)
                (<= n2 (+ n4 (- addr4 addr2))))
           (separate :r n1 addr1 :r n2 addr2)))

;gen
;why is this needed? maybe because of ACL2::<-BECOMES-BVLT-DAG-ALT-GEN-BETTER2
(defthm UNSIGNED-BYTE-P-2-of-bvchop-when-bvlt-of-4
  (implies (BVLT '32 x '4)
           (UNSIGNED-BYTE-P '2 (BVCHOP '32 x))))

(defthmd rationalp-when-integerp
  (implies (integerp x)
           (rationalp x)))

(defthm acl2-numberp-of--
  (acl2-numberp (- x)))

(defthm x86isa::canonical-address-p-between-special5
  (implies (and (canonical-address-p text-offset)
                (canonical-address-p (+ k2 text-offset))
                (<= (+ k x) k2)
                (natp k)
                (natp x)
                (natp k2))
           ;; ex (BINARY-+ '192 (BINARY-+ TEXT-OFFSET (ASH (BVCHOP '32 (RDI X86)) '2)))
           (canonical-address-p (+ k text-offset x))))

(DEFTHM X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL5-alt
  (IMPLIES (AND (CANONICAL-ADDRESS-P TEXT-OFFSET)
                (CANONICAL-ADDRESS-P (+ K2 TEXT-OFFSET))
                (<= (+ K X) K2)
                (NATP K)
                (NATP X)
                (NATP K2))
           (CANONICAL-ADDRESS-P (+ K X TEXT-OFFSET))))

(defthm x86isa::canonical-address-p-between-special6
  (implies (and (canonical-address-p (+ k1 base))
                (syntaxp (quotep k1))
                (canonical-address-p (+ k2 base))
                (syntaxp (quotep k2))
                (< k1 k2) ; break symmetry
                (<= k1 (+ x1 x2))
                (<= (+ x1 x2) k2)
                (integerp k1)
                (integerp x1)
                (integerp x2)
                (integerp k2))
           (canonical-address-p (+ x1 x2 base))))

;gen!
(defthm acl2::bvsx-when-bvlt
  (implies (BVLT '32 x '4)
           (equal (BVSX '64 '32 x)
                  (bvchop 32 x)))
 :hints (("Goal" :in-theory (enable BVSX))))


(defthmd bvlt-hack-1
  (implies (not (bvlt 16 x 1))
           (equal (bvlt 16 x 2)
                  (equal (bvchop 16 x) 1)))
  :hints (("Goal" :in-theory (enable bvlt))))

;loops with boolif-of-bvlt-strengthen-to-equal?
(defthmd bvlt-hack-1-gen
  (implies (and (syntaxp (quotep k))
                (not (bvlt 16 x (+ -1 k)))
                (< k (expt 2 16))
                (posp k))
           (equal (bvlt 16 x k)
                  (equal (bvchop 16 x) (+ -1 k))))
  :hints (("Goal" :in-theory (enable bvlt
                                     acl2::bvchop-of-sum-cases))))

;; (defthm acl2::boolif-of-t-and-nil-when-booleanp
;;   (implies (booleanp x)
;;            (equal (acl2::boolif x t nil)
;;                   x)))

(defthm boolif-of-bvlt-strengthen-to-equal-gen
  (implies (and (syntaxp (quotep k))
                (not (bvlt 16 x (+ -1 k)))
                (< k (expt 2 16))
                (posp k))
           (equal (acl2::boolif (bvlt 16 x k) then else)
                  (acl2::boolif (equal (bvchop 16 x) (+ -1 k)) then else)))
  :hints (("Goal" :in-theory (enable acl2::boolor
                                     bvlt ;todo
                                     acl2::bvchop-of-sum-cases
                                     ACL2::BOOLIF
                                     ))))

(defthm boolif-of-bvlt-strengthen-to-equal
  (implies (and (syntaxp (quotep k))
                (not (bvlt 16 x (+ -1 k)))
                (< k (expt 2 16))
                (posp k))
           (equal (acl2::boolif (bvlt 16 x k) t else)
                  (acl2::boolif (equal (bvchop 16 x) (+ -1 k)) t else)))
  :hints (("Goal" :in-theory (enable acl2::boolor
                                     bvlt ;todo
                                     acl2::bvchop-of-sum-cases
                                     ))))


;; use polarities?
(defthm bvlt-reduce-when-not-equal-one-less
  (implies (and (syntaxp (quotep k))
                (not (equal (+ -1 k) (bvchop 16 x)))
                (< k (expt 2 16))
                (posp k))
           (equal (bvlt 16 x k)
                  (bvlt 16 x (+ -1 k))))
  :hints (("Goal" :in-theory (enable acl2::boolor
                                     bvlt ;todo
                                     acl2::bvchop-of-sum-cases
                                     ))))

;todo: gen, or change bvshl to always return a bv, or change the bvchop-identity rule to know about bvshl
(defthm bvchop-of-bvshl-same
  (implies (and (natp size)
                (< amt size)
                (natp amt))
           (equal (bvchop size (acl2::bvshl size x amt))
                  (acl2::bvshl size x amt)))
  :hints (("Goal" :in-theory (enable acl2::bvshl))))

(theory-invariant (incompatible (:rewrite bvcat-of-minus-becomes-bvshl)
                                (:definition acl2::bvshl )))


(defthm equal-of-bvshl-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)))
                (natp amt)
                (< amt 32))
           (equal (equal k (acl2::bvshl 32 k2 amt))
                  (and (unsigned-byte-p 32 k)
                       (equal 0 (bvchop amt k))
                       (equal (slice 31 amt k)
                              (bvchop (- 32 amt) k2)))))
  :hints (("Goal" :in-theory (e/d (acl2::bvshl)
                                  (;bvcat-of-minus-becomes-bvshl
                                   )))))

;; (defthm not-equal-of-0-and-bvshl-of-1
;;   (implies (and (natp amt)
;;                 (< amt 32))
;;            (not (equal 0 (acl2::bvshl 32 1 amt))))
;;   :hints (("Goal" :in-theory (e/d (acl2::bvshl)
;;                                   (bvcat-of-minus-becomes-bvshl)))))


;; Library stuff:

;; or commute the 1 forward first
;; or use the fact that 1 is a mask of all 1s
(defthm logand-of-1-arg2
  (equal (logand x 1)
         (getbit 0 x))
  :hints (("Goal" :cases ((integerp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;can loop with bvxor's def
(DEFTHM ACL2::LOGXOR-of-BVCHOP-becomes-bvxor-arg1
  (IMPLIES (AND (INTEGERP X)
                (natp ACL2::SIZE)
                (unsigned-byte-p ACL2::SIZE y))
           (EQUAL (LOGXOR (BVCHOP ACL2::SIZE X) y)
                  (BVXOR ACL2::SIZE X Y)))
  :HINTS (("Goal" :IN-THEORY (ENABLE BVXOR))))

; probably only needed for Axe
(defthmd integerp-of-logxor
  (integerp (logxor x y)))

;todo: generalize with a set of rules like the trim rules
;gen
(defthm bvplus-of-logxor-arg1
  (equal (bvplus 32 (logxor x y) z)
         (bvplus 32 (bvxor 32 x y) z))
  :hints (("Goal" :in-theory (enable bvxor))))

;todo: more like this
(defthm bvxor-of-logxor-arg2
  (equal (bvxor size x (logxor y z))
         (bvxor size x (bvxor size y z)))
  :hints (("Goal" :in-theory (enable bvxor))))

(DEFTHM ACL2::BVIF-OF---ARG3
  (IMPLIES (INTEGERP X)
           (EQUAL (BVIF ACL2::SIZE ACL2::TEST (- X) ACL2::Z)
                  (BVIF ACL2::SIZE ACL2::TEST (BVuminus ACL2::SIZE X) ACL2::Z)))
  :HINTS (("Goal" :IN-THEORY (ENABLE BVIF BVuminus bvminus))))

(DEFTHM ACL2::BVIF-OF---ARG4
  (IMPLIES (INTEGERP X)
           (EQUAL (BVIF ACL2::SIZE ACL2::TEST ACL2::Z (- X))
                  (BVIF ACL2::SIZE ACL2::TEST ACL2::Z (BVuminus ACL2::SIZE X))))
  :HINTS (("Goal" :IN-THEORY (ENABLE BVIF BVuminus bvminus))))

(DEFTHM ACL2::INTEGERP-OF---when-integerp
  (implies (INTEGERP X)
           (INTEGERP (- X)))
)

(defthm bvdiv-tighten-64-32 ;gen
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ACL2::BVDIV 64 x y)
                  (ACL2::BVDIV 32 x y)))
  :hints (("Goal" :in-theory (enable acl2::bvdiv))))

(defthm bvmod-tighten-64-32 ;gen
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ACL2::BVmod 64 x y)
                  (ACL2::BVmod 32 x y)))
  :hints (("Goal" :in-theory (enable acl2::bvmod))))

(defthm not-bvlt-of-max-when-unsiged-byte-p
  (implies (unsigned-byte-p 32 x)
           (not (bvlt 64 4294967295 x))))

;(in-theory (disable X86ISA::INTEGERP-WHEN-CANONICAL-ADDRESS-P-CHEAP)) ;todo

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;gen the sizes
(defthm bvuminus-of-bvif-constants
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)))
           (equal (bvuminus '32 (bvif '1 test k1 k2))
                  (bvif 32 test (bvuminus 32 (bvchop 1 k1)) (bvuminus 32 (bvchop 1 k2)))))
  :hints (("Goal" :in-theory (enable acl2::boolif))))

(defthm of-spec-of-logext-32
  (equal (of-spec32$inline (logext '32 x))
         0)
  :hints (("Goal" :in-theory (enable of-spec32))))

(defthm bvchop-of-logext-becomes-bvsx
  (implies (and (< size2 size)
                (natp size)
                (posp size2))
           (equal (bvchop size (logext size2 x))
                  (bvsx size size2 x)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvchop-of-zf-spec
  (implies (posp size)
           (equal (BVCHOP size (ZF-SPEC$INLINE result))
                  (ZF-SPEC$INLINE result))))

(defthm logext-of-zf-spec
  (implies (and (< 1 size)
                (integerp size))
           (equal (logext size (ZF-SPEC$INLINE result))
                  (ZF-SPEC$INLINE result))))

(defthm integerp-of-zf-spec
  (integerp (ZF-SPEC$INLINE result)))

(defthm SF-SPEC64-of-bvchop-64
  (equal (SF-SPEC64$INLINE (BVCHOP '64 x))
         (SF-SPEC64$INLINE x))
  :hints (("Goal" :in-theory (enable SF-SPEC64))))

(defthm of-spec64-of-logext-64
  (equal (of-spec64 (logext 64 x))
         0)
  :hints (("Goal" :in-theory (enable of-spec64))))


(acl2::def-constant-opener X86ISA::!PREFIXES->REP$inline)
(acl2::def-constant-opener X86ISA::PREFIXES->REP$INLINE)

(defthm ctri-of-xw-irrel
  (implies (not (equal :ctr fld))
           (equal (X86ISA::CTRI i (xw fld index val x86))
                  (X86ISA::CTRI i x86)))
  :hints (("Goal" :in-theory (enable X86ISA::CTRI))))

(defthm ctri-of-write
  (equal (X86ISA::CTRI i (write n base-addr val x86))
         (X86ISA::CTRI i x86))
  :hints (("Goal" :in-theory (enable X86ISA::CTRI))))

(defthm ctri-of-set-flag
  (equal (X86ISA::CTRI i (set-flag flag val x86))
         (X86ISA::CTRI i x86))
  :hints (("Goal" :in-theory (enable X86ISA::CTRI))))

(defthm X86ISA::FEATURE-FLAGS-opener
  (implies (consp features)
           (equal (X86ISA::FEATURE-FLAGS features)
                  (if (equal 0 (X86ISA::FEATURE-FLAG (FIRST FEATURES)))
                      0
                    (X86ISA::FEATURE-FLAGS (rest features)))))
  :hints (("Goal" :in-theory (enable X86ISA::FEATURE-FLAGS))))

(defthm X86ISA::FEATURE-FLAGS-base
  (implies (not (consp features))
           (equal (X86ISA::FEATURE-FLAGS features)
                  1))
  :hints (("Goal" :in-theory (enable X86ISA::FEATURE-FLAGS))))

;; probably only needed for axe
(defthmd integerp-of-ctri
  (integerp (x86isa::ctri acl2::i x86)))

(defthm cr0bits->ts-of-bvchop
  (implies (and (< 3 n)
                (integerp n))
           (equal (x86isa::cr0bits->ts (bvchop n x))
                  (x86isa::cr0bits->ts x)))
  :hints (("Goal" :in-theory (enable x86isa::cr0bits->ts
                                     x86isa::cr0bits-fix))))

(defthm cr0bits->em-of-bvchop
  (implies (and (< 2 n)
                (integerp n))
           (equal (x86isa::cr0bits->em (bvchop n x))
                  (x86isa::cr0bits->em x)))
  :hints (("Goal" :in-theory (enable x86isa::cr0bits->em
                                     x86isa::cr0bits-fix))))

(defthm cr4bits->OSFXSR-of-bvchop
  (implies (and (< 9 n)
                (integerp n))
           (equal (x86isa::cr4bits->OSFXSR (bvchop n x))
                  (x86isa::cr4bits->OSFXSR x)))
  :hints (("Goal" :in-theory (enable x86isa::cr4bits->OSFXSR
                                     x86isa::cr4bits-fix))))

(defthm integerp-of-PART-INSTALL-WIDTH-LOW$INLINE
  (integerp (BITOPS::PART-INSTALL-WIDTH-LOW$INLINE BITOPS::VAL X BITOPS::WIDTH BITOPS::LOW))
  )

(defthm 64-BIT-MODEP-of-if
  (equal (64-BIT-MODEP (if test x86_1 x86_2))
         (if test (64-BIT-MODEP x86_1)
           (64-BIT-MODEP x86_2))))

;; ;todo!
;; ;or use a defun-sk to state that all states have the same cpuid
;; (skip-proofs
;;  (defthm feature-flag-sse-of-xw
;;   (equal (x86isa::feature-flag ':sse (xw fld index val x86))
;;          (x86isa::feature-flag ':sse x86))
;;   :hints (("Goal" :in-theory (enable x86isa::ctri)))))

;; (skip-proofs
;;  (defthm feature-flag-sse-of-write
;;   (equal (x86isa::feature-flag ':sse (write n base-addr val x86))
;;          (x86isa::feature-flag ':sse x86))
;;   :hints (("Goal" :in-theory (enable x86isa::ctri)))))

;; (skip-proofs
;;  (defthm feature-flag-sse-of-set-flag
;;   (equal (x86isa::feature-flag ':sse (set-flag flag val x86))
;;          (x86isa::feature-flag ':sse x86))
;;   :hints (("Goal" :in-theory (enable x86isa::ctri)))))

;; (skip-proofs
;;  (defthm feature-flag-sse2-of-xw
;;   (equal (x86isa::feature-flag ':sse2 (xw fld index val x86))
;;          (x86isa::feature-flag ':sse2 x86))
;;   :hints (("Goal" :in-theory (enable x86isa::ctri)))))

;; (skip-proofs
;;  (defthm feature-flag-sse2-of-write
;;   (equal (x86isa::feature-flag ':sse2 (write n base-addr val x86))
;;          (x86isa::feature-flag ':sse2 x86))
;;   :hints (("Goal" :in-theory (enable x86isa::ctri)))))

;; (skip-proofs
;;  (defthm feature-flag-sse2-of-set-flag
;;   (equal (x86isa::feature-flag ':sse2 (set-flag flag val x86))
;;          (x86isa::feature-flag ':sse2 x86))
;;   :hints (("Goal" :in-theory (enable x86isa::ctri)))))

(in-theory (disable x86isa::sub-zf-spec32))

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

(defthm app-view-of-if
  (equal (app-view (if test x86 x86_2))
         (if test (app-view x86) (app-view x86_2))))

(defthm program-at-of-if
  (equal (program-at prog-addr bytes (if test x86 x86_2))
         (if test (program-at prog-addr bytes x86) (program-at prog-addr bytes x86_2))))

(defthm x86p-of-if
  (equal (x86p (if test x86 x86_2))
         (if test (x86p x86) (x86p x86_2))))

(defthm get-flag-of-if
  (equal (get-flag flag (if test x86 x86_2))
         (if test (get-flag flag x86) (get-flag flag x86_2))))

;todo: add ctri to x pkg
(defthm ctri-of-if
  (equal (x86isa::ctri i (if test x86 x86_2))
         (if test (x86isa::ctri i x86) (x86isa::ctri i x86_2))))

;; (defthm feature-flag-of-if
;;   (equal (x86isa::feature-flag flag (if test x86 x86_2))
;;          (if test (x86isa::feature-flag flag x86) (x86isa::feature-flag flag x86_2))))

(defthm ALIGNMENT-CHECKING-ENABLED-P-of-if
  (equal (ALIGNMENT-CHECKING-ENABLED-P (if test x86 x86_2))
         (if test (ALIGNMENT-CHECKING-ENABLED-P x86) (ALIGNMENT-CHECKING-ENABLED-P x86_2))))



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

(defthm ifix-of-if
  (equal (ifix (if test x86 x86_2))
         (if test (ifix x86) (ifix x86_2))))

(defthm integerp-of-xr-mxcsr
  (INTEGERP (XR :MXCSR NIL X86)))

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
(acl2::def-constant-opener X86ISA::!EVEX-PREFIXES->BYTE0$INLINE)

;; should not be needed
(defthm xr-of-!rflags-irrel
  (implies (not (equal fld :rflags))
           (equal (XR fld index (!RFLAGS v x86))
                  (XR fld index x86))))

(defthm !RFLAGS-of-if-arg1
  (equal (X86ISA::!RFLAGS (if test v1 v2) x86)
         (if test (X86ISA::!RFLAGS v1 x86) (X86ISA::!RFLAGS v2 x86))))

(defthm !RFLAGS-of-if-arg2
  (equal (X86ISA::!RFLAGS v (if test x86_1 x86_2))
         (if test (X86ISA::!RFLAGS v x86_1) (X86ISA::!RFLAGS v x86_2))))

(local (include-book "kestrel/arithmetic-light/ash" :dir :system))

(defthm <-of-fp-to-rat
  (implies (and (natp frac)
                (natp exp)
                (not (equal 0 exp))
                (natp frac-width)
                (equal 8 exp-width) ; todo: gen
                )
           (equal (< (X86ISA::FP-TO-RAT SIGN EXP frac BIAS EXP-WIDTH FRAC-WIDTH) 0)
                  (and (not (equal 0 sign))
                       (if (equal 0 exp)
                           (not (equal 0 FRAC))
                         (<= exp (x86isa::fp-max-finite-exp exp-width))))))
  :hints (("Goal" :in-theory (enable X86ISA::FP-TO-RAT))))

;; (thm
;;  (IMPLIES (AND (< J 0)
;;                (INTEGERP I)
;;                (INTEGERP J))
;;           (<= (- (/ i j)) (FLOOR I J))))

;; (thm
;;  (IMPLIES (AND (< J 0)
;;                (INTEGERP I)
;;                (posp k) ; gen?
;;                (< I k)
;;                (INTEGERP J))
;;           (<= (- k) (FLOOR I J))))

(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/top" :dir :system)) ; todo

;gen!
(defthm *-of-/-linear-when-both-negative-free-linear
  (implies (and (< free i)
                (integerp free)
                (< free 0)
                (<= j -1)
                (integerp i)
                (integerp j)
                (< i 0)
                )
           (< (* i (/ j)) (- free)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable acl2::<-of-*-of-/-arg1))))

;gen!
(defthm *-of-/-linear-when-i-negative-and-positive-linear
  (implies (and (< i free)
                (integerp free)
                (< free 0)
                (<= j -1)
                (integerp i)
                (integerp j)
                (<= 0 i))
           (< (- free) (* i (/ j))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable acl2::<-of-*-of-/-arg1))))

;(in-theory (disable X86ISA::<-WHEN-CANONICAL-ADDRESS-P-IMPOSSIBLE X86ISA::<-WHEN-CANONICAL-ADDRESS-P)) ;todo bad

(defthm acl2::logext-of-truncate
  (implies (and (signed-byte-p acl2::size acl2::i)
                (posp acl2::size)
                (integerp acl2::j))
           (equal (logext acl2::size (truncate acl2::i acl2::j))
                  (if (and (equal (- (expt 2 (+ -1 acl2::size)))
                                  acl2::i)
                           (equal -1 acl2::j))
                      (- (expt 2 (+ -1 acl2::size)))
                    (truncate acl2::i acl2::j)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: add versions for other sizes
(defthm mv-nth-1-of-idiv-spec-32
  (equal (mv-nth 1 (x86isa::idiv-spec-32 dst src))
         (let ((res (acl2::sbvdiv 64 dst (acl2::bvsx 64 32 src))))
           (if (sbvlt 64 res -2147483648)
               0
             (if (sbvlt 64 2147483647 res)
                 0
               (bvchop 32 res)))))
  :hints (("Goal" :in-theory (e/d (x86isa::idiv-spec-32 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

(defthm mv-nth-0-of-idiv-spec-32
  (equal (mv-nth 0 (x86isa::idiv-spec-32 dst src))
         (let ((res (acl2::sbvdiv 64 dst (acl2::bvsx 64 32 src))))
           (if (sbvlt 64 res -2147483648)
               (LIST (CONS 'X86ISA::QUOTIENT-INT
                           (TRUNCATE (LOGEXT 64 DST)
                                     (LOGEXT 32 SRC)))
                     (CONS 'X86ISA::REMAINDER-INT
                           (REM (LOGEXT 64 DST) (LOGEXT 32 SRC))))
             (if (sbvlt 64 2147483647 res)
                 (LIST (CONS 'X86ISA::QUOTIENT-INT
                             (TRUNCATE (LOGEXT 64 DST)
                                       (LOGEXT 32 SRC)))
                       (CONS 'X86ISA::REMAINDER-INT
                             (REM (LOGEXT 64 DST) (LOGEXT 32 SRC))))
               nil))))
  :hints (("Goal" :in-theory (e/d (x86isa::idiv-spec-32 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

;todo: add versions for other sizes
(defthm mv-nth-1-of-idiv-spec-64
  (equal (mv-nth 1 (x86isa::idiv-spec-64 dst src))
         (let ((res (acl2::sbvdiv 128 dst (acl2::bvsx 128 64 src))))
           (if (sbvlt 128 res (- (expt 2 63)))
               0
             (if (sbvlt 128 (+ -1 (expt 2 63)) res)
                 0
               (bvchop 64 res)))))
  :hints (("Goal" :in-theory (e/d (x86isa::idiv-spec-64 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

(defthm mv-nth-0-of-idiv-spec-64
  (equal (mv-nth 0 (x86isa::idiv-spec-64 dst src))
         (let ((res (acl2::sbvdiv 128 dst (acl2::bvsx 128 64 src))))
           (if (sbvlt 128 res (- (expt 2 63)))
               (LIST (CONS 'X86ISA::QUOTIENT-INT
                           (TRUNCATE (LOGEXT 128 DST)
                                     (LOGEXT 64 SRC)))
                     (CONS 'X86ISA::REMAINDER-INT
                           (REM (LOGEXT 128 DST) (LOGEXT 64 SRC))))
             (if (sbvlt 128 (+ -1 (expt 2 63)) res)
                 (LIST (CONS 'X86ISA::QUOTIENT-INT
                             (TRUNCATE (LOGEXT 128 DST)
                                       (LOGEXT 64 SRC)))
                       (CONS 'X86ISA::REMAINDER-INT
                             (REM (LOGEXT 128 DST) (LOGEXT 64 SRC))))
               nil))))
  :hints (("Goal" :in-theory (e/d (x86isa::idiv-spec-64 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

(DEFthm x86isa::X86-CWD/CDQ/CQO-alt-def
  (equal (x86isa::X86-CWD/CDQ/CQO PROC-MODE START-RIP TEMP-RIP PREFIXES REX-BYTE OPCODE MODR/M SIB x86)
         (B* ((?CTX 'X86-CWD/CDQ/CQO))
           (B* (((THE (INTEGER 1 8) SRC-SIZE)
                 (x86isa::SELECT-OPERAND-SIZE
                  PROC-MODE NIL
                  REX-BYTE NIL PREFIXES NIL NIL NIL X86))
                (SRC (x86isa::RGFI-SIZE SRC-SIZE *RAX* REX-BYTE X86))
                ;; rdx gets the high part of the sign-extension
                ;; avoids a case split and supports putting the parts back together (e.g., to do a divide):
                (RDX (slice (+ -1 (* 16 src-size))
                            (* 8 src-size)
                            (bvsx (* 16 src-size) (* 8 src-size) src)))
                (X86 (x86isa::!RGFI-SIZE SRC-SIZE *RDX* RDX REX-BYTE X86))
                (X86 (x86isa::WRITE-*IP PROC-MODE TEMP-RIP X86)))
             X86)))
  :hints (("Goal" :in-theory (enable x86isa::X86-CWD/CDQ/CQO))))

;; Shows that the division can't be too negative
;todo: add sbvdiv to x pkg
;todo: gen the 2
(defthm not-sbvlt-64-of-sbvdiv-64-of-bvsx-64-32-and--2147483648
  (not (sbvlt 64 (acl2::sbvdiv 64 (bvsx 64 32 x) 2) -2147483648))
  :hints (("Goal" :cases ((equal 0 (getbit 31 x)))
           :in-theory (e/d (sbvlt acl2::sbvdiv bvsx bvlt acl2::logext-cases bvcat logapp
                                  acl2::truncate-becomes-floor-gen
                                  acl2::getbit-of-plus
                                  bvplus
                                  acl2::bvchop-of-sum-cases)
                           (acl2::sbvlt-rewrite ;disable
                            )))))

;; Shows that the division can't be too positive
;; todo: gen the 2 but watch for the one weird case
(defthm not-sbvlt-64-of-2147483647-and-sbvdiv-64-of-bvsx-64-32
  (not (sbvlt 64 2147483647 (acl2::sbvdiv 64 (bvsx 64 32 x) 2) ))
  :hints (("Goal" :cases ((equal 0 (getbit 31 x)))
           :in-theory (e/d (sbvlt acl2::sbvdiv bvsx bvlt acl2::logext-cases bvcat logapp
                                  acl2::truncate-becomes-floor-gen
                                  acl2::getbit-of-plus
                                  bvplus
                                  acl2::bvchop-of-sum-cases)
                           (acl2::sbvlt-rewrite ;disable
                            )))))

;; todo: recharacterize the x86 shift instruction so we don't need rules to put in the shifts
(defthm bvcat-of-minus-becomes-bvshl
  (implies (and (natp amt)
                (< amt 32))
           (equal (bvcat (+ 32 (- amt)) val amt 0)
                  (acl2::bvshl 32 val amt)))
  :hints (("Goal" :in-theory (enable acl2::bvshl))))

(defthm X86ISA::RFLAGSBITS->PF-of-if
  (equal (X86ISA::RFLAGSBITS->PF (if test x1 x2))
         (if test (X86ISA::RFLAGSBITS->PF x1) (X86ISA::RFLAGSBITS->PF x2))))

(defthm X86ISA::RFLAGSBITS->CF-of-if
  (equal (X86ISA::RFLAGSBITS->CF (if test x1 x2))
         (if test (X86ISA::RFLAGSBITS->CF x1) (X86ISA::RFLAGSBITS->cF x2))))

(defthm X86ISA::RFLAGSBITS->OF-of-if
  (equal (X86ISA::RFLAGSBITS->OF (if test x1 x2))
         (if test (X86ISA::RFLAGSBITS->OF x1) (X86ISA::RFLAGSBITS->of x2))))

(defthm X86ISA::RFLAGSBITS->SF-of-if
  (equal (X86ISA::RFLAGSBITS->SF (if test x1 x2))
         (if test (X86ISA::RFLAGSBITS->SF x1) (X86ISA::RFLAGSBITS->sf x2))))

(defthm X86ISA::RFLAGSBITS->ZF-of-if
  (equal (X86ISA::RFLAGSBITS->ZF (if test x1 x2))
         (if test (X86ISA::RFLAGSBITS->ZF x1) (X86ISA::RFLAGSBITS->zf x2))))

;; since we can get better context info from boolif than from boolor?
(defthmd boolor-becomes-boolif
  (equal (acl2::boolor x y)
         (acl2::boolif x t y)))

(theory-invariant (incompatible (:rewrite ACL2::BOOLIF-WHEN-QUOTEP-ARG2) (:rewrite boolor-becomes-boolif)))

(defthm acl2::bvchop-subst-constant-alt
  (implies (and (syntaxp (not (quotep x)))
                (equal (bvchop free x) k) ; this rule
                (syntaxp (quotep k))
                (<= size free)
                ;(natp size)
                (integerp free))
           (equal (bvchop size x)
                  (bvchop size k)))
  :hints (("Goal" :use (:instance acl2::bvchop-subst-constant (acl2::free free) (acl2::size size))
           :in-theory (disable acl2::bvchop-subst-constant))))

;gen
(defthm bvcat-of-repeatbit-of-getbit-of-bvsx-same
  (implies (and (equal oldsize-1 (+ oldsize -1))
                (posp oldsize)
                (natp newsize)
                (< oldsize newsize)
                (posp size2) ; gen?
                )
           (equal (BVCAT size2 (REPEATBIT size2 (GETBIT oldsize-1 x)) newsize (BVSX newsize oldsize x))
                  (bvsx (+ size2 newsize) oldsize x))))

(defthmd bvcat-of-repeatbit-of-getbit-becomes-bvsx
  (implies (and (equal n (+ -1 lowsize))
                (posp lowsize)
                (natp highsize))
           (equal (bvcat highsize (repeatbit highsize (getbit n x)) lowsize x)
                  (bvsx (+ highsize lowsize) lowsize x)))
  :hints (("Goal" :in-theory (enable acl2::bvsx-alt-def-2
                                     acl2::repeatbit-of-1-arg2))))

(defthm not-sbvlt-of-bvsx-of-constant-arg2-64-8
  (implies (and (syntaxp (quotep k))
                (sbvle 64 k -128))
           (not (sbvlt 64 (bvsx 64 8 x) k)))
  :hints (("Goal" :in-theory (enable acl2::bvsx-alt-def-2 acl2::booland bvlt acl2::equal-of-slice))))

(defthm not-sbvlt-of-bvsx-of-constant-arg2-64-16
  (implies (and (syntaxp (quotep k))
                (sbvle 64 k (- (expt 2 (+ -1 16)))))
           (not (sbvlt 64 (bvsx 64 16 x) k)))
  :hints (("Goal" :in-theory (enable acl2::bvsx-alt-def-2 acl2::booland bvlt acl2::equal-of-slice))))

(defthm not-sbvlt-of-bvsx-of-constant-arg2-64-32
  (implies (and (syntaxp (quotep k))
                (sbvle 64 k (- (expt 2 (+ -1 32)))))
           (not (sbvlt 64 (bvsx 64 32 x) k)))
  :hints (("Goal" :in-theory (enable acl2::bvsx-alt-def-2 acl2::booland bvlt acl2::equal-of-slice))))

(defthm not-sbvlt-of-bvsx-of-constant-arg2-128-64
  (implies (and (syntaxp (quotep k))
                (sbvle 128 k (- (expt 2 (+ -1 64)))))
           (not (sbvlt 128 (bvsx 128 64 x) k)))
  :hints (("Goal" :in-theory (enable acl2::bvsx-alt-def-2 acl2::booland bvlt acl2::equal-of-slice))))

;; (defthm not-sbvlt-of-bvsx-of-constant-arg2-64
;;   (implies (and (syntaxp (quotep k))
;;                 (posp size)
;; ;                (equal size 8)
;;                 (< size 64)
;;                 (sbvle 64 k (- (expt 2 (+ -1 size)))))
;;            (not (sbvlt 64 (bvsx 64 size x) k)))
;;   :hints (("Goal" :cases ((EQUAL (GETBIT (+ -1 SIZE) k) 1))
;;            :in-theory (e/d (acl2::bvsx-alt-def-2 acl2::booland bvlt acl2::equal-of-slice)
;;                                   (acl2::exponents-add)))))

;gen!
(defthm not-sbvlt-of-bvsx-of-constant-arg3-64-8
  (implies (and (syntaxp (quotep k))
                (sbvle 64 (+ -1 128) k))
           (not (sbvlt 64 k (bvsx 64 8 x))))
  :hints (("Goal" :in-theory (enable acl2::bvsx-alt-def-2 acl2::booland bvlt acl2::equal-of-slice))))

(defthm not-sbvlt-of-bvsx-of-constant-arg3-64-16
  (implies (and (syntaxp (quotep k))
                (sbvle 64 (+ -1 (expt 2 (+ -1 16))) k))
           (not (sbvlt 64 k (bvsx 64 16 x))))
  :hints (("Goal" :in-theory (enable acl2::bvsx-alt-def-2 acl2::booland bvlt acl2::equal-of-slice))))

(defthm not-sbvlt-of-bvsx-of-constant-arg3-64-32
  (implies (and (syntaxp (quotep k))
                (sbvle 64 (+ -1 (expt 2 (+ -1 32))) k))
           (not (sbvlt 64 k (bvsx 64 32 x))))
  :hints (("Goal" :in-theory (enable acl2::bvsx-alt-def-2 acl2::booland bvlt acl2::equal-of-slice))))

(defthm not-sbvlt-of-bvsx-of-constant-arg3-128-64
  (implies (and (syntaxp (quotep k))
                (sbvle 128 (+ -1 (expt 2 (+ -1 64))) k))
           (not (sbvlt 128 k (bvsx 128 64 x))))
  :hints (("Goal" :in-theory (enable acl2::bvsx-alt-def-2 acl2::booland bvlt acl2::equal-of-slice))))

(defthm bvcat-of-repeatit-tighten-64-32 ;gen!
  (equal (bvcat 64 (repeatbit 32 bit) 32 lowval)
         (bvcat 32 (repeatbit 32 bit) 32 lowval)))

(defthm sbvlt-of-bvsx-32-16-constant
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 15 k) ;gen?
                )
           (equal (sbvlt 32 k (bvsx 32 16 x))
                  (and (sbvlt 16 k x)
                       (not (sbvlt 16 x 0)))))
  :hints (("Goal" :in-theory (enable bvlt ACL2::BVSX-ALT-DEF-2))))

;; todo: constant opener for X86ISA::!RFLAGSBITS->AF$INLINE

;todo: gen the 0
(defthm if-of-sbvlt-and-not-sbvlt-helper
  (implies (and (posp size)
                (sbvle size 0 k) ; gen?
                )
           (equal (if (sbvlt size k x)
                      (not (sbvlt size x 0))
                    else)
                  (if (sbvlt size k x)
                      t
                    else)))
  :hints (("Goal" :in-theory (disable))))

(defthm if-of-set-flag-and-set-flag
  (equal (if test (set-flag flag val1 x86) (set-flag flag val2 x86))
         (set-flag flag (if test val1 val2) x86)))

;todo: why is !rflags remaining in some examples like test_popcount_32_one_bit?


(defthm boolif-same-arg1-arg2
  (implies (syntaxp (not (quotep x))) ; avoids loop when x='t, this hyp is supported by Axe
           (equal (acl2::boolif x x y)
                  (acl2::boolif x t y))))

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

;; arises in array indexing -- try without this
(defthm logext-of-+-of-bvplus-same-size
  (implies (and (integerp k)
                (integerp text-offset)
                (integerp index))
           (equal (logext '64 (binary-+ k (bvplus '64 text-offset index)))
                  (logext '64 (binary-+ k (+ text-offset index)))))
  :hints (("Goal" :in-theory (enable acl2::equal-of-logext-and-logext))))

;slow!
;; arises in array indexing -- try without this
(defthm logext-of-+-of-+-of-mult-same-size ; alt versions?
  (implies (and (integerp k)
                (integerp text-offset)
                (integerp index)
                (integerp val))
           (equal (logext '64 (+ k (+ (bvmult 64 val index) text-offset)))
                  (logext '64 (+ k (+ (* val index) text-offset)))))
  :hints (("Goal" :in-theory (e/d (acl2::equal-of-logext-and-logext bvmult)
                                  (ACL2::SLICE-OF-* ;looped
                                   acl2::getbit-of-* ; looped
                                   ;X86ISA::LOGEXT-64-DOES-NOTHING-WHEN-CANONICAL-ADDRESS-P
                                   ;BVCHOP-TIGHTEN-WHEN-UNSIGNED-BYTE-P
                                   ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS
                                   )))))

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

(defthm BV-ARRAY-READ-of-*-arg3
  (implies (and (syntaxp (quotep len))
                (natp len)
                (integerp i1)
                (integerp i2)
                )
           (equal (acl2::BV-ARRAY-READ ELEMENT-SIZE LEN (* i1 i2) DATA)
                  (acl2::BV-ARRAY-READ ELEMENT-SIZE LEN (bvmult (acl2::CEILING-OF-LG LEN) i1 i2) DATA)))
  :hints (("Goal" :in-theory (e/d (acl2::BV-ARRAY-READ bvmult)
                                  (ACL2::GETBIT-OF-NTH-BECOMES-BV-ARRAY-READ
                                   ACL2::BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ)))))

(defthm BV-ARRAY-READ-of-+-arg3
  (implies (and (syntaxp (quotep len))
                (natp len)
                (integerp i1)
                (integerp i2)
                )
           (equal (acl2::BV-ARRAY-READ ELEMENT-SIZE LEN (+ i1 i2) DATA)
                  (acl2::BV-ARRAY-READ ELEMENT-SIZE LEN (bvplus (acl2::CEILING-OF-LG LEN) i1 i2) DATA)))
  :hints (("Goal" :in-theory (e/d (acl2::BV-ARRAY-READ bvplus)
                                  (ACL2::GETBIT-OF-NTH-BECOMES-BV-ARRAY-READ
                                   ACL2::BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ)))))

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
  (implies (and (separate :r text-offset-k text-offset :r rsp-k (+ neg-rsp-k (rsp x86))) ; example: (separate ':r '150 text-offset ':r '80 (binary-+ '-80 (rsp x86)))
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
  (implies (and (separate :r text-offset-k (+ k1 text-offset) :r rsp-k (+ neg-rsp-k (rsp x86))) ; example: (SEPARATE ':R '512 (BINARY-+ '224 TEXT-OFFSET) ':R '80 (BINARY-+ '-80 (RSP X86)))
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
  (implies (and (separate :r text-offset-k (+ k3 text-offset) :r rsp-k (+ neg-rsp-k (rsp x86))) ; example: (SEPARATE ':R '512 (BINARY-+ '224 TEXT-OFFSET) ':R '80 (BINARY-+ '-80 (RSP X86)))
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

(defthm separate-of-1-and-1
  (implies (and (integerp ad1)
                (integerp ad2))
           (equal (SEPARATE :R 1 ad1 :R 1 ad2)
                  (not (equal ad1 ad2))))
  :hints (("Goal" :in-theory (enable separate))))

(defthm <-of-+-and-+-arg3-and-arg1
  (equal (< (+ x (+ y z)) z)
         (< (+ x y) 0)))

(defthm write-of-write-byte-included
  (implies (and ;; ad2 is in the interval [ad1,ad1+n):
            (< (bvminus 48 ad2 ad1) n)
            (integerp ad1)
            (integerp ad2)
            (natp n))
           (equal (write n ad1 val (write-byte ad2 byte x86))
                  (write n ad1 val x86)))
  :hints (("Goal" :in-theory (enable write
                                     acl2::bvchop-of-sum-cases
                                     bvminus))))

(defthm write-of-write-byte-not-included
  (implies (and ;; ad2 is NOT in the interval [ad1,ad1+n):
            (not (< (bvminus 48 ad2 ad1) n))
            (integerp ad1)
            (integerp ad2)
            (natp n))
           (equal (write n ad1 val (write-byte ad2 byte x86))
                  (write-byte ad2 byte (write n ad1 val x86))))
  :hints (("Goal" :in-theory (enable write
                                     acl2::bvchop-of-sum-cases
                                     bvminus))))

(defthm write-of-write-byte
  (implies (and (integerp ad1)
                (integerp ad2)
                (natp n))
           (equal (write n ad1 val (write-byte ad2 byte x86))
                  (if (< (bvminus 48 ad2 ad1) n)
                      ;; ad2 is in the interval [ad,ad+n).
                      (write n ad1 val x86)
                    (write-byte ad2 byte (write n ad1 val x86))))))

;todo: gen
(defthm write-of-write-of-write-same
  (implies (and (integerp addr)
                (integerp addr2)
                (natp n)
                (natp n2)
                (unsigned-byte-p 48 n) ; drop? but first change the write-of-write-same
                )
           (equal (write n addr val3 (write n2 addr2 val2 (write n addr val1 x86)))
                  (write n addr val3 (write n2 addr2 val2 x86))))
  :hints (("Goal" :expand (write n2 addr2 val2 (write n addr val1 x86))
           :in-theory (enable write)
           :do-not '(generalize eliminate-destructors)
           :induct (write n2 addr2 val2 x86))))

;todo: gen
(defthm write-of-write-of-write-of-write-same
  (implies (and (integerp addr)
                (integerp addr2)
                (integerp addr3)
                (natp n)
                (natp n2)
                (natp n3)
                (unsigned-byte-p 48 n) ; drop? but first change the write-of-write-same
                )
           (equal (write n addr val4 (write n3 addr3 val3 (write n2 addr2 val2 (write n addr val1 x86))))
                  (write n addr val4 (write n3 addr3 val3 (write n2 addr2 val2 x86)))))
  :hints (("Goal" :use ((:instance write-of-write-of-write-same
                                   (val3 val4)
                                   (n2 n3)
                                   (addr2 addr3)
                                   (val2 val3)
                                   (val1 val4)
                                   (x86 (write n2 addr2 val2 (write n addr val1 x86))))
                        (:instance write-of-write-of-write-same
                                   (val3 val4)
                                   (n2 n3)
                                   (addr2 addr3)
                                   (val2 val3)
                                   (val1 val4)
                                   (x86 (write n2 addr2 val2 x86)))
                        (:instance write-of-write-of-write-same
                                   (val3 val4)))
           :in-theory (disable write-of-write-of-write-same write))))

;; ;; write of write, with 3 intervening writes
;; ;todo: gen
;; (defthm write-of-write-of-write-of-write-of-write-same
;;   (implies (and (integerp addr)
;;                 (integerp addr2)
;;                 (integerp addr3)
;;                 (integerp addr4)
;;                 (natp n)
;;                 (natp n2)
;;                 (natp n3)
;;                 (natp n4)
;;                 (unsigned-byte-p 48 n) ; drop? but first change the write-of-write-same
;;                 )
;;            (equal (write n addr val5 (write n4 addr4 val4 (write n3 addr3 val3 (write n2 addr2 val2 (write n addr val1 x86)))))
;;                   (write n addr val5 (write n4 addr4 val4 (write n3 addr3 val3 (write n2 addr2 val2 x86))))))
;;   :hints (("Goal" :use ((:instance write-of-write-of-write-same
;;                                    (val3 val4)
;;                                    (n2 n3)
;;                                    (addr2 addr3)
;;                                    (val2 val3)
;;                                    (val1 val4)
;;                                    (x86 (write n2 addr2 val2 (write n addr val1 x86))))
;;                         (:instance write-of-write-of-write-same
;;                                    (val3 val4)
;;                                    (n2 n3)
;;                                    (addr2 addr3)
;;                                    (val2 val3)
;;                                    (val1 val4)
;;                                    (x86 (write n2 addr2 val2 x86)))
;;                         (:instance write-of-write-of-write-same
;;                                    (val3 val4)))
;;            :in-theory (disable write-of-write-of-write-same write))))

(defthm bvminus-of-+-of-1-same
  (implies (integerp x)
           (equal (bvminus size x (+ 1 x))
                  (bvchop size -1)))
  :hints (("Goal" :in-theory (enable bvminus))))

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
;;  (implies (and (signed-byte-p 48 x)
;;                (signed-byte-p 48 y))
;;           (equal (equal (bvchop 48 x) (bvchop 48 y))
;;                  (equal x y)))
;;  :hints (("Goal" :in-theory (enable ))))

;; for when we have to disable the executable-counterpart
(defthm expt-of-2-and-48
  (equal (expt 2 48)
         281474976710656))

(defthm equal-of-constant-and-bvchop-when-signed-byte-p
  (implies (and (syntaxp (quotep k))
                (signed-byte-p size x))
           (equal (equal k (bvchop size x))
                  (and (unsigned-byte-p size k)
                       (equal (logext size k) x))))
  :hints (("Goal" :in-theory (enable signed-byte-p)
           :use (:instance acl2::logext-of-bvchop-same
                           (acl2::size size)))))

(defthmd equal-of-bvchop-when-signed-byte-p
  (implies (and ;; (syntaxp (quotep k))
                (signed-byte-p size x))
           (equal (equal k (bvchop size x))
                  (and (unsigned-byte-p size k)
                       (equal (logext size k) x))))
  :hints (("Goal" :in-theory (enable signed-byte-p)
           :use (:instance acl2::logext-of-bvchop-same
                                  (acl2::size size)))))


(defthm bvchop-when-signed-byte-p-and-<-of-0
  (implies (and (signed-byte-p 48 x)
                (< x 0))
           (equal (bvchop 48 x)
                  (+ x (expt 2 48))))
  :hints (("Goal" :in-theory (enable equal-of-bvchop-when-signed-byte-p))))

;; Pretty aggressive
(defthmd bvchop-when-signed-byte-p-cases-cheap
  (implies (signed-byte-p 48 x)
           (equal (bvchop 48 x)
                  (if (< x 0)
                      (+ x (expt 2 48))
                    x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable equal-of-bvchop-when-signed-byte-p))))

(defthm <-of-bvchop-and-bvchop-when->=-and-signed-byte-p-and-signed-byte-p
  (implies (and (<= x y)
                (signed-byte-p 48 x)
                (signed-byte-p 48 y))
           (equal (< (bvchop 48 y) (bvchop 48 x))
                  (and (< x 0)
                       (and (<= 0 y)
                            (< y (expt 2 47))))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil))))

;; restrict to constant k?
(defthm signed-byte-p-of-+-forward
  (implies (signed-byte-p 48 (+ k x))
           (and (< x (- (expt 2 47) k))
                (<= (+ (- (expt 2 47)) (- k)) x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable signed-byte-p))))

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


;move
;; todo: gen the 1?
(defthm read-of-write-included-1
  (implies (and (bvlt 48 (bvminus 48 addr1 addr2) n)
                (integerp addr1)
                (integerp addr2)
                (unsigned-byte-p 48 n))
           (equal (read 1 addr1 (write n addr2 val x86))
                  (slice (+ 7 (* 8 (bvminus 48 addr1 addr2)))
                         (* 8 (bvminus 48 addr1 addr2))
                         val)))
  :hints (("Goal" :induct (write n addr2 val x86)
           :in-theory (enable read write bvminus bvlt acl2::bvchop-of-sum-cases))))

;; todo: gen the 1?
(defthm read-of-write-1-both
  (implies (and (integerp addr1)
                (integerp addr2)
                (natp n)
                (unsigned-byte-p 48 n))
           (equal (read 1 addr1 (write n addr2 val x86))
                  (if (bvlt 48 (bvminus 48 addr1 addr2) n)
                      (slice (+ 7 (* 8 (bvminus 48 addr1 addr2)))
                             (* 8 (bvminus 48 addr1 addr2))
                             val)
                    (read 1 addr1 x86))))
  :hints (("Goal" :in-theory (disable read write))))

(defthmd bvminus-of-+-arg2
  (implies (and (integerp x1)
                (integerp x2))
           (equal (bvminus size (+ x1 x2) y)
                  (bvminus size (bvplus size x1 x2) y)))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

(defthmd bvminus-of-+-arg3
  (implies (and (integerp y1)
                (integerp y2))
           (equal (bvminus size x (+ y1 y2))
                  (bvminus size x (bvplus size y1 y2))))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

(defthm acl2::bvminus-of-bvplus-and-bvplus-same-2-2
  (equal (bvminus '48 (bvplus '48 y1 x) (bvplus '48 y2 x))
         (bvminus '48 y1 y2)))


;; usually negoffset, n1, n2, and minusn2 are constants
(defthm not-equal-of-+-when-separate
  (implies (and (separate :r n1 text-offset ':r n2 (binary-+ minusn2 (rsp x86)))
                (posp n2)
                (integerp negoffset)
                (< negoffset 0)
                (<= (- negoffset) n2)
                (equal minusn2 (- n2))
                (posp n1))
           (not (equal text-offset (+ negoffset (rsp x86)))))
  :hints (("Goal" :in-theory (enable separate))))

(defthm not-equal-of-+-when-separate-alt
  (implies (and (separate :r n1 text-offset ':r n2 (binary-+ minusn2 (rsp x86)))
                (posp n2)
                (integerp negoffset)
                (< negoffset 0)
                (<= (- negoffset) n2)
                (equal minusn2 (- n2))
                (posp n1))
           (not (equal (+ negoffset (rsp x86)) text-offset)))
  :hints (("Goal" :in-theory (enable separate))))

(defthm slice-of-bvand-of-constant
  (implies (and (syntaxp (and (quotep x)
                              (quotep high)
                              (quotep low)))
                (<= low high)
                (<= (+ 1 high) size) ;drop?
                (natp size)
                (natp low)
                (natp high))
           (equal (slice high low (bvand size x y))
                  (bvand size
                         (slice high low x) ; gets computed
                         (slice high low y))))
  :hints (("Goal" :in-theory (e/d (bvand)
                                  (acl2::logand-of-bvchop-becomes-bvand-alt ;loop
                                   acl2::logand-of-bvchop-becomes-bvand ;loop
                                   )))))

;;todo: or use a trim-like scheme for stuff like this
(defthm bvand-of-lognot-arg2
  (equal (bvand size (lognot x) y)
         (bvand size (bvnot size x) y))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm bvand-of-lognot-arg3
  (equal (bvand size x (lognot y))
         (bvand size x (bvnot size y)))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm bvxor-of-lognot-arg2
  (equal (bvxor size (lognot x) y)
         (bvxor size (bvnot size x) y))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm bvxor-of-lognot-arg3
  (equal (bvxor size x (lognot y))
         (bvxor size x (bvnot size y)))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm acl2::bvchop-of-lognot
  (equal (bvchop size (lognot x))
         (bvnot size x))
  :hints (("Goal" :in-theory (enable bvnot))))

(def-constant-opener x86isa::!prefixes->seg$inline)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvif-of-if-constants-nil-nonnil
  (implies (and (syntaxp (quotep k))
                (not (equal nil k)))
           (equal (bvif size (if test nil k) tp ep)
                  (bvif size (not test) tp ep))))

(defthm bvif-of-if-constants-nonnil-nil
  (implies (and (syntaxp (quotep k))
                (not (equal nil k)))
           (equal (bvif size (if test k nil) tp ep)
                  (bvif size test tp ep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognize a NaN
(defund is-nan (val)
  (IF
   (EQUAL 'X86ISA::SNAN val)
   'T
   (IF
    (EQUAL 'X86ISA::QNAN val)
    'T
    ;; a special type of QNAN:
    (EQUAL 'X86ISA::INDEF val))))

(defthmd booleanp-of-is-nan
  (booleanp (is-nan val)))

(defthmd is-nan-intro
  (equal (IF
          (EQUAL 'X86ISA::SNAN val)
          'T
          (IF
           (EQUAL 'X86ISA::QNAN val)
           'T
           (EQUAL 'X86ISA::INDEF val)))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

(theory-invariant (incompatible (:rewrite is-nan-intro) (:definition is-nan)))

(defthm if-of-equal-of-indef-and-is-nan
  (equal (IF
          (EQUAL 'X86ISA::INDEF val)
          'T
          (IS-NAN val))
         (IS-NAN val))
  :hints (("Goal" :in-theory (enable is-nan))))

(defthm if-of-equal-of-qnan-and-is-nan
  (equal (IF
          (EQUAL 'X86ISA::QNAN val)
          'T
          (IS-NAN val))
         (IS-NAN val))
  :hints (("Goal" :in-theory (enable is-nan))))

(defthm if-of-equal-of-snan-and-is-nan
  (equal (IF
          (EQUAL 'X86ISA::SNAN val)
          'T
          (IS-NAN val))
         (IS-NAN val))
  :hints (("Goal" :in-theory (enable is-nan))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm boolif-of-boolif-of-t-and-nil
  (equal (boolif (boolif x t y) x nil)
         (acl2::bool-fix x)))

;; This reduces one mention of X and only increases the mentions of nil
(defthm boolif-combine-1
  (equal (boolif (boolif x z1 z2) (boolif x z3 z4) nil)
         (boolif x
                 (boolif z1 z3 nil)
                 (boolif z2 z4 nil)))
  :hints (("Goal" :in-theory (enable boolif))))

;todo: drop
(defthm bvchop-of-bool-to-bit
  (implies (posp n)
           (equal (bvchop n (bool-to-bit bool))
                  (bool-to-bit bool))))

;todo: drop?
(defthm logext-of-bool-to-bit
  (implies (and (< 1 n)
                (integerp n))
           (equal (logext n (bool-to-bit bool))
                  (bool-to-bit bool))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm equal-of-bvif-safe2 ; todo: replace the other
  (implies (syntaxp (and (quotep x)
                         ;; ;;could drop this one?:
                         ;; (or (quotep a)
                         ;;     (quotep b))
                         (quotep size)))
           (equal (equal x (bvif size test a b))
                  ;one of the branches here will be computed
                  (boolif test
                          (equal x (bvchop size a))
                          (equal x (bvchop size b)))))
    :hints (("Goal" :in-theory (enable bvif))))
