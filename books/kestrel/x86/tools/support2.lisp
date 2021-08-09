; More supporting material for x86 reasoning
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;todo: move this material to libraries

(include-book "read-and-write")
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv-lists/unpackbv" :dir :system)
(include-book "kestrel/lists-light/finalcdr" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(local (include-book "kestrel/bv/arith" :dir :system))
(local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system)) ;prevent calls of expt on huge args
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;todo

(local (in-theory (enable acl2::expt-becomes-expt-limited
                          acl2::car-becomes-nth-of-0)))

(local (in-theory (disable (:e expt)
                           ;; for speed:
                           ;ACL2::BVCHOP-IDENTITY
                           ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS
                           )))

;todo: dup
(defthm segment-base-and-bounds-of-set-flag
  (equal (segment-base-and-bounds proc-mode seg-reg (x::set-flag flg val x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (e/d (segment-base-and-bounds
                                   x::set-flag)
                                  (;; x86isa::seg-hidden-basei-is-n64p
                                   ;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-attri-is-n16p
                                   )))))

(defthm mv-nth-0-of-ia32e-la-to-pa-of-set-flag
  (implies (and ;(not (equal :ac flag))
            (app-view x86))
           (equal (mv-nth 0 (x86isa::ia32e-la-to-pa lin-addr r-w-x (set-flag flag val x86)))
                  (mv-nth 0 (x86isa::ia32e-la-to-pa lin-addr r-w-x x86))))
  :hints (("Goal" :in-theory (enable x86isa::ia32e-la-to-pa
                                     set-flag
                                     x86isa::rflagsbits->ac
                                     ))))

(defthm mv-nth-2-of-ia32e-la-to-pa-of-set-flag
  (implies (and ;(not (equal :ac flag))
            (app-view x86)
            (not (mv-nth 0 (x86isa::ia32e-la-to-pa lin-addr r-w-x (set-flag flag val x86)))))
           (equal (mv-nth 2 (x86isa::ia32e-la-to-pa lin-addr r-w-x (set-flag flag val x86)))
                  (set-flag flag val (mv-nth 0 (x86isa::ia32e-la-to-pa lin-addr r-w-x x86)))))
  :hints (("Goal" :in-theory (enable x86isa::ia32e-la-to-pa
                                     set-flag
                                     x86isa::rflagsbits->ac
                                     ))))

(defthm app-view-of-mv-nth-2-of-ia32e-la-to-pa
  (implies (app-view x86)
           (app-view (mv-nth 2 (x86isa::ia32e-la-to-pa lin-addr r-w-x x86))))
  :hints (("Goal" :in-theory (enable x86isa::ia32e-la-to-pa))))

;; zz
;; (defthm mv-nth-0-of-las-to-pas-of-set-flag
;;   (implies (and (app-view x86)
;; ;                (not (mv-nth 0 (x86isa::las-to-pas n lin-addr r-w-x x86)))
;;                 )
;;            (equal (mv-nth 0 (x86isa::las-to-pas n lin-addr r-w-x (set-flag flag val x86)))
;;                   (mv-nth 0 (x86isa::las-to-pas n lin-addr r-w-x x86))))
;;   :hints (("Goal" :in-theory (enable x86isa::las-to-pas ;set-flag
;;                                      ;app-view
;;                                      ))))

;; (defthm mv-nth-1-of-las-to-pas-of-set-flag
;;   (implies (app-view x86)
;;            (equal (mv-nth 1 (x86isa::las-to-pas n lin-addr r-w-x (set-flag flag val x86)))
;;                   (mv-nth 1 (x86isa::las-to-pas n lin-addr r-w-x x86))))
;;   :hints (("Goal" :in-theory (enable x86isa::las-to-pas ;set-flag
;;                                      ;app-view
;;                                      ))))

;; (thm
;;  (equal (mv-nth 1 (RB n addr r-x (set-flag flag val x86)))
;;         (mv-nth 1 (RB n addr r-x x86)))
;;  :hints (("Goal" :in-theory (enable rb))))

(defthm get-one-byte-prefix-array-code-of-if
  (equal (x86isa::get-one-byte-prefix-array-code (if test b1 b2))
         (if test
             (x86isa::get-one-byte-prefix-array-code b1)
           (x86isa::get-one-byte-prefix-array-code b2))))

(defthm 64-bit-mode-one-byte-opcode-modr/m-p$inline-of-if
  (equal (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline (if test tp ep))
         (if test
             (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline tp)
             (x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline ep))))

(defthm acl2::bvcat-of-if-arg2
  (equal (acl2::bvcat higsize (if test highval1 highval2) lowsize lowval)
         (if test
             (acl2::bvcat higsize highval1 lowsize lowval)
           (acl2::bvcat higsize highval2 lowsize lowval))))

(defthm acl2::bvcat-of-if-arg4
  (equal (acl2::bvcat higsize highval lowsize (if test lowval1 lowval2))
         (if test
             (acl2::bvcat higsize highval lowsize lowval1)
           (acl2::bvcat higsize highval lowsize lowval2))))

;;todo: need to get the standard 32-bit assumptions gathered up:

;; TODO: reads like this (READ 4 4214784 X86) should now be resolvable?

(acl2::defopeners X86ISA::RR08$inline :hyps ((syntaxp (and (quotep X86ISA::REG) (quotep X86ISA::REX)))))

;(acl2::defopeners X86ISA::RME-SIZE$inline :hyps ((< X86ISA::EFF-ADDR '2000)))

;todo
(acl2::def-constant-opener logcount)
(acl2::def-constant-opener separate)
(acl2::def-constant-opener nonnegative-integer-quotient)
(acl2::def-constant-opener evenp)

;this case seems safe to handle:
; (SLICE '10 '7 (BVCAT '3 x '8 y))

(defthm read-1-of-write-4-same
  (implies (and (natp read-ad)
                (< read-ad (bvplus 48 4 write-ad))
                (<= write-ad read-ad)
                (app-view x86) ;drop
                (canonical-address-p read-ad)
                ;; (canonical-address-p write-ad)
                (canonical-address-p (+ 3 write-ad))
                (natp write-ad)
                (< write-ad 5000000000) ;fixme
                (X86P X86))
           (equal (read 1 read-ad (write 4 write-ad val x86))
                  (let ((byte-num (- read-ad write-ad)))
                    (slice (+ 7 (* 8 byte-num))
                           (* 8 byte-num)
                           val))))
  :hints (("Goal"
           :in-theory (e/d ( ;memi
                            bvplus
                            CANONICAL-ADDRESS-P
                            SIGNED-BYTE-P
                            ;;READ-BYTE
                            write
                            acl2::bvchop-of-logtail-becomes-slice
                            )
                           ( ;read
                            ACL2::BVPLUS-RECOLLAPSE
                            write !memi
                            ACL2::SLICE-OF-+ ;looped
                            ))
           :expand ((:free (x) (WRITE 3 (+ 1 WRITE-AD)
                                      (LOGTAIL 8 VAL) x))
                    (:free (ad val x86) (WRITE 1 ad val x86))
                    (WRITE 4 WRITE-AD VAL X86)
                    (:free (x) (WRITE 2 (+ 2 WRITE-AD)
                                      (LOGTAIL 16 VAL) x))
                    ))))

;; (defthmd xw-of-set-flag
;;   (implies (not (equal x86isa::field :rflags))
;;            (equal (xw x86isa::field x86isa::index value (set-flag x86isa::flg x86isa::val x86))
;;                   (set-flag x86isa::flg x86isa::val
;;                             (xw x86isa::field x86isa::index value x86))))
;;   :hints (("Goal" :in-theory (acl2::e/d* (set-flag) (force (force))))))

;todo: why are cons nests arising during rewriting?

(defthm write-of-write-combine-constants-1
  (implies (and (syntaxp (quotep val1))
                (syntaxp (quotep val2))
                (equal (bvchop 48 ad1)
                       (+ n2 ad2))
                (natp n1)
                (natp n2)
                (integerp ad1)
                (integerp ad2)
                )
           (equal (write n1 ad1 val1 (write n2 ad2 val2 x86))
                  (write (+ n1 n2)
                         ad2
                         (bvcat (* 8 n1) val1
                                (* 8 n2) val2)
                         x86)))
  :hints (("Goal" :in-theory (enable acl2::bvcat-of-logtail-low)
           :expand ((WRITE (+ N1 N2)
                           AD2 (BVCAT (* 8 N1) VAL1 (* 8 N2) VAL2)
                           X86)))))

(defthm xr-of-write-too-low-alt
  (implies (and (< (bvchop 48 addr1) (bvchop 48 addr2))
                (natp n)
                (<= (+ n addr2) (expt 2 48)) ;gen?
                (unsigned-byte-p 48 addr1)
                (unsigned-byte-p 48 addr2))
           (equal (xr :mem addr1 (write n addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :in-theory (enable write write-byte))))

(defthm xr-of-write-too-high-alt
  (implies (and (< (+ n addr2) addr1)
                (natp n)
;                (< (+ n addr2) (expt 2 48)) ;gen?
                (unsigned-byte-p 48 addr1)
                (unsigned-byte-p 48 addr2))
           (equal (xr :mem addr1 (write n addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :in-theory (enable write write-byte))))

(defthm xr-of-write-irrel
  (implies (and (<= n (bvchop 48 (- addr1 addr2)))
                (natp n)
                (integerp addr1)
                (integerp addr2))
           (equal (xr :mem addr1 (write n addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :induct (write n addr2 val x86)
           :in-theory (e/d (write write-byte canonical-address-p bvplus acl2::bvchop-of-sum-cases)
                           (acl2::bvplus-recollapse)))))

(defthm memi-of-write-irrel
  (implies (and (<= n (bvchop 48 (- addr1 addr2)))
                (integerp addr1)
                (integerp addr2)
                (natp n))
           (equal (memi addr1 (write n addr2 val x86))
                  (memi addr1 x86)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write memi separate)
                           (acl2::bvplus-recollapse)))))

(defthm memi-of-write-same
  (implies (and (<= n (expt 2 48))
                (unsigned-byte-p 48 addr)
                (posp n)
                )
           (equal (memi addr (write n addr val x86))
                  (bvchop 8 val)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (write n addr val x86)
           :expand (write 1 addr val x86)
           :in-theory (e/d (write write-byte)
                           (acl2::bvplus-recollapse)))))

(defthm acl2::slice-of-logtail-gen
  (implies (and (integerp acl2::high)
                (natp acl2::low)
                (natp n))
           (equal (slice acl2::high acl2::low (logtail n x))
                  (if (natp acl2::high)
                      (slice (+ acl2::high n)
                             (+ acl2::low n)
                             x)
                    0))))

(defthm read-of-write-within
  (implies (and (<= ad2 ad1) ;gen
                (< ad1 (+ n ad2))
                (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 ad2)
                (< (+ ad2 n) (expt 2 48)) ;gen
                (posp n)
                )
           (equal (read 1 ad1 (write n ad2 val x86))
                  (slice (+ 7 (* 8 (- ad1 ad2)))
                         (* 8 (- ad1 ad2))
                         val)))
  :hints (("Subgoal *1/8" :cases ((equal ad1 ad2)))
          ("Goal"   ;:expand ((WRITE N AD1 VAL X86))
           :in-theory (e/d (posp read-byte write-byte)
                           ()))))

;; no loop stopper
;; (defthm set-flag-set-flag-different-concrete-indices-better
;;   (implies (and (syntaxp (quotep i1))
;;                 (syntaxp (quotep i2))
;;                 (< i1 i2) ;gets computed
;;                 (member i1 *flg-names*)
;;                 (member i2 *flg-names*)
;;                 (x86p x86))
;;            (equal (set-flag i2 v2 (set-flag i1 v1 x86))
;;                   (set-flag i1 v1 (set-flag i2 v2 x86)))))

;; Critically, this uses equal for the comparisons, so the huge IF can usually be resolved
;; Also, the force is gone
(defthm x86isa::x86p-xw-better
  (implies (and (member-equal x86isa::fld x86isa::*x86-field-names-as-keywords*)
                (if (equal x86isa::fld ':rgf)
                    (if (integerp x86isa::index)
                        (signed-byte-p '64 value)
                      'nil)
                  (if (equal x86isa::fld ':rip)
                      (signed-byte-p '48 value)
                    (if (equal x86isa::fld ':rflags)
                        (unsigned-byte-p '32 value)
                      (if (equal x86isa::fld ':seg-visible)
                          (AND (INTEGERP X86ISA::INDEX)
                               (UNSIGNED-BYTE-P 16 VALUE))
                        (if (equal x86isa::fld ':seg-hidden-base)
                            (AND (INTEGERP X86ISA::INDEX)
                                 (UNSIGNED-BYTE-P 64 VALUE))
                          (if (equal x86isa::fld ':seg-hidden-limit)
                              (AND (INTEGERP X86ISA::INDEX)
                                   (UNSIGNED-BYTE-P 32 VALUE))
                            (if (equal x86isa::fld ':seg-hidden-attr)
                                (AND (INTEGERP X86ISA::INDEX)
                                     (UNSIGNED-BYTE-P 16 VALUE))
                              (if (equal x86isa::fld ':str)
                                  (if (integerp x86isa::index)
                                      (unsigned-byte-p '80 value)
                                    'nil)
                                (if (equal x86isa::fld ':ssr-visible)
                                    (AND (INTEGERP X86ISA::INDEX)
                                         (UNSIGNED-BYTE-P 16 VALUE))
                                  (if (equal x86isa::fld ':ssr-hidden-base)
                                      (AND (INTEGERP X86ISA::INDEX)
                                           (UNSIGNED-BYTE-P 64 VALUE))
                                    (if (equal x86isa::fld ':ssr-hidden-limit)
                                        (AND (INTEGERP X86ISA::INDEX)
                                             (UNSIGNED-BYTE-P 32 VALUE))
                                      (if (equal x86isa::fld ':ssr-hidden-attr)
                                          (AND (INTEGERP X86ISA::INDEX)
                                               (UNSIGNED-BYTE-P 16 VALUE))
                                        (if (equal x86isa::fld ':ctr)
                                            (if (integerp x86isa::index)
                                                (unsigned-byte-p '64 value)
                                              'nil)
                                          (if (equal x86isa::fld ':dbg)
                                              (if (integerp x86isa::index)
                                                  (unsigned-byte-p '64 value)
                                                'nil)
                                            (if (equal x86isa::fld ':fp-data)
                                                (if (integerp x86isa::index)
                                                    (unsigned-byte-p '80 value)
                                                  'nil)
                                              (if (equal x86isa::fld ':fp-ctrl)
                                                  (unsigned-byte-p '16 value)
                                                (if (equal x86isa::fld ':fp-status)
                                                    (unsigned-byte-p '16 value)
                                                  (if (equal x86isa::fld ':fp-tag)
                                                      (unsigned-byte-p '16 value)
                                                    (if (equal x86isa::fld ':fp-last-inst)
                                                        (unsigned-byte-p '48 value)
                                                      (if (equal x86isa::fld ':fp-last-data)
                                                          (unsigned-byte-p '48 value)
                                                        (if (equal x86isa::fld ':fp-opcode)
                                                            (unsigned-byte-p '11 value)
                                                          (if (equal x86isa::fld ':zmm)
                                                              (if (integerp x86isa::index)
                                                                  (unsigned-byte-p '128 value)
                                                                'nil)
                                                            (if (equal x86isa::fld ':mxcsr)
                                                                (unsigned-byte-p '32 value)
                                                              (if (equal x86isa::fld ':msr)
                                                                  (if (integerp x86isa::index)
                                                                      (unsigned-byte-p '64 value)
                                                                    'nil)
                                                                (if (equal x86isa::fld ':env)
                                                                    (x86isa::env-alistp value)
                                                                  (if (equal x86isa::fld ':app-view)
                                                                      (booleanp value)
                                                                    (if (equal x86isa::fld
                                                                               ':marking-view)
                                                                        (booleanp value)
                                                                      (if (equal x86isa::fld ':os-info)
                                                                          (keywordp value)
                                                                        (if (equal x86isa::fld ':mem)
                                                                            (if (integerp x86isa::index)
                                                                                (unsigned-byte-p '8 value)
                                                                              'nil)
                                                                          (equal x86isa::index
                                                                                 '0))))))))))))))))))
                                        ;;))
                                        ))))))))))))
                (x86p x86))
           (x86p (xw x86isa::fld x86isa::index value x86)))
  :hints (("Goal" :in-theory (disable X86ISA::ENV-READ-LOGIC
                                      ;;X86ISA::ENV$INLINE
                                      ))))

(defthm plus-of-minus1-and-bvcat-of-0
  (implies (and (posp lowsize)
                (integerp highval)
                (natp HIGHSIZE))
           (equal (+ -1 (bvcat highsize highval lowsize 0))
                  (if (equal (bvchop highsize highval) 0)
                      -1
                    (bvcat highsize (+ -1 highval) lowsize (+ -1 (expt 2 lowsize))))))
  :hints (("Goal" :in-theory (e/d (bvcat bvplus acl2::bvchop-of-sum-cases)
                                  (acl2::bvplus-recollapse
                                   acl2::equal-of-+-when-negative-constant)))))

(defthm bvchop-of-ash-when-negative-becomes-bvshr
  (implies (and (< c 0)
                (integerp c)
                ;(integerp i)
                ;(natp places)
                )
           (equal (bvchop places (ash i c))
                  (acl2::bvshr (- places c) i (- c))))
  :hints (("Goal" :in-theory (e/d (ash acl2::bvshr slice logtail ACL2::FLOOR-OF-/ ifix)
                                  (acl2::bvchop-of-logtail-becomes-slice acl2::floor-of-2)))))

(defthm bvshr-of-logand-becomes-bvshr-of-bvand
  (implies (and (natp amt)
                (< amt 32))
           (equal (acl2::bvshr 32 (logand x y) amt)
                  (acl2::bvshr 32 (bvand (+ 32 amt) x y) amt)))
  :hints (("Goal" :in-theory (e/d (acl2::bvshr bvand slice acl2::logtail-of-bvchop)
                                  (acl2::slice-of-logand
                                   acl2::logand-of-bvchop-becomes-bvand-alt
                                   acl2::logand-of-bvchop-becomes-bvand
                                   acl2::bvchop-of-logtail-becomes-slice
                                   acl2::anti-slice
                                   ACL2::BVAND-LOGTAIL-ARG2 ;looped
                                   ACL2::BVAND-LOGTAIL-ARG1 ;looped
                                   )))))

(defthm +-of-minus1-and-bvcat-of-0
  (implies (natp size)
           (equal (+ -1 (BVCAT 1 1 size 0))
                  (+ -1 (expt 2 size))))
  :hints (("Goal" :in-theory (enable bvcat))))

;; (thm
;;  (implies (zp amt)
;;           (equal (acl2::bvshr 32 x amt)
;;                  (bvchop 32 x)))
;;  :hints (("Goal" :in-theory (enable acl2::bvshr zp))))

(defthm bvchop-of-ash-right-shift
  (implies (and (< n 0)
                (natp size)
                (integerp n))
           (equal (acl2::bvchop size (ash x n))
                  (acl2::slice (+ -1 size (- n)) (- n) x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (ash acl2::slice logtail ifix ACL2::FLOOR-OF-/)
                           (acl2::bvchop-of-logtail-becomes-slice)))))


(defthm slice-of-expt-same-as-low
  (implies (and (natp low)
                (natp high))
           (equal (slice high low (expt 2 low))
                  (if (<= low high)
                      1
                    0)))
  :hints (("Goal" :in-theory (e/d (slice)
                                  (acl2::bvchop-of-logtail-becomes-slice)))))

(defthm slice-of-minus-of-expt-same-as-low
  (implies (and (natp k)
                (natp high))
           (equal (slice high k (- (expt 2 k)))
                  (if (<= k high)
                      (+ -1 (expt 2 (- (+ 1 high) k)))
                    0)))
  :hints (("Goal" :in-theory (enable acl2::slice-of-minus))))


(defthm floor-lemma
  (IMPLIES (AND (< N 0)
                (NATP LOW)
                (INTEGERP HIGH)
                (<= LOW HIGH)
                (INTEGERP N)
                (INTEGERP X))
           (EQUAL (FLOOR X (* (EXPT 2 LOW) (/ (EXPT 2 N))))
                  (FLOOR (* X (EXPT 2 N)) (EXPT 2 LOW)))))

;can't just turn ash into slice because we don't know what the top bit is, so
;we need the overarching slice.
(defthm slice-of-ash-right
  (implies (and (< n 0)
                ;(<= n low)
                (natp low)
                (natp high)
                (<= low high)
                (integerp n))
           (equal (acl2::slice high low (ash x n))
                  (acl2::slice (+ high (- n)) (+ low (- n)) x)))
  :hints (("Goal" :in-theory (e/d (ash acl2::slice logtail ;floor
                                       ifix
                                       acl2::expt-of-+
                                       )
                                  (acl2::bvchop-of-logtail-becomes-slice
                                   acl2::floor-of-2
                                   acl2::slice-of-*)))))

(defthm rotate-left-becomes-leftrotate
  (implies (and (natp places)
                (<= places 32) ;gen
                )
           (equal (BITOPS::ROTATE-LEFT-32 x places)
                  (ACL2::LEFTROTATE 32 places x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (ACL2::ROTATE-LEFT ACL2::LEFTROTATE
                                              acl2::bvchop-of-logtail-becomes-slice)
                           (;ACL2::EXPONENTS-ADD
                            ACL2::LOGTAIL-OF-ONE-MORE ;looped?
                            )))))

;todo: figure out how to print the hits but not the result of the rewrite

;; ;; what a mess is bitops::rotate-left-32.
;; (thm
;;  (implies (and (natp x)
;;                (natp places)
;;                (< places 32))
;;           (equal (bitops::rotate-left-32 x places)
;;                  (acl2::leftrotate 32 places x)))
;;  :hints (("Goal" :in-theory (e/d (acl2::rotate-left
;;                                   acl2::leftrotate
;;                                   ;;repeatbit
;;                                   )
;;                                  (ACL2::EXPONENTS-ADD)))))

;; Sections:
;; Idx Name          Size      VMA       LMA       File off  Algn
;;   0 UPX0          00004000  00401000  00401000  00000400  2**2
;;                   CONTENTS, ALLOC, CODE
;;   1 UPX1          00000a00  00405000  00405000  00000400  2**2
;;                   CONTENTS, ALLOC, LOAD, CODE, DATA
;;   2 UPX2          00000200  00406000  00406000  00000e00  2**2
;;                   CONTENTS, ALLOC, LOAD, DATA

;; It's trying to read from #x40445C.  Add assumption (equal 0 (read #x4000 #x401000 x86)).
;; Now it's reading from #x405A00, which is after the end of the UPX1 section but before UPX2. Add assumption (equal 0 (read #x600 #x405a00 x86)).
;; Now it's reading from #x406200, which is after the UPX2 section.  Should we try assuming those bytes are 0 as well?


(defthm mv-nth-0-of-las-to-pas-of-set-flag
  (implies (app-view x86)
           (equal (mv-nth 0 (x86isa::las-to-pas n lin-addr r-w-x (set-flag flag val x86)))
                  (mv-nth 0 (x86isa::las-to-pas n lin-addr r-w-x x86))))
  :hints (("Goal" :in-theory (enable x86isa::las-to-pas x86isa::ia32e-la-to-pa))))

(defthm mv-nth-0-of-rb-1-of-set-flag
  (equal (mv-nth 0 (rb-1 n addr r-x (set-flag flag val x86)))
         (mv-nth 0 (rb-1 n addr r-x x86)))
  :hints (("Goal" :in-theory (enable rb-1))))

(defthm mv-nth-0-of-rvm08-of-set-flag
  (equal (mv-nth 0 (rvm08 addr (set-flag flag val x86)))
         (mv-nth 0 (rvm08 addr x86)))
  :hints (("Goal" :in-theory (enable rvm08))))

(defthm mv-nth-1-of-rvm08-of-set-flag
  (equal (mv-nth 1 (rvm08 addr (set-flag flag val x86)))
         (mv-nth 1 (rvm08 addr x86)))
  :hints (("Goal" :in-theory (enable rvm08))))

(defthm mv-nth-1-of-rb-1-of-set-flag
  (implies (app-view x86)
           (equal (mv-nth 1 (rb-1 n addr r-x (set-flag flag val x86)))
                  (mv-nth 1 (rb-1 n addr r-x x86))))
  :hints (("Goal" :in-theory (enable rb-1))))

(defthm mv-nth-0-of-rme08-of-set-flag
  (implies (app-view x86)
           (equal (mv-nth 0 (x86isa::rme08 proc-mode eff-addr seg-reg rx (set-flag flag val x86)))
                  (mv-nth 0 (x86isa::rme08 proc-mode eff-addr seg-reg rx x86))))
  :hints (("Goal" :in-theory (enable x86isa::rme08 rb))))

(defthm mv-nth-1-of-rme08-of-set-flag
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rme08 proc-mode eff-addr seg-reg rx (set-flag flag val x86)))
                  (mv-nth 1 (x86isa::rme08 proc-mode eff-addr seg-reg rx x86))))
  :hints (("Goal" :in-theory (enable x86isa::rme08 rb))))

;; (defthm mv-nth-0-of-get-prefixes-of-set-flag
;;   (implies (app-view x86)
;;            (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-flag flag val x86)))
;;                   (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86))))
;;   :hints (("Goal" :expand (:free (proc-mode)
;;                                  (get-prefixes proc-mode start-rip
;;                                                prefixes rex-byte cnt (set-flag flag val x86)))
;;            :induct (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
;;            :in-theory (enable get-prefixes x86isa::add-to-*ip))))

;; (defthm mv-nth-1-of-get-prefixes-of-set-flag
;;   (implies (app-view x86)
;;            (equal (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-flag flag val x86)))
;;                   (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86))))
;;   :hints (("Goal" :expand (:free (proc-mode) (get-prefixes proc-mode start-rip
;;                                         prefixes rex-byte cnt (set-flag flag val x86)))
;;            :induct (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
;;            :in-theory (enable get-prefixes x86isa::add-to-*ip))))



;todo: avoid the reverse?
(defthmd write-becomes-write-bytes
  (equal (write n base-addr val x86)
         (write-bytes base-addr (reverse (acl2::unpackbv n 8 val)) x86))
  :hints (("Goal" :in-theory (e/d (;list::cdr-append
                                   write-byte)
                                  (;ACL2::LEN-CONS-META-RULE
                                   ;;ACL2::TAKE-OF-CONS
                                   last
                                   ACL2::UNPACKBV-OPENER
                                   write-bytes))
           :induct (WRITE N BASE-ADDR VAL X86)
           :expand ((WRITE 1 BASE-ADDR VAL X86)
                    (WRITE-BYTES BASE-ADDR
                                (ACL2::REVERSE-LIST (ACL2::UNPACKBV N 8 VAL))
                                X86)))))

(in-theory (disable butlast))

(local (in-theory (disable ACL2::CAR-BECOMES-NTH-OF-0))) ;todo

(defthmd write-bytes-becomes-write
  (equal (write-bytes base-addr vals x86)
         (write (len vals) base-addr (acl2::packbv (len vals) 8 (acl2::reverse-list vals)) x86))
  :hints (("Goal" :in-theory (e/d (;list::cdr-append
                                   write-byte)
                                  (;ACL2::LEN-CONS-META-RULE
                                   ;;ACL2::TAKE-OF-CONS
                                   last
                                   ACL2::UNPACKBV-OPENER
                                   ;;write-bytes
                                   ;ACL2::NTH-WHEN-ZP
                                   ))
           :expand (WRITE (LEN VALS)
                          BASE-ADDR
                          (ACL2::PACKBV (LEN VALS)
                                        8 (acl2::reverse-list VALS))
                          X86)
           :induct (WRITE-BYTES BASE-ADDR VALS X86))))

(acl2::def-constant-opener acl2::unpackbv)
(acl2::def-constant-opener reverse)

;; (DEFUN WRITE-2-addr-induct (N BASE-ADDR addr2 VAL X86)
;;   (declare (xargs :stobjs x86
;;                   :verify-guards nil)
;;            (irrelevant addr2))
;;   (IF (ZP N)
;;       x86
;;       (LET ((X86 (!MEMI (BVCHOP 48 BASE-ADDR)
;;                         (BVCHOP 8 VAL)
;;                         X86)))
;;            (WRITE-2-addr-induct (+ -1 N)
;;                                 (+ 1 BASE-ADDR)
;;                                 (+ 1 addr2)
;;                                 (LOGTAIL 8 VAL)
;;                                 X86))))

(defthm write-of-281474976710656
  (equal (write n 281474976710656 val x86)
         (write n 0 val x86))
  :hints (("Goal" :use (:instance write-of-bvchop-48 (addr 281474976710656))
           :in-theory (disable write-of-bvchop-48))))

;; (thm
;;  (implies (and ;(< addr1 281474976710655)
;;                (< addr1 n)
;;                (unsigned-byte-p 48 addr1)
;;                (<= n 281474976710656)
;; ;(not (zp n))
;;                (natp n)
;;                )
;;           (equal (memi addr1 (write n 0 val x86))
;;                  (slice (+ 7 (* 8 addr1))
;;                         (* 8 addr1)
;;                         val))))

(defthm memi-of-write-not-irrel
  (implies (and (< (bvchop 48 (- addr1 addr2)) n) ;rephrase?
                (integerp addr2)
                (unsigned-byte-p 48 addr1)
                (<= n (expt 2 48))
                (natp n))
           (equal (memi addr1 (write n addr2 val x86))
                  (acl2::slice (+ 7 (* 8 (bvminus 48 addr1 addr2)))
                               (* 8 (bvminus 48 addr1 addr2))
                               val)))
  :hints (("Goal"
           :expand ((write n addr2 val x86)
                    (write 1 addr1 val x86)
                    (write n 0 val x86))
           :induct (write n addr2 val x86)
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus write-byte)
                           (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus)))))

(defthm read-of-write-disjoint-gen
  (implies (and (<= n2 (bvminus 48 addr1 addr2))
                (<= n1 (bvminus 48 addr2 addr1))
                (natp n1)
                (natp n2)
;                (x86p x86)
                (integerp addr2)
                (integerp addr1))
           (equal (read n1 addr1 (write n2 addr2 val x86))
                  (read n1 addr1 x86)))
  :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read n1 addr1 x86)
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus
                                   read-byte ; todo
                                   )
                           (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    ACL2::SLICE-OF-+ ;looped
                                                    ACL2::BVCAT-OF-+-HIGH
                                                    )))))

(defthm read-byte-of-write-bytes-irrel
  (implies (and (<= (len bytes) (bvminus 48 addr1 addr2))
                (integerp addr2)
                (integerp addr1))
           (equal (read-byte addr1 (write-bytes addr2 bytes x86))
                  (read-byte addr1 x86)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE-BYTES ADDR2 BYTES X86)
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases bvuminus bvminus write-bytes ;ACL2::NTH-WHEN-N-IS-ZP
                                   )
                           (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::slice-of-+ ;looped
                                                    acl2::bvcat-of-+-high
;                                                    ACL2::NTH-OF-CDR
                                                    )))))

(defthm read-of-write-bytes-disjoint
  (implies (and (<= (len vals) (bvminus 48 addr1 addr2))
                (<= n1 (bvminus 48 addr2 addr1))
                (natp n1)
                (integerp addr2)
                (integerp addr1))
           (equal (read n1 addr1 (write-bytes addr2 vals x86))
                  (read n1 addr1 x86)))
  :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read n1 addr1 x86)
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus ;read-byte
                                   )
                           (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    ACL2::SLICE-OF-+ ;looped
                                                    ACL2::BVCAT-OF-+-HIGH
                                                    )))))

(acl2::defopeners REVAPPEND)

;for axe
(defthm not-stringp-of-cons
  (not (stringp (cons a b))))

;remove theorems about memi once we use read-byte more?

;mixes abstraction levels - todo remove
(defthm memi-of-write-byte-same
  (implies (and (<= n (expt 2 48))
                (unsigned-byte-p 48 addr)
                (posp n))
           (equal (memi addr (write-byte addr byte x86))
                  (bvchop 8 byte)))
  :hints (("Goal" :in-theory (e/d (write-byte)
                                  ()))))

;mixes abstraction levels - todo remove
(defthm memi-of-write-byte-irrel
  (implies (and (not (equal (bvchop 48 addr1)
                            (bvchop 48 addr2)))
                (integerp addr1)
                (integerp addr2))
           (equal (memi addr1 (write-byte addr2 byte x86))
                  (memi addr1 x86)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write-byte memi)
                           (acl2::bvplus-recollapse)))))

;mixes abstraction levels - todo remove
(defthm memi-of-write-byte
  (implies (and (unsigned-byte-p 48 addr1)
                (integerp addr2))
           (equal (memi addr1 (write-byte addr2 byte x86))
                  (if (equal (bvchop 48 addr1)
                             (bvchop 48 addr2))
                      (bvchop 8 byte)
                    (memi addr1 x86))))
    :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write-byte memi)
                           (acl2::bvplus-recollapse)))))

(include-book "kestrel/axe/axe-rules-mixed" :dir :system) ;todo: reduce?

(defthm read-of-write-byte-disjoint
  (implies (and (<= 1 (bvminus 48 addr1 addr2))
                (<= n1 (bvminus 48 addr2 addr1))
                (natp n1)
                (integerp addr2)
                (integerp addr1))
           (equal (read n1 addr1 (write-byte addr2 byte x86))
                  (read n1 addr1 x86)))
  :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read n1 addr1 x86)
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus read-byte)
                           (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    ACL2::SLICE-OF-+ ;looped
                                                    ACL2::BVCAT-OF-+-HIGH
                                                    )))))

(defthm read-1-of-write-byte-same
  (implies (integerp addr)
           (equal (read 1 addr (write-byte addr byte x86))
                  (bvchop 8 byte)))
  :hints (("Goal" :in-theory (enable read-byte))))

;; (thm
;;  (implies (and (equal 1 (len vals2))
;;                (equal k+1 (bvplus 1 k)))
;;           (equal (write-bytes k+1 vals1 (write-bytes k vals2 x86))
;;                  (write-bytes k+1 (cons (first vals2s)) x86))))

;; (defthm read-of-write-bytes-not-irrel
;;   (implies (and (< (bvminus 48 addr1 addr2) (len vals))
;;                 (<= n1 (bvminus 48 addr2 addr1))
;;                 (natp n1)
;;                 (integerp addr2)
;;                 (integerp addr1))
;;            (equal (read n1 addr1 (write-bytes addr2 vals x86))
;;                   (read n1 addr1 x86)))
;;   :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
;;           ("Goal" :do-not '(generalize eliminate-destructors)
;;            :induct (read n1 addr1 x86)
;;            :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus)
;;                            (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
;;                                                     ACL2::SLICE-OF-+ ;looped
;;                                                     ACL2::BVCAT-OF-+-HIGH
;;                                                     )))))

(local
 (defthm <-of-if-arg2
   (equal (< x (if test y z))
          (if test
              (< x y)
            (< x z)))))

(defthm read-byte-of-write-bytes-not-irrel
  (implies (and (< (bvminus 48 addr1 addr2) (len bytes))
                (integerp addr2)
                (integerp addr1)
                (<= (len bytes) (expt 2 48)))
           (equal (read-byte addr1 (write-bytes addr2 bytes x86))
                  (bvchop 8 (nth (bvminus 48 addr1 addr2) bytes))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE-BYTES ADDR2 BYTES X86)
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases bvuminus bvminus write-bytes)
                           (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::slice-of-+ ;looped
                                                    acl2::bvcat-of-+-high
;                                                    ACL2::NTH-OF-CDR
                                                    )))))

(defthm move-neg-addend
  (implies (acl2-numberp y)
           (equal (equal 1 (+ (- x) y))
                  (equal (+ 1 x) y))))

;; inner write is at lower address
(defthmd write-byte-of-write-byte-adjacent-1
  (implies (and (equal 1 (bvminus 48 k+1 k))
                (integerp k)
                (integerp k+1))
           (equal (write-byte k+1 byte1 (write-byte k byte2 x86))
                  (write-bytes k (list byte2 byte1) x86)))
  :hints (("Goal" :in-theory (enable write-byte bvminus acl2::bvchop-of-sum-cases))))

(defthm equal-of-bvchop-and-bvplus-same
  (implies (natp size)
           (equal (EQUAL (BVCHOP size K) (BVPLUS size n K))
                  (equal (bvchop size n) 0)))
  :hints (("Goal"
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases bvuminus bvminus)
                           (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::slice-of-+ ;looped
                                                    acl2::bvcat-of-+-high
   ;                                                    ACL2::NTH-OF-CDR
                                                    )) )))

;; outer write is at lower addresses
(defthmd write-byte-of-write-byte-adjacent-2
  (implies (and (equal 1 (bvminus 48 k+1 k))
                (integerp k)
                (integerp k+1))
           (equal (write-byte k byte1 (write-byte k+1 byte2 x86))
                  (write-bytes k (list byte1 byte2) x86)))
  :hints (("Goal" :in-theory (enable WRITE-BYTE bvminus acl2::bvchop-of-sum-cases))))

(in-theory (disable acl2::bvplus-recollapse))

;; (defthm write-bytes-of-281474976710656
;;   (equal (write-bytes 281474976710656 vals x86)
;;          (write-bytes 0 vals x86))
;;   )

(defun-nx double-write-bytes-induct-two-addrs (base-addr base-addr2 vals x86)
  (if (endp vals)
      (list base-addr base-addr2 vals x86)
    (double-write-bytes-induct-two-addrs (+ 1 base-addr)
                                        (+ 1 base-addr2)
                                        (cdr vals)
                                        (WRITE-BYTE base-addr (CAR VALS) X86))))

(defthmd write-bytes-of-bvchop-arg1-helper
  (implies (and (equal (bvchop 48 ad1)
                       (bvchop 48 ad2))
                (integerp ad1)
                (integerp ad2))
           (equal (write-bytes ad1 vals x86)
                  (write-bytes ad2 vals x86)))
  :hints (("Goal" ;:expand ((WRITE-BYTES AD2 VALS X86))
           :induct (double-write-bytes-induct-two-addrs ad1 ad2 vals x86)
           :expand ((WRITE-BYTES AD1 VALS X86)
                    (WRITE-BYTES AD2 VALS X86))
           :in-theory (enable bvplus write-bytes WRITE-BYTE)
           )))

(defthm write-bytes-of-bvchop-arg1
  (implies (integerp addr)
           (equal (write-bytes (bvchop 48 addr) vals x86)
                  (write-bytes addr vals x86)))
  :hints (("Goal" :use (:instance write-bytes-of-bvchop-arg1-helper (ad1  (bvchop 48 addr)) (ad2 addr))
           :in-theory (disable write-bytes-of-bvchop-arg1-helper))))

(defthm bvplus-combine-constants-hack
  (implies (and (integerp x)
                (integerp y))
           (equal (bvplus 48 (+ 1 x) (+ -1 y))
                  (bvplus 48 x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; inner write is at lower addresses
(defthmd write-bytes-of-write-bytes-adjacent-1
  (implies (and (equal addr1 (bvplus 48 addr2 (len vals2)))
                (integerp addr2))
           (equal (write-bytes addr1 vals1 (write-bytes addr2 vals2 x86))
                  (write-bytes addr2 (append vals2 vals1) x86))))

(defthm write-bytes-of-write-bytes-disjoint
  (implies (and (syntaxp (acl2::smaller-termp addr1 addr2))
                (<= (len vals2) (bvminus 48 addr1 addr2))
                (<= (len vals1) (bvminus 48 addr2 addr1))
                (integerp addr2)
                (integerp addr1))
           (equal (write-bytes addr2 vals2 (write-bytes addr1 vals1 x86))
                  (write-bytes addr1 vals1 (write-bytes addr2 vals2 x86))))
  :hints (("Goal"
           :induct (WRITE-BYTES ADDR1 VALS1 X86)
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases bvuminus bvminus)
                           (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::slice-of-+ ;looped
                                                    acl2::bvcat-of-+-high)) )))

(defthm bvuminus-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (bvuminus '48 (+ x y))
                  (bvuminus '48 (bvplus 48 x y))))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthmd bvminus-of-+-arg2
  (implies (and (integerp y)
                (integerp z))
           (equal (bvminus size x (+ y z))
                  (bvminus size x (bvplus size y z))))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

(theory-invariant (incompatible (:rewrite bvminus-of-+-arg2) (:rewrite acl2::bvchop-of-sum-cases)))

(defthm bvminus-of-bvplus-same-arg2
  (equal (bvminus size k (bvplus size j k))
         (bvuminus size j))
  :hints (("Goal" :in-theory (e/d (bvplus bvuminus acl2::bvchop-of-sum-cases bvminus) (;BVPLUS-OF-MINUS-1
                                                                               )))))

(defthm write-bytes-of-append
  (implies (and (integerp ad)
                (<= (+ (len vals1) (len vals2)) (expt 2 48)))
           (equal (write-bytes ad (append vals1 vals2) x86)
                  (write-bytes ad vals1 (write-bytes (+ ad (len vals1)) vals2 x86))))
  :hints (("Goal" :in-theory (enable append bvminus-of-+-arg2))))

(defthm bvminus-of-+-same-arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (bvminus size x (binary-+ x y))
                  (bvuminus size y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvuminus acl2::bvchop-of-sum-cases bvminus) ( ;bvplus-of-minus-1
                                                                                        )))))

(defthm bvminus-of-+-same-arg2-alt
  (implies (and (integerp x)
                (integerp y))
           (equal (bvminus size x (binary-+ y x))
                  (bvuminus size y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvuminus acl2::bvchop-of-sum-cases bvminus) ( ;bvplus-of-minus-1
                                                                                        )))))
(in-theory (disable WRITE-BYTES))

;; outer write is at lower addresses
(defthmd write-bytes-of-write-bytes-adjacent-2
  (implies (and (equal addr1 (bvplus 48 addr2 (len vals2)))
                (integerp addr2)
                (<= (len vals2) (bvminus 48 addr1 addr2))
                (<= (+ (len vals1) (len vals2)) (expt 2 48)))
           (equal (write-bytes addr2 vals2 (write-bytes addr1 vals1 x86))
                  (write-bytes addr2 (append vals2 vals1) x86)))
  :hints (("Goal" :in-theory (enable BVPLUS))))



;; outer write is at lower addresses
(defthmd write-byte-of-write-bytes-adjacent
  (implies (and (equal addr1 (bvplus 48 addr2 1))
                (integerp addr2)
                (<= 1 (bvminus 48 addr1 addr2))
                (<= (+ (len vals1) 1) (expt 2 48)))
           (equal (write-byte addr2 val (write-bytes addr1 vals1 x86))
                  (write-bytes addr2 (cons val vals1) x86)))
  :hints (("Goal" :use (:instance write-bytes-of-write-bytes-adjacent-2 (vals2 (list val)))
           :in-theory (disable write-bytes-of-write-bytes-adjacent-2))))

;; outer write is at lower addresses
(defthmd write-bytes-of-write-byte-adjacent
  (implies (and (equal addr1 (bvplus 48 addr2 (len vals2)))
                (integerp addr2)
                (<= (len vals2) (bvminus 48 addr1 addr2))
                (<= (+ 1 (len vals2)) (expt 2 48)))
           (equal (write-bytes addr2 vals2 (write-byte addr1 val x86))
                  (write-bytes addr2 (append vals2 (list val)) x86)))
  :hints (("Goal" :use (:instance write-bytes-of-write-bytes-adjacent-2 (vals1 (list val)))
           :in-theory (disable write-bytes-of-write-bytes-adjacent-2))))


   ;kill
;; (defthm write-bytes-of-write-bytes-adjacent-1
;;   (implies (and (equal addr1 (bvplus 48 addr2 (len vals2)))
;;                 (integerp addr2))
;;            (equal (write-bytes addr1 vals1 (write-bytes addr2 vals2 x86))
;;                   (write-bytes addr2 (append vals2 vals1) x86))))

;; inner write is at lower addresses
(defthmd write-bytes-of-write-byte-adjacent-2
  (implies (and (equal addr2 (bvplus 48 1 addr1))
                (integerp addr1)
                (<= (len vals2) (bvminus 48 addr1 addr2))
                (<= (+ 1 (len vals2)) (expt 2 48)))
           (equal (write-bytes addr2 vals2 (write-byte addr1 val x86))
                  (write-bytes addr1 (cons val vals2) x86)))
  :hints (("Goal" :use (:instance write-bytes-of-write-bytes-adjacent-1
                                  (addr1 addr2)
                                  (vals1 vals2)
                                  (addr2 addr1)
                                  (vals2 (list val)))
           :in-theory (disable write-bytes-of-write-bytes-adjacent-1))))

;; inner write is at lower addresses
(defthmd write-byte-of-write-bytes-adjacent-1
  (implies (and (equal addr1 (bvplus 48 addr2 (len vals2)))
                (integerp addr2))
           (equal (write-byte addr1 val (write-bytes addr2 vals2 x86))
                  (write-bytes addr2 (append vals2 (list val)) x86)))
  :hints (("Goal" :use (:instance write-bytes-of-write-bytes-adjacent-1 (vals1 (list val)))
           :in-theory (disable write-bytes-of-write-bytes-adjacent-1))))




;;                   ;; (WRITE-BYTES
;;                   ;;  4198450 '(5 156 131 196 8 137)
;;                   ;;  (WRITE-BYTES
;;                   ;;   4198442
;;                   ;;   '(232 253 255 255 82 232 2 0 0 141)


;; (thm
;;  (implies (and (integerp ad1)
;;                (integerp ad2)

;;                )
;;           (equal (WRITE-BYTES ad1 vals1 (WRITE-BYTES ad2 vals2 x86))
;;                  (WRITE-BYTES ad1 vals1 (WRITE-BYTES ad2 (butlast vals2 (- (len vals2) (- ad1 ad2))) x86))))


(defthm write-bytes-subst-constant-arg1
  (implies (and (equal (bvchop 48 ad) freek)
                (syntaxp (and (quotep freek)
                              (not (quotep ad))))
                (integerp ad))
           (equal (write-bytes ad bytes x86)
                  (write-bytes freek bytes x86))))

;;todo: why isn't the non-alt rule sufficient?
(defthm write-bytes-subst-constant-arg1-alt
  (implies (and (equal freek (bvchop 48 ad))
                (syntaxp (and (quotep freek)
                              (not (quotep ad))))
                (integerp ad))
           (equal (write-bytes ad bytes x86)
                  (write-bytes freek bytes x86))))

(defthm write-bytes-of-write-byte-same
  (implies (integerp ad)
           (equal (write-bytes ad bytes (write-byte ad byte x86))
                  (if (consp bytes)
                      (write-bytes ad bytes x86)
                    (write-byte ad byte x86))))
  :hints (("Goal" :expand ((WRITE-BYTES AD BYTES X86)
                           (WRITE-BYTES AD BYTES (WRITE-BYTE AD BYTE X86))))))

(defthm write-bytes-when-not-consp
  (implies (not (consp bytes))
           (equal (write-bytes ad bytes x86)
                  x86))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm write-byte-of-write-bytes-same
  (implies (and (integerp ad)
                (<= (len bytes) (expt 2 48)) ;gen
                )
           (equal (write-byte ad byte (write-bytes ad bytes x86))
                  (write-byte ad byte (write-bytes (+ 1 ad) (cdr bytes) x86))))
  :hints (("Goal" :expand ((write-bytes ad bytes x86)))))

(defun-nx double-write-bytes-induct-two-lists (addr vals1 vals2 x86)
  (if (endp vals1)
      (list addr vals1 vals2 x86)
    (double-write-bytes-induct-two-lists (+ 1 addr)
                                        (cdr vals1)
                                        (cdr vals2)
                                        (WRITE-BYTE addr (CAR VALS1) X86))))

(defthm write-bytes-of-write-bytes-same
  (implies (and (<= (len vals2) (len vals1))
                (<= (len vals2) (expt 2 48))
                (integerp ad))
           (equal (write-bytes ad vals1 (write-bytes ad vals2 x86))
                  (write-bytes ad vals1 x86)))
  :hints (("Goal"
           :induct (double-write-bytes-induct-two-lists ad vals1 vals2 x86)
           :in-theory (enable write-bytes))))

(defthm write-bytes-equal-when-bvchops-equal
  (implies (and (equal (bvchop 48 ad1) (bvchop 48 ad2))
                (integerp ad1)
                (integerp ad2))
           (equal (equal (write-bytes ad1 bytes x86) (write-bytes ad2 bytes x86))
                  t))
  :hints (("Goal" :use ((:instance write-bytes-of-bvchop-arg1
                                   (addr ad1)
                                   (vals bytes))
                        (:instance write-bytes-of-bvchop-arg1
                                   (addr ad2)
                                   (vals bytes)))
           :in-theory (disable WRITE-BYTES-OF-BVCHOP-ARG1))))

(defthm write-bytes-subst-term-arg1
  (implies (and (equal (bvchop 48 ad) (bvchop 48 free))
                (syntaxp (acl2::smaller-termp free ad))
                (integerp ad)
                (integerp free))
           (equal (write-bytes ad bytes x86)
                  (write-bytes free bytes x86))))

(defthm write-bytes-subst-term-arg1-plus-version
  (implies (and (equal (bvchop 48 ad) freek)
                (syntaxp (quotep freek))
                (integerp ad)
                (integerp free))
           (equal (write-bytes (+ 1 ad) bytes x86)
                  (write-bytes (+ 1 freek) bytes x86))))

(defthm write-bytes-subst-term-arg1-plus-version-alt
  (implies (and (equal (bvchop 48 ad) (bvchop 48 free))
                (syntaxp (acl2::smaller-termp free ad))
                (integerp ad)
                (integerp free))
           (equal (write-bytes (+ 1 ad) bytes x86)
                  (write-bytes (+ 1 free) bytes x86))))

(defthm write-byte-equal-when-bvchops-equal
  (implies (and (equal (bvchop 48 ad1) (bvchop 48 ad2))
                (integerp ad1)
                (integerp ad2))
           (equal (equal (write-byte ad1 byte x86) (write-byte ad2 byte x86))
                  t))
  :hints (("Goal" :use ((:instance write-byte-of-bvchop-arg1
                                   (ad ad1)
                                   (byte byte))
                        (:instance write-byte-of-bvchop-arg1
                                   (ad ad2)
                                   (byte byte)))
           :in-theory (disable write-byte-of-bvchop-arg1))))

(defthm write-bytes-of-write-byte-same-gen
  (implies (and (< (bvminus 48 ad2 ad1) (len bytes))
                (integerp ad1)
                (integerp ad2))
           (equal (write-bytes ad1 bytes (write-byte ad2 byte x86))
                  (write-bytes ad1 bytes x86)))
  :hints (("Goal"
           :induct (WRITE-BYTES AD1 BYTES X86)
           :in-theory (e/d (write-bytes bvplus acl2::bvchop-of-sum-cases bvuminus bvminus) (acl2::bvminus-becomes-bvplus-of-bvuminus))
           )))

(defthm write-bytes-of-write-byte-too-many
  (implies (and (>= (len bytes) (expt 2 48))
                (integerp ad)
                (integerp ad2))
           (equal (write-bytes ad bytes (write-byte ad2 byte x86))
                  (write-bytes ad bytes x86)))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm write-bytes-of-write-byte-gen
  (implies (and (integerp ad1)
                (integerp ad2)
   ;                (<= (len bytes) (expt 2 48))
                )
           (equal (write-bytes ad1 bytes (write-byte ad2 byte x86))
                  (if (< (bvminus 48 ad2 ad1) (len bytes))
                      (write-bytes ad1 bytes x86)
                    (write-byte ad2 byte (write-bytes ad1 bytes x86))))))


(defun-nx double-write-bytes-induct-two-ads-two-lists (ad1 ad2 vals1 vals2 x86)
  (if (endp vals1)
      (list ad1 ad2 vals1 vals2 x86)
    (double-write-bytes-induct-two-ads-two-lists (+ 1 ad1)
                                                (+ 1 ad2)
                                                (cdr vals1)
                                                (cdr vals2)
                                                x86)))

;nested induction.  expand more?
(defthm write-bytes-of-write-bytes-same-gen
  (implies (and (<= (+ (bvminus 48 ad2 ad1) (len vals2)) (len vals1))
;                (<= (len vals2) (expt 2 48)) ;gen?
 ;               (<= (len vals1) (expt 2 48)) ;gen?
                (integerp ad1)
                (integerp ad2))
           (equal (write-bytes ad1 vals1 (write-bytes ad2 vals2 x86))
                  (write-bytes ad1 vals1 x86)))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :expand ((WRITE-BYTES 0 VALS1 (WRITE-BYTES AD2 VALS2 X86))
                    (WRITE-BYTES AD1 VALS1 (WRITE-BYTES AD2 VALS2 X86))
                    (WRITE-BYTES AD2 VALS2 X86)
                    (WRITE-BYTES 0 VALS2 X86)
                    (WRITE-BYTES AD1 VALS1 X86)
                    (WRITE-BYTES 0 VALS1 X86)
                    (WRITE-BYTES 0 VALS1
                            (WRITE-BYTES (+ 1 AD2) (CDR VALS2) X86)))
           :induct ;(write-bytes ad2 vals2 x86)
           (double-write-bytes-induct-two-ads-two-lists ad1 ad2 vals1 vals2 x86)
           :in-theory (e/d (write-bytes bvplus acl2::bvchop-of-sum-cases bvuminus bvminus)
                           (;(:e ash) ;blows out the memory
                            ;(:e expt)
                            acl2::bvminus-becomes-bvplus-of-bvuminus)))))

(in-theory (disable ACL2::INEQ-HACK2 ACL2::INEQ-HACK ACL2::CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER ACL2::NATP-MEANS-NON-NEG))

(in-theory (disable ACL2::PLUS-BVCAT-WITH-0 ACL2::PLUS-BVCAT-WITH-0-ALT))

(defthm write-byte-of-+-subst-arg1
  (implies (and (equal (bvchop 48 ad) freek)
                (syntaxp (and (quotep freek) (not (quotep ad))))
                (integerp ad)
                (integerp freek))
           (equal (write-byte (+ 1 ad) byte x86)
                  (write-byte (+ 1 freek) byte x86))))

;;cut down vals2 when it contains values that will be overwritten
(defthm write-bytes-of-write-bytes-chop-inner
  (implies (and (< (bvminus 48 ad1 ad2) (len vals2))
                (<= (len vals2) (+ (len vals1) (bvminus 48 ad1 ad2)))
                (syntaxp (and (quotep vals2)
                              (quotep ad1)
                              (quotep ad2)))
                (<= (len vals2) (expt 2 48))
                (integerp ad1)
                (integerp ad2)
                )
           (equal (write-bytes ad1 vals1 (write-bytes ad2 vals2 x86))
                  (write-bytes ad1 vals1 (write-bytes ad2 (acl2::firstn (bvminus 48 ad1 ad2) vals2) x86))))
  :hints (("Goal"
           :induct (write-bytes ad2 vals2 x86)
           :expand ((:free (vals x86) (write-bytes ad2 vals x86))
                    (WRITE-BYTES 0
                                (ACL2::TAKE (BVCHOP 48 AD1) VALS2)
                                X86)
                    (WRITE-BYTES 2 VALS1 X86)
                    ;(ACL2::SUBRANGE 1 (+ -1 (BVCHOP 48 AD1))
                                                  ;;VALS2)
                    ;; (WRITE-BYTES 0
                    ;;             (CONS (CAR VALS2)
                    ;;                   (ACL2::SUBRANGE 1 (+ -1 (BVCHOP 48 AD1))
                    ;;                                   VALS2))
                    ;;             X86)
                    (WRITE-BYTES 0 (ACL2::TAKE (BVCHOP 48 AD1) VALS2) X86))
           :in-theory (e/d (WRITE-BYTES bvplus acl2::bvchop-of-sum-cases bvuminus bvminus
                                        ;ACL2::CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
                                        )
                           (ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                            ACL2::BVCAT-OF-+-LOW ;looped
                            ACL2::TAKE-OF-CDR-BECOMES-SUBRANGE
                            )))))

(defthm write-bytes-of-append-gen
  (implies (integerp ad)
           (equal (write-bytes ad (append vals1 vals2) x86)
                  (write-bytes (+ ad (len vals1)) vals2 (write-bytes ad vals1 x86))))
  :hints (("Goal" :in-theory (enable append WRITE-BYTES))))

(defthm write-bytes-of-append-of-finalcdr
  (equal (write-bytes ad (append vals (acl2::finalcdr vals2)) x86)
         (write-bytes ad vals x86))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm <-of-if-arg1
  (equal (< (if test x y) z)
         (if test (< x z) (< y z))))

(defthmd write-bytes-of-write-bytes-same-contained-helper2
  (implies (and (<= (+ (bvminus 48 ad1 ad2) (len vals1)) (len vals2))
                (integerp ad1)
                (integerp ad2))
           (equal (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                          (acl2::firstn (len vals1) (nthcdr (bvminus 48 ad1 ad2) vals2))
                          (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))
                  vals2))
  :hints (("Goal" :in-theory (enable acl2::equal-of-append))))

(defthm write-bytes-of-+-of-2^48
  (implies (integerp ad)
           (equal (write-bytes (+ 281474976710656 ad) vals x86)
                  (write-bytes ad vals x86)))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm write-bytes-of-write-bytes-of-write-bytes-inner-irrel
  (implies (and (integerp ad1)
                (integerp ad2)
                (<= (len vals11) (len vals1)))
           (equal (write-bytes ad1 vals1 (write-bytes ad2 vals2 (write-bytes ad1 vals11 x86)))
                  (write-bytes ad1 vals1 (write-bytes ad2 vals2 x86))))
  :hints (("Goal"
           :expand ((:free (vals x86) (write-bytes ad1 vals x86)))
           :in-theory (e/d (write-bytes bvplus acl2::bvchop-of-sum-cases bvuminus bvminus)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
;                            append-take-nthcdr
                            acl2::append-of-take-and-nthcdr-2 ;compare to  list::append-take-nthcdr
    ;write-bytes-of-append-gen write-bytes-of-append
                            ;list::equal-append-reduction!
                            )))))

;todo: very slow
;; to state this, we manually put in an append for vals2. next we'll replace it with just vals2 (using helper2 above)
;slow
(defthm write-bytes-of-write-bytes-same-contained-helper
  (implies (and (<= (+ (bvminus 48 ad1 ad2) (len vals1)) (len vals2))
                (< (len vals2) (expt 2 48)) ;gen?
                (< (len vals1) (expt 2 48)) ;gen?
                (integerp ad1)
                (integerp ad2)
                (true-listp vals2)
                (true-listp vals1)
                (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 ad2)
                )
           (equal (write-bytes ad1 vals1 (write-bytes ad2
                                                      ;;vals2
                                                      (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                                                              (acl2::firstn (len vals1) (nthcdr (bvminus 48 ad1 ad2) vals2))
                                                              (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))
                                                      x86))
                  (write-bytes ad2 (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                                           vals1
                                           (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))
                               x86)))
  :otf-flg t
  :hints (("Goal"
           ;; :cases ((equal VALS2
           ;;                (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
           ;;                        (acl2::firstn (len vals1) (nthcdr (bvminus 48 ad1 ad2) vals2))
           ;;                        (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))))
           :use ( ;; (:instance write-bytes-of-append-gen
                 ;;            (ad ad1)
                 ;;            (vals1 (acl2::firstn (bvminus 48 ad1 ad2) vals2))
                 ;;            (vals2 (append (acl2::firstn (len vals1) (nthcdr (bvminus 48 ad1 ad2) vals2))
                 ;;                           (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))))
                 ;; (:instance write-bytes-of-append-gen
                 ;;            (ad (+ ad1 (bvminus 48 ad1 ad2)))
                 ;;            (vals1 (acl2::firstn (len vals1) (nthcdr (bvminus 48 ad1 ad2) vals2)))
                 ;;            (vals2 (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2)))
                 (:instance WRITE-BYTES-OF-WRITE-BYTES-DISJOINT
                            (X86 (WRITE-BYTES
                                  AD2
                                  (ACL2::TAKE (bvminus 48 ad1 ad2)
                                                  VALS2)
                                  X86))
                            (VALS1 (NTHCDR (+ (len vals1) (bvminus 48 ad1 ad2))
                                           VALS2))
                            (ADDR1 (+ AD1 (LEN VALS1)))
                            (VALS2 VALS1)
                            (ADDR2 AD1))
                 )
           :do-not-induct t
           :in-theory (e/d (WRITE-BYTES bvplus acl2::bvchop-of-sum-cases bvuminus bvminus ;ACL2::<-OF-IF-ARG1 ACL2::<-OF-IF-ARG2
                                        unsigned-byte-p
                                        )
                           (ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                            ;APPEND-TAKE-NTHCDR
                            ACL2::APPEND-OF-TAKE-AND-NTHCDR-2 ;compare to  LIST::APPEND-TAKE-NTHCDR
     ;write-bytes-of-append-gen write-bytes-of-append
                            ;LIST::EQUAL-APPEND-REDUCTION!
                            WRITE-BYTES-OF-WRITE-BYTES-DISJOINT
                            ACL2::TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                            )))))

(defthmd write-bytes-of-write-bytes-same-contained
  (implies (and (<= (+ (bvminus 48 ad1 ad2) (len vals1)) (len vals2))
                (< (len vals2) (expt 2 48)) ;gen?
                (< (len vals1) (expt 2 48)) ;gen?
                (integerp ad1)
                (integerp ad2)
                (true-listp vals2)
                (true-listp vals1)
                (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 ad2)
                )
           (equal (write-bytes ad1 vals1 (write-bytes ad2 vals2 x86))
                  (write-bytes ad2 (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                                          vals1
                                          (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))
                              x86)))
  :hints (("Goal" :use (write-bytes-of-write-bytes-same-contained-helper
                        write-bytes-of-write-bytes-same-contained-helper2)
           :in-theory nil)))

(defthmd write-bytes-of-write-bytes-same-contained-constants
  (implies (and (syntaxp (and (quotep ad1)
                              (quotep ad2)
                              (quotep vals1)
                              (quotep vals2)))
                (<= (+ (bvminus 48 ad1 ad2) (len vals1)) (len vals2))
                (< (len vals2) (expt 2 48)) ;gen?
                (< (len vals1) (expt 2 48)) ;gen?
                (integerp ad1)
                (integerp ad2)
                (true-listp vals2)
                (true-listp vals1)
                (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 ad2)
                )
           (equal (write-bytes ad1 vals1 (write-bytes ad2 vals2 x86))
                  (write-bytes ad2
                              ;; this whole thing gets computed:
                              (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                                          vals1
                                          (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))
                              x86)))
  :hints (("Goal" :use (write-bytes-of-write-bytes-same-contained-helper
                        write-bytes-of-write-bytes-same-contained-helper2)
           :in-theory nil)))

(defthmd write-byte-of-write-bytes-same-contained-constants
  (implies (and (syntaxp (and (quotep ad1)
                              (quotep ad2)
                              (quotep byte)
                              (quotep vals2)))
                (<= (+ (bvminus 48 ad1 ad2) 1) (len vals2))
                (< (len vals2) (expt 2 48)) ;gen?
                (integerp ad1)
                (integerp ad2)
                (true-listp vals2)
                (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 ad2)
                )
           (equal (write-byte ad1 byte (write-bytes ad2 vals2 x86))
                  (write-bytes ad2
                              ;; this whole thing gets computed:
                              (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                                          (list byte)
                                          (nthcdr (+ 1 (bvminus 48 ad1 ad2)) vals2))
                              x86)))
  :hints (("Goal" :use (:instance write-bytes-of-write-bytes-same-contained-constants (vals1 (list byte)))
           :in-theory (disable write-bytes-of-write-bytes-same-contained-constants))))
