; Redefinining functions from the x86isa model
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book redefines functions from the x86isa model in terms of our
;; functions, such as the BV functions.  Redefinitions that do not need any of
;; our functions should go into x86-changes.lisp.

(include-book "portcullis")
(include-book "projects/x86isa/machine/instructions/rotates-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/divide-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/xor-spec" :dir :system)
;(include-book "centaur/bitops/fast-rotate" :dir :system)
;(include-book "projects/x86isa/machine/get-prefixes" :dir :system)
(local (include-book "flags"))
;(include-book "kestrel/bv-lists/packbv" :dir :system)
;(include-book "kestrel/bv/bvshr" :dir :system)
;(include-book "kestrel/bv/bvchop" :dir :system)
;(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bvlt-def" :dir :system)
(include-book "kestrel/bv/sbvlt" :dir :system) ; reduce?
(include-book "kestrel/bv/bvdiv" :dir :system) ; reduce?
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system) ; reduce?
(include-book "kestrel/bv/bvsx" :dir :system) ; reduce?
(include-book "kestrel/bv/rightrotate" :dir :system)
;(local (include-book "kestrel/bv/sbvlt-rules" :dir :system))
(local (include-book "kestrel/bv/rules3" :dir :system)) ; for logext-of-bvsx
;(local (include-book "kestrel/bv/logext" :dir :system))
;(local (include-book "linear-memory"))
;(local (include-book "kestrel/bv/rules10" :dir :system)) ; todo, for floor-of-/-arg2
;(local (include-book "kestrel/bv/rules3" :dir :system)) ; todo, for logtail-of-one-more
;(local (include-book "kestrel/bv/logand-b" :dir :system))
;(local (include-book "kestrel/bv/logior-b" :dir :system))
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/bv/logapp" :dir :system)) ; for loghead-becomes-bvchop, todo
(local (include-book "kestrel/bv/bitops" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv/getbit" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p-forced-rules" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system)) ;prevent calls of expt on huge args
;; (local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
;; (local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
;; (local (include-book "kestrel/lists-light/take" :dir :system))
;; (local (include-book "kestrel/lists-light/cons" :dir :system))
;; (local (include-book "kestrel/lists-light/append" :dir :system))
;; (local (include-book "kestrel/lists-light/nthcdr" :dir :system))
;; (local (include-book "kestrel/lists-light/len" :dir :system))
;; (local (include-book "kestrel/lists-light/nth" :dir :system))
;; (local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;todo

(in-theory (disable mv-nth))

(local (in-theory (disable truncate)))

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

;; TODO: Other sizes.
(defthm ror-spec-64-alt-def
  (equal (ror-spec-64 x n rflags)
         (let* ((chopped-n (bvchop 6 n))
                (result-value (rightrotate 64 n x)) ; note the unchopped n here
                )
           (mv result-value
               ;; output flags:
               (if (equal chopped-n 0)
                   (bvchop 32 rflags)
                 (if (equal chopped-n 1)
                     ;; nicer than what the naive definition does?:
                     (!rflagsbits->cf
                       (getbit 0 x) ;(getbit 63 (rightrotate 64 1 x))
                       (!rflagsbits->of
                         (bitxor (getbit 0 x) ; (getbit 63 (rightrotate 64 1 x))
                                 (getbit 63 x) ; (getbit 62 (rightrotate 64 1 x))
                                 )
                         rflags))
                   (!rflagsbits->cf (getbit 63 result-value) rflags)))
               ;; undefined flags:
               (if (equal chopped-n 1) 0 2048))))
  :hints (("Goal" :in-theory (e/d (acl2::logapp-becomes-bvcat-when-bv
                                   x86isa::ror-spec-64
                                   !rflagsbits->cf
                                   !rflagsbits->of
                                   rflagsbits
                                   x86isa::rflagsbits-fix
                                   bitops::rotate-right-64
                                   rflagsbits->af
                                   rflagsbits->df
                                   rflagsbits->zf
                                   rflagsbits->res5
                                   rflagsbits->vm
                                   rflagsbits->iopl
                                   rflagsbits->id
                                   rflagsbits->tf
                                   rflagsbits->res3
                                   rflagsbits->vif
                                   rflagsbits->nt
                                   rflagsbits->sf
                                   rflagsbits->ac
                                   rflagsbits->rf
                                   rflagsbits->pf
                                   rflagsbits->res4
                                   rflagsbits->vip
                                   rflagsbits->res2
                                   rflagsbits->intf
                                   rflagsbits->res1
                                   acl2::slice-becomes-getbit
                                   acl2::logtail-of-bvchop-becomes-slice
                                   acl2::rightrotate-open-when-constant-shift-amount)
                                  (;;ACL2::EQUAL-OF-CONS-AND-CONS
                                   ;;ACL2::EQUAL-OF-CONS
                                   ;;X86ISA::PART-SELECT-WIDTH-LOW-BECOMES-SLICE
                                   ;;ACL2::LOGAPP-EQUAL-REWRITE
                                   )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this value is whether it overflows
;; todo: might be faster to not even reify this structure in the overflow case?
(defthm mv-nth-0-of-div-spec-8
  (equal (mv-nth 0 (div-spec-8 dst src))
         (if (bvlt 16 (+ -1 (expt 2 8))
                   (bvdiv 16 dst (bvchop 8 src)))
             (list (cons 'x86isa::quotient (bvdiv 16 dst (bvchop 8 src)))
                   (cons 'x86isa::remainder (bvmod 16 dst (bvchop 8 src))))
           nil))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-8
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the quotient
;; todo: letify?
(defthm mv-nth-1-of-div-spec-8
  (equal (mv-nth 1 (DIV-SPEC-8 dst src))
         (if (bvlt 16
                   (+ -1 (expt 2 8))
                   (bvdiv 16 DST (BVCHOP 8 SRC)))
             0
           (bvdiv 16 dst (bvchop 8 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-8
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the remainder
(defthm mv-nth-2-of-div-spec-8
  (equal (mv-nth 2 (DIV-SPEC-8 dst src))
         (if (bvlt 16
                   (+ -1 (expt 2 8))
                   (bvdiv 16 DST (BVCHOP 8 SRC)))
             0
           (bvmod 16 dst (bvchop 8 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-8
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; todo: rewrite the whole DIV-SPEC-8 call?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this value is whether it overflows
(defthm mv-nth-0-of-div-spec-16
  (equal (mv-nth 0 (DIV-SPEC-16 dst src))
         (if (bvlt 64
                   (+ -1 (expt 2 16))
                   (bvdiv 32 DST (BVCHOP 16 SRC)))
             (LIST (CONS 'x86isa::QUOTIENT
                         (bvdiv 32 dst (bvchop 16 src)))
                   (CONS 'x86ISA::REMAINDER
                         (bvmod 32 dst (bvchop 16 src))))
           nil))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-16
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the quotient
(defthm mv-nth-1-of-div-spec-16
  (equal (mv-nth 1 (DIV-SPEC-16 dst src))
         (if (bvlt 32
                   (+ -1 (expt 2 16))
                   (bvdiv 32 DST (BVCHOP 16 SRC)))
             0
           (bvdiv 32 dst (bvchop 16 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-16
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the remainder
(defthm mv-nth-2-of-div-spec-16
  (equal (mv-nth 2 (DIV-SPEC-16 dst src))
         (if (bvlt 32
                   (+ -1 (expt 2 16))
                   (bvdiv 32 DST (BVCHOP 16 SRC)))
             0
           (bvmod 32 dst (bvchop 16 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-16
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this value is whether it overflows
(defthm mv-nth-0-of-div-spec-32
  (equal (mv-nth 0 (DIV-SPEC-32 dst src))
         (if (bvlt 64
                   (+ -1 (expt 2 32))
                   (bvdiv 64 DST (BVCHOP 32 SRC)))
             (LIST (CONS 'x86isa::QUOTIENT
                         (bvdiv 64 dst (bvchop 32 src)))
                   (CONS 'x86ISA::REMAINDER
                         (bvmod 64 dst (bvchop 32 src))))
           nil))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-32
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the quotient
(defthm mv-nth-1-of-div-spec-32
  (equal (mv-nth 1 (DIV-SPEC-32 dst src))
         (if (bvlt 64
                   (+ -1 (expt 2 32))
                   (bvdiv 64 DST (BVCHOP 32 SRC)))
             0
           (bvdiv 64 dst (bvchop 32 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-32
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the remainder
(defthm mv-nth-2-of-div-spec-32
  (equal (mv-nth 2 (DIV-SPEC-32 dst src))
         (if (bvlt 64
                   (+ -1 (expt 2 32))
                   (bvdiv 64 DST (BVCHOP 32 SRC)))
             0
           (bvmod 64 dst (bvchop 32 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-32
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this value is whether it overflows
(defthm mv-nth-0-of-div-spec-64
  (equal (mv-nth 0 (DIV-SPEC-64 dst src))
         (if (bvlt 128
                   (+ -1 (expt 2 64))
                   (bvdiv 128 DST (BVCHOP 64 SRC)))
             (LIST (CONS 'x86isa::QUOTIENT
                         (bvdiv 128 dst (bvchop 64 src)))
                   (CONS 'x86ISA::REMAINDER
                         (bvmod 128 dst (bvchop 64 src))))
           nil))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-64
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the quotient
(defthm mv-nth-1-of-div-spec-64
  (equal (mv-nth 1 (DIV-SPEC-64 dst src))
         (if (bvlt 128
                   (+ -1 (expt 2 64))
                   (bvdiv 128 DST (BVCHOP 64 SRC)))
             0
           (bvdiv 128 dst (bvchop 64 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-64
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the remainder
(defthm mv-nth-2-of-div-spec-64
  (equal (mv-nth 2 (DIV-SPEC-64 dst src))
         (if (bvlt 128
                   (+ -1 (expt 2 64))
                   (bvdiv 128 DST (BVCHOP 64 SRC)))
             0
           (bvmod 128 dst (bvchop 64 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-64
                                   bvdiv
                                   bvmod
                                   bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: add versions for other sizes

;; Puts in bv functions
(defthm mv-nth-0-of-idiv-spec-32
  (equal (mv-nth 0 (idiv-spec-32 dst src))
         (let ((res (acl2::sbvdiv 64 dst (acl2::bvsx 64 32 src))))
           (if (acl2::sbvlt 64 res -2147483648)
               (LIST (CONS 'x86isa::QUOTIENT-INT
                           (TRUNCATE (LOGEXT 64 DST)
                                     (LOGEXT 32 SRC)))
                     (CONS 'x86ISA::REMAINDER-INT
                           (REM (LOGEXT 64 DST) (LOGEXT 32 SRC))))
             (if (acl2::sbvlt 64 2147483647 res)
                 (LIST (CONS 'x86isa::QUOTIENT-INT
                             (TRUNCATE (LOGEXT 64 DST)
                                       (LOGEXT 32 SRC)))
                       (CONS 'x86ISA::REMAINDER-INT
                             (REM (LOGEXT 64 DST) (LOGEXT 32 SRC))))
               nil))))
  :hints (("Goal" :in-theory (e/d (idiv-spec-32 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

(defthm mv-nth-1-of-idiv-spec-32
  (equal (mv-nth 1 (idiv-spec-32 dst src))
         (let ((res (acl2::sbvdiv 64 dst (acl2::bvsx 64 32 src))))
           (if (acl2::sbvlt 64 res -2147483648)
               0
             (if (acl2::sbvlt 64 2147483647 res)
                 0
               (bvchop 32 res)))))
  :hints (("Goal" :in-theory (e/d (idiv-spec-32 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))


(defthm mv-nth-0-of-idiv-spec-64
  (equal (mv-nth 0 (idiv-spec-64 dst src))
         (let ((res (acl2::sbvdiv 128 dst (acl2::bvsx 128 64 src))))
           (if (acl2::sbvlt 128 res (- (expt 2 63)))
               (LIST (CONS 'x86isa::QUOTIENT-INT
                           (TRUNCATE (LOGEXT 128 DST)
                                     (LOGEXT 64 SRC)))
                     (CONS 'x86ISA::REMAINDER-INT
                           (REM (LOGEXT 128 DST) (LOGEXT 64 SRC))))
             (if (acl2::sbvlt 128 (+ -1 (expt 2 63)) res)
                 (LIST (CONS 'x86isa::QUOTIENT-INT
                             (TRUNCATE (LOGEXT 128 DST)
                                       (LOGEXT 64 SRC)))
                       (CONS 'x86ISA::REMAINDER-INT
                             (REM (LOGEXT 128 DST) (LOGEXT 64 SRC))))
               nil))))
  :hints (("Goal" :in-theory (e/d (idiv-spec-64 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

;todo: add versions for other sizes
(defthm mv-nth-1-of-idiv-spec-64
  (equal (mv-nth 1 (idiv-spec-64 dst src))
         (let ((res (acl2::sbvdiv 128 dst (acl2::bvsx 128 64 src))))
           (if (acl2::sbvlt 128 res (- (expt 2 63)))
               0
             (if (acl2::sbvlt 128 (+ -1 (expt 2 63)) res)
                 0
               (bvchop 64 res)))))
  :hints (("Goal" :in-theory (e/d (idiv-spec-64 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

;; reduces the number of rules needed for symbolic execution of a single xor from ~220 to ~200
(defthm gpr-xor-spec-8-alt-def-axe
  (equal (x86isa::gpr-xor-spec-8 dst src input-rflags)
         (b* (;(dst (bvchop 64 dst))
              ;(src (bvchop 64 src))
              ;(input-rflags (bvchop 32 input-rflags))
              (result (bvxor 64 dst src))
              (cf 0)
              (pf (pf-spec64 result))
              (zf (zf-spec result))
              (sf (sf-spec64 result))
              (of 0)
              ;; doesn't really matter how we phrase this, as write-user-rflags will extract the relevant flags:
              ;; todo: some better way to deal with this, avoiding a term whose size is proportional to the number of flags?
              (x86isa::output-rflags (change-rflagsbits input-rflags
                                                        :cf cf
                                                        :pf pf
                                                        :zf zf
                                                        :sf sf
                                                        :of of))
              (x86isa::undefined-flags 16 ;(!rflagsbits->af 1 0)
                                       ))
           (mv result x86isa::output-rflags x86isa::undefined-flags)))
  :hints (("Goal" :in-theory (acl2::e/d* (x86isa::gpr-xor-spec-8 x86isa::rflag-rows-enables bvxor)
                                         ((tau-system))))))
