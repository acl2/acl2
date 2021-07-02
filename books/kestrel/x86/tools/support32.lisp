; Utilities in support of reasoning about / lifting 32-bit code.
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "support-x86")
(include-book "linear-memory")
(include-book "flags" )
(include-book "register-readers-and-writers")
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(local (include-book "kestrel/bv-lists/packbv-theorems" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/bv/arith" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop, for floor-mod-elim
(local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;todo

;for speed:
(local (in-theory (disable acl2::slice-too-high-is-0-new
                           ;;acl2::unsigned-byte-p-logior
                           ;;acl2::unsigned-byte-p-from-bounds
                           ;;acl2::rewrite-unsigned-byte-p-when-term-size-is-larger
                           bitops::logior-<-0-linear-2
                           bitops::ash-<-0
                           acl2::<-of-logior-and-0
                           acl2::unsigned-byte-p-of-ash
                           acl2::signed-byte-p-when-unsigned-byte-p
                           acl2::unsigned-byte-p-of-logior
                           bitops::signed-byte-p-of-ash-split
                           ;; acl2::signed-byte-p-logops
                           )))

(defthm segment-base-and-bounds-of-set-flag
  (equal (segment-base-and-bounds proc-mode seg-reg (x::set-flag flg val x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (e/d (segment-base-and-bounds
                                   x::set-flag)
                                  (;; x86isa::seg-hidden-basei-is-n64p
                                   ;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-attri-is-n16p
                                   )))))

(defthm data-segment-descriptor-attributesbits->w-of-bvchop
  (equal (x86isa::data-segment-descriptor-attributesbits->w (bvchop 16 attr))
         (x86isa::data-segment-descriptor-attributesbits->w attr))
  :hints (("Goal" :in-theory (enable x86isa::data-segment-descriptor-attributesbits->w
                                     x86isa::data-segment-descriptor-attributesbits-fix
                                     bvchop))))

(defthm code-segment-descriptor-attributesbits->r-of-bvchop
  (equal (x86isa::code-segment-descriptor-attributesbits->r (bvchop 16 attr))
         (x86isa::code-segment-descriptor-attributesbits->r attr))
  :hints (("Goal" :in-theory (enable x86isa::code-segment-descriptor-attributesbits->r
                                     x86isa::code-segment-descriptor-attributesbits-fix
                                     bvchop))))

;;todo: why is the bvchop being done?  it's in SEGMENT-BASE-AND-BOUNDS.
(defthm data-segment-descriptor-attributesbits->e-of-bvchop
  (equal (x86isa::data-segment-descriptor-attributesbits->e (bvchop 16 attr))
         (x86isa::data-segment-descriptor-attributesbits->e attr))
  :hints (("Goal" :in-theory (enable x86isa::data-segment-descriptor-attributesbits->e
                                     x86isa::data-segment-descriptor-attributesbits-fix
                                     bvchop))))

(defthm data-segment-descriptor-attributesbits->d/b-of-bvchop
  (equal (x86isa::data-segment-descriptor-attributesbits->d/b (bvchop 16 attr))
         (x86isa::data-segment-descriptor-attributesbits->d/b attr))
  :hints (("Goal" :in-theory (enable x86isa::data-segment-descriptor-attributesbits->d/b
                                     x86isa::data-segment-descriptor-attributesbits-fix
                                     bvchop))))



;(in-theory (disable ACL2::UNSIGNED-BYTE-P-LOGIOR)) ;forcing

;dup
(defthm x86isa::canonical-address-p-when-unsigned-byte-p
  (implies (unsigned-byte-p 47 x86isa::ad)
           (canonical-address-p x86isa::ad))
  :hints (("Goal" :in-theory (enable canonical-address-p))))

;;gen
(defthm bvplus-subst-smaller-term
  (implies (and (equal (bvchop 32 x) (bvchop 32 x2))
                (syntaxp (acl2::smaller-termp x2 x)))
           (equal (bvplus 32 x y)
                  (bvplus 32 x2 y))))

;dup in bv3
(defthmd acl2::bvplus-recollapse
  (implies (and (integerp x) (integerp y))
           (equal (bvchop acl2::size (+ x y))
                  (bvplus acl2::size x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

;(local (in-theory (disable X86ISA::MEMI-IS-N08P))) ;does forcing

;move
(defthm integerp-of-xr-mem
  (implies (x86p x86)
           (integerp (xr :mem acl2::i x86)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance x86isa::unsigned-byte-p-of-xr-of-mem (size 8))
           :in-theory (disable x86isa::unsigned-byte-p-of-xr-of-mem))))

;;;
;;; seg-regp
;;;

;; Recognize a numeric name for a segment (e.g., 1 for the code segment)
;; TODO: Why the "reg" in this name?
(defund seg-regp (seg-reg)
  (declare (xargs :guard t))
  (integer-range-p 0 *segment-register-names-len* seg-reg))

(defthm <-6-when-seg-regp
  (implies (seg-regp seg-reg)
           (< seg-reg 6))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable seg-regp))))

(defthm natp-when-seg-regp
  (implies (seg-regp seg-reg)
           (natp seg-reg))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable seg-regp))))

;;;
;;; the expand-down-bit
;;;

(defund segment-expand-down-bit (seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (seg-regp seg-reg)))
  (if (equal *cs* seg-reg)
      0 ;code segment is always expand-up
    ;; anything other than a code segment (including a stack segment) is treated like a data sgement:
    (x86isa::data-segment-descriptor-attributesbits->e (seg-hidden-attri seg-reg x86))))

(defthm segment-expand-down-bit-intro
  (implies (not (equal *cs* seg-reg))
           (equal (x86isa::data-segment-descriptor-attributesbits->e (xr :seg-hidden-attr seg-reg x86))
                  (segment-expand-down-bit seg-reg x86)))
  :hints (("Goal" :in-theory (enable segment-expand-down-bit))))

(theory-invariant (incompatible (:definition segment-expand-down-bit) (:rewrite segment-expand-down-bit-intro)))

(defthm segment-expand-down-bit-of-xw-irrel
  (implies (not (equal fld :seg-hidden-attr))
           (equal (segment-expand-down-bit seg-reg1 (xw fld index val x86))
                  (segment-expand-down-bit seg-reg1 x86)))
  :hints (("Goal" :in-theory (e/d (segment-expand-down-bit)
                                  (segment-expand-down-bit-intro)))))

;;;
;;; segment-base32
;;;

;; The "base" address of a 32-bit segment.  This is a linear address. Note that
;; this is *not* necessarily the smallest linear address in the segment, since
;; it might be an expand-down segment, in which case the legal addresses are
;; below the base.  This assumes we are in *compatibility-mode* (see comment
;; above).
(defun segment-base32 (seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (seg-regp seg-reg)))
  (b* (((mv base & &)
        (segment-base-and-bounds *compatibility-mode* seg-reg x86)))
     base))

;;;
;;; segment-min-eff-addr32
;;;

;; The minimum valid effective address in the segment. This assumes we are in
;; *compatibility-mode* (see comment above).
(defund segment-min-eff-addr32 (seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (seg-regp seg-reg)))
  (b* (((mv & lower &)
        (segment-base-and-bounds *compatibility-mode* seg-reg x86)))
    lower))

;; The minimum effective address of an expand-up segment is 0.
(defthm segment-min-eff-addr32-when-expand-up
  (implies (equal (segment-expand-down-bit seg-reg x86) 0)
           (equal (segment-min-eff-addr32 seg-reg x86)
                  0))
  :hints (("Goal" :in-theory (e/d (segment-min-eff-addr32
                                   segment-base-and-bounds
                                   ACL2::MOD-OF-EXPT-OF-2-CONSTANT-VERSION)
                                  (;; x86isa::seg-hidden-basei-is-n64p
                                   ;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-attri-is-n16p
                                   )))))

;; The minimum effective address of an expand-down segment
(defthm segment-min-eff-addr32-when-expand-down
  (implies (equal (segment-expand-down-bit seg-reg x86) 1)
           (equal (segment-min-eff-addr32 seg-reg x86)
                  (if (equal seg-reg *cs*)
                      0
                    ;; what if this overflows?:
                    (+ 1
                       (bvchop 32 (xr :seg-hidden-limit seg-reg x86))))))
  :hints (("Goal" :in-theory (e/d (segment-min-eff-addr32
                                   segment-base-and-bounds
                                   acl2::mod-of-expt-of-2-constant-version)
                                  (;; x86isa::seg-hidden-basei-is-n64p
                                   ;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-attri-is-n16p
                                   )))))

(defthm segment-min-eff-addr32-of-xw
  (implies (and (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (segment-min-eff-addr32 seg-reg (xw fld index val x86))
                  (segment-min-eff-addr32 seg-reg x86)))
  :hints (("Goal" :in-theory (enable SEGMENT-MIN-EFF-ADDR32))))

(defthm segment-min-eff-addr32-of-set-flag
  (equal (segment-min-eff-addr32 seg-reg (set-flag flg val x86))
         (segment-min-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (e/d (set-flag)
                                  ()))))

(defthm natp-of-segment-min-eff-addr32
  (implies (and (seg-regp seg-reg)
                (x86p x86))
           (natp (segment-min-eff-addr32 seg-reg x86)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable segment-min-eff-addr32))))

;;;
;;; segment-max-eff-addr32
;;;

;; The maximum valid effective address in the segment. This assumes we are in
;; *compatibility-mode* (see comment above).
(defund segment-max-eff-addr32 (seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (seg-regp seg-reg)))
  (b* (((mv & & upper)
        (segment-base-and-bounds *compatibility-mode* seg-reg x86)))
    upper))

(defthm segment-max-eff-addr32-of-xw
  (implies (and (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (segment-max-eff-addr32 seg-reg (xw fld index val x86))
                  (segment-max-eff-addr32 seg-reg x86)))
  :hints (("Goal" :in-theory (enable SEGMENT-MAX-EFF-ADDR32))))

(defthm segment-max-eff-addr32-of-set-flag
  (equal (segment-max-eff-addr32 seg-reg (set-flag flg val x86))
         (segment-max-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (e/d (set-flag) ()))))

(defthm natp-of-segment-max-eff-addr32
  (implies (and (seg-regp seg-reg)
                (x86p x86))
           (natp (segment-max-eff-addr32 seg-reg x86)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable segment-max-eff-addr32))))

;;;
;;; segment-is-32-bitsp
;;;

;; Check whether the segment is a 32-bit segment, not a 16-bit segment.
(defund segment-is-32-bitsp (seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (seg-regp seg-reg)))
  (if (equal *cs* seg-reg)
      (equal 1 (x86isa::code-segment-descriptor-attributesbits->d (seg-hidden-attri seg-reg x86)))
    (equal 1 (x86isa::data-segment-descriptor-attributesbits->d/b (seg-hidden-attri seg-reg x86)))))

(acl2::add-known-boolean segment-is-32-bitsp)

(defthm segment-is-32-bitsp-intro-code
  (equal (x86isa::code-segment-descriptor-attributesbits->d (xr :seg-hidden-attr *cs* x86))
         (if (segment-is-32-bitsp *cs* x86)
             1
           0))
  :hints (("Goal" :in-theory (enable segment-is-32-bitsp
                                     x86isa::code-segment-descriptor-attributesbits->d))))

;; For any seg-reg other than *cs*.
(defthm segment-is-32-bitsp-intro-data
  (implies (not (equal *cs* seg-reg))
           (equal (x86isa::data-segment-descriptor-attributesbits->d/b (xr :seg-hidden-attr seg-reg x86))
                  (if (segment-is-32-bitsp seg-reg x86)
                      1
                    0)))
  :hints (("Goal" :in-theory (enable segment-is-32-bitsp
                                     x86isa::data-segment-descriptor-attributesbits->d/b))))

(defthm segment-is-32-bitsp-of-xw-irrel
  (implies (not (equal :seg-hidden-attr fld))
           (equal (segment-is-32-bitsp seg-reg (xw fld index val x86))
                  (segment-is-32-bitsp seg-reg x86)))
  :hints (("Goal" :in-theory (e/d (segment-is-32-bitsp)
                                  (;segment-is-32-bitsp-intro-1
                                   ;segment-is-32-bitsp-intro-2
                                   )))))

(defthm segment-is-32-bitsp-of-set-flag
  (equal (segment-is-32-bitsp seg-reg (set-flag flg val x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (e/d (segment-is-32-bitsp) ()))))

;todo: rename?
;; Returns the lowest address in the given segment (a linear address) and the
;; size of the segment in bytes.  See also SEGMENT-BASE-AND-BOUNDS.
(defund 32-bit-segment-start-and-size (seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (seg-regp seg-reg)))
  (b* (;(hidden (xr :seg-hidden seg-reg x86))
       (base (seg-hidden-basei seg-reg x86) ;(bvchop 32 (x86isa::hidden-seg-reg-layout-slice :base-addr hidden))
             ) ;base should only be 32-bits, right?
       (limit (seg-hidden-limiti seg-reg x86) ;(x86isa::hidden-seg-reg-layout-slice :limit hidden)
              )
       (attr (seg-hidden-attri seg-reg x86) ;(x86isa::hidden-seg-reg-layout-slice :attr hidden)
             )
       (d/b (if (equal *cs* seg-reg)
                (x86isa::code-segment-descriptor-attributesbits->d attr)
              (x86isa::data-segment-descriptor-attributesbits->d/b attr)))
       (e (if (equal *cs* seg-reg)
              0 ;code segment is always expand-up ;(x86isa::code-segment-descriptor-attributesbits->e attr)
            (x86isa::data-segment-descriptor-attributesbits->e attr)))
       ;; the smallest legal effective address:
       (lower (if (= e 1) (1+ limit) 0))
       ;; the largest legal effective address:
       (upper (if (= e 1)
                  (if (= d/b 1) 4294967295 65535)
                limit))
       (size (+ 1 (- upper lower)))
       (start (if (= e 1)
                  (bvplus 32 base lower)
                (+ base lower))))
    (mv start size)))

(defthm natp-of-mv-nth-1-of-32-bit-segment-start-and-size
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (x86p x86))
           (natp (mv-nth 1 (32-bit-segment-start-and-size seg-reg x86))))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start-and-size))))

(defthm integerp-of-mv-nth-0-of-32-bit-segment-start-and-size
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (x86p x86))
           (integerp (mv-nth 0 (32-bit-segment-start-and-size seg-reg x86))))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start-and-size))))

;; An expand down segment can't have size 2^32.
(defthmd stack-segment-max-size-2
  (implies (and (equal (segment-expand-down-bit seg-reg x86) 1)
                (not (equal *cs* seg-reg)) ;*cs* is always expand up
                )
           (not (equal (cadr (32-bit-segment-start-and-size seg-reg x86))
                       4294967296)))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start-and-size))))

;; An expand down segment can have size 2^32-1, and that's the best we can do.
(defthmd stack-segment-max-size
  (implies (and (segment-is-32-bitsp *ss* x86)
                (equal (segment-expand-down-bit *ss* x86) 1)
                (equal (xr :seg-hidden-limit 2 x86) 0) ;to max the size
                )
           (equal (cadr (32-bit-segment-start-and-size *ss* x86))
                  4294967295))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start-and-size))))

(defund 32-bit-segment-size (seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (seg-regp seg-reg)))
  (+ 1 (- (segment-max-eff-addr32 seg-reg x86)
          (segment-min-eff-addr32 seg-reg x86))))

;just as a cross check
(defthmd 32-bit-segment-size-matches-cadr-of-32-bit-segment-start-and-size
  (equal (32-bit-segment-size seg-reg x86)
         (cadr (32-bit-segment-start-and-size seg-reg x86)))
  :hints (("Goal" :in-theory (enable 32-bit-segment-size
                                     32-bit-segment-start-and-size
                                     segment-max-eff-addr32
                                     segment-min-eff-addr32
                                     segment-base-and-bounds))))

(defthm 32-bit-segment-size-of-xw
  (implies (and (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal :msr fld)))
           (equal (32-bit-segment-size code (xw fld index val x86))
                  (32-bit-segment-size code x86)))
  :hints (("Goal" :in-theory (enable 32-bit-segment-size))))

(defthm unsigned-byte-p-of-xr-of-seg-hidden-limit
  (implies (and ;(equal (segment-expand-down-bit seg-reg x86) 1)
                (segment-is-32-bitsp seg-reg x86)
                (x86p x86))
           (unsigned-byte-p 32 (xr :seg-hidden-limit seg-reg x86))))

(defthm xr-of-seg-hidden-limit-type
  (implies (and ;(equal (segment-expand-down-bit seg-reg x86) 1)
            (segment-is-32-bitsp seg-reg x86)
            (x86p x86))
           (natp (xr :seg-hidden-limit seg-reg x86)))
  :rule-classes :type-prescription)

(defthm eff-addr-bounds
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (< 0 (32-bit-segment-size seg-reg x86)) ;give us: (not (equal (xr :seg-hidden-limit seg-reg x86) 4294967295)) ;why?
                (x86p x86))
           (<= (segment-min-eff-addr32 seg-reg x86) (segment-max-eff-addr32 seg-reg x86)))
  :hints (("Goal" :in-theory (enable segment-min-eff-addr32 segment-max-eff-addr32 segment-base-and-bounds 32-BIT-SEGMENT-SIZE))))

(defthm eff-addr-bounds2
  (implies (and (segment-is-32-bitsp seg-reg x86)
;                (< 0 (32-bit-segment-size seg-reg x86)) ;give us: (not (equal (xr :seg-hidden-limit seg-reg x86) 4294967295)) ;why?
                (x86p x86))
           (<= (+ -1 (segment-min-eff-addr32 seg-reg x86)) (segment-max-eff-addr32 seg-reg x86)))
  :hints (("Goal" :in-theory (enable segment-min-eff-addr32 segment-max-eff-addr32 segment-base-and-bounds 32-BIT-SEGMENT-SIZE
                                     ))))

(defthm natp-of-32-bit-segment-size
  (implies (and (seg-regp seg-reg)
                (segment-is-32-bitsp seg-reg x86)
                (x86p x86))
           (natp (32-bit-segment-size seg-reg x86)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance eff-addr-bounds2)
           :in-theory (e/d (32-bit-segment-size) (eff-addr-bounds2)))))

;; A linear address
(defund 32-bit-segment-start (seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (seg-regp seg-reg)))
  (mv-let (start size)
    (32-bit-segment-start-and-size seg-reg x86)
    (declare (ignore size))
    start))

(defthm natp-of-32-bit-segment-start
  (implies (and (seg-regp seg-reg)
                (x86p x86))
           (natp (32-bit-segment-start seg-reg x86)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable 32-bit-segment-start 32-bit-segment-start-and-size))))

(defthm 32-bit-segment-start-of-xw
  (implies (and (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal :msr fld)))
           (equal (32-bit-segment-start code (xw fld index val x86))
                  (32-bit-segment-start code x86)))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start
                                     32-bit-segment-start-and-size))))

;; Read the byte at effective address EFF-ADDR in the segment indicated by
;; SEG-REG.  Just read the byte, don't do any checking.
;todo: should this take the eff-addr mod the size of the segment?
;todo: chop to 8 bits?
(defund read-byte-from-segment (eff-addr seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (and (seg-regp seg-reg)
                              (integerp eff-addr))))
  (let ((base (segment-base32 seg-reg x86)))
    ;; The ifix is so we don't need to know x86p when rewriting to this:
    (ifix (memi (bvchop 32 (+ base eff-addr)) x86))
    ;; The bvchop is for the guard proof:
    ;;(ifix (memi (bvchop 52 (+ base eff-addr)) x86))
    ))

;; Read N bytes, starting at EFF-ADDR, from the segment indicated by SEG-REG.
;; Returns a list of bytes
(defun read-byte-list-from-segment (n eff-addr seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (and (seg-regp seg-reg)
                              (integerp eff-addr)
                              (natp n))))
  (if (zp n)
      nil
    (cons (read-byte-from-segment eff-addr seg-reg x86)
          (read-byte-list-from-segment (- n 1) (+ 1 eff-addr) seg-reg x86))))

;TODO: Add a function to read several bytes into a large BV.

(local
 (defun read-byte-list-from-segment-induct (n i eff-addr)
   (if (or (zp n)
           (zp i))
       (list n i eff-addr)
     (read-byte-list-from-segment-induct (- n 1) (- i 1) (+ 1 eff-addr)))))

(defthm nth-of-read-byte-list-from-segment
  (implies (and (natp n)
                (natp i)
                (< i n)
                (natp eff-addr))
           (equal (nth i (read-byte-list-from-segment n eff-addr seg-reg x86))
                  (read-byte-from-segment (+ i eff-addr) seg-reg x86)))
  :hints (("Goal" ;:in-theory (enable list::nth-of-cons) ;could put this back but need the list package
           :in-theory (e/d (nth) (;ACL2::NTH-OF-CDR
                                  ))
           :expand (READ-BYTE-LIST-FROM-SEGMENT N EFF-ADDR SEG-REG X86)
           :induct (read-byte-list-from-segment-induct n i eff-addr))))

;;can loop?
(defthmd read-byte-from-segment-when-equal-of-read-byte-list-from-segment
  (implies (and (equal (read-byte-list-from-segment n eff-addr2 seg-reg x86)
                       code)
                ;(syntaxp (quotep code))
                (<= eff-addr2 eff-addr)
                (< (- eff-addr eff-addr2) n)
                (natp n)
                (natp eff-addr)
                (natp eff-addr2))
           (equal (read-byte-from-segment eff-addr seg-reg x86)
                  (nth (- eff-addr eff-addr2)
                       code))))

(defthm read-byte-from-segment-when-equal-of-read-byte-list-from-segment-quotep
  (implies (and (equal (read-byte-list-from-segment n eff-addr2 seg-reg x86)
                       code)
                (syntaxp (quotep code))
                (<= eff-addr2 eff-addr)
                (< (- eff-addr eff-addr2) n)
                (natp n)
                (natp eff-addr)
                (natp eff-addr2))
           (equal (read-byte-from-segment eff-addr seg-reg x86)
                  (nth (- eff-addr eff-addr2)
                       code))))

;prove that this follows from the code and stack segment preds
;todo: what about expand down segments?  maybe those are covered here too
(defun well-formed-32-bit-segmentp (seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (and (seg-regp seg-reg)
                              (segment-is-32-bitsp seg-reg x86))))
  (and (unsigned-byte-p 32 (seg-hidden-basei seg-reg x86))
       (not (< (seg-visiblei seg-reg x86) 4))
       (<= (+ (32-bit-segment-start seg-reg x86)
              (32-bit-segment-size seg-reg x86))
           (expt 2 32))))

;todo: rename
(defthm seg-visible-not-equal-0-when-well-formed-32-bit-segmentp
  (implies (well-formed-32-bit-segmentp seg-reg x86)
           (not (< (xr :seg-visible seg-reg x86) 4))))

(acl2::add-known-boolean well-formed-32-bit-segmentp)

;;;
;;; code-segment-readable-bit
;;;

;; Check whether a code segment is readable.
(defund code-segment-readable-bit (x86)
  (declare (xargs :stobjs x86))
  (x86isa::code-segment-descriptor-attributesbits->r (seg-hidden-attri *cs* x86)))

(defthm code-segment-readable-bit-intro
  (equal (x86isa::code-segment-descriptor-attributesbits->r (xr :seg-hidden-attr *cs* x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable code-segment-readable-bit))))

(theory-invariant (incompatible (:definition code-segment-readable-bit) (:rewrite code-segment-readable-bit-intro)))

(defthm code-segment-readable-bit-of-xw-irrel
  (implies (not (equal :seg-hidden-attr fld))
           (equal (code-segment-readable-bit (xw fld index val x86))
                  (code-segment-readable-bit x86)))
  :hints (("Goal" :in-theory (e/d (code-segment-readable-bit)
                                  (code-segment-readable-bit-intro)))))

(defthm code-segment-readable-bit-of-set-flag
  (equal (code-segment-readable-bit (set-flag flg val x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (e/d (code-segment-readable-bit) (code-segment-readable-bit-intro)))))

;;;
;;; code-segment-well-formedp
;;;

;; These do not depend on the code itself:
;; TODO: Maybe add 32 to the name.
(defund code-segment-well-formedp (x86)
  (declare (xargs :stobjs x86))
  (and (segment-is-32-bitsp *cs* x86) ;; The code segment is a 32-bit segment, not 16-bit:
       (well-formed-32-bit-segmentp *cs* x86)
       ;; The code segment is expand-up: the expand-down (e) bit is 0:
       (equal (segment-expand-down-bit *cs* x86) 0)

       ;; The code segment is readable:
       (equal (code-segment-readable-bit x86) 1)
       (let ;; The code segment begins at some unknown (linear) address:
           ((code-segment-base (seg-hidden-basei *cs* x86)))
         (unsigned-byte-p 32 code-segment-base) ;needed?
         )))

(defthm segment-is-32-bitsp-when-code-segment-well-formedp
  (implies (code-segment-well-formedp x86)
           (segment-is-32-bitsp *cs* x86))
  :hints (("Goal" :in-theory (enable code-segment-well-formedp))))

(defthm well-formed-32-bit-segmentp-when-code-segment-well-formedp
  (implies (code-segment-well-formedp x86)
           (well-formed-32-bit-segmentp *cs* x86))
  :hints (("Goal" :in-theory (enable code-segment-well-formedp))))

(defthm code-segment-readable-bit-when-code-segment-well-formedp
  (implies (code-segment-well-formedp x86)
           (equal (code-segment-readable-bit x86)
                  1))
  :hints (("Goal" :in-theory (enable code-segment-well-formedp))))

(defthm segment-expand-down-bit-of-cs-when-code-segment-well-formedp
  (implies (code-segment-well-formedp x86)
           (equal (segment-expand-down-bit *cs* x86)
                  0))
  :hints (("Goal" :in-theory (enable code-segment-well-formedp))))

;;;
;;; code-segment-assumptions32-for-code
;;;

;todo: Do we need to say something about the base+limit not overflowing?
;; Says that CODE is present in the code segment, starting at OFFSET.
(defund code-segment-assumptions32-for-code (code
                                             offset ; offset to the code from the base of the code segment
                                             x86)
  (declare (xargs :stobjs x86
                  :guard (and (natp offset)
                              (true-listp code)
                              (acl2::all-unsigned-byte-p 8 code))))
  (let ( ;; The code segment limit (an offset from the base of the code
        ;; segment) is some unknown amount large enough for the code
        ;; to fit:
        (code-segment-limit (seg-hidden-limiti *cs* x86))
        (last-byte (+ offset (+ -1 (len code)))))
    (and
     ;;(unsigned-byte-p 32 code-segment-limit) ;implied by the above

     ;; The code-segment-limit is large enough for the code to fit in the code segment:
     (<= last-byte code-segment-limit)

     ;; The program is loaded, starting at the base of the code segment:
     ;; todo: gen this to indicate some offset from the code-segment-base and constrain the PC to start there.
     (equal (read-byte-list-from-segment (len code)
                                         offset
                                         *cs* x86)
            code))))

(defthm read-byte-from-segment-when-code-segment-assumptions32-for-code
  (implies (and (code-segment-assumptions32-for-code code offset x86)
                ;(syntaxp (quotep code))
                (<= offset eff-addr)
                (< eff-addr (+ offset (len code)))
                (natp offset)
                (natp eff-addr))
           (equal (read-byte-from-segment eff-addr *cs* x86)
                  (nth (- eff-addr offset) code)))
  :hints (("Goal" :use (:instance read-byte-from-segment-when-equal-of-read-byte-list-from-segment
                                  (eff-addr2 offset)
                                  (seg-reg *cs*)
                                  (n (len code))
                                  )
           :in-theory (e/d (code-segment-assumptions32-for-code)
                           (read-byte-from-segment-when-equal-of-read-byte-list-from-segment)))))

;; Get the 32-bit instruction pointer:
(defun eip (x86)
  (declare (xargs :stobjs x86))
  (rip x86))

;; Turn a call of read-*ip into a call of EIP, which is a much simpler function
;; Do we need the bvchop?
(defthm read-*ip-becomes-eip
  (implies (segment-is-32-bitsp *cs* x86)
           (equal (x86isa::read-*ip *compatibility-mode* x86)
                  (bvchop 32 (eip x86))))
  :hints (("Goal" :in-theory (enable x86isa::read-*ip bvchop))))

;; Converting a valid effective address in the code segment to a linear address returns no error:
(defthm not-mv-nth-0-of-ea-to-la-of-cs
  (implies (and (not (64-bit-modep x86))
                (code-segment-assumptions32-for-code code offset x86) ;code is a free var and usually will be a constant
                (< eff-addr (+ offset (len code)))
                (<= offset eff-addr)
                (integerp eff-addr)
                (natp offset)
                (x86p x86) ;drop?
                )
           (not (mv-nth 0 (ea-to-la *compatibility-mode* eff-addr *cs* 1 x86))))
  :hints (("Goal" :in-theory (e/d (code-segment-assumptions32-for-code
                                   segment-base-and-bounds) ()))))

;; ;; Under suitable assumptions, we turn rme08 into a call of read-byte-from-segment, which is a much simpler function
;; (defthm mv-nth-1-of-rme08-of-cs-becomes-read-byte-from-segment
;;   (implies (and (not (64-bit-modep x86))
;;                 (app-view x86)
;;                 (code-segment-assumptions32 code x86) ;code is a free var and usually will be a constant
;;                 (< eff-addr (len code))
;;                 (<= 0 eff-addr)
;;                 (integerp eff-addr)
;;                 (X86P X86) ;drop?
;;                 )
;;            (equal (mv-nth 1 (x86isa::rme08 *compatibility-mode* eff-addr *cs* r-x x86))
;;                   (read-byte-from-segment eff-addr *cs* x86)))
;;   :hints (("Goal" :expand (RB-1 1
;;                                 (BVCHOP 32
;;                                          (+ EFF-ADDR (XR :SEG-HIDDEN-BASE 1 X86)))
;;                                 R-X X86)
;;            :in-theory (e/d (x86isa::rme08 segment-base-and-bounds rb rb-1 rvm08 n48 read-byte-from-segment) ()))))

;; (defthm mv-nth-1-of-rme08-of-cs-becomes-read-byte-from-segment-gen
;;   (implies (and (not (64-bit-modep x86))
;;                 (app-view x86)
;;                 (code-segment-assumptions32 code x86-2) ;code is a free var and usually will be a constant
;;                 (code-segment-assumptions32 code x86) ;code is a free var and usually will be a constant
;;                 (< eff-addr (len code))
;;                 (<= 0 eff-addr)
;;                 (integerp eff-addr)
;;                 (X86P X86) ;drop?
;;                 )
;;            (equal (mv-nth 1 (x86isa::rme08 *compatibility-mode* eff-addr *cs* r-x x86))
;;                   (read-byte-from-segment eff-addr *cs* x86)))
;;   :hints (("Goal" :expand (RB-1 1
;;                                 (BVPLUS 32 EFF-ADDR (XR :SEG-HIDDEN-base *cs* X86))
;;                                 R-X X86)
;;            :in-theory (e/d (x86isa::rme08 segment-base-and-bounds rb rb-1 rvm08 n48 read-byte-from-segment)
;;                            (X86ISA::SEG-HIDDEN-LIMITI-IS-N32P
;;                             X86ISA::SEG-HIDDEN-BASEI-IS-N64P
;;                             X86ISA::SEG-HIDDEN-ATTRI-IS-N16P)))))

(acl2::add-known-boolean code-segment-well-formedp)
(acl2::add-known-boolean code-segment-assumptions32-for-code)

;; incrementing the eip returns no error:
(defthm not-mv-nth-0-of-add-to-*ip
  (implies (and (not (64-bit-modep x86))
                (code-segment-assumptions32-for-code code offset x86-2) ;binds the free var
                (code-segment-assumptions32-for-code code offset x86) ;code is a free var and usually will be a constant
                (< (+ *ip delta) (+ offset (len code)))
                (<= offset (+ *IP DELTA))
                (integerp *ip)
                (integerp delta)
                (natp offset)
                (x86p x86) ;drop?
                )
           (not (mv-nth 0 (x86isa::add-to-*ip *compatibility-mode* *ip delta x86))))
  :hints (("Goal" :in-theory (enable X86ISA::ADD-TO-*IP
                                     code-segment-assumptions32-for-code
                                     segment-base-and-bounds))))

(defthm mv-nth-1-of-add-to-*ip
  (implies (and (not (64-bit-modep x86))
                (code-segment-assumptions32-for-code code offset x86-2) ;binds the free var
                (code-segment-assumptions32-for-code code offset x86) ;code is a free var and usually will be a constant
                (< (+ *ip delta) (+ offset (len code)))
                (<= offset (+ *ip delta))
                (integerp *ip)
                (integerp delta)
                (natp offset)
                (x86p x86) ;drop?
                )
           (equal (mv-nth 1 (x86isa::add-to-*ip *compatibility-mode* *ip delta x86))
                  (+ *ip delta)))
  :hints (("Goal" :in-theory (enable x86isa::add-to-*ip
                                     code-segment-assumptions32-for-code
                                     segment-base-and-bounds))))

(defthm fix-of-ifix
  (equal (fix (ifix x))
         (ifix x)))

;;;
;;; data-segment-writeable-bit
;;;

;; Check whether a data segment is writeable.
(defund data-segment-writeable-bit (seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (seg-regp seg-reg)))
  (x86isa::data-segment-descriptor-attributesbits->w (seg-hidden-attri seg-reg x86)))

(defthm data-segment-writeable-bit-intro
  (equal (x86isa::data-segment-descriptor-attributesbits->w (xr :seg-hidden-attr seg-reg x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable data-segment-writeable-bit))))

(theory-invariant (incompatible (:definition data-segment-writeable-bit) (:rewrite data-segment-writeable-bit-intro)))

(defthm data-segment-writeable-bit-of-xw-irrel
  (implies (not (equal :seg-hidden-attr fld))
           (equal (data-segment-writeable-bit seg-reg (xw fld index val x86))
                  (data-segment-writeable-bit seg-reg x86)))
  :hints (("Goal" :in-theory (e/d (data-segment-writeable-bit)
                                  (data-segment-writeable-bit-intro)))))

(defthm data-segment-writeable-bit-of-set-flag
  (equal (data-segment-writeable-bit seg-reg (set-flag flg val x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (e/d (data-segment-writeable-bit) (data-segment-writeable-bit-intro)))))

(defun stack-segment-assumptions32-helper (stack-segment-base stack-segment-limit esp stack-slots-needed)
  (declare (xargs :guard (and (unsigned-byte-p 32 stack-segment-base)
                              (unsigned-byte-p 32 stack-segment-limit)
                              (unsigned-byte-p 32 esp)
                              (natp stack-slots-needed))))
  (let* ( ;; lower limit seems exclusive: see (ss-lower (if (= ss.e 1) (1+ ss.limit) 0)) in add-to-*sp:
         (relative-lower-bound (+ 1 stack-segment-limit)) ;;  (todo: check this, the limit is exclusive?)
;          (relative-upper-bound (+ -1 (expt 2 32))) ; a linear address (todo: check this)
         (available-space (+ 1 (-
                                (+ -1 esp) ;esp is the lowest occupied address, so ESP-1 is available
                                  relative-lower-bound))))
    (and (not (equal 0 stack-segment-limit)) ;todo: think about this

         (<= (bvuminus 32 stack-segment-limit) stack-segment-base)

;(< (+ 3 esp) (+ -1 (expt 2 32))) ;need enough space to store an item on the stack at ESP...
         (<= (* 4 stack-slots-needed) available-space)

         ;; the stack has enough space to expand downward the given number of slots:

         (natp stack-slots-needed)
         ;; (<= (+ relative-lower-bound (* 4 (- stack-slots-needed 1)))
         ;;     esp)

         ;;need to know that the stack frame itself is ok (TODO: how big might it be?  pass in the number of args?)
         ;; for now, assuming it's at least 12 bytes (RSP, RBP, return address)
         (<= (+ esp 11) (+ -1 (expt 2 32)))
         )))

; test: (stack-segment-assumptions32-helper #x7000000 #xffff0000 #xffff7000 10)

;; in a flat model, the stack segment would take up 2^32 bytes, but you can only write above the limit
(defun stack-segment-assumptions32 (stack-slots-needed x86)
  (declare (xargs :stobjs x86
                  :guard (natp stack-slots-needed)))
  (and ;; the stack segment is a 32-bit segment, not 16-bit:
   (segment-is-32-bitsp *ss* x86)
   (well-formed-32-bit-segmentp *ss* x86)
   (equal (data-segment-writeable-bit *ss* x86) 1)
   ;; the segment is expand-down (the expand-down (e) bit is 1):
   (equal (segment-expand-down-bit *ss* x86) 1)
   (let* ((stack-segment-base (seg-hidden-basei *ss* x86)) ;example: 0, which is essentially #x10000000?
          ;; limit (effective, offset from base, essentially negative), leaves usable space above the limit:
          (stack-segment-limit (seg-hidden-limiti *ss* x86)) ;example:  ;#xffff0000
          (esp (rgfi *rsp* x86)) ;relative to the base? essentially negative? ;example: #xffff7000 (but note that this is an effective address)
          )
     (and (unsigned-byte-p 32 stack-segment-base)
          (unsigned-byte-p 32 esp)
          (stack-segment-assumptions32-helper stack-segment-base stack-segment-limit esp stack-slots-needed)))))

(defthm data-segment-writeable-bit-when-stack-segment-assumptions32
  (implies (stack-segment-assumptions32 stack-slots-needed x86)
           (equal (data-segment-writeable-bit *ss* x86)
                  1)))

(defthm well-formed-32-bit-segmentp-when-stack-segment-assumptions32
  (implies (stack-segment-assumptions32 stack-slots-needed x86)
           (well-formed-32-bit-segmentp *ss* x86)))

(defthm not-<-of-esp-when-stack-segment-assumptions32
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (natp k)
                (natp stack-slots-needed)
                (<= k (* 4 stack-slots-needed)) ;think about this
                (x86p x86))
           (not (< (esp x86) k)))
  :hints (("Goal" :in-theory (enable esp well-formed-32-bit-segmentp 32-bit-segment-start 32-bit-segment-start-and-size 32-bit-segment-size
                                     segment-min-eff-addr32
                                     segment-max-eff-addr32
                                     segment-base-and-bounds))))

;; Turn a call of read-*sp into a call of ESP, which is a much simpler function.
(defthm read-*sp-becomes-esp
  (implies (and (segment-is-32-bitsp *ss* x86)
                (not (64-bit-modep x86)))
           (equal (x86isa::read-*sp *compatibility-mode* x86)
                  (bvchop 32 (esp x86))))
  :hints (("Goal" :in-theory (enable x86isa::read-*sp esp bvchop))))

;; incrementing the esp returns no error:
(defthm not-mv-nth-0-of-add-to-*sp
  (implies (and (< delta 0) ;stack is expanding downward (e.g., delta is -4)
                (stack-segment-assumptions32 stack-slots-needed x86) ;stack-slots-needed is a free var and usually will be a constant
                (not (64-bit-modep x86))
                (<= (* -4 (+ -1 stack-slots-needed)) delta) ;gen?
                (integerp delta)
                (x86p x86))
           (not (mv-nth 0 (x86isa::add-to-*sp *compatibility-mode* (esp x86) delta x86))))
  :hints (("Goal" :in-theory (e/d (x86isa::add-to-*sp
                                   segment-base-and-bounds
                                   ;;segment-is-32-bitsp-intro-2
                                   esp
                                   )
                                  (;acl2::bvplus-recollapse
                                   )))))

(defthm not-mv-nth-0-of-add-to-*sp-gen
  (implies (and (<= (+ delta delta2) 0) ;stack is expanding downward (e.g., delta is -4)
                (stack-segment-assumptions32 stack-slots-needed x86) ;stack-slots-needed is a free var and usually will be a constant
;(stack-segment-assumptions32 stack-slots-needed x86-2)
                (equal (segment-base-and-bounds *compatibility-mode* *ss* x86)
                       (segment-base-and-bounds *compatibility-mode* *ss* x86-2))
                (not (64-bit-modep x86-2))
                (not (64-bit-modep x86))
                (<= (* -4 stack-slots-needed) (+ delta delta2))
                (integerp delta)
                (integerp delta2)
                (x86p x86-2)
                (x86p x86))
           (not (mv-nth 0 (x86isa::add-to-*sp *compatibility-mode* (+ delta2 (esp x86)) delta x86-2))))
  :hints (("Goal" :in-theory (e/d (x86isa::add-to-*sp
                                   esp
                                   segment-base-and-bounds
                                   ;;segment-is-32-bitsp-intro-2
                                   ACL2::MOD-OF-EXPT-OF-2-CONSTANT-VERSION
                                   )
                                  (;acl2::bvplus-recollapse
                                   )))))

;ironic name
(defthm not-mv-nth-0-of-add-to-*sp-gen-special
  (implies (and (<= delta 0) ;stack is expanding downward (e.g., delta is -4)
                (stack-segment-assumptions32 stack-slots-needed x86) ;stack-slots-needed is a free var and usually will be a constant
;(stack-segment-assumptions32 stack-slots-needed x86-2)
                (equal (segment-base-and-bounds *compatibility-mode* *ss* x86)
                       (segment-base-and-bounds *compatibility-mode* *ss* x86-2))
                (not (64-bit-modep x86-2))
                (not (64-bit-modep x86))
                (<= (* -4 stack-slots-needed) delta)
                (integerp delta)
                (x86p x86-2)
                (x86p x86))
           (not (mv-nth 0 (x86isa::add-to-*sp *compatibility-mode* (esp x86) delta x86-2))))
  :hints (("Goal" :use (:instance not-mv-nth-0-of-add-to-*sp-gen (delta2 0))
           :in-theory (e/d (esp) (not-mv-nth-0-of-add-to-*sp-gen)))))

(defthm mv-nth-1-of-add-to-*sp
  (implies (and (< delta 0) ;stack is expanding downward (e.g., delta is -4)
                (stack-segment-assumptions32 stack-slots-needed x86) ;stack-slots-needed is a free var and usually will be a constant
                (not (64-bit-modep x86))
                (<= (- delta) (* 4 (+ -1 stack-slots-needed))) ;gen?
                (integerp delta)
                (x86p x86)
                )
           (equal (mv-nth 1 (x86isa::add-to-*sp *compatibility-mode* (esp x86) delta x86))
                  (+ delta (esp x86))))
  :hints (("Goal" :in-theory (e/d (x86isa::add-to-*sp
                                   segment-base-and-bounds
                                   ;;segment-is-32-bitsp-intro-2
                                   esp
                                   )
                                  (;acl2::bvplus-recollapse
                                   )))))

(defthm mv-nth-1-of-add-to-*sp-gen
  (implies (and (<= (+ delta delta2) 0) ;stack is expanding downward (e.g., delta is -4)
                (stack-segment-assumptions32 stack-slots-needed x86) ;stack-slots-needed is a free var and usually will be a constant
                (equal (segment-base-and-bounds *compatibility-mode* *ss* x86)
                       (segment-base-and-bounds *compatibility-mode* *ss* x86-2))
                (not (64-bit-modep x86))
                (<= (* -4 stack-slots-needed) (+ delta delta2))
                (integerp delta)
                (integerp delta2)
                (x86p x86)
                (x86p x86-2)
                )
           (equal (mv-nth 1 (x86isa::add-to-*sp *compatibility-mode* (+ delta2 (esp x86)) delta x86-2))
                  (+ delta delta2 (esp x86))))
  :hints (("Goal" :in-theory (e/d (x86isa::add-to-*sp
                                   esp
                                   segment-base-and-bounds
                                   ;;segment-is-32-bitsp-intro-2
                                   ACL2::MOD-OF-EXPT-OF-2-CONSTANT-VERSION
                                   )
                                  (;acl2::bvplus-recollapse
                                   )))))

;ironic name
(defthm mv-nth-1-of-add-to-*sp-gen-special
  (implies (and (<= delta 0) ;stack is expanding downward (e.g., delta is -4)
                (stack-segment-assumptions32 stack-slots-needed x86) ;stack-slots-needed is a free var and usually will be a constant
                (equal (segment-base-and-bounds *compatibility-mode* *ss* x86)
                       (segment-base-and-bounds *compatibility-mode* *ss* x86-2))
                (not (64-bit-modep x86))
                (<= (* -4 stack-slots-needed) delta)
                (integerp delta)
                (x86p x86)
                (x86p x86-2)
                )
           (equal (mv-nth 1 (x86isa::add-to-*sp *compatibility-mode* (esp x86) delta x86-2))
                  (+ delta (esp x86))))
  :hints (("Goal" :use (:instance mv-nth-1-of-add-to-*sp-gen (delta2 0))
           :in-theory (e/d (esp) (mv-nth-1-of-add-to-*sp-gen)))))

;;;
;;; write-byte-to-segment
;;;

;; Just write at location BASE + EFF_ADDR.  Don't do any checking.
(defund write-byte-to-segment (eff-addr seg-reg val x86)
  (declare (xargs :stobjs x86
                  :guard (and (seg-regp seg-reg)
                              (integerp eff-addr)
                              (unsigned-byte-p 8 val))))
  (!memi (x86isa::n32 (+ (segment-base32 seg-reg x86) eff-addr))
         (bvchop 8 val)
         x86))

(defthm xr-of-write-byte-to-segment
  (implies (not (equal fld :mem))
           (equal (xr fld index  (write-byte-to-segment eff-addr seg-reg val x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm mv-nth-1-of-segment-base-and-bounds-of-write-byte-to-segment
  (equal (mv-nth 1 (segment-base-and-bounds 1 seg-reg (write-byte-to-segment eff-addr2 seg-reg2 val x86)))
         (mv-nth 1 (segment-base-and-bounds 1 seg-reg x86)))
  :hints (("Goal" :in-theory (e/d (segment-base-and-bounds) (;; x86isa::seg-hidden-basei-is-n64p
                                                             ;; x86isa::seg-hidden-limiti-is-n32p
                                                             ;; x86isa::seg-hidden-attri-is-n16p
                                                             )))))

(defthm mv-nth-2-of-segment-base-and-bounds-of-write-byte-to-segment
  (equal (mv-nth 2 (segment-base-and-bounds 1 seg-reg (write-byte-to-segment eff-addr2 seg-reg2 val x86)))
         (mv-nth 2 (segment-base-and-bounds 1 seg-reg x86)))
  :hints (("Goal" :in-theory (e/d (segment-base-and-bounds) (;; x86isa::seg-hidden-basei-is-n64p
                                                             ;; x86isa::seg-hidden-limiti-is-n32p
                                                             ;; x86isa::seg-hidden-attri-is-n16p
                                                             )))))

(defthm 64-bit-modep-of-write-byte-to-segment
  (equal (64-bit-modep (write-byte-to-segment eff-addr seg-reg val x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm segment-is-32-bitsp-of-write-byte-to-segment
  (equal (segment-is-32-bitsp seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (segment-is-32-bitsp seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))


(defthm 32-bit-segment-start-of-write-byte-to-segment
  (equal (32-bit-segment-start seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (32-bit-segment-start seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment 32-bit-segment-size 32-bit-segment-start 32-bit-segment-start-and-size))))

(defthm segment-min-eff-addr32-of-write-byte-to-segment
  (equal (segment-min-eff-addr32 seg-reg (write-byte-to-segment eff-addr2 seg-reg2 val x86))
         (segment-min-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-min-eff-addr32))))

(defthm segment-max-eff-addr32-of-write-byte-to-segment
  (equal (segment-max-eff-addr32 seg-reg (write-byte-to-segment eff-addr2 seg-reg2 val x86))
         (segment-max-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-max-eff-addr32))))

(defthm x86p-of-write-byte-to-segment
  (implies (x86p x86)
           (x86p (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm well-formed-32-bit-segmentp-of-write-byte-to-segment
  (equal (well-formed-32-bit-segmentp seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (well-formed-32-bit-segmentp seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

;;;
;;; write-byte-list-to-segment
;;;

;; Writes a list of N bytes, starting at EFF-ADDR in the indicated segment.
(defun write-byte-list-to-segment (n eff-addr seg-reg bytes x86)
  (declare (xargs :stobjs x86
                  :guard (and (seg-regp seg-reg)
                              (integerp eff-addr)
                              (natp n)
                              (true-listp bytes)
                              (acl2::all-unsigned-byte-p 8 bytes)
                              (equal (len bytes) n))))
  (if (zp n)
      x86
    (let ((x86 (write-byte-to-segment eff-addr seg-reg (first bytes) x86)))
      (write-byte-list-to-segment (- n 1) (+ 1 eff-addr) seg-reg (rest bytes) x86))))

;;;
;;; write-to-segment
;;;

;write a chunk of data (little-endian)
(defund write-to-segment (n eff-addr seg-reg val x86)
  (declare (xargs :stobjs x86
                  :guard (and (natp n)
                              (unsigned-byte-p (* 8 n) val)
                              (integerp eff-addr)
                              (seg-regp seg-reg))))
  (if (zp n)
      x86
    (let ((x86 (write-byte-to-segment eff-addr seg-reg
                                      (bvchop 8 val)
                                      x86)))
      (write-to-segment (+ -1 n)
                        (+ 1 eff-addr)
                        seg-reg
                        (logtail 8 val)
                        x86))))

(defthm write-to-segment-of-0
  (equal (write-to-segment 0 eff-addr seg-reg val x86)
         x86)
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm xr-of-write-to-segment
  (implies (not (equal fld :mem))
           (equal (xr fld index (write-to-segment n eff-addr seg-reg val x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;; (defthm not-mv-nth-0-of-WME-SIZE$inline
;;   (implies (and (< delta 0) ;stack is expanding downward (e.g., delta is -4)
;;                 (stack-segment-assumptions32 stack-slots-needed x86) ;stack-slots-needed is a free var and usually will be a constant
;;                 (not (64-bit-modep x86))
;;                 (<= (- delta) (* 4 (+ -1 stack-slots-needed))) ;gen?
;;                 (integerp delta)
;;                 (app-view x86)
;;                 (x86p x86) ;;drop?
;;                 )
;;            (not (mv-nth 0 (X86ISA::WME-SIZE$inline *compatibility-mode*
;;                                                    4 ;gen!
;;                                                    (+ delta (ESP X86))
;;                                                    *ss*
;;                                                    val
;;                                                    nil
;;                                                    X86
;;                                                    nil))))
;;   :hints (("Goal" :in-theory (enable X86ISA::WME-SIZE$inline SEGMENT-BASE-AND-BOUNDS wb))))

;; (defthm 64-bit-modep-of-write-*sp
;;   (equal (64-bit-modep (x86isa::write-*sp *compatibility-mode* *sp x86))
;;          (64-bit-modep x86))
;;   :hints (("Goal" :in-theory (enable x86isa::write-*sp))))

(defthm xr-of-!memi-irrel
  (implies (not (equal fld :mem))
           (equal (XR fld seg-reg (!MEMI i v x86))
                  (XR fld seg-reg x86)))
  :hints (("Goal" :in-theory (enable !memi))))

(defthm 64-bit-modep-of-!memi
  (equal (64-bit-modep (!memi i v x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable !memi))))

;example: if one stack slot is needed, we can use a delta of -4 from the ESP
(defthm stack-access-in-bounds-lemma
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (<= (- delta) (* 4 (+ -1 stack-slots-needed))) ;gen?
                (integerp delta)
                (< delta 0)
                (natp stack-slots-needed)
                (x86p x86) ;;drop?
                )
           (<= 0
               (+ delta (xr :rgf *rsp* x86))))
  :hints (("Goal" :in-theory (enable stack-segment-assumptions32))))

(defthm segment-expand-down-bit-of-ss-when-stack-segment-assumptions32
  (implies (stack-segment-assumptions32 stack-slots-needed x86)
           (equal (segment-expand-down-bit *ss* x86)
                  1)))

;the access must be above the limit to be legal
(defthm stack-access-in-bounds-lemma-2
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (<= (- delta) (* 4 (+ -1 stack-slots-needed))) ;gen?
                (integerp delta)
                (< delta 0)
                (natp stack-slots-needed))
           (< (xr :seg-hidden-limit 2 x86)
              (+ delta (bvchop 32 (xr :rgf *rsp* x86)))))
  :hints (("Goal" :in-theory (enable stack-segment-assumptions32))))

;the access must be above the limit to be legal
(defthm stack-access-in-bounds-lemma-3
  (implies (stack-segment-assumptions32 stack-slots-needed x86)
           (unsigned-byte-p 32 (XR :RGF *RSP* X86)))
  :hints (("Goal" :in-theory (enable stack-segment-assumptions32))))

(defthm stack-access-in-bounds-lemma-4
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (<= (- delta) (* 4 (+ -1 stack-slots-needed))) ;gen?
                (integerp delta)
                (< delta 0)
                (natp stack-slots-needed))
           (< (+ DELTA (XR :RGF *RSP* X86))
              4294967296))
  :hints (("Goal" :in-theory (enable stack-segment-assumptions32))))

;; (defthm stack-access-in-bounds-lemma-5
;;   (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
;;                 (<= (- delta) (* 4 (+ -1 stack-slots-needed)))
;;                 (integerp delta)
;;                 (< delta 0)
;;                 (natp stack-slots-needed))
;;            (not (equal (bvchop 32
;;                               (+ delta (xr :rgf *rsp* x86)
;;                                  (bvchop 32 (seg-hidden-basei 2 x86))))
;;                      4294967295)))
;;   :hints (("Goal" :in-theory (enable stack-segment-assumptions32))))

(defthmd bvchop-when-negative-lemma
  (implies (and (< x 0) ;stack is expanding downward (e.g., delta is -4)
                (<= (- (expt 2 size)) x)
                (integerp x)
                (natp size))
           (equal (bvchop size x)
                  (+ (expt 2 size) x)))
  :hints (("Goal"
           :use (:instance acl2::bvchop-identity (acl2::size size) (i (+ (expt 2 size) X)))
           :in-theory (e/d (bvchop
                            UNSIGNED-BYTE-P
                            ) (       ;acl2::mod-of-expt-of-2 ;mod
                               ACL2::EQUAL-OF-+-AND-BV
;                               ACL2::BVPLUS-RECOLLAPSE
                               )))))

(defthm <-when-<-one-of-less-strengthen
  (implies (and (syntaxp (acl2::want-to-strengthen (< x k)))
                (syntaxp (quotep k))
                (<= kminus1 x)
                (syntaxp (quotep kminus1))
                (equal kminus1 (+ -1 k))
                (integerp k)
                (integerp x))
           (equal (< x k)
                  (equal x kminus1))))

(defthm bvchop-tighten-when-unsigned-byte-p
  (implies (unsigned-byte-p 32 (bvchop 64 x))
           (equal (bvchop 64 x)
                  (bvchop 32 x)))
  :hints (("Goal" :in-theory (disable ACL2::REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1))))

(defthm esp-bound-hack
  (implies (stack-segment-assumptions32 stack-slots-needed x86)
           (< (ESP X86) '4294967297))
  :hints (("Goal" :in-theory (enable esp))))

(defthm <-of-esp-when-constant
  (implies (and (syntaxp (quotep k))
                (<= 4294967296 k)
                (integerp k)
                (stack-segment-assumptions32 stack-slots-needed x86))
           (< (esp x86) k))
  :hints (("Goal" :in-theory (enable esp))))

; now we need to characterize wme-size in terms of write-byte-list-to-segment
;; (defthm mv-nth-1-of-wme-size
;;   (implies (and (< delta 0) ;stack is expanding downward (e.g., delta is -4)
;;                 (stack-segment-assumptions32 stack-slots-needed x86) ;stack-slots-needed is a free var and usually will be a constant
;;                 (not (64-bit-modep x86))
;;                 (< (- delta) (* 4 stack-slots-needed)) ;why strict?
;;                 (integerp delta)
;;                 (app-view x86)
;;                 (< stack-slots-needed 1000) ;gen
;;                 (natp stack-slots-needed)
;;                 (< (+ 3 delta (esp x86)) (expt 2 32))
;;                 (x86p x86)
;;                 )
;;            (equal (mv-nth 1 (x86isa::wme-size$inline *compatibility-mode*
;;                                                      4 ;gen!
;;                                                      (+ delta (esp x86))
;;                                                      *ss*
;;                                                      val
;;                                                      nil
;;                                                      x86
;;                                                      nil))
;;                   (write-to-segment 4
;;                                     (+ delta (esp x86))
;;                                     *ss*
;;                                     val
;;                                     x86)))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :expand ((:free (a b c d x86) (write-to-segment a b c d x86))
;;                     (:free (a b c d x86) (wb-1 a b c d x86))
;;                     (:free (stack-slots-needed) (stack-segment-assumptions32 stack-slots-needed x86)))
;;            :in-theory (e/d (bvchop-when-negative-lemma
;;                             x86isa::wme-size$inline
;;                             segment-base-and-bounds
;;                             wb
;;                             write-byte-to-segment
;;                             wvm08
;;                             n48
;;                             stack-segment-assumptions32
;;                             acl2::bvchop-of-sum-cases
;;                             BVUMINUS
;;                             BVMINUS
;; ;                            SEGMENT-IS-32-BITSP
;;                             )
;;                            ( ;ACL2::BVCHOP-IDENTITY
;; ;                            ACL2::BVCHOP-IDENTITY-cheap
;;                             x86isa::!memi$inline
;; ;                            acl2::bvplus-recollapse
;;                             stack-segment-assumptions32
;;                             acl2::bvchop-of-sum-of-bvchop-same-alt acl2::bvchop-of-sum-of-bvchop-gen-arg3 ;todo: compare these
;;                             ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
;;                             ACL2::REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER
;;                             )))))

(local (in-theory (enable ACL2::MOD-OF-EXPT-OF-2-CONSTANT-VERSION)))

;;We thought we needed to turn off WML32 and especially WME-SIZE and wme32 (why?)
;;Lift the subroutine into logic as a 32-bit program:

(defthm x86isa::write-*sp-when-not-64-bit-modep
  (implies (and (not (64-bit-modep x86))
                (segment-is-32-bitsp *ss* x86))
           (equal (x86isa::write-*sp *compatibility-mode* x86isa::*sp x86)
                  (xw :rgf *rsp* (bvchop 32 x86isa::*sp)
                      x86)))
  :hints (("Goal" :in-theory (enable x86isa::write-*sp))))

(defthm 64-bit-modep-of-write-to-segment
  (equal (64-bit-modep (write-to-segment n eff-addr seg-reg val x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm 64-bit-modep-of-write-bytes-to-segment
  (equal (64-bit-modep (write-to-segment n eff-addr seg-reg val x86))
         (64-bit-modep x86)))

(defthm segment-is-32-bitsp-of-write-to-segment
  (equal (segment-is-32-bitsp seg-reg1 (write-to-segment n eff-addr seg-reg2 val x86))
         (segment-is-32-bitsp seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm 32-bit-segment-start-and-size-of-write-to-segment
  (equal (32-bit-segment-start-and-size seg-reg (write-to-segment n eff-addr seg-reg2 val x86))
         (32-bit-segment-start-and-size seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start-and-size))))

(defthm 32-bit-segment-start-of-write-to-segment
  (equal (32-bit-segment-start seg-reg (write-to-segment n eff-addr seg-reg2 val x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start))))

(defthm mv-nth-1-of-segment-base-and-bounds-of-write-to-segment
  (equal (mv-nth 1 (segment-base-and-bounds 1 seg-reg (write-to-segment n eff-addr2 seg-reg2 val x86)))
         (mv-nth 1 (segment-base-and-bounds 1 seg-reg x86)))
  :hints (("Goal" :in-theory (e/d (segment-base-and-bounds) (;; x86isa::seg-hidden-basei-is-n64p
                                                             ;; x86isa::seg-hidden-limiti-is-n32p
                                                             ;; x86isa::seg-hidden-attri-is-n16p
                                                             )))))


(defthm mv-nth-2-of-segment-base-and-bounds-of-write-to-segment
  (equal (mv-nth 2 (segment-base-and-bounds 1 seg-reg (write-to-segment n eff-addr2 seg-reg2 val x86)))
         (mv-nth 2 (segment-base-and-bounds 1 seg-reg x86)))
  :hints (("Goal" :in-theory (e/d (segment-base-and-bounds) (;; x86isa::seg-hidden-basei-is-n64p
                                                             ;; x86isa::seg-hidden-limiti-is-n32p
                                                             ;; x86isa::seg-hidden-attri-is-n16p
                                                             )))))

(defthm segment-min-eff-addr32-of-write-to-segment
  (equal (segment-min-eff-addr32 seg-reg (write-to-segment n eff-addr seg-reg2 val x86))
         (segment-min-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-min-eff-addr32))))

(defthm segment-max-eff-addr32-of-write-to-segment
  (equal (segment-max-eff-addr32 seg-reg (write-to-segment n eff-addr seg-reg2 val x86))
         (segment-max-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-max-eff-addr32))))

(defthm bvchop-of-decrement-esp-hack
  (implies (and (stack-segment-assumptions32 10 x86)
                (x86p x86) ;;drop?
                )
           (equal (BVCHOP '32 (BINARY-+ '-4 (ESP X86)))
                  (BINARY-+ '-4 (ESP X86))))
  :hints (("Goal" :in-theory (enable esp acl2::bvchop-of-sum-cases))))

(defthm read-byte-from-segment-of-xw
  (implies (and (not (equal :mem fld))
                (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (read-byte-from-segment eff-addr seg-reg (xw fld index val x86))
                  (read-byte-from-segment eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-byte-from-segment))))

(defthm read-byte-list-from-segment-of-xw
  (implies (and (not (equal :mem fld))
                (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (read-byte-list-from-segment n eff-addr seg-reg (xw fld index val x86))
                  (read-byte-list-from-segment n eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-byte-list-from-segment))))

(defthm code-segment-well-formedp-of-xw
  (implies (and (not (equal :mem fld))
                (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal :seg-visible fld))
                (not (equal :msr fld)))
           (equal (code-segment-well-formedp (xw fld index val x86))
                  (code-segment-well-formedp x86)))
  :hints (("Goal" :in-theory (e/d (code-segment-well-formedp)
                                  (;; x86isa::seg-hidden-basei-is-n64p
                                   ;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-attri-is-n16p
                                   )))))

(defthm code-segment-assumptions32-for-code-of-xw
  (implies (and (not (equal :mem fld))
                (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal :seg-visible fld))
                (not (equal :msr fld)))
           (equal (code-segment-assumptions32-for-code code offset (xw fld index val x86))
                  (code-segment-assumptions32-for-code code offset x86)))
  :hints (("Goal" :in-theory (e/d (code-segment-assumptions32-for-code)
                                  (;; x86isa::seg-hidden-basei-is-n64p
                                   ;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-attri-is-n16p
                                   )))))



;; lower1 and lower2 are linear addresses
(defund segments-separate-helper (lower1 size1 lower2 size2)
  (declare (xargs :guard (and (integerp lower1)
                              (integerp lower2)
                              (natp size1)
                              (natp size2))))
  (or (zp size1)
      (zp size2)
      (separate :r size1 lower1
                :r size2 lower2)))

;; this is for 32-bit segs
(defund segments-separate (seg-reg1 seg-reg2 x86)
  (declare (xargs :stobjs x86
                  :guard (and (seg-regp seg-reg1)
                              (seg-regp seg-reg2)
                              (segment-is-32-bitsp seg-reg1 x86) ;not a 16-bit segment
                              (segment-is-32-bitsp seg-reg2 x86) ;not a 16-bit segment
                              )))
  (b* (((mv segment1-lower segment1-size)
        (32-bit-segment-start-and-size seg-reg1 x86))
       ((mv segment2-lower segment2-size)
        (32-bit-segment-start-and-size seg-reg2 x86)))
    ;; (let* ( ;; The code segment begins at some (linear) address:
    ;;        (code-segment-base (xr ':seg-hidden-base *cs* x86))
    ;;        ;; The code segment limit is an offset from the base of the code
    ;;        ;; segment):
    ;;        (code-segment-limit (xr ':seg-hidden-limit *cs* x86))
    ;;        (code-segment-size (+ 1 code-segment-limit))

    ;;        (stack-segment-base (xr ':seg-hidden-base *ss* x86))
    ;;        ;; limit (effective, offset from base, essentially negative), leaves usable space above the limit:
    ;;        (stack-segment-limit (xr ':seg-hidden-limit *ss* x86)) ;example:  ;#xffff0000
    ;;        (stack-segment-relative-lower-bound (+ 1 stack-segment-limit))
    ;;        (stack-segment-relative-upper-bound 4294967295)
    ;;        (stack-segment-size (+ 1 (- stack-segment-relative-upper-bound stack-segment-relative-lower-bound)))
    ;;        )
    (segments-separate-helper segment1-lower segment1-size
                              segment2-lower segment2-size)))

(defthm segments-separate-of-write-to-segment
  (equal (segments-separate seg-reg1 seg-reg2 (write-to-segment n eff-addr seg-reg val x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable segments-separate))))

(defund code-and-stack-segments-separate (x86)
  (declare (xargs :stobjs x86
                  :guard (and (segment-is-32-bitsp *cs* x86) ;not a 16-bit segment
                              (segment-is-32-bitsp *ss* x86) ;not a 16-bit segment
                              )
     ;                  :guard (not (equal 4294967295 (seg-hidden-limiti 2 X86))) ;stack limit of -1 is not allowed?
                  ))
  (segments-separate *cs* *ss* x86))

(defthm integerp-of-mv-nth-0-of-segment-base-and-bounds
  (implies (x86p x86)
           (integerp (mv-nth 0 (segment-base-and-bounds proc-mode seg-reg x86))))
  :hints (("Goal" :in-theory (e/d (segment-base-and-bounds)
                                  ()))))

;same seg-reg
(defthm read-byte-from-segment-of-write-byte-to-segment-both
  (implies (and (integerp eff-addr1)
                (integerp eff-addr2)
                (x86p x86))
           (equal (read-byte-from-segment eff-addr1 seg-reg (write-byte-to-segment eff-addr2 seg-reg val x86))
                  (if (equal (bvchop 32 eff-addr1) (bvchop 32 eff-addr2))
                      (bvchop 8 val)
                    (read-byte-from-segment eff-addr1 seg-reg x86))))
  :hints (("Goal" :in-theory (e/d (read-byte-from-segment write-byte-to-segment memi)
                                  ( ;acl2::bvchop-+-cancel-seconds
                                   )))))

(defthm write-byte-to-segment-of-write-byte-to-segment-both
  (implies (and (syntaxp (acl2::smaller-termp eff-addr2 eff-addr1))
                (integerp eff-addr1)
                (integerp eff-addr2)
                (x86p x86))
           (equal (write-byte-to-segment eff-addr1 seg-reg val1 (write-byte-to-segment eff-addr2 seg-reg val2 x86))
                  (if (equal (bvchop 32 eff-addr1)
                             (bvchop 32 eff-addr2))
                      (write-byte-to-segment eff-addr1 seg-reg val1 x86)
                    (write-byte-to-segment eff-addr2 seg-reg val2 (write-byte-to-segment eff-addr1 seg-reg val1 x86)))))
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment ACL2::BVPLUS-RECOLLAPSE)
                                  ()))))

(defthm write-byte-to-segment-of-write-byte-to-segment-same
  (implies (and (integerp eff-addr)
                (x86p x86))
           (equal (write-byte-to-segment eff-addr seg-reg val1 (write-byte-to-segment eff-addr seg-reg val2 x86))
                  (write-byte-to-segment eff-addr seg-reg val1 x86)))
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment ACL2::BVPLUS-RECOLLAPSE)
                                  ()))))

(defthmd write-to-segment-of-write-byte-to-segment
  (implies (and (integerp eff-addr1)
                (integerp eff-addr2)
                (<= n (bvchop 32 (- eff-addr2 eff-addr1)))
                (x86p x86))
           (equal (write-to-segment n eff-addr1 seg-reg val1 (write-byte-to-segment eff-addr2 seg-reg val2 x86))
                  (write-byte-to-segment eff-addr2 seg-reg val2 (write-to-segment n eff-addr1 seg-reg val1 x86))))
  :hints (("subgoal *1/2" :cases ((equal (bvchop 32 eff-addr1)
                                         (bvchop 32 eff-addr2))))
          ("Goal" :induct (write-to-segment n eff-addr1 seg-reg val1 x86)
           :expand (write-to-segment n eff-addr1 seg-reg val1
                                     (write-byte-to-segment eff-addr2 seg-reg val2 x86))
           :in-theory (e/d (write-to-segment bvplus acl2::bvchop-of-sum-cases)
                           (;acl2::bvplus-recollapse
                            )))))

(defthm x86p-of-write-to-segment
  (implies (x86p x86)
           (x86p (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;; Check whether the effective address EFF-ADDR is a valid effective address
;; in the segment indicated by SEG-REG.
(defun eff-addr-okp (eff-addr seg-reg x86)
  (declare (xargs :guard (and (seg-regp seg-reg)
                              (segment-is-32-bitsp seg-reg x86)
                              (integerp eff-addr))
                  :stobjs x86))
  (and (<= (segment-min-eff-addr32 seg-reg x86) eff-addr)
       (<= eff-addr (segment-max-eff-addr32 seg-reg x86))))

;; Check whether the N effective addresss starting at EFF-ADDR are all valid
;; effective addresses in the segment indicated by SEG-REG.  Theorem
;; mv-nth-0-of-ea-to-la shows that this function characterizes the inputs for
;; which ea-to-la does not return an error.
(defun eff-addrs-okp (n eff-addr seg-reg x86)
  (declare (xargs :guard (and (integerp eff-addr)
                              (natp n)
                              (seg-regp seg-reg)
                              (segment-is-32-bitsp seg-reg x86))
                  :stobjs x86))
  (and (<= (segment-min-eff-addr32 seg-reg x86) eff-addr)
       (<= (+ -1 n eff-addr) (segment-max-eff-addr32 seg-reg x86))))

(acl2::add-known-boolean eff-addrs-okp)

(defthm eff-addrs-okp-of-1
  (equal (eff-addrs-okp 1 eff-addr seg-reg x86)
         (eff-addr-okp eff-addr seg-reg x86)))

  ;; (if (equal (segment-expand-down-bit seg-reg x86) 0)
  ;;     ;;expand-up segment:
  ;;     (< eff-addr (32-bit-segment-size seg-reg x86))
  ;;   ;;expand-down segment:
  ;;   (and (< (bvuminus 32 (32-bit-segment-size seg-reg x86)) eff-addr) ;gen the <?
  ;;        ;why?:
  ;;        (not (equal (seg-hidden-limiti seg-reg x86)
  ;;                    4294967295)))))

(defthm read-byte-from-segment-of-write-byte-to-segment-diff-segments
  (implies (and (segments-separate seg-reg1 seg-reg2 x86)
                ;; (not (equal seg-reg1 (seg-reg2)))
                (eff-addr-okp eff-addr1 seg-reg1 x86)
                (eff-addr-okp eff-addr2 seg-reg2 x86)
;                (< 0 (32-bit-segment-size seg-reg1 x86)) ;gen?
                (seg-regp seg-reg1)
                (seg-regp seg-reg2)
                (segment-is-32-bitsp seg-reg1 x86)
                (segment-is-32-bitsp seg-reg2 x86)
                (x86p x86)
                (not (64-bit-modep x86)) ;32-bit mode
                ;;(natp eff-addr1)
                ;;(natp eff-addr2)
                (well-formed-32-bit-segmentp seg-reg1 x86)
                (well-formed-32-bit-segmentp seg-reg2 x86)
                (integerp eff-addr1) ;; (unsigned-byte-p 32 eff-addr1)
                (integerp eff-addr2) ;; (unsigned-byte-p 32 eff-addr2)
                )
           (equal (read-byte-from-segment eff-addr1 seg-reg1 (write-byte-to-segment eff-addr2 seg-reg2 val x86))
                  (read-byte-from-segment eff-addr1 seg-reg1 x86)))
  :hints (("Goal" :in-theory (e/d (read-byte-from-segment write-byte-to-segment memi
                                                          segment-base-and-bounds segments-separate
                                                          segments-separate-helper
                                                          32-bit-segment-start-and-size
;                                                          segment-is-32-bitsp
                                                          separate
                                                          32-bit-segment-size
                                                          bvplus
                                                          bvuminus
                                                          bvminus
                                                          acl2::bvchop-of-sum-cases
                                                          32-bit-segment-start
                                                          SEGMENT-MIN-EFF-ADDR32
                                                          SEGMENT-MAX-EFF-ADDR32)
                                  ( ;acl2::bvchop-+-cancel-seconds
                                   ;x86isa::msri$inline
                                   acl2::bvplus-recollapse
                                   acl2::bvminus-becomes-bvplus-of-bvuminus
                                   )))))

(defthm segments-separate-of-write-byte-to-segment
  (equal (segments-separate seg-reg1 seg-reg2 (write-byte-to-segment eff-addr seg-reg3 val x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment
                                   segments-separate
                                   32-bit-segment-size
                                   32-bit-segment-start-and-size)
                                  (;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-basei-is-n64p
                                   )))))

(defthm read-byte-list-from-segment-of-1
  (equal (read-byte-list-from-segment 1 eff-addr seg-reg x86)
         (list (read-byte-from-segment eff-addr seg-reg x86)))
  :hints (("Goal" :expand (read-byte-list-from-segment 1 eff-addr seg-reg x86))))

(defthm read-byte-list-from-segment-of-write-byte-to-segment
  (implies (and (segments-separate seg-reg1 seg-reg2 x86)
                (eff-addrs-okp n1 eff-addr1 seg-reg1 x86)
                (eff-addr-okp eff-addr2 seg-reg2 x86)
                (seg-regp seg-reg1)
                (seg-regp seg-reg2)
                (segment-is-32-bitsp seg-reg1 x86)
                (segment-is-32-bitsp seg-reg2 x86)
                (< n1 (expt 2 32))
                (posp n1)
                (natp eff-addr1)
                (natp eff-addr2)
                (not (64-bit-modep x86))
;                (not (equal seg-reg1 seg-reg2))
;                (< (+ -1 n1 eff-addr1) (32-bit-segment-size seg-reg1 x86))
;              (< eff-addr2 (32-bit-segment-size seg-reg2 x86))
                (well-formed-32-bit-segmentp seg-reg1 x86)
                (well-formed-32-bit-segmentp seg-reg2 x86)
                (x86p x86))
           (equal (read-byte-list-from-segment n1 eff-addr1 seg-reg1 (write-byte-to-segment eff-addr2 seg-reg2 byte x86))
                  (read-byte-list-from-segment n1 eff-addr1 seg-reg1 x86)))
  :hints (("Goal"
;           :induct (READ-BYTE-LIST-FROM-SEGMENT N1 EFF-ADDR1 SEG-REG1 X86)
           :expand ((:free (EFF-ADDR1 seg-reg1 x86)
                           (READ-BYTE-LIST-FROM-SEGMENT 1 EFF-ADDR1 SEG-REG1 X86)))
           :in-theory (e/d (read-byte-list-from-segment
                            write-to-segment
                            write-to-segment-of-write-byte-to-segment
                            SEGMENT-MIN-EFF-ADDR32
                            SEGMENT-Max-EFF-ADDR32)
                           (READ-BYTE-FROM-SEGMENT)))))

(local (in-theory (disable well-formed-32-bit-segmentp)))

;; (defthm <-of-
;;  (implies (well-formed-32-bit-segmentp seg-reg x86)
;;           (NOT (< '4294967296
;;                   (BINARY-+ (32-BIT-SEGMENT-SIZE seg-reg X86)
;;                             (32-BIT-SEGMENT-START seg-reg X86))))))


;not sure if I want this enabled
(defthm segment-max-eff-addr32-when-expand-up
  (implies (and (equal (segment-expand-down-bit seg-reg x86) 0)
                ;; (well-formed-32-bit-segmentp seg-reg x86)
                )
           (equal (segment-max-eff-addr32 seg-reg x86)
                  (bvchop 32 (xr :seg-hidden-limit seg-reg x86))))
  :hints (("Goal" :in-theory (e/d (segment-max-eff-addr32
                                   segment-base-and-bounds
                                   well-formed-32-bit-segmentp)
                                  (;; x86isa::seg-hidden-basei-is-n64p
                                   ;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-attri-is-n16p
                                   )))))

;not sure if I want this enabled
(defthm 32-bit-segment-size-when-expand-up
  (implies (and (equal (segment-expand-down-bit seg-reg x86) 0)
                ;; (well-formed-32-bit-segmentp seg-reg x86)
                )
           (equal (32-bit-segment-size seg-reg x86)
                  (+ 1
                     (bvchop 32 (xr :seg-hidden-limit seg-reg x86)))))
  :hints (("Goal" :in-theory (e/d (32-bit-segment-size
                                   segment-max-eff-addr32
                                   segment-base-and-bounds
                                   well-formed-32-bit-segmentp)
                                  (;; x86isa::seg-hidden-basei-is-n64p
                                   ;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-attri-is-n16p
                                   )))))

(defthm well-formed-32-bit-segmentp-of-xw
  (implies (and (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal :seg-visible fld))
                (not (equal fld :msr)))
           (equal (well-formed-32-bit-segmentp seg-reg1 (xw fld index val x86))
                  (well-formed-32-bit-segmentp seg-reg1 x86)))
  :hints (("Goal" :in-theory (enable well-formed-32-bit-segmentp))))

(defthm mv-nth-1-of-rme08-of-ss-becomes-read-byte-from-segment
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86) ;code is a free var and usually will be a constant
                (not (64-bit-modep x86))
                (app-view x86)
                (< (bvuminus 32 (* 4 stack-slots-needed)) eff-addr)
;                (<= 0 eff-addr)
                (unsigned-byte-p 32 eff-addr) ;; (integerp eff-addr)
                (x86p x86) ;drop?
                (natp stack-slots-needed)
                (< 0 stack-slots-needed) ;todo think
;                (< stack-slots-needed 100) ;gen
;                (equal stack-slots-needed 20) ;drop
                )
           (equal (mv-nth 1 (x86isa::rme08 *compatibility-mode* eff-addr *ss* r-x x86))
                  (read-byte-from-segment eff-addr *ss* x86)))
  :hints (("Goal"
           :in-theory (e/d (x86isa::rme08 segment-base-and-bounds rb rb-1 rvm08 n48 read-byte-from-segment unsigned-byte-p
                                          bvuminus
                                          bvplus
                                          BVMINUS
                                          acl2::bvchop-of-sum-cases
                                          )
                           (ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                            ACL2::BVPLUS-RECOLLAPSE)))))

(defthm segment-is-32-bitsp-when-stack-segment-assumptions32
  (implies (stack-segment-assumptions32 stack-slots-needed x86)
           (segment-is-32-bitsp *ss* x86)))

;;todo: rethink STACK-SEGMENT-ASSUMPTIONS32

(defthm natp-of-+-of-esp-lemma ;gen!
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (natp stack-slots-needed)
                (<= (+ -1 (* -4 stack-slots-needed)) k) ;not sure about the -1, but it seems harmless
                (integerp k)
                (x86p x86))
           (natp (binary-+ k (esp x86))))
  :hints (("Goal" :in-theory (enable esp))))

(defthm not-<-of-32-bit-segment-size
  (implies (and (code-segment-assumptions32-for-code code offset x86)
                (code-segment-well-formedp x86)
                (<= k (+ offset (len code)))
                (x86p x86))
           (not (< (32-bit-segment-size *cs* x86) k)))
  :hints (("Goal" :in-theory (enable code-segment-assumptions32-for-code))))

(defthm <-of-32-bit-segment-size-helper
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (natp stack-slots-needed)
                (x86p x86))
           (<= (* 4 stack-slots-needed) (32-bit-segment-size *ss* x86)))
  :hints (("Goal" :in-theory (e/d (32-bit-segment-size
                                   segment-min-eff-addr32
                                   segment-max-eff-addr32
                                   segment-base-and-bounds
                                   bvuminus
                                   bvminus
                                   bvplus
                                   acl2::bvchop-of-sum-cases)
                                  (acl2::bvminus-becomes-bvplus-of-bvuminus
                                   acl2::bvplus-recollapse)))))

(defthm <-of-32-bit-segment-size
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (natp stack-slots-needed)
                (<= k (+ -1 (* 4 stack-slots-needed)))
                (integerp k)
                (x86p x86))
           (< k (32-bit-segment-size *ss* x86)))
  :hints (("Goal" :use (:instance <-of-32-bit-segment-size-helper)
           :in-theory (disable <-of-32-bit-segment-size-helper
                               stack-segment-assumptions32))))

(defthm segment-min-eff-addr32-bound-when-stack-segment-assumptions32
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (natp stack-slots-needed)
                (x86p x86))
           (<= (+ (* 4 stack-slots-needed)
                  (segment-min-eff-addr32 2 x86))
               (esp x86)))
  :hints (("Goal" :in-theory (e/d (32-bit-segment-size
                                   segment-min-eff-addr32
                                   segment-base-and-bounds
                                   bvuminus
                                   bvminus
                                   bvplus
                                   acl2::bvchop-of-sum-cases
                                   esp)
                                  (acl2::bvminus-becomes-bvplus-of-bvuminus
                                   acl2::bvplus-recollapse)))))

(defthm segment-max-eff-addr32-bound-when-stack-segment-assumptions32
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (natp stack-slots-needed)
                (x86p x86))
           (<= (esp x86)
               (segment-max-eff-addr32 2 x86)))
  :hints (("Goal" :in-theory (e/d (32-bit-segment-size
                                   segment-max-eff-addr32
                                   segment-base-and-bounds
                                   bvuminus
                                   bvminus
                                   bvplus
                                   acl2::bvchop-of-sum-cases
                                   esp)
                                  (acl2::bvminus-becomes-bvplus-of-bvuminus
                                   acl2::bvplus-recollapse)))))

(local (in-theory (disable esp))) ;prevents loops

(defthm eff-addrs-lemma-1
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (natp stack-slots-needed)
                (<= 1 stack-slots-needed)
                (x86p x86))
           (eff-addrs-okp '4 (binary-+ '-4 (esp x86)) *ss* x86))
  :hints (("Goal" :use ( segment-max-eff-addr32-bound-when-stack-segment-assumptions32
                                  segment-min-eff-addr32-bound-when-stack-segment-assumptions32)
           :in-theory (disable segment-min-eff-addr32-bound-when-stack-segment-assumptions32
                               segment-max-eff-addr32-bound-when-stack-segment-assumptions32
                               STACK-SEGMENT-ASSUMPTIONS32))))

(defthm eff-addrs-lemma
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86)
                (natp stack-slots-needed)
;                (<= 1 stack-slots-needed)
;                (integerp k)
                (integerp k)
                (<= (- k) (* 4 stack-slots-needed))
                (<= n (- k))
                (integerp n)
                (x86p x86))
           (eff-addrs-okp n (binary-+ k (esp x86)) *ss* x86))
  :hints (("Goal" :use ( segment-max-eff-addr32-bound-when-stack-segment-assumptions32
                                  segment-min-eff-addr32-bound-when-stack-segment-assumptions32)
           :in-theory (disable segment-min-eff-addr32-bound-when-stack-segment-assumptions32
                               segment-max-eff-addr32-bound-when-stack-segment-assumptions32
                               STACK-SEGMENT-ASSUMPTIONS32))))

;slow
(defthm eip-of-xw-irrel
  (implies (not (equal fld :rip))
           (equal (eip (xw fld index value x86))
                  (eip x86)))
  :hints (("Goal" :in-theory (enable eip))))

(defthm eip-of-xw-of-rip
  (equal (eip (xw :rip nil value x86))
         (logext 48 value))
  :hints (("Goal" :in-theory (enable eip))))

(defthm eff-addr-okp-when-code-segment-assumptions32-for-code
  (implies (and (code-segment-assumptions32-for-code code offset x86-2) ;binds the free var
                (code-segment-assumptions32-for-code code offset x86)
                (code-segment-well-formedp x86)
                (integerp eff-addr)
                (<= offset eff-addr)
                (< eff-addr (+ offset (len code)))
                (natp offset)
                (x86p x86))
           (eff-addr-okp eff-addr *cs* x86))
  :hints (("Goal" :in-theory (enable code-segment-assumptions32-for-code))))

(defthm eff-addrs-okp-when-code-segment-assumptions32-for-code
  (implies (and (code-segment-assumptions32-for-code code offset x86-2) ;binds the free var
                (code-segment-assumptions32-for-code code offset x86)
                (code-segment-well-formedp x86)
                (natp n)
                (integerp eff-addr)
                (<= offset eff-addr)
                (< (+ -1 eff-addr n) (+ offset (len code)))
                (natp offset)
                (x86p x86))
           (eff-addrs-okp n eff-addr *cs* x86))
  :hints (("Goal" :in-theory (enable code-segment-assumptions32-for-code))))

(acl2::add-known-boolean eff-addr-okp)

(acl2::def-constant-opener seg-regp)
(acl2::def-constant-opener INTEGER-RANGE-P)

;could widen these ranges
(defthm SIGNED-BYTE-P-of-+-of-esp
  (implies (and (integerp n)
                (<= (- (expt 2 32)) n)
                (<= n (expt 2 32))
                (unsigned-byte-p 32 (esp x86))
                )
           (signed-byte-p '64 (binary-+ n (esp x86))))
  :hints (("Goal" :in-theory (enable esp SIGNED-BYTE-P))))

(defthm x86isa::ea-to-la-of-write-byte-to-segment
  (equal (ea-to-la x86isa::proc-mode x86isa::eff-addr x86isa::seg-reg nbytes (write-byte-to-segment eff-addr2 seg-reg2 val x86))
         (ea-to-la x86isa::proc-mode x86isa::eff-addr x86isa::seg-reg nbytes x86))
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment)
                                  (ea-to-la)))))

(defthm ea-to-la-of-write-to-segment
  (equal (ea-to-la x86isa::proc-mode x86isa::eff-addr x86isa::seg-reg nbytes (write-to-segment n2 eff-addr2 seg-reg2 val x86))
         (ea-to-la x86isa::proc-mode x86isa::eff-addr x86isa::seg-reg nbytes x86))
  :hints (("Goal" :in-theory (e/d (write-to-segment)
                                  (ea-to-la)))))

(defthm alignment-checking-enabled-p-of-write-byte-to-segment
  (equal (alignment-checking-enabled-p (write-byte-to-segment eff-addr seg-reg val x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm alignment-checking-enabled-p-of-write-to-segment
  (equal (alignment-checking-enabled-p (write-to-segment n eff-addr seg-reg val x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;; I wonder if this fact would let us drop come checks from the model
(defthm canonical-address-p-of-mv-nth-1-of-ea-to-la-of-cs
  (canonical-address-p (mv-nth 1 (ea-to-la *compatibility-mode* eff-addr *cs* nbytes x86))))

;; I wonder if this fact would let us drop come checks from the model
(defthm canonical-address-p-of-mv-nth-1-of-ea-to-la-of-ss
  (canonical-address-p (mv-nth 1 (ea-to-la *compatibility-mode* eff-addr *ss* nbytes x86))))

(defthm fix-of-mv-nth-1-of-ea-to-la
  (equal (fix (mv-nth '1 (ea-to-la$inline proc-mode eff-addr seg-reg nbytes x86)))
         (mv-nth '1 (ea-to-la$inline proc-mode eff-addr seg-reg nbytes x86))))

;; (defthm read-of-ea-to-la-becomes-read-byte-from-segment
;;   (implies (and (eff-addrs-okp nbytes eff-addr seg-reg x86)
;;                 (equal (ea-to-la *compatibility-mode* eff-addr seg-reg nbytes x86-2)
;;                        (ea-to-la *compatibility-mode* eff-addr seg-reg nbytes x86))
;;                 ;(x86p x86)
;;                 (x86p x86-2)
;;                 )
;;            (equal (read 1 (mv-nth 1 (ea-to-la *compatibility-mode* eff-addr seg-reg nbytes x86)) x86-2)
;;                   (read-byte-from-segment eff-addr seg-reg x86-2)))
;;   :hints (("Goal" :in-theory (enable read-byte-from-segment read-byte
;;                                      segment-min-eff-addr32
;;                                      segment-max-eff-addr32))))

;; (defthm read-of-ea-to-la-becomes-read-byte-from-segment-simple
;;   (implies (and (eff-addrs-okp nbytes eff-addr seg-reg x86)
;;                 (x86p x86))
;;            (equal (read 1 (mv-nth 1 (ea-to-la *compatibility-mode* eff-addr seg-reg nbytes x86)) x86)
;;                   (read-byte-from-segment eff-addr seg-reg x86)))
;;   :hints (("Goal" :in-theory (enable read-byte-from-segment read-byte
;;                                      segment-min-eff-addr32
;;                                      segment-max-eff-addr32))))

(defthm mv-nth-0-of-ea-to-la
  (implies (and (or (equal seg-reg *cs*)
                    (equal seg-reg *ss*)
                    (not (< (xr :seg-visible seg-reg x86) 4)))
                (x86p x86))
           (iff (mv-nth 0 (ea-to-la *compatibility-mode* eff-addr seg-reg nbytes x86))
                (not (eff-addrs-okp nbytes eff-addr seg-reg x86))))
  :hints (("Goal" :in-theory (enable segment-max-eff-addr32 segment-base-and-bounds segment-min-eff-addr32))))

(defthm integerp-of-if
  (equal (integerp (if test tp ep))
         (if test (integerp tp) (integerp ep))))

;; I wonder if this fact would let us drop come checks from the model
(defthm canonical-address-p-of-+-of-mv-nth-1-of-ea-to-la-of-ss
  (implies (and (signed-byte-p 33 k) ;gen?
                )
           (canonical-address-p (+ k (mv-nth 1 (ea-to-la *compatibility-mode* eff-addr *ss* nbytes x86)))))
  :hints (("Goal" :in-theory (enable SIGNED-BYTE-P CANONICAL-ADDRESS-P))))

(defthm 32-bit-segment-size-of-set-flag
  (equal (32-bit-segment-size seg-reg (set-flag flg val x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (e/d (32-bit-segment-size) ()))))

(defthm 32-bit-segment-start-and-size-of-set-flag
  (equal (32-bit-segment-start-and-size seg-reg (set-flag flg val x86))
         (32-bit-segment-start-and-size seg-reg x86))
  :hints (("Goal" :in-theory (e/d (32-bit-segment-start-and-size) ()))))

(defthm 32-bit-segment-start-of-set-flag
  (equal (32-bit-segment-start seg-reg (set-flag flg val x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (e/d (32-bit-segment-start) ()))))

(defthm well-formed-32-bit-segmentp-of-set-flag
  (equal (well-formed-32-bit-segmentp seg-reg (set-flag flg val x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (e/d (well-formed-32-bit-segmentp) ()))))

(defthm read-byte-from-segment-of-set-flag
  (equal (read-byte-from-segment eff-addr seg-reg (set-flag flg val x86))
         (read-byte-from-segment eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm read-byte-list-from-segment-of-set-flag
  (equal (read-byte-list-from-segment n eff-addr seg-reg (set-flag flg val x86))
         (read-byte-list-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable read-byte-list-from-segment))))

(defthm code-segment-assumptions32-for-code-of-set-flag
  (equal (code-segment-assumptions32-for-code code offset (set-flag flg val x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (e/d (code-segment-assumptions32-for-code set-flag)
                                  (;; x86isa::seg-hidden-basei-is-n64p x86isa::seg-hidden-limiti-is-n32pg
                                   ;;                                  x86isa::seg-hidden-attri-is-n16p
                                                                    )))))

(defthm code-segment-well-formedp-of-set-flag
  (equal (code-segment-well-formedp (set-flag flg val x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (e/d (code-segment-well-formedp set-flag)
                                  (;; x86isa::seg-hidden-basei-is-n64p x86isa::seg-hidden-limiti-is-n32p
                                   ;;                                  x86isa::seg-hidden-attri-is-n16p
                                                                    )))))

(defthm eff-addr-okp-of-set-flag
  (equal (eff-addr-okp eff-addr seg-reg (set-flag flg val x86))
         (eff-addr-okp eff-addr seg-reg x86)))

(defthm eff-addr-okp-of-WRITE-TO-SEGMENT
  (equal (eff-addr-okp eff-addr seg-reg (WRITE-TO-SEGMENT N2 EFF-ADDR2 SEG-REG2 VAL2 X86))
         (eff-addr-okp eff-addr seg-reg X86)))

(defthm stack-segment-assumptions32-of-xw-of-rgf
  (implies (not (equal *rsp* reg))
           (equal (stack-segment-assumptions32 stack-slots-needed (xw :rgf reg val x86))
                  (stack-segment-assumptions32 stack-slots-needed x86)))
  :hints (("Goal" :in-theory (e/d (stack-segment-assumptions32)
                                  (;; x86isa::rgfi-is-i64p
                                   ;; x86isa::seg-hidden-basei-is-n64p
                                   ;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-attri-is-n16p
                                   )))))

;slow
(defthm esp-of-xw-irrel
  (implies (not (and (equal :rgf fld)
                     (equal *rsp* index)))
           (equal (esp (xw fld index val x86))
                  (esp x86)))
  :hints (("Goal" :in-theory (enable esp))))

(defthm esp-of-xw-of-rgf-and-rsp
  (equal (esp (xw :rgf *rsp* val x86))
         (logext 64 val))
  :hints (("Goal" :in-theory (enable esp))))

(defthm eff-addr-okp-of-+-of-esp
  (implies (and (<= off 0)
                (stack-segment-assumptions32 stack-slots-needed x86) ;binds stack-slots-needed
                ;(stack-segment-assumptions32 stack-slots-needed x86-2)
                (equal (segment-base-and-bounds *compatibility-mode* *ss* x86)
                       (segment-base-and-bounds *compatibility-mode* *ss* x86-2))
                (integerp off)
                (<= (* -4 stack-slots-needed) off)
                (x86p x86))
           (eff-addr-okp (binary-+ off (esp x86)) *ss* x86-2))
  :hints (("Goal" :in-theory (enable esp segment-max-eff-addr32 segment-min-eff-addr32 SEGMENT-BASE-AND-BOUNDS))))

(defthm eff-addr-okp-of-esp
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86) ;binds stack-slots-needed
                ;(stack-segment-assumptions32 stack-slots-needed x86-2)
                (equal (segment-base-and-bounds *compatibility-mode* *ss* x86)
                       (segment-base-and-bounds *compatibility-mode* *ss* x86-2))
                (natp stack-slots-needed)
                (x86p x86)
;                (x86p x86-2)
                )
           (eff-addr-okp (esp x86) *ss* x86-2))
  :hints (("Goal" :in-theory (enable esp segment-max-eff-addr32 segment-min-eff-addr32 SEGMENT-BASE-AND-BOUNDS))))

(defthm eff-addr-okp-of-+-of-esp-positive-offset
  (implies (and (natp off)
                (<= off 11)
                (stack-segment-assumptions32 stack-slots-needed x86) ;binds stack-slots-needed
;                (stack-segment-assumptions32 stack-slots-needed x86-2)
                (equal (segment-base-and-bounds *compatibility-mode* *ss* x86)
                       (segment-base-and-bounds *compatibility-mode* *ss* x86-2))
                (x86p x86)
;                (x86p x86-2)
                )
           (eff-addr-okp (binary-+ off (esp x86)) *ss* x86-2))
  :hints (("Goal" :in-theory (enable esp segment-max-eff-addr32 segment-min-eff-addr32 SEGMENT-BASE-AND-BOUNDS))))

(defthm ea-to-la-of-set-flag
  (equal (ea-to-la proc-mode eff-addr seg-reg nbytes (set-flag flg val x86))
         (ea-to-la proc-mode eff-addr seg-reg nbytes x86)))

;; (defthm read-of-ea-to-la-becomes-read-from-segment
;;   (implies (and (eff-addrs-okp n eff-addr seg-reg x86-2)
;;                 (equal (ea-to-la *compatibility-mode* eff-addr seg-reg x86)
;;                        (ea-to-la *compatibility-mode* eff-addr seg-reg x86-2))
;;                 (x86p x86)
;;                 (x86p x86-2))
;;            (equal (read n (mv-nth 1 (ea-to-la *compatibility-mode* eff-addr seg-reg n x86)) x86-2)
;;                   ;; convert to a chunk:
;;                   (read-from-segment n eff-addr seg-reg x86-2)))
;; )

;; (defthm fix-of-esp
;;   (equal (fix (esp x86))
;;          (esp x86)))

(defthm unsigned-byte-p-of-esp-when-stack-segment-assumptions32
  (implies (stack-segment-assumptions32 stack-slots-needed x86)
           (unsigned-byte-p 32 (esp x86)))
  :hints (("Goal" :in-theory (enable stack-segment-assumptions32 esp))))

;; (defthm bvchop-32-of-esp
;;   (implies (and (segment-is-32-bitsp 2 x86)
;;                 (not (64-bit-modep x86)))
;;            (equal (bvchop 32 (esp x86))
;;                   (esp x86)))
;;   :hints (("Goal" :in-theory (enable esp))))

;; (defthm unsigned-byte-p-of-esp
;;   (implies (and (segment-is-32-bitsp 2 x86)
;;                 (not (64-bit-modep x86)))
;;            (unsigned-byte-p 32 (esp x86)))
;;   :hints (("Goal" :in-theory (enable esp))))

(defthm natp-of-esp-when-stack-segment-assumptions32
  (implies (stack-segment-assumptions32 stack-slots-needed x86)
           (natp (esp x86)))
  :hints (("Goal" :in-theory (enable stack-segment-assumptions32 esp))))

;; (defthm natp-of-esp
;;   (implies (and ;(segment-is-32-bitsp 2 x86)
;;                 (not (64-bit-modep x86)))
;;            (natp (esp x86)))
;;   :hints (("Goal" :in-theory (enable esp))))

(defthm integerp-of-esp
  (integerp (esp x86))
  :hints (("Goal" :in-theory (enable esp))))

(defthm signed-byte-p-64-of-esp
  (implies (and (segment-is-32-bitsp 2 x86)
                (not (64-bit-modep x86)))
           (signed-byte-p 64 (esp x86)))
  :hints (("Goal" :in-theory (enable esp))))

(defthm not-mv-nth-0-of-add-to-*sp-positive-offset
  (implies (and (<= delta 11) ;because of the 11 in stack-segment-assumptions32-helper
                (natp delta)
                (stack-segment-assumptions32 stack-slots-needed x86) ;stack-slots-needed is a free var and usually will be a constant
                ;;(stack-segment-assumptions32 stack-slots-needed x86-2)
                (equal (segment-base-and-bounds *compatibility-mode* *ss* x86)
                       (segment-base-and-bounds *compatibility-mode* *ss* x86-2))
                (not (64-bit-modep x86-2))
                (not (64-bit-modep x86))
                (x86p x86-2)
                (x86p x86))
           (not (mv-nth 0 (x86isa::add-to-*sp *compatibility-mode* (esp x86) delta x86-2))))
  :hints (("Goal" :in-theory (e/d (x86isa::add-to-*sp
                                   esp
                                   segment-base-and-bounds
                                   ;;segment-is-32-bitsp-intro-2
                                   )
                                  (acl2::bvplus-recollapse)))))

;;;
;;; read-from-segment
;;;

;; Read an N-byte chunk of data at effective address EFF-ADDR in the segment
;; indicated by SEG-REG.  Reads in a little-endian fashion: bytes with lower
;; addresses occupy less significant bits of the result.
(defun read-from-segment (n eff-addr seg-reg x86)
  (declare (xargs :stobjs x86
                  :guard (and (seg-regp seg-reg)
                              (integerp eff-addr)
                              (natp n))))
  (if (zp n)
      0
    (bvcat  (* 8 (- N 1))
            (read-from-segment (- n 1) (+ 1 eff-addr) seg-reg x86)
            8
            (read-byte-from-segment eff-addr seg-reg x86)
            )))

(defthm unsigned-byte-p-of-read-byte-from-segment
  (implies (x86p x86)
           (unsigned-byte-p 8 (read-byte-from-segment eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-byte-from-segment ifix))))

(defthm unsigned-byte-p-of-read-from-segment-helper
  (implies (natp n)
           (unsigned-byte-p (* 8 n) (read-from-segment n eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-from-segment))))

(defthm unsigned-byte-p-of-read-from-segment
  (implies (and (<= (* 8 n) n2)
                (natp n2)
                (natp n))
           (unsigned-byte-p n2 (read-from-segment n eff-addr seg-reg x86)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-read-from-segment-helper)
           :in-theory (disable unsigned-byte-p-of-read-from-segment-helper))))

(defthm read-from-segment-not-negative
  (not (< (read-from-segment n eff-addr seg-reg x86) 0)))

(local (in-theory (disable acl2::bvplus-recollapse)))

(defthm read-from-segment-of-xw
  (implies (and (not (equal :mem fld))
                (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (read-from-segment n eff-addr seg-reg (xw fld index val x86))
                  (read-from-segment n eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-from-segment))))

;; ;todo: don't go via read (that should be for 64-bit only)
;; (defthm read-of-mv-nth-1-of-ea-to-la-becomes-read-from-segment
;;   (implies (and (eff-addrs-okp n eff-addr seg-reg x86)
;; ;               (equal n 2)
;;                 (natp n)
;;                 (natp eff-addr)
;;                 (<= (+ n eff-addr) (expt 2 32))
;;                 ;; the segmentation info is the same in x86 and x86-2:
;;                 (equal (32-bit-segment-size seg-reg x86-2)
;;                        (32-bit-segment-size seg-reg x86))
;;                 (equal (32-bit-segment-start seg-reg x86-2)
;;                        (32-bit-segment-start seg-reg x86))
;;                 (equal (segment-expand-down-bit seg-reg x86)
;;                        (segment-expand-down-bit seg-reg x86-2))
;;                 (segment-is-32-bitsp seg-reg x86)
;;                 (segment-is-32-bitsp seg-reg x86-2)
;;                 (well-formed-32-bit-segmentp seg-reg x86)
;;                 (well-formed-32-bit-segmentp seg-reg x86-2)
;;                 (x86p x86)
;;                 (x86p x86-2))
;;            (equal (read n (mv-nth 1 (ea-to-la *compatibility-mode* eff-addr seg-reg n x86)) x86-2)
;;                   (read-from-segment n eff-addr seg-reg x86-2)))
;;   :otf-flg t
;;   :hints (("Goal" ;:expand ((:free (n EFF-ADDR SEG-REG X86) (READ-FROM-SEGMENT n EFF-ADDR SEG-REG X86)))
;;            :expand ((READ-BYTE-FROM-SEGMENT EFF-ADDR SEG-REG X86-2)
;;                     (:free (addr x86) (READ N addr x86)))
;;            :induct (READ-FROM-SEGMENT N EFF-ADDR SEG-REG X86-2)
;;            :in-theory (e/d (READ-BYTE-FROM-SEGMENT
;;                             bvplus
;;                             acl2::bvchop-of-sum-cases
;;                             well-formed-32-bit-segmentp
;;                             READ-FROM-SEGMENT
;;                             SEGMENT-BASE-AND-BOUNDS
;;                             SEGMENT-MAX-EFF-ADDR32
;;                             SEGMENT-MIN-EFF-ADDR32
;;                             read
;;                             READ-BYTE
;;                             32-BIT-SEGMENT-START
;;                             32-BIT-SEGMENT-Size
;;                             32-BIT-SEGMENT-START-AND-SIZE
;;                             )
;;                            ( ;ea-to-la
;;                             ACL2::BVCAT-EQUAL-REWRITE-ALT
;;                             ACL2::BVCAT-EQUAL-REWRITE)))))

(defthm unsigned-byte-p-of-+-of-esp
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86-orig)
                (stack-segment-assumptions32 stack-slots-needed x86)
                (natp k)
                (<= k 11)
                )
           (unsigned-byte-p 32 (+ k (esp x86))))
  :hints (("Goal" :in-theory (enable esp))))

(defthm eff-addrs-okp-of-+-of-esp-positive-offset
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86-orig) ;binds the free var
                (stack-segment-assumptions32 stack-slots-needed x86)
                (natp k)
                (natp n)
                (<= (+ k n) 12)
                (x86p x86))
           (eff-addrs-okp n (+ k (esp x86)) *ss* x86))
  :hints (("Goal" :in-theory (enable esp SEGMENT-MAX-EFF-ADDR32
                                     SEGMENT-MIN-EFF-ADDR32
                                     SEGMENT-BASE-AND-BOUNDS))))

(defthm esp-bound
  (implies  (and (stack-segment-assumptions32 stack-slots-needed x86-orig) ;binds the free var stack-slots-needed
                 (stack-segment-assumptions32 stack-slots-needed x86)
                 (natp k)
                 (<= 4294967284 k) ;gen?
                 )
            (not (< k (ESP X86))))
  :hints (("Goal" :in-theory (enable esp))))

(defthm eff-addrs-okp-of-esp
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86-orig) ;binds the free var stack-slots-needed
                (stack-segment-assumptions32 stack-slots-needed x86)
                (natp stack-slots-needed)
;                (<= 1 stack-slots-needed)
                (x86p x86))
           (eff-addrs-okp 4 (esp x86) *ss* x86))
  :hints (("Goal"
           :in-theory (e/d (esp
                            stack-segment-assumptions32
                            segment-max-eff-addr32
                            segment-base-and-bounds
                            segment-min-eff-addr32)
                           ()))))



;or have this chop
;; (defun sep-eff-addr-ranges (eff-addr1 n1 eff-addr2 n2)
;;   (or (<= (+ n1 eff-addr1) eff-addr2)
;;       (<= (+ n2 eff-addr2) eff-addr1)))

(local (in-theory (disable acl2::bvminus-becomes-bvplus-of-bvuminus)))

;; Check whether the ranges of effective addresses (which may wrap around mod 2^32) are disjoint.
;uses cyclic ranges
(defun sep-eff-addr-ranges (eff-addr1 n1 eff-addr2 n2)
  (declare (xargs :guard (and (unsigned-byte-p 32 eff-addr1)
                              (unsigned-byte-p 32 eff-addr2)
                              (unsigned-byte-p 32 n2)
                              (unsigned-byte-p 32 n1))))
  (or (zp n1)
      (zp n2)
      (and (bvle 32 n1 (bvminus 32 eff-addr2 eff-addr1))
           (bvle 32 n2 (bvminus 32 eff-addr1 eff-addr2)))))

(defthm sep-eff-addr-ranges-of-0-arg2
  (sep-eff-addr-ranges eff-addr1 0 eff-addr2 n2))

(defthm sep-eff-addr-ranges-of-0-arg4
  (sep-eff-addr-ranges eff-addr1 n1 eff-addr2 0))

(defthm sep-eff-addr-ranges-of-all-but-first
  (implies (and (sep-eff-addr-ranges eff-addr1 n1 eff-addr2 n2)
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n2) ;gen?
                (unsigned-byte-p 32 n1) ;gen?
                )
           (sep-eff-addr-ranges (+ 1 eff-addr1) (+ -1 n1) eff-addr2 n2))
  :hints (("Goal" :in-theory (e/d (bvlt
                                   bvplus
                                   bvuminus
                                   bvminus
                                   acl2::bvchop-of-sum-cases)
                                  (acl2::bvplus-recollapse)))) )

(defthm sep-eff-addr-ranges-of-all-but-first-alt
  (implies (and (sep-eff-addr-ranges eff-addr1 n1 eff-addr2 n2)
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n2)
                (unsigned-byte-p 32 n1))
           (sep-eff-addr-ranges eff-addr1 n1 (+ 1 eff-addr2) (+ -1 n2)))
  :hints (("Goal"
           :in-theory (e/d (bvlt
                            bvplus
                            bvuminus
                            bvminus
                            acl2::bvchop-of-sum-cases)
                           (acl2::bvplus-recollapse)))) )

(defthm sep-eff-addr-ranges-of-all-but-first-alt-alt
  (implies (and (sep-eff-addr-ranges eff-addr2 n2 eff-addr1 n1)
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n2)
                (unsigned-byte-p 32 n1))
           (sep-eff-addr-ranges (+ 1 eff-addr1) (+ -1 n1) eff-addr2 n2))
  :hints (("Goal" :in-theory (e/d (bvlt
                                   bvplus
                                   bvuminus
                                   bvminus
                                   acl2::bvchop-of-sum-cases)
                                  (acl2::bvplus-recollapse)))) )

;; potentially could mess things up
(defthmd sep-eff-addr-ranges-swap
  (implies (syntaxp (acl2::smaller-termp eff-addr2 eff-addr1))
           (equal (sep-eff-addr-ranges eff-addr1 n1 eff-addr2 n2)
                  (sep-eff-addr-ranges eff-addr2 n2 eff-addr1 n1)))
  :hints (("Goal" :in-theory (enable sep-eff-addr-ranges))))

(defthm sep-eff-addr-ranges-monotone-arg2
  (implies (and (sep-eff-addr-ranges eff-addr1 n1+ eff-addr2 n2)
                (<= n1 n1+)
                (unsigned-byte-p 32 n1)
                (unsigned-byte-p 32 n1+))
           (sep-eff-addr-ranges eff-addr1 n1 eff-addr2 n2))
  :hints (("Goal"
           :in-theory (e/d (sep-eff-addr-ranges
                            bvlt
                            bvplus
                            bvuminus
                            bvminus
                            acl2::bvchop-of-sum-cases)
                           (acl2::bvplus-recollapse)))))

(defthm sep-eff-addr-ranges-of-1-arg2-adjacent
  (implies (and (integerp eff-addr)
                (unsigned-byte-p 32 n))
           (sep-eff-addr-ranges eff-addr 1 (+ 1 eff-addr) n))
  :hints (("Goal" :in-theory (e/d (bvlt
                                   bvplus
                                   bvuminus
                                   bvminus
                                   acl2::bvchop-of-sum-cases)
                                  (acl2::bvplus-recollapse)))))

(local (acl2::limit-expt)) ;prevent crashes

(defthm read-byte-from-segment-of-write-to-segment-irrel
  (implies (and (sep-eff-addr-ranges eff-addr1 1 eff-addr2 n2)
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n2)
                (x86p x86))
           (equal (read-byte-from-segment eff-addr1 seg-reg (write-to-segment n2 eff-addr2 seg-reg val x86))
                  (read-byte-from-segment eff-addr1 seg-reg x86)))
  :hints (("Goal" :induct (write-to-segment n2 eff-addr2 seg-reg val x86)
           :in-theory (enable write-to-segment
                              bvlt
                              bvplus
                              bvuminus
                              bvminus
                              acl2::bvchop-of-sum-cases
                              write-to-segment-of-write-byte-to-segment))))

(defthm integerp-of-mv-nth-0-of-segment-base-and-bounds-gen
  (integerp (mv-nth 0 (segment-base-and-bounds 1 seg-reg x86)))
  :hints (("Goal" :in-theory (e/d (segment-base-and-bounds)
                                  (;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-attri-is-n16p
                                   ;; x86isa::seg-hidden-basei-is-n64p
                                   )))))

(defthm write-byte-to-segment-of-bvchop
  (implies (integerp eff-addr)
           (equal (write-byte-to-segment (bvchop 32 eff-addr) seg-reg val x86)
                  (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm write-byte-to-segment-subst
  (implies (and (equal (bvchop 32 eff-addr) (bvchop 32 eff-addr2))
                (syntaxp (acl2::smaller-termp eff-addr2 eff-addr))
                (integerp eff-addr)
                (integerp eff-addr2))
           (equal (write-byte-to-segment eff-addr seg-reg val x86)
                  (write-byte-to-segment eff-addr2 seg-reg val x86)))
  :hints (("Goal" :use ((:instance write-byte-to-segment-of-bvchop)
                        (:instance write-byte-to-segment-of-bvchop (eff-addr eff-addr2))))))

(defthm bvchop-of-+-of+-subst-smaller
  (implies (and (equal (bvchop 32 b) (bvchop 32 b0))
                (syntaxp (acl2::smaller-termp b0 b))
                (integerp b)
                (integerp b0)
                (integerp a)
                (integerp c))
           (equal (bvchop '32 (binary-+ a (binary-+ c (- b))))
                  (bvchop '32 (binary-+ a (binary-+ c (- b0)))))))

;dup
(defun double-write-induct-two-addrs
  (n base-addr base-addr2 val x86)
  (if (zp n)
      (list n base-addr base-addr2 val x86)
      (double-write-induct-two-addrs (+ -1 n)
                                     (+ 1 base-addr)
                                     (+ 1 base-addr2)
                                     (logtail 8 val)
                                     x86)))

(local (include-book "kestrel/bv/rules3" :dir :system))
(local (in-theory (disable ACL2::PLUS-BVCAT-WITH-0))) ;todo

(defthm write-to-segment-of-bvchop-helper
  (implies (and (equal (bvchop 32 eff-addr1)
                       (bvchop 32 eff-addr2))
                (syntaxp (acl2::smaller-termp eff-addr2 eff-addr1))
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n)
                (x86p x86) ;drop?
                )
           (equal (write-to-segment n eff-addr1 seg-reg val x86)
                  (write-to-segment n eff-addr2 seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment
                                     write-to-segment-of-write-byte-to-segment)
           :induct (double-write-induct-two-addrs n eff-addr1 eff-addr2 val x86)
           :expand ((write-to-segment n eff-addr1 seg-reg val x86)
                    (write-to-segment n eff-addr2 seg-reg val x86)))))

(defthm write-to-segment-of-bvchop
  (implies (and (integerp eff-addr)
                (unsigned-byte-p 32 n)
                (x86p x86) ;drop?
                )
           (equal (write-to-segment n (bvchop 32 eff-addr) seg-reg val x86)
                  (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :use (:instance write-to-segment-of-bvchop-helper
                                  (eff-addr1 eff-addr)
                                  (eff-addr2 (bvchop 32 eff-addr)))
           :in-theory (disable write-to-segment-of-bvchop-helper))))

(defthm logtail-of-logtail-gen
  (equal (logtail m (logtail n x))
         (logtail (+ (nfix m) (nfix n)) x))
  :hints (("Goal" :in-theory (enable logtail acl2::expt-of-+))))

;move
(defthm acl2::bvchop-of-logtail-becomes-slice-gen
  (implies (and (natp acl2::size1)
                ;;(natp acl2::size2)
                )
           (equal (bvchop acl2::size1 (logtail acl2::size2 x))
                  (slice (+ -1 acl2::size1 (nfix acl2::size2))
                         (nfix acl2::size2)
                         x)))
  :hints (("Goal" :in-theory (enable nfix acl2::bvchop-of-logtail-becomes-slice))))

;simple ordering
(defthm read-byte-from-segment-of-write-to-segment-not-irrel-1
  (implies (and (<= eff-addr2 eff-addr1)
                (< eff-addr1 (+ eff-addr2 n2))
                (unsigned-byte-p 32 n2)
                (unsigned-byte-p 32 eff-addr1) ;gen?
                (unsigned-byte-p 32 eff-addr2) ;gen?
                (x86p x86))
           (equal (read-byte-from-segment eff-addr1 seg-reg (write-to-segment n2 eff-addr2 seg-reg val x86))
                  (bvchop 8 (logtail
                              (* 8 (- eff-addr1 eff-addr2)) ;k
                              val))))
  :hints (("Goal"
           :induct (write-to-segment n2 eff-addr2 seg-reg val x86)
           :in-theory (enable write-to-segment
                              bvlt
                              bvplus
                              bvuminus
                              bvminus
                              acl2::bvchop-of-sum-cases
                              unsigned-byte-p
                              write-to-segment-of-write-byte-to-segment))))


;; (defthm read-byte-from-segment-of-write-to-segment-not-irrel
;;   (implies (and ;(not (sep-eff-addr-ranges eff-addr1 1 eff-addr2 n2))
;;             (< (bvminus 32 eff-addr1 eff-addr2) n2)
;;             (integerp eff-addr1)
;;             (integerp eff-addr2)
;;             (unsigned-byte-p 32 n2)
;;             (unsigned-byte-p 32 eff-addr1)
;;             (unsigned-byte-p 32 eff-addr2)
;; ;            (equal 6 eff-addr2)
;; ;            (equal 8 eff-addr1)
;;             (x86p x86))
;;            (equal (read-byte-from-segment eff-addr1 seg-reg (write-to-segment n2 eff-addr2 seg-reg val x86))
;;                   (bvchop 8 (logtail
;;                               (* 8 (- eff-addr1 eff-addr2)) ;k
;;                               val))))
;;   :hints (("Goal"
;;            :induct (write-to-segment n2 eff-addr2 seg-reg val x86)
;;            ;:induct (double-write-induct-two-addrs n2 eff-addr1 eff-addr2 val x86)
;;            :in-theory (e/d (write-to-segment
;;                               bvlt
;;                               bvplus
;;                               bvuminus
;;                               bvminus
;;                               acl2::bvchop-of-sum-cases
;;                               unsigned-byte-p
;;                               write-to-segment-of-write-byte-to-segment)
;;                            (ACL2::BVCHOP-PLUS-1-SPLIT)))))

;; (defthm read-byte-from-segment-of-write-to-segment-both
;;   (implies (and (integerp eff-addr1)
;;                 (integerp eff-addr2)
;;                 (unsigned-byte-p 32 n2)
;;                 (unsigned-byte-p 32 eff-addr1)
;;                 (unsigned-byte-p 32 eff-addr2)
;;                 (x86p x86))
;;            (equal (read-byte-from-segment eff-addr1 seg-reg (write-to-segment n2 eff-addr2 seg-reg val x86))
;;                   (if  (< (bvminus 32 eff-addr1 eff-addr2) n2)
;;                       (bvchop 8 (logtail (* 8 (- eff-addr1 eff-addr2)) val))
;;                     (read-byte-from-segment eff-addr1 seg-reg x86)))))



;; (thm
;;  (implies (and (<= (+ eff-addr1 n1) eff-addr2)
;;                (<= (+ eff-addr2 n2) 4294967295)
;;                (unsigned-byte-p 32 eff-addr2)
;;                (unsigned-byte-p 32 eff-addr1)
;;                (unsigned-byte-p 32 n2)
;;                (unsigned-byte-p 32 n1)
;;                (x86p x86))
;;           (equal (read-from-segment n1 eff-addr1 seg-reg (write-to-segment n2 eff-addr2 seg-reg val x86))
;;                  (read-from-segment n1 eff-addr1 seg-reg x86)))
;;  :hints (("Goal"; :induct (read-from-segment n1 addr seg-reg x86)
;;           :expand ((read-from-segment n1 eff-addr1 seg-reg x86)
;;                    (read-from-segment n1 eff-addr1 seg-reg
;;                                    (write-to-segment n2 eff-addr2 seg-reg val x86)))
;;           :in-theory (enable write-to-segment
;;                              bvplus
;;                              bvuminus
;;                              bvminus
;;                              acl2::bvchop-of-sum-cases
;;                              write-to-segment-of-write-byte-to-segment)
;;           )))

(local (in-theory (disable ACL2::+-OF-MINUS-CONSTANT-VERSION))) ;looped

(defthm read-byte-from-segment-of-bvchop
  (implies (integerp eff-addr)
           (equal (read-byte-from-segment (bvchop 32 eff-addr) seg-reg x86)
                  (read-byte-from-segment eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-byte-from-segment))))

(defthm read-byte-from-segment-subst
  (implies (and (equal (bvchop 32 eff-addr) (bvchop 32 eff-addr2))
                (syntaxp (acl2::smaller-termp eff-addr2 eff-addr))
                (integerp eff-addr)
                (integerp eff-addr2))
           (equal (read-byte-from-segment eff-addr seg-reg x86)
                  (read-byte-from-segment eff-addr2 seg-reg x86)))
  :hints (("Goal" :use ((:instance read-byte-from-segment-of-bvchop)
                        (:instance read-byte-from-segment-of-bvchop (eff-addr eff-addr2))))))

(defthm read-from-segment-of-bvchop-helper
  (implies (and (equal (bvchop 32 eff-addr1)
                       (bvchop 32 eff-addr2))
                (syntaxp (acl2::smaller-termp eff-addr2 eff-addr1))
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n)
                (x86p x86) ;drop?
                )
           (equal (read-from-segment n eff-addr1 seg-reg x86)
                  (read-from-segment n eff-addr2 seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-from-segment)
           :induct (double-write-induct-two-addrs n eff-addr1 eff-addr2
                                                  val ;dummy
                                                  x86)
           :expand ((read-from-segment n eff-addr1 seg-reg x86)
                    (read-from-segment n eff-addr2 seg-reg x86)))))

(defthm read-from-segment-of-bvchop
  (implies (and (integerp eff-addr)
                (unsigned-byte-p 32 n)
                (x86p x86) ;drop?
                )
           (equal (read-from-segment n (bvchop 32 eff-addr) seg-reg x86)
                  (read-from-segment n eff-addr seg-reg x86)))
  :hints (("Goal" :use (:instance read-from-segment-of-bvchop-helper
                                  (eff-addr1 eff-addr)
                                  (eff-addr2 (bvchop 32 eff-addr)))
           :in-theory (disable read-from-segment-of-bvchop-helper))))

(defthm read-from-segment-normalize-arg2
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (not (unsigned-byte-p 32 k))
                (UNSIGNED-BYTE-P 32 N)
                (x86p x86) ;drop?
                )
           (equal (read-from-segment n k seg-reg x86)
                  (read-from-segment n (bvchop 32 k) seg-reg x86))))

(defthm read-byte-from-segment-of-write-to-segment-irrel-simple
  (implies (and ;(sep-eff-addr-ranges eff-addr1 1 eff-addr2 n2)
            (< eff-addr1 eff-addr2)
            (<= (+ eff-addr2 n2) 4294967295)
            (integerp eff-addr1)
            (integerp eff-addr2)
            (unsigned-byte-p 32 n2)
            (unsigned-byte-p 32 eff-addr1)
            (unsigned-byte-p 32 eff-addr2)
            (x86p x86))
           (equal (read-byte-from-segment eff-addr1 seg-reg (write-to-segment n2 eff-addr2 seg-reg val x86))
                  (read-byte-from-segment eff-addr1 seg-reg x86)))
  :hints (("Goal" ;:induct (write-to-segment n2 eff-addr2 seg-reg val x86)
           :in-theory (enable write-to-segment bvlt bvplus bvuminus
                              bvminus acl2::bvchop-of-sum-cases
                              write-to-segment-of-write-byte-to-segment))))

;this one uses sep-eff-addr-ranges
(defthm read-byte-from-segment-of-write-to-segment-irrel-simple-alt
  (implies (and (sep-eff-addr-ranges eff-addr1 1 eff-addr2 n2)
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n2)
                (x86p x86))
           (equal (read-byte-from-segment eff-addr1 seg-reg (write-to-segment n2 eff-addr2 seg-reg val x86))
                  (read-byte-from-segment eff-addr1 seg-reg x86)))
  :hints (("Goal" ;:induct (write-to-segment n2 eff-addr2 seg-reg val x86)
           :in-theory (enable write-to-segment bvlt bvplus bvuminus
                              bvminus acl2::bvchop-of-sum-cases
                              write-to-segment-of-write-byte-to-segment))))

;;do we still need this?  requires eff-addr2 to be greater
(defthm read-from-segment-of-write-to-segment-irrel-simple
  (implies (and (natp n1)
                (natp eff-addr1)
;               (< eff-addr2 4294967295)
                (<= (+ eff-addr1 n1) eff-addr2)
                (<= (+ eff-addr2 n2) 4294967295)
                (integerp eff-addr2)
                (integerp n2)
                (<= 0 n2)
                (< n2 4294967296)
                (x86p x86))
           (equal (read-from-segment n1 eff-addr1 seg-reg (write-to-segment n2 eff-addr2 seg-reg val x86))
                  (read-from-segment n1 eff-addr1 seg-reg x86))))

(local (include-book "kestrel/axe/rules2" :dir :system)) ;why?

;same segment (we don't know how other segmentes are laid out)
(defthm read-from-segment-of-write-to-segment-irrel
  (implies (and (sep-eff-addr-ranges eff-addr1 n1 eff-addr2 n2)
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n2)
                (unsigned-byte-p 32 n1)
                (x86p x86))
           (equal (read-from-segment n1 eff-addr1 seg-reg (write-to-segment n2 eff-addr2 seg-reg val x86))
                  (read-from-segment n1 eff-addr1 seg-reg x86)))
  :hints (("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal"
           :do-not '(fertilize)
           :induct (READ-FROM-SEGMENT N1 EFF-ADDR1 SEG-REG X86)
           :in-theory (e/d (bvlt
                            BVPLUS
                            bvuminus
                            bvminus
                            acl2::bvchop-of-sum-cases
                            UNSIGNED-BYTE-P)
                           (sep-eff-addr-ranges
                            ACL2::BVCAT-EQUAL-REWRITE-ALT
                            ACL2::BVPLUS-RECOLLAPSE
                            ACL2::BVCAT-EQUAL-REWRITE)))))

(defthm unsigned-byte-p-of-+-of-esp-negative-offset-simple
  (implies (and (stack-segment-assumptions32 stack-slots-needed x86-orig)
                (stack-segment-assumptions32 stack-slots-needed x86)
                (integerp k)
                (<= k 0)
                (<= (- k) (* 4 stack-slots-needed))
                (x86p x86)
                )
           (unsigned-byte-p 32 (+ k (esp x86))))
  :hints (("Goal" :in-theory (enable
                              ;BVPLUS
                              bvuminus
                              bvminus
                              acl2::bvchop-of-sum-cases
                              UNSIGNED-BYTE-P
                              esp SEGMENT-MAX-EFF-ADDR32
                              SEGMENT-MIN-EFF-ADDR32
                              SEGMENT-BASE-AND-BOUNDS
                              WELL-FORMED-32-BIT-SEGMENTP
                              32-BIT-SEGMENT-SIZE
                              32-BIT-SEGMENT-Start
                              32-BIT-SEGMENT-START-AND-SIZE))))

(defthm write-byte-to-segment-of-bvchop-arg3
  (equal (write-byte-to-segment eff-addr2 seg-reg (bvchop 8 val) x86)
         (write-byte-to-segment eff-addr2 seg-reg val x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm read-from-segment-of-write-byte-to-segment-irrel
  (implies (and (sep-eff-addr-ranges eff-addr1 n1 eff-addr2 1)
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n1)
                (x86p x86))
           (equal (read-from-segment n1 eff-addr1 seg-reg (write-byte-to-segment eff-addr2 seg-reg val x86))
                  (read-from-segment n1 eff-addr1 seg-reg x86)))
  :hints (("Goal" :use (:instance read-from-segment-of-write-to-segment-irrel (n2 1))
           :expand (WRITE-TO-SEGMENT 1 EFF-ADDR2 SEG-REG VAL X86)
           :in-theory (e/d (UNSIGNED-BYTE-P ;;bvlt
                            ;;bvminus bvplus bvuminus
                            ;;acl2::bvchop-of-sum-cases
                            WRITE-TO-SEGMENT
                            )
                           ( read-from-segment-of-write-to-segment-irrel)))))

(defthm read-from-segment-of-write-to-segment-same
  (implies (and (integerp eff-addr)
                (unsigned-byte-p 32 n)
                (x86p x86))
           (equal (read-from-segment n eff-addr seg-reg (write-to-segment n eff-addr seg-reg val x86))
                  (bvchop (* 8 n) val)))
  :hints (("Goal"
           :induct (WRITE-TO-SEGMENT N EFF-ADDR SEG-REG VAL X86)
           :expand ((write-to-segment n eff-addr seg-reg val x86))
           :in-theory (e/d (WRITE-TO-SEGMENT
                            WRITE-TO-SEGMENT-OF-WRITE-BYTE-TO-SEGMENT
                            unsigned-byte-p)
                           ((:e expt)
                            acl2::bvcat-equal-rewrite-alt
                            acl2::bvcat-equal-rewrite)))))


(defthm bvminus-cancel-2-2
  (implies (and (integerp a)
                (integerp b)
                (integerp c))
           (equal (bvminus 32 (+ a b) (+ c b))
                  (bvminus 32 a c)))
  :hints (("Goal" :in-theory (enable bvminus acl2::bvchop-of-sum-cases))))

(defthm bvminus-cancel-2-all
  (implies (and (integerp a)
                (integerp b))
           (equal (bvminus 32 (+ a b) b)
                  (bvminus 32 a 0)))
  :hints (("Goal" :in-theory (enable bvminus acl2::bvchop-of-sum-cases))))

(defthm bvminus-cancel-all-2
  (implies (and (integerp a)
                (integerp b))
           (equal (bvminus 32 b (+ a b))
                  (bvminus 32 0 a)))
  :hints (("Goal" :in-theory (enable bvminus acl2::bvchop-of-sum-cases))))

(defthm mv-nth-1-of-add-to-*sp-positive-offset
  (implies (and (<= delta 11)
                (natp delta)
                (stack-segment-assumptions32 stack-slots-needed x86) ;stack-slots-needed is a free var and usually will be a constant
;(stack-segment-assumptions32 stack-slots-needed x86-2)
                (equal (segment-base-and-bounds *compatibility-mode* *ss* x86)
                       (segment-base-and-bounds *compatibility-mode* *ss* x86-2))
                (not (64-bit-modep x86-2))
                (not (64-bit-modep x86))
                (x86p x86-2)
                (x86p x86))
           (equal (mv-nth 1 (x86isa::add-to-*sp *compatibility-mode* (esp x86) delta x86-2))
                  (+ delta (esp x86))))
  :hints (("Goal" :in-theory (e/d (x86isa::add-to-*sp
                                   esp
                                   segment-base-and-bounds
                                   ;;segment-is-32-bitsp-intro-2
                                   )
                                  (acl2::bvplus-recollapse)))))

(defthm segments-separate-of-code-and-stack
  (implies (code-and-stack-segments-separate x86)
           (segments-separate *cs* *ss* x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

(acl2::add-known-boolean segments-separate)

(defthm not-mv-nth-0-of-rme-size$inline
  (implies (and (eff-addrs-okp nbytes eff-addr seg-reg x86)
                (<= nbytes (expt 2 32))
                (natp nbytes)
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86)))
                 (or (equal seg-reg *cs*)
                     (equal seg-reg *ss*)
                     (not (< (xr :seg-visible seg-reg x86) 4)))
                (app-view x86)
                (x86p x86))
           (not (mv-nth 0 (x86isa::rme-size$inline *compatibility-mode*
                                                   nbytes
                                                   eff-addr
                                                   seg-reg
                                                   r-x
                                                   nil ;check-alignment?
                                                   x86
                                                   nil ;gross keyword param
                                                   ))))
  :hints (("Goal" :in-theory (enable ;code-segment-readable-bit
                                     x86isa::rme-size$inline segment-base-and-bounds
                                     segment-min-eff-addr32
                                     segment-max-eff-addr32
                                     rb
                                     (:e expt)
                                     canonical-address-p
                                     SIGNED-BYTE-P))))

(defthm mv-nth-2-of-rme-size$inline
  (implies (app-view x86)
           (equal (mv-nth 2 (x86isa::rme-size$inline proc-mode ;*compatibility-mode*
                                                     nbytes
                                                     eff-addr
                                                     seg-reg
                                                     r-x
                                                     CHECK-ALIGNMENT? ;nil ;check-alignment?
                                                     x86
                                                     mem-ptr? ;nil ;gross keyword param
                                                     ))
                  x86))
  :hints (("Goal" :in-theory (e/d (x86isa::rme-size$inline segment-base-and-bounds
                                                           segment-min-eff-addr32
                                                           segment-max-eff-addr32
                                                           rb)
                                  (X86ISA::SEGMENT-BASE-AND-BOUNDS$INLINE)))))

(defthm eff-addr-okp-of-xw-irrel
  (implies (and (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (eff-addr-okp eff-addr seg-reg (xw fld index val x86))
                  (eff-addr-okp eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable eff-addr-okp))))

;(local (in-theory (disable x86isa::ash-monotone-2))) ;bad rule

;gen
(defthm slice-of-ash-same
  (implies (and (integerp x)
                (natp high)
                (natp low)
;            (<= low high)
                )
           (equal (slice high low (ash x low))
                  (bvchop (+ 1 (- high low)) x)))
  :hints (("Goal" :cases ((<= low high)))))

(defthm canonical-address-p$inline-of-n-minus-2 ;gen
  (implies (and (natp n)
                (< n (expt 2 32)))
           (canonical-address-p$inline (binary-+ '-2 n)))
  :hints (("Goal" :in-theory (enable canonical-address-p$inline signed-byte-p))))

;move
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
           :in-theory (e/d (ash rb-1)
                           (x86isa::size-of-rb-1)))))

;; (defthm bound-hack ;should not be needed (also, this should be proved automatically by linear)
;;   (implies (and (<= eff-addr 4294967296)
;;                 (integerp eff-addr)
;;                 (unsigned-byte-p 32 (xr ':seg-hidden-base seg-reg x86)))
;;            (< (+ eff-addr (xr ':seg-hidden-base seg-reg x86)) '140741783322624))
;;   :hints (("Goal" :use (:instance ACL2::UNSIGNED-BYTE-P-FORWARD
;;                                   (acl2::bits 32)
;;                                   (acl2::i (xr ':seg-hidden-base seg-reg x86)))
;;            :in-theory (disable ACL2::BOUND-WHEN-USB2)
;;            )))

;; (defthm bound-hack2 ;should not be needed (also, this should be proved automatically by linear)
;;   (implies (and (<= eff-addr 4294967296)
;;                 (integerp eff-addr)
;;                 (unsigned-byte-p 32 (xr ':seg-hidden-base seg-reg x86)))
;;            (< (+ eff-addr (xr ':seg-hidden-base seg-reg x86)) '140741783322625))
;;   :hints (("Goal" :use (:instance ACL2::UNSIGNED-BYTE-P-FORWARD
;;                                   (acl2::bits 32)
;;                                   (acl2::i (xr ':seg-hidden-base seg-reg x86)))
;;            :in-theory (disable ACL2::BOUND-WHEN-USB2)
;;            )))

;; (defthm bound-hack2b ;should not be needed (also, this should be proved automatically by linear)
;;   (implies (and (<= eff-addr 4294967296)
;;                 (integerp eff-addr)
;;                 (unsigned-byte-p 32 (xr ':seg-hidden-base seg-reg x86)))
;;            (< (+ eff-addr (xr ':seg-hidden-base seg-reg x86)) '140741783322623))
;;   :hints (("Goal" :use (:instance ACL2::UNSIGNED-BYTE-P-FORWARD
;;                                   (acl2::bits 32)
;;                                   (acl2::i (xr ':seg-hidden-base seg-reg x86)))
;;            :in-theory (disable ACL2::BOUND-WHEN-USB2)
;;            )))

;; (defthm bound-hack3 ;should not be needed (also, this should be proved automatically by linear)
;;   (implies (and (<= (+ eff-addr n) 4294967296)
;;                 (integerp eff-addr)
;;                 (integerp n)
;;                 (unsigned-byte-p 32 (xr ':seg-hidden-base seg-reg x86)))
;;            (< (+ eff-addr n (xr ':seg-hidden-base seg-reg x86)) '140741783322625))
;;   :hints (("Goal" :use (:instance ACL2::UNSIGNED-BYTE-P-FORWARD
;;                                   (acl2::bits 32)
;;                                   (acl2::i (xr ':seg-hidden-base seg-reg x86)))
;;            :in-theory (disable ACL2::BOUND-WHEN-USB2)
;;            )))

;todo: maybe limiting (:e expt) is screwing up acl2::unsigned-byte-p-forward, so i enable it below

(defthm mv-nth-1-of-rme-size$inline-becomes-read-from-segment
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp n eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ n eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (natp n)
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86)))
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::rme-size$inline *compatibility-mode*
                                                     n
                                                     eff-addr
                                                     seg-reg
                                                     r-x
                                                     nil ;check-alignment?
                                                     x86
                                                     nil ;gross keyword param
                                                     ))
                  (read-from-segment n eff-addr seg-reg x86)))
  :hints (("Goal" :expand ((:free (eff-addr) (read-byte-from-segment eff-addr seg-reg x86))
                    (:free (n eff-addr) (read-from-segment s eff-addr seg-reg x86))
           ;         (:free (n addr) (rb-1 n addr r-x x86))
                    )
           :do-not '(generalize eliminate-destructors)
           :induct
           (read-from-segment n eff-addr seg-reg x86)
           :in-theory (e/d (x86isa::rme-size$inline
                            read-byte-from-segment
                            bvplus
                            acl2::bvchop-of-sum-cases
                            well-formed-32-bit-segmentp
                            read-from-segment
                            segment-base-and-bounds
                            segment-max-eff-addr32
                            segment-min-eff-addr32
;                            read
 ;                           read-byte
                            32-bit-segment-start
                            32-bit-segment-size
                            32-bit-segment-start-and-size
                            rb
                            rvm08
                            n48
                            acl2::slice-too-high-is-0-new
                            x86isa::rml-size-becomes-rb
                            canonical-address-p$inline
                            signed-byte-p
                            (:e expt)
                            ifix
                            rb-1
                            )
                           (;;ea-to-la
                            ;mv-nth-1-of-rb-becomes-read
                            ;mv-nth-1-of-rb-1-becomes-read
                            ;acl2::bvcat-equal-rewrite-alt
                            acl2::bvcat-equal-rewrite
                            ;rvm08-becomes-read-byte
                            acl2::slice-of-+
                            acl2::bvplus-recollapse)))))

(defthm mv-nth-1-of-rme08-becomes-read-from-segment
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addr-okp eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 1 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86)))
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::rme08 *compatibility-mode* eff-addr seg-reg r-x x86))
                  (read-from-segment 1 eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (e/d (x86isa::rme08
                                   read-byte-from-segment
                                   bvplus
                                   acl2::bvchop-of-sum-cases
                                   well-formed-32-bit-segmentp
                                   read-from-segment
                                   segment-base-and-bounds
                                   segment-max-eff-addr32
                                   segment-min-eff-addr32
                                   32-bit-segment-start
                                   32-bit-segment-size
                                   32-bit-segment-start-and-size
                                   rb
                                   rvm08
                                   n48
                                   acl2::slice-too-high-is-0-new
                                   canonical-address-p$inline
                                   signed-byte-p
                                   (:e expt)
                                   ifix
                                   rb-1
                                   )
                                  (;;ea-to-la
;;mv-nth-1-of-rb-becomes-read
;;mv-nth-1-of-rb-1-becomes-read
;;acl2::bvcat-equal-rewrite-alt
                                   acl2::bvcat-equal-rewrite
;;rvm08-becomes-read-byte
                                   acl2::slice-of-+
                                   acl2::bvplus-recollapse)))))

(defthm mv-nth-1-of-rme16-becomes-read-from-segment
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addr-okp eff-addr seg-reg x86)
                (eff-addr-okp (+ 1 eff-addr) seg-reg x86)
                (natp eff-addr)
                (<= (+ 1 eff-addr) (expt 2 32)) ;drop?
                (<= (+ 2 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86)))
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::rme16 *compatibility-mode* eff-addr seg-reg r-x nil x86))
                  (read-from-segment 2 eff-addr seg-reg x86)))
  :hints (("Goal" :expand ((RB-1 2 EFF-ADDR R-X X86)
                           (RB-1 2
                                 (+ -4294967296 EFF-ADDR
                                    (xr :seg-hidden-base SEG-REG X86))
                                 R-X X86)
                           (RB-1 2
                                 (+ -4294967296 EFF-ADDR
                                    (xr :seg-hidden-base 2 X86))
                                 R-X X86)
                           (RB-1 2
                                 (+ EFF-ADDR (xr :seg-hidden-base 1 X86))
                                 :R X86)
                           (RB-1 2
                                  (+ EFF-ADDR (xr :seg-hidden-base 2 X86))
                                  R-X X86)
                           (RB-1 2
                                  (+ EFF-ADDR (xr :seg-hidden-base seg-reg X86))
                                  R-X X86))
           :in-theory (e/d (x86isa::rme16
;read-byte
                            read-byte-from-segment
                            bvplus
                            acl2::bvchop-of-sum-cases
                            well-formed-32-bit-segmentp
                            read-from-segment
                            segment-base-and-bounds
                            segment-max-eff-addr32
                            segment-min-eff-addr32
                            32-bit-segment-start
                            32-bit-segment-size
                            32-bit-segment-start-and-size
                            rb
                            rvm08
                            n48
                            acl2::slice-too-high-is-0-new
                            canonical-address-p$inline
                            signed-byte-p
                            (:e expt)
                            ifix
                            rb-1
                            )
                           ( ;;ea-to-la
                            ;;mv-nth-1-of-rb-becomes-read
                            ;;mv-nth-1-of-rb-1-becomes-read
;;;acl2::bvcat-equal-rewrite-alt
                            acl2::bvcat-equal-rewrite
                            ;;rvm08-becomes-read-byte
                            acl2::slice-of-+
                            acl2::bvplus-recollapse)))))

(defthm eff-addrs-okp-of-xw-irrel
  (implies (and (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (eff-addrs-okp n eff-addr seg-reg (xw fld index val x86))
                  (eff-addrs-okp n eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable eff-addrs-okp))))

(defthm eff-addrs-okp-of-set-flag
  (equal (eff-addrs-okp n eff-addr seg-reg (set-flag flg val x86))
         (eff-addrs-okp n eff-addr seg-reg x86)))

(defthm eff-addrs-okp-of-write-to-segment
  (equal (eff-addrs-okp n eff-addr seg-reg (write-to-segment n2 eff-addr2 seg-reg2 val2 x86))
         (eff-addrs-okp n eff-addr seg-reg x86)))



(defthm read-from-segment-of-set-flag
  (equal (read-from-segment n eff-addr seg-reg (set-flag flg val x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable read-from-segment))))

(defun set-eip (eip x86)
  (declare (xargs :stobjs x86
                  :guard (signed-byte-p 48 eip))) ;todo: tighten?
  (x86isa::!rip eip x86))

(defthm write-*ip-inline-becomes-xw
  (implies (segment-is-32-bitsp *cs* x86)
           (equal (x86isa::write-*ip$inline *compatibility-mode* eip x86)
                  (xw :rip nil (bvchop 32 eip) x86)))
  :hints (("Goal" :in-theory (enable x86isa::write-*ip$inline))))

;; (defthm write-*ip-inline-becomes-set-eip
;;   (implies (segment-is-32-bitsp *cs* x86)
;;            (equal (x86isa::write-*ip$inline *compatibility-mode* eip x86)
;;                   (set-eip (bvchop 32 eip) x86)))
;;   :hints (("Goal" :in-theory (enable x86isa::write-*ip$inline))))

;; This introduces set-eip, if we want to.  We probably only want this for 32-bits!
(defthmd xw-becomes-set-eip
  (equal (xw :rip nil eip x86)
         (set-eip eip x86)))

(defthm eip-of-set-eip
  (equal (eip (set-eip eip x86))
         (logext 48 eip)))

(defthm xr-of-set-eip-irrel
  (implies (not (equal fld :rip))
           (equal (xr fld index (set-eip eip x86))
                  (xr fld index x86))))

(defthm segment-is-32-bitsp-of-set-eip
  (equal (segment-is-32-bitsp seg-reg (set-eip eip x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip))))

;open less in the proof?
(defthm 32-bit-segment-size-of-set-eip
  (equal (32-bit-segment-size seg-reg (set-eip eip x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip 32-bit-segment-size 32-bit-segment-start-and-size))))

(defthm 32-bit-segment-start-of-set-eip
  (equal (32-bit-segment-start seg-reg (set-eip eip x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip 32-bit-segment-size 32-bit-segment-start 32-bit-segment-start-and-size))))

(defthm segment-min-eff-addr32-of-set-eip
  (equal (segment-min-eff-addr32 seg-reg (set-eip eip x86))
         (segment-min-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-min-eff-addr32))))

(defthm segment-max-eff-addr32-of-set-eip
  (equal (segment-max-eff-addr32 seg-reg (set-eip eip x86))
         (segment-max-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-max-eff-addr32))))

(defthm x86p-of-set-eip
  (implies (and (x86p x86)
                (signed-byte-p 48 eip))
           (x86p (set-eip eip x86)))
  :hints (("Goal" :in-theory (e/d (set-eip) ()))))

(defthm well-formed-32-bit-segmentp-of-set-eip
  (equal (well-formed-32-bit-segmentp seg-reg (set-eip eip x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm code-segment-assumptions32-for-code-of-set-eip
  (equal (code-segment-assumptions32-for-code code offset (set-eip eip x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm code-segment-well-formedp-of-set-eip
  (equal (code-segment-well-formedp (set-eip eip x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm alignment-checking-enabled-p-of-set-eip
  (equal (alignment-checking-enabled-p (set-eip eip x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-eip))))

;;;

(defthm ea-to-la-of-set-eip
  (equal (ea-to-la proc-mode eff-addr seg-reg nbytes (set-eip eip x86))
         (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm ea-to-la-of-set-esp
  (equal (ea-to-la proc-mode eff-addr seg-reg nbytes (set-esp esp x86))
         (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm ea-to-la-of-set-ebp
  (equal (ea-to-la proc-mode eff-addr seg-reg nbytes (set-ebp ebp x86))
         (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

(defthm ea-to-la-of-set-eax
  (equal (ea-to-la proc-mode eff-addr seg-reg nbytes (set-eax eax x86))
         (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm ea-to-la-of-set-ebx
  (equal (ea-to-la proc-mode eff-addr seg-reg nbytes (set-ebx ebx x86))
         (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm ea-to-la-of-set-ecx
  (equal (ea-to-la proc-mode eff-addr seg-reg nbytes (set-ecx ecx x86))
         (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm ea-to-la-of-set-edx
  (equal (ea-to-la proc-mode eff-addr seg-reg nbytes (set-edx edx x86))
         (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
  :hints (("Goal" :in-theory (enable set-edx))))

;;;

(defthm xw-of-set-eip-irrel
  (implies (not (equal fld :rip))
           (equal (xw fld index val (set-eip eip x86))
                  (set-eip eip  (xw fld index val x86)))))

(defthm set-flag-of-set-eip-irrel
  (equal (set-flag flg val (set-eip eip x86))
         (set-eip eip (set-flag flg val x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm set-eip-of-set-eip
  (equal (set-eip eip1 (set-eip eip2 x86))
         (set-eip eip1 x86)))

(defthm eff-addr-okp-of-set-eip
  (equal (eff-addr-okp eff-addr seg-reg (set-eip eip x86))
         (eff-addr-okp eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm eff-addrs-okp-of-set-eip
  (equal (eff-addrs-okp n eff-addr seg-reg (set-eip eip x86))
         (eff-addrs-okp n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip))))

;todo: commute set-eip with other writers (e.g., write-byte-to-segment)

(defthm not-mv-nth-0-of-rime-size$inline
  (implies (and (eff-addrs-okp n eff-addr seg-reg x86)
                (member-equal n '(1 2 4 8))
                (app-view x86)
                (or (equal seg-reg *cs*)
                    (equal seg-reg *ss*)
                    (not (< (xr :seg-visible seg-reg x86) 4)))
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86)))

                (x86p x86))
           (not (mv-nth 0 (x86isa::rime-size$inline *compatibility-mode*
                                                    n
                                                    eff-addr
                                                    seg-reg
                                                    r-x
                                                    nil ;check-alignment?
                                                    x86
                                                    nil ;gross keyword param
                                                    ))))
  :hints (("Goal" :in-theory (enable x86isa::rime-size$inline
                                     segment-base-and-bounds
                                     segment-min-eff-addr32
                                     segment-max-eff-addr32
                                     rb))))

(defthm mv-nth-2-of-rime-size$inline
  (implies (app-view x86)
           (equal (mv-nth 2 (x86isa::rime-size$inline proc-mode ;*compatibility-mode*
                                                      nbytes
                                                      eff-addr
                                                      seg-reg
                                                      r-x
                                                      check-alignment? ;nil ;check-alignment?
                                                      x86
                                                      mem-ptr? ;nil ;gross keyword param
                                                      ))
                  x86))
  :hints (("Goal" :in-theory (e/d (x86isa::rime-size$inline
                                   rb)
                                  (x86isa::segment-base-and-bounds$inline)))))



(defthm read-from-segment-of-1
  (implies (x86p x86)
           (equal (read-from-segment 1 eff-addr seg-reg x86)
                  (read-byte-from-segment eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-from-segment))))

;; calling rme08 to read from a valid effective address in a segment returns no error.
(defthm not-mv-nth-0-of-rme08
  (implies (and (eff-addr-okp eff-addr seg-reg x86)
                (app-view x86)
                (or (equal seg-reg *cs*)
                    (equal seg-reg *ss*)
                    (not (< (xr :seg-visible seg-reg x86) 4)))
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86)))
                (x86p x86))
           (not (mv-nth 0 (x86isa::rme08$inline *compatibility-mode*
                                                eff-addr
                                                seg-reg
                                                r-x
                                                x86))))
  :hints (("Goal" :in-theory (enable x86isa::rme08$inline segment-base-and-bounds
                                     segment-min-eff-addr32
                                     segment-max-eff-addr32
                                     rb
                                     (:e expt)
                                     canonical-address-p
                                     signed-byte-p))))

(defthm not-mv-nth-0-of-rme16
  (implies (and (eff-addr-okp eff-addr seg-reg x86)
                (eff-addr-okp (+ 1 eff-addr) seg-reg x86)
                (app-view x86)
                (or (equal seg-reg *cs*)
                    (equal seg-reg *ss*)
                    (not (< (xr :seg-visible seg-reg x86) 4)))
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86)))
                (x86p x86))
           (not (mv-nth 0 (x86isa::rme16 *compatibility-mode* eff-addr seg-reg r-x nil x86))))
  :hints (("Goal" :in-theory (enable x86isa::rme16$inline
                                     segment-base-and-bounds
                                     segment-min-eff-addr32
                                     segment-max-eff-addr32 rb (:e expt)
                                     canonical-address-p signed-byte-p))))

(defthm mv-nth-1-of-rime-size$inline-becomes-read-from-segment-1
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addr-okp eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 1 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86)
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86))))
           (equal (mv-nth 1 (x86isa::rime-size$inline *compatibility-mode*
                                                     1
                                                     eff-addr
                                                     seg-reg
                                                     r-x
                                                     nil ;check-alignment?
                                                     x86
                                                     nil ;gross keyword param
                                                     ))
                  (logext 8 (read-from-segment 1 eff-addr seg-reg x86))))
  :otf-flg t
  :hints (("Goal" :expand ((:free (eff-addr) (read-byte-from-segment eff-addr seg-reg x86))
                    (:free (n eff-addr) (read-from-segment s eff-addr seg-reg x86))
;         (:free (n addr) (rb-1 n addr r-x x86))
                    (read-from-segment n eff-addr seg-reg x86)
                    )
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t
;           :induct (read-from-segment n eff-addr seg-reg x86)
           :in-theory (e/d (x86isa::rime-size$inline
                            read-byte-from-segment
                            ;bvplus
                            acl2::bvchop-of-sum-cases
                            well-formed-32-bit-segmentp
                            read-from-segment
                            segment-base-and-bounds
                            segment-max-eff-addr32
                            segment-min-eff-addr32
;                            read
 ;                           read-byte
                            32-bit-segment-start
                            32-bit-segment-size
                            32-bit-segment-start-and-size
                            rb
                            rb-1
                            rvm08
                            n48
                            acl2::slice-too-high-is-0-new
                            x86isa::rml-size-becomes-rb
                            canonical-address-p$inline
                            signed-byte-p
                            (:e expt)
                            )
                           (;;ea-to-la
;                            mv-nth-1-of-rb-becomes-read
 ;                           mv-nth-1-of-rb-1-becomes-read
                            ;acl2::bvcat-equal-rewrite-alt
                            acl2::bvcat-equal-rewrite
                            ;rvm08-becomes-read-byte
                            acl2::slice-of-+)))))

(defthm mv-nth-1-of-rime-size$inline-becomes-read-from-segment-2
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp 2 eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 2 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86)
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86))))
           (equal (mv-nth 1 (x86isa::rime-size$inline *compatibility-mode*
                                                     2
                                                     eff-addr
                                                     seg-reg
                                                     r-x
                                                     nil ;check-alignment?
                                                     x86
                                                     nil ;gross keyword param
                                                     ))
                  (logext 16 (read-from-segment 2 eff-addr seg-reg x86))))
  :otf-flg t
  :hints (("Goal" :expand ((:free (eff-addr seg-reg) (read-byte-from-segment eff-addr seg-reg x86))
                           (:free (n addr r-x) (rb-1 n addr r-x x86)))
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t
;           :induct (read-from-segment n eff-addr seg-reg x86)
           :in-theory (e/d (acl2::equal-of-logext
                            x86isa::rime-size$inline
                            read-byte-from-segment
                            bvplus
                            acl2::bvchop-of-sum-cases
                            well-formed-32-bit-segmentp
                            read-from-segment
                            segment-base-and-bounds
                            segment-max-eff-addr32
                            segment-min-eff-addr32
                            32-bit-segment-start
                            32-bit-segment-size
                            32-bit-segment-start-and-size
                            rb
                            rb-1
                            rvm08
                            n48
                            acl2::slice-too-high-is-0-new
                            x86isa::rml-size-becomes-rb
                            canonical-address-p$inline
                            ;signed-byte-p
                            (:e expt)
                            )
                           (acl2::bvplus-recollapse
                            ;acl2::bvcat-equal-rewrite
                            ;acl2::bvcat-equal-rewrite-alt
                            acl2::slice-of-+
                            ACL2::LOGEXT-OF-LOGIOR)))))

(defthm mv-nth-1-of-rime-size$inline-becomes-read-from-segment-4
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp 4 eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 4 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86)
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86))))
           (equal (mv-nth 1 (x86isa::rime-size$inline *compatibility-mode*
                                                      4
                                                      eff-addr
                                                      seg-reg
                                                      r-x
                                                      nil ;check-alignment?
                                                      x86
                                                      nil ;gross keyword param
                                                      ))
                  (logext 32 (read-from-segment 4 eff-addr seg-reg x86))))
  :hints (("Goal" :expand ((:free (eff-addr seg-reg) (READ-BYTE-FROM-SEGMENT EFF-ADDR SEG-REG X86))
                           (:free (n eff-addr seg-reg) (READ-FROM-SEGMENT n EFF-ADDR SEG-REG X86))
                           (:free (n addr r-x) (rb-1 n addr r-x x86))
                           )
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t
;           :induct (READ-FROM-SEGMENT N EFF-ADDR SEG-REG X86)
           :in-theory (e/d (acl2::equal-of-logext
                            x86isa::rime-size$inline
                            READ-BYTE-FROM-SEGMENT
                            bvplus
                            acl2::bvchop-of-sum-cases
                            well-formed-32-bit-segmentp
                            READ-FROM-SEGMENT
                            SEGMENT-BASE-AND-BOUNDS
                            SEGMENT-MAX-EFF-ADDR32
                            SEGMENT-MIN-EFF-ADDR32
                            32-BIT-SEGMENT-START
                            32-BIT-SEGMENT-Size
                            32-BIT-SEGMENT-START-AND-SIZE
                            rb
                            rb-1
                            RVM08
                            n48
                            ACL2::SLICE-TOO-HIGH-IS-0-NEW
                            x86isa::rml-size-becomes-rb
                            CANONICAL-ADDRESS-P$INLINE
                            ;SIGNED-BYTE-P
                            (:e expt)
                            )
                           (acl2::bvplus-recollapse
                            ACL2::SLICE-OF-+
                            ACL2::LOGEXT-OF-LOGIOR)))))

(defthm mv-nth-1-of-rime-size$inline-becomes-read-from-segment-8
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp 8 eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 8 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86)
                (implies (and (equal seg-reg *cs*)
                              (equal r-x :r))
                         (equal 1 (code-segment-readable-bit x86))))
           (equal (mv-nth 1 (x86isa::rime-size$inline *compatibility-mode*
                                                      8
                                                      eff-addr
                                                      seg-reg
                                                      r-x
                                                      nil ;check-alignment?
                                                      x86
                                                      nil ;gross keyword param
                                                      ))
                  (logext 64 (read-from-segment 8 eff-addr seg-reg x86))))
  :hints (("Goal" :expand ((:free (eff-addr seg-reg) (READ-BYTE-FROM-SEGMENT EFF-ADDR SEG-REG X86))
                           (:free (n eff-addr seg-reg) (READ-FROM-SEGMENT n EFF-ADDR SEG-REG X86))
                           (:free (n addr r-x) (rb-1 n addr r-x x86))
                           )
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t
;           :induct (READ-FROM-SEGMENT N EFF-ADDR SEG-REG X86)
           :in-theory (e/d (acl2::equal-of-logext
                            x86isa::rime-size$inline
                            READ-BYTE-FROM-SEGMENT
                            bvplus
                            acl2::bvchop-of-sum-cases
                            well-formed-32-bit-segmentp
                            READ-FROM-SEGMENT
                            SEGMENT-BASE-AND-BOUNDS
                            SEGMENT-MAX-EFF-ADDR32
                            SEGMENT-MIN-EFF-ADDR32
                            32-BIT-SEGMENT-START
                            32-BIT-SEGMENT-Size
                            32-BIT-SEGMENT-START-AND-SIZE
                            rb
                            rb-1
                            RVM08
                            n48
                            ACL2::SLICE-TOO-HIGH-IS-0-NEW
                            x86isa::rml-size-becomes-rb
                            CANONICAL-ADDRESS-P$INLINE
                            ;SIGNED-BYTE-P
                            (:e expt)
                            )
                           (acl2::bvplus-recollapse
                            ACL2::SLICE-OF-+
                            ;for speed:
                            ACL2::LOGEXT-OF-LOGIOR
                            ACL2::UNSIGNED-BYTE-P-LOGIOR
                            ACL2::UNSIGNED-BYTE-P-OF-ASH-alt
                            ACL2::UNSIGNED-BYTE-P-ASH
                            ACL2::LOGEXT-IDENTITY)))))

(defthm not-mv-nth-0-of-wme-size
  (implies (and (eff-addrs-okp nbytes eff-addr seg-reg x86)
                (<= nbytes (expt 2 32))
                (natp nbytes)
                (app-view x86)
                (or (equal seg-reg *cs*)
                    (equal seg-reg *ss*)
                    (not (< (xr :seg-visible seg-reg x86) 4)))
                (x86p x86)
                (not (equal seg-reg *cs*))
                (equal 1 (data-segment-writeable-bit seg-reg x86)))
           (not (mv-nth 0 (x86isa::wme-size$inline *compatibility-mode*
                                                   nbytes
                                                   eff-addr
                                                   seg-reg
                                                   val
                                                   nil
                                                   x86
                                                   nil))))
  :hints (("Goal" :in-theory (enable x86isa::wme-size$inline
                                     segment-base-and-bounds
                                     segment-min-eff-addr32
                                     segment-max-eff-addr32
                                     x86isa::wml48
                                     x86isa::wml80
                                     x86isa::wml128
                                     (:e expt)
                                     canonical-address-p
                                     signed-byte-p))))

(acl2::defopeners write-to-segment)
(in-theory (disable write-to-segment-unroll))
(acl2::defopeners wb-1)

(defthm mv-nth-1-of-wml08-of-mv-nth-1-of-ea-to-la
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addr-okp eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 1 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::wml08 (mv-nth 1 (ea-to-la 1 eff-addr seg-reg 1 x86)) val x86))
                  (write-to-segment 1 eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (x86isa::wml16
                                   write-to-segment-base
                                   write-to-segment-unroll
                                   wb
                                   wvm08
                                   write-byte-to-segment
                                   bvplus
                                   acl2::bvchop-of-sum-cases
                                   well-formed-32-bit-segmentp
                                   segment-base-and-bounds
                                   segment-max-eff-addr32
                                   segment-min-eff-addr32
                                   32-bit-segment-start
                                   32-bit-segment-size
                                   32-bit-segment-start-and-size
                                   n48
                                   acl2::slice-too-high-is-0-new
                                   canonical-address-p$inline
                                   signed-byte-p
                                   (:e expt)
                                   ifix)
                                  (acl2::bvplus-recollapse)))))

(defthm mv-nth-1-of-wml16-of-mv-nth-1-of-ea-to-la
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp 2 eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 2 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::wml16 (mv-nth 1 (ea-to-la 1 eff-addr seg-reg 2 x86)) val x86))
                  (write-to-segment 2 eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (x86isa::wml16
                                   write-to-segment-base
                                   write-to-segment-unroll
                                   wb
                                   wvm08
                                   write-byte-to-segment
                                   bvplus
                                   acl2::bvchop-of-sum-cases
                                   well-formed-32-bit-segmentp
                                   segment-base-and-bounds
                                   segment-max-eff-addr32
                                   segment-min-eff-addr32
                                   32-bit-segment-start
                                   32-bit-segment-size
                                   32-bit-segment-start-and-size
                                   n48
                                   acl2::slice-too-high-is-0-new
                                   canonical-address-p$inline
                                   signed-byte-p
                                   (:e expt)
                                   ifix)
                                  (acl2::bvplus-recollapse)))))

(defthm mv-nth-1-of-wml32-of-mv-nth-1-of-ea-to-la
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp 4 eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 4 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::wml32 (mv-nth 1 (ea-to-la 1 eff-addr seg-reg 4 x86)) val x86))
                  (write-to-segment 4 eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (x86isa::wml32
                                   write-to-segment-base
                                   write-to-segment-unroll
                                   wb
                                   wvm08
                                   write-byte-to-segment
                                   bvplus
                                   acl2::bvchop-of-sum-cases
                                   well-formed-32-bit-segmentp
                                   segment-base-and-bounds
                                   segment-max-eff-addr32
                                   segment-min-eff-addr32
                                   32-bit-segment-start
                                   32-bit-segment-size
                                   32-bit-segment-start-and-size
                                   n48
                                   acl2::slice-too-high-is-0-new
                                   canonical-address-p$inline
                                   signed-byte-p
                                   (:e expt)
                                   ifix)
                                  (acl2::bvplus-recollapse)))))

(defthm mv-nth-1-of-wml48-of-mv-nth-1-of-ea-to-la
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp 6 eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 6 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::wml48 (mv-nth 1 (ea-to-la 1 eff-addr seg-reg 6 x86)) val x86))
                  (write-to-segment 6 eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (x86isa::wml48
                                   write-to-segment-base
                                   write-to-segment-unroll
                                   wb
                                   wvm08
                                   write-byte-to-segment
                                   bvplus
                                   acl2::bvchop-of-sum-cases
                                   well-formed-32-bit-segmentp
                                   segment-base-and-bounds
                                   segment-max-eff-addr32
                                   segment-min-eff-addr32
                                   32-bit-segment-start
                                   32-bit-segment-size
                                   32-bit-segment-start-and-size
                                   n48
                                   acl2::slice-too-high-is-0-new
                                   canonical-address-p$inline
                                   signed-byte-p
                                   (:e expt)
                                   ifix)
                                  (acl2::bvplus-recollapse)))))

(defthm mv-nth-1-of-wml64-of-mv-nth-1-of-ea-to-la
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp 8 eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 8 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::wml64 (mv-nth 1 (ea-to-la 1 eff-addr seg-reg 8 x86)) val x86))
                  (write-to-segment 8 eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (x86isa::wml64
                                   write-to-segment-base
                                   write-to-segment-unroll
                                   wb
                                   wvm08
                                   write-byte-to-segment
                                   bvplus
                                   acl2::bvchop-of-sum-cases
                                   well-formed-32-bit-segmentp
                                   segment-base-and-bounds
                                   segment-max-eff-addr32
                                   segment-min-eff-addr32
                                   32-bit-segment-start
                                   32-bit-segment-size
                                   32-bit-segment-start-and-size
                                   n48
                                   acl2::slice-too-high-is-0-new
                                   canonical-address-p$inline
                                   signed-byte-p
                                   (:e expt)
                                   ifix)
                                  (acl2::bvplus-recollapse)))))

(defthm mv-nth-1-of-wml80-of-mv-nth-1-of-ea-to-la
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp 10 eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 10 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::wml80 (mv-nth 1 (ea-to-la 1 eff-addr seg-reg 10 x86)) val x86))
                  (write-to-segment 10 eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (x86isa::wml80
                                   write-to-segment-base
                                   write-to-segment-unroll
                                   wb
                                   wvm08
                                   write-byte-to-segment
                                   bvplus
                                   acl2::bvchop-of-sum-cases
                                   well-formed-32-bit-segmentp
                                   segment-base-and-bounds
                                   segment-max-eff-addr32
                                   segment-min-eff-addr32
                                   32-bit-segment-start
                                   32-bit-segment-size
                                   32-bit-segment-start-and-size
                                   n48
                                   acl2::slice-too-high-is-0-new
                                   canonical-address-p$inline
                                   signed-byte-p
                                   (:e expt)
                                   ifix)
                                  (acl2::bvplus-recollapse)))))

(defthm mv-nth-1-of-wml128-of-mv-nth-1-of-ea-to-la
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp 16 eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ 16 eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::wml128 (mv-nth 1 (ea-to-la 1 eff-addr seg-reg 16 x86)) val x86))
                  (write-to-segment 16 eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (x86isa::wml128
                                   write-to-segment-base
                                   write-to-segment-unroll
                                   wb
                                   wvm08
                                   write-byte-to-segment
                                   bvplus
                                   acl2::bvchop-of-sum-cases
                                   well-formed-32-bit-segmentp
                                   segment-base-and-bounds
                                   segment-max-eff-addr32
                                   segment-min-eff-addr32
                                   32-bit-segment-start
                                   32-bit-segment-size
                                   32-bit-segment-start-and-size
                                   n48
                                   acl2::slice-too-high-is-0-new
                                   canonical-address-p$inline
                                   signed-byte-p
                                   (:e expt)
                                   ifix)
                                  (acl2::bvplus-recollapse)))))

(defthm mv-nth-1-of-wb-of-mv-nth-1-of-ea-to-la
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp nbytes eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ nbytes eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (wb nbytes (mv-nth 1 (ea-to-la 1 eff-addr seg-reg nbytes x86)) :w val x86))
                  (write-to-segment nbytes eff-addr seg-reg val x86)))
  :hints (("Goal" :induct (write-to-segment nbytes eff-addr seg-reg val x86)
           :in-theory (e/d ( ;;write-to-segment-base
                            ;;write-to-segment-unroll
                            write-to-segment
                            wb
                            wvm08
                            write-byte-to-segment
                            bvplus
                            acl2::bvchop-of-sum-cases
                            well-formed-32-bit-segmentp
                            segment-base-and-bounds
                            segment-max-eff-addr32
                            segment-min-eff-addr32
                            32-bit-segment-start
                            32-bit-segment-size
                            32-bit-segment-start-and-size
                            n48
                            acl2::slice-too-high-is-0-new
                            canonical-address-p$inline
                            signed-byte-p
                            (:e expt)
                            ifix)
                           (acl2::bvplus-recollapse)))))

(defthm canonical-address-p-of-+-of-ea-to-la-last-address
  (implies (and (eff-addrs-okp nbytes eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ nbytes eff-addr) (expt 2 32))
                (natp nbytes)
                )
           (canonical-address-p
            (+ -1 nbytes
               (mv-nth 1
                       (ea-to-la 1 eff-addr seg-reg nbytes x86)))))
  :hints (("Goal" :in-theory (e/d (canonical-address-p$inline
                                   signed-byte-p
                                   (:e expt)
                                   ifix
                                   bvplus) (acl2::bvplus-recollapse)))))

(defthm mv-nth-1-of-wml-size-of-mv-nth-1-of-ea-to-la
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp nbytes eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ nbytes eff-addr) (expt 2 32))
                (natp nbytes)
                (app-view x86)
                (x86p x86)
                (well-formed-32-bit-segmentp seg-reg x86))
           (equal (mv-nth 1 (x86isa::wml-size nbytes (mv-nth 1 (ea-to-la 1 eff-addr seg-reg nbytes x86)) val x86))
                  (write-to-segment nbytes eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d ()
                                  (acl2::bvplus-recollapse
                                   x86isa::wml08
                                   x86isa::wml16
                                   x86isa::wml32
                                   x86isa::wml48
                                   x86isa::wml64
                                   ea-to-la)))))

(defthm mv-nth-1-of-wme-size
  (implies (and (segment-is-32-bitsp seg-reg x86)
                (eff-addrs-okp nbytes eff-addr seg-reg x86)
                (natp eff-addr)
                (<= (+ nbytes eff-addr) (expt 2 32))
                (app-view x86)
                (x86p x86)
                (natp nbytes)
                (well-formed-32-bit-segmentp seg-reg x86)
                (not (equal seg-reg *cs*))
                (equal 1 (data-segment-writeable-bit seg-reg x86)))
           (equal (mv-nth 1 (x86isa::wme-size$inline *compatibility-mode*
                                                     nbytes
                                                     eff-addr
                                                     seg-reg
                                                     val
                                                     nil ;check-alignment?
                                                     x86
                                                     mem-ptr?))
                  (write-to-segment nbytes
                                    eff-addr
                                    seg-reg
                                    val
                                    x86)))
  :hints (("Goal" :induct (write-to-segment nbytes
                                            eff-addr
                                            seg-reg
                                            val
                                            x86)
           :expand ( ;(:free (eff-addr val) (write-byte-to-segment eff-addr seg-reg val x86))
;                    (:free (n eff-addr val x86) (write-to-segment n eff-addr seg-reg val x86))
;(:free (n addr w value x86) (wb-1 n addr w value x86))
                    )
           :in-theory (e/d (x86isa::wme-size$inline
;write-byte-to-segment
;bvplus
;acl2::bvchop-of-sum-cases
                            well-formed-32-bit-segmentp
                            (:i write-to-segment)
;write-to-segment
                            segment-base-and-bounds
                            segment-max-eff-addr32
                            segment-min-eff-addr32
                            32-bit-segment-start
                            32-bit-segment-size
                            32-bit-segment-start-and-size
;wb
;wb-1
;wvm08
                            n48
                            acl2::slice-too-high-is-0-new
;wml-size-becomes-wb
                            canonical-address-p$inline
                            signed-byte-p
                            (:e expt)
                            ifix
                            )
                           (ea-to-la
                            x86isa::wml-size
                            x86isa::wml08
                            x86isa::wml16
                            x86isa::wml32
                            x86isa::wml48
                            x86isa::wml64
                            x86isa::wml80
                            x86isa::wml128
                            ;;x86isa::wml-size
                            acl2::bvcat-equal-rewrite
                            acl2::slice-of-+
                            acl2::bvplus-recollapse
                            write-to-segment-unroll
                            write-to-segment-base)))))

;todo:replace the other
(defthm mv-nth-1-of-add-to-*ip-gen
  (implies (and (eff-addr-okp (+ *ip delta) *cs* x86)
                (not (64-bit-modep x86))
                (segment-is-32-bitsp *cs* x86)
                (equal (segment-expand-down-bit *cs* x86)
                        0)
;                (code-segment-assumptions32 code x86-2) ;binds the free var
 ;               (code-segment-assumptions32 code x86) ;code is a free var and usually will be a constant
  ;              (< (+ *ip delta) (len code))
                (<= 0 (+ *ip delta))
                (integerp *ip)
                (integerp delta)
                (x86p x86) ;drop?
                )
           (equal (mv-nth 1 (x86isa::add-to-*ip *compatibility-mode* *ip delta x86))
                  (+ *ip delta)))
  :hints (("Goal" :in-theory (enable x86isa::add-to-*ip
                                     segment-max-eff-addr32
                                     segment-base-and-bounds))))

(defthm code-and-stack-segments-separate-of-write-to-segment
  (equal (code-and-stack-segments-separate (write-to-segment n eff-addr seg-reg val x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

(defthm 32-bit-segment-start-and-size-of-xw-irrel
  (implies (not (member-equal fld '(:seg-hidden-limit :seg-hidden-base :seg-hidden-attr)))
           (equal (32-bit-segment-start-and-size seg-reg (xw fld index val x86))
                  (32-bit-segment-start-and-size seg-reg x86)))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start-and-size))))

(defthm segments-separate-of-xw-irrel
  (implies (not (member-equal fld '(:seg-hidden-limit :seg-hidden-base :seg-hidden-attr)))
           (equal (segments-separate seg-reg1 seg-reg2 (xw fld index val x86))
                  (segments-separate seg-reg1 seg-reg2 x86)))
  :hints (("Goal" :in-theory (enable set-eip segments-separate segments-separate-helper ;list::memberp-of-cons
                                     ))))

(defthm segments-separate-of-set-eip
  (equal (segments-separate seg-reg1 seg-reg2 (set-eip eip x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-eip segments-separate segments-separate-helper))))

(defthm segments-separate-of-set-flag
  (equal (segments-separate seg-reg1 seg-reg2 (set-flag flag val x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-flag segments-separate segments-separate-helper))))

(defthm code-and-stack-segments-separate-of-set-eip
  (equal (code-and-stack-segments-separate (set-eip eip x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

(defthm code-and-stack-segments-separate-of-xw-irrel
  (implies (not (member-equal fld '(:seg-hidden-limit :seg-hidden-base :seg-hidden-attr)))
           (equal (code-and-stack-segments-separate (xw fld index val x86))
                  (code-and-stack-segments-separate x86)))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate ;list::memberp-of-cons
                                     ))))

(defthm code-and-stack-segments-separate-of-set-flag
  (equal (code-and-stack-segments-separate (set-flag flag val x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

(defthm code-and-stack-segments-separate-of-write-byte-to-segment
  (equal (code-and-stack-segments-separate (write-byte-to-segment eff-addr seg-reg val x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

;for axe
(defthm integerp-of-read-from-segment
  (integerp (read-from-segment n eff-addr seg-reg x86)))

(defthm eff-addrs-okp-of-+-of-esp-negative-offset
  (implies (and (<= off 0)
                (stack-segment-assumptions32 stack-slots-needed x86) ;binds stack-slots-needed
                ;(stack-segment-assumptions32 stack-slots-needed x86-2)
                (equal (segment-base-and-bounds *compatibility-mode* *ss* x86)
                       (segment-base-and-bounds *compatibility-mode* *ss* x86-2))
                (integerp off)
                (<= (* -4 stack-slots-needed) off)
                (natp n)
                (<= n (- off))
                (x86p x86))
           (eff-addrs-okp n (binary-+ off (esp x86)) *ss* x86-2))
  :hints (("Goal" :in-theory (e/d (esp segment-max-eff-addr32 segment-min-eff-addr32 segment-base-and-bounds
                                       bvuminus
                                       32-bit-segment-size
                                       32-bit-segment-start
                                       32-bit-segment-start-and-size
                                     )
                                  (acl2::bvminus-becomes-bvplus-of-bvuminus)))))

(defthm segment-base-and-bounds-of-set-eip
  (equal (segment-base-and-bounds proc-mode seg-reg (set-eip eip x86))
         (segment-base-and-bounds proc-mode seg-reg x86)))

(defthm segment-base-and-bounds-of-write-byte-to-segment
  (equal (segment-base-and-bounds proc-mode seg-reg (write-byte-to-segment eff-addr seg-reg val x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm segment-base-and-bounds-of-write-to-segment
  (equal (segment-base-and-bounds proc-mode seg-reg (write-to-segment n eff-addr seg-reg val x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;move
(defthm nthcdr-of-1
  (equal (nthcdr 1 code)
         (cdr code)))

(defthm read-from-segment-when-code-segment-assumptions32-for-code
  (implies (and (code-segment-assumptions32-for-code code offset x86)
                (code-segment-well-formedp x86)
                ;;(syntaxp (quotep code))
                ;;(<= 0 eff-addr)
                (< (+ -1 eff-addr n) (+ offset (len code)))
                (natp n)
                (<= offset eff-addr)
                (integerp eff-addr)
                (natp offset))
           (equal (read-from-segment n eff-addr *cs* x86)
                  ;;todo: define a little-endian version of packbv:
                  (acl2::packbv n 8 (acl2::reverse-list (acl2::firstn n (nthcdr (- eff-addr offset) code))))))
  :hints (("Goal"
           :induct (READ-FROM-SEGMENT N EFF-ADDR 1 X86)
           :do-not '(generalize eliminate-destructors)
;           :expand (READ-BYTE-FROM-SEGMENT EFF-ADDR 1 X86)
           ;; :expand ((NTH EFF-ADDR CODE)
           ;;          )
           :in-theory (e/d (read-from-segment
                            acl2::packbv
                            ;;read-byte-from-segment
                            ;;segment-base-and-bounds
                            ACL2::CDR-OF-NTHCDR
                            )
                           ( read-byte-from-segment-when-equal-of-read-byte-list-from-segment
                             ;acl2::nth-of-cdr
                             ;;LIST::NTH-N-MINUS-ONE-OF-CDR
                             )))
          ("subgoal *1/2"
           ;; :use (:instance NTH-OF-READ-BYTE-LIST-FROM-SEGMENT (i (+ -1 EFF-ADDR))
           ;;                 (n (+ -1 (LEN CODE)))
           ;;                 (eff-addr 1)
           ;;                 (seg-reg 1))
           :expand (;;(READ-BYTE-FROM-SEGMENT 0 1 X86)
                    ;;(READ-BYTE-FROM-SEGMENT EFF-ADDR 1 X86)
                    (NTH EFF-ADDR CODE) ; to subst for the cdr
                    )
           :in-theory (e/d (read-from-segment
                            acl2::packbv
                            ;nth
                            acl2::equal-of-cons
                            ;;read-byte-from-segment
                            ;;segment-base-and-bounds
                            take
                            ACL2::CDR-OF-NTHCDR
                            )
                           (read-byte-from-segment-when-equal-of-read-byte-list-from-segment
                            ;acl2::nth-of-cdr
                            ;list::nth-n-minus-one-of-cdr
                            nth-of-read-byte-list-from-segment
                            ;; LIST::EQUAL-APPEND-REDUCTION!-ALT
                            ;; LIST::EQUAL-APPEND-REDUCTION!
                            ACL2::TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                            ACL2::NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                            ACL2::CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
                            ;ACL2::<-OF-LEN-WHEN-INTEGERP-OF-NTH ACL2::<-OF-LEN-WHEN-NTH-NON-NIL ;why?
                            )))))

;; should (seg-HIDDEN-LIMITI 1 X86) be showing up?
(defthm not-<-of-seg-hidden-limit-when-code-segment-assumptions32-for-code
  (implies (and (code-segment-assumptions32-for-code code offset x86)
                (< k (+ offset (len code)))
                (natp k)
                (natp offset))
           (not (< (xr :seg-hidden-limit 1 x86) k)))
  :hints (("Goal" :in-theory (enable code-segment-assumptions32-for-code
                                     32-bit-segment-start))))

;; this next batch is not strictly necessary since not-mv-nth-0-of-rme-size$inline should fire, but this can get rid of irrelevant stuff

(defthm mv-nth-0-of-rme-size-of-set-eip-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-eip eip x86) mem-ptr?))
                  (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm mv-nth-0-of-rme-size-of-set-esp-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-esp esp x86) mem-ptr?))
                  (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm mv-nth-0-of-rme-size-of-set-ebp-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-ebp ebp x86) mem-ptr?))
                  (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (enable set-ebp))))

;todo: more like this
(defthm mv-nth-0-of-rme-size-of-set-eax-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-eax eax x86) mem-ptr?))
                  (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm mv-nth-0-of-rme-size-of-set-ebx-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-ebx ebx x86) mem-ptr?))
                  (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm mv-nth-0-of-rme-size-of-set-ecx-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-ecx ecx x86) mem-ptr?))
                  (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm mv-nth-0-of-rme-size-of-set-edx-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-edx edx x86) mem-ptr?))
                  (mv-nth 0 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (enable set-edx))))

;;;

;not strictly necessary but helps keep terms small
(defthm mv-nth-1-of-rml-size-of-set-eip-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x (set-eip eip x86)))
                  (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable set-eip x86isa::rml-size))))

;not strictly necessary but helps keep terms small
(defthm mv-nth-1-of-rml-size-of-set-esp-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x (set-esp esp x86)))
                  (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable set-esp x86isa::rml-size))))

;not strictly necessary but helps keep terms small
(defthm mv-nth-1-of-rml-size-of-set-ebp-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x (set-ebp ebp x86)))
                  (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable set-ebp x86isa::rml-size))))

(defthm mv-nth-1-of-rml-size-of-set-eax-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x (set-eax eax x86)))
                  (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable set-eax x86isa::rml-size))))

(defthm mv-nth-1-of-rml-size-of-set-ebx-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x (set-ebx ebx x86)))
                  (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable set-ebx x86isa::rml-size))))

(defthm mv-nth-1-of-rml-size-of-set-ecx-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x (set-ecx ecx x86)))
                  (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable set-ecx x86isa::rml-size))))

(defthm mv-nth-1-of-rml-size-of-set-edx-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x (set-edx edx x86)))
                  (mv-nth 1 (x86isa::rml-size$inline nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable set-edx x86isa::rml-size))))

;not strictly necessary but helps keep terms small
(defthm mv-nth-1-of-rme-size-of-set-eip-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-eip eip x86) mem-ptr?))
                  (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (e/d (x86isa::rme-size) (ea-to-la set-eip)))))

;not strictly necessary but helps keep terms small
(defthm mv-nth-1-of-rme-size-of-set-esp-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-esp esp x86) mem-ptr?))
                  (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (e/d (x86isa::rme-size) (ea-to-la set-esp)))))

;not strictly necessary but helps keep terms small
(defthm mv-nth-1-of-rme-size-of-set-ebp-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-ebp ebp x86) mem-ptr?))
                  (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (e/d (x86isa::rme-size) (ea-to-la set-ebp)))))

(defthm mv-nth-1-of-rme-size-of-set-eax-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-eax eax x86) mem-ptr?))
                  (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (e/d (x86isa::rme-size) (ea-to-la set-eax)))))

(defthm mv-nth-1-of-rme-size-of-set-ebx-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-ebx ebx x86) mem-ptr?))
                  (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (e/d (x86isa::rme-size) (ea-to-la set-ebx)))))

(defthm mv-nth-1-of-rme-size-of-set-ecx-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-ecx ecx x86) mem-ptr?))
                  (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (e/d (x86isa::rme-size) (ea-to-la set-ecx)))))

(defthm mv-nth-1-of-rme-size-of-set-edx-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? (set-edx edx x86) mem-ptr?))
                  (mv-nth 1 (x86isa::rme-size$inline proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86 mem-ptr?))))
  :hints (("Goal" :in-theory (e/d (x86isa::rme-size) (ea-to-la set-edx)))))

(in-theory (disable set-eip)) ;move up

(acl2::add-known-boolean acl2::bitp)

;;hyp phrased in terms of sep-eff-addr-ranges
(defthmd write-to-segment-of-write-byte-to-segment-2
  (implies (and (integerp eff-addr1)
                (integerp eff-addr2)
                (sep-eff-addr-ranges eff-addr1 n eff-addr2 1) ;this version
                (unsigned-byte-p 32 n)
                (x86p x86))
           (equal (write-to-segment n eff-addr1 seg-reg val1 (write-byte-to-segment eff-addr2 seg-reg val2 x86))
                  (write-byte-to-segment eff-addr2 seg-reg val2 (write-to-segment n eff-addr1 seg-reg val1 x86))))
  :hints (("Goal" :use (:instance write-to-segment-of-write-byte-to-segment)
           :in-theory (e/d (bvlt
                            BVPLUS
                            bvuminus
                            bvminus
                            acl2::bvchop-of-sum-cases)
                           (write-to-segment-of-write-byte-to-segment
                            ACL2::BVPLUS-RECOLLAPSE)))))

(defun double-write-induct-two-vals (n eff-addr val1 val2 x86)
  (if (zp n)
      (list n eff-addr val1 val2 x86)
    (double-write-induct-two-vals (+ -1 n)
                                  (+ 1 eff-addr)
                                  (logtail 8 val1)
                                  (logtail 8 val2)
                                  x86)))

(defthm write-to-segment-of-write-to-segment-same
  (implies (and (integerp eff-addr)
                (unsigned-byte-p 32 n)
                (x86p x86))
           (equal (write-to-segment n eff-addr seg-reg val1 (write-to-segment n eff-addr seg-reg val2 x86))
                  (write-to-segment n eff-addr seg-reg val1 x86)))
  :hints (("subgoal *1/2" :expand ((:free (x86 eff-addr val) (write-to-segment n eff-addr seg-reg val x86))))
          ("Goal" :induct (double-write-induct-two-vals n eff-addr val1 val2 x86)
           :in-theory (e/d (sep-eff-addr-ranges-swap
                            write-to-segment
                            write-to-segment-of-write-byte-to-segment-2
                            unsigned-byte-p)
                           (sep-eff-addr-ranges
                            acl2::bvcat-equal-rewrite-alt
                            acl2::bvplus-recollapse
                            acl2::bvcat-equal-rewrite)))))

;same segment (we don't know how other segmentes are laid out)
(defthm write-to-segment-of-write-to-segment-diff
  (implies (and (syntaxp (acl2::smaller-termp eff-addr2 eff-addr1))
                (sep-eff-addr-ranges eff-addr1 n1 eff-addr2 n2)
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n2)
                (unsigned-byte-p 32 n1)
                (x86p x86))
           (equal (write-to-segment n1 eff-addr1 seg-reg val1 (write-to-segment n2 eff-addr2 seg-reg val2 x86))
                  (write-to-segment n2 eff-addr2 seg-reg val2 (write-to-segment n1 eff-addr1 seg-reg val1 x86))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("subgoal *1/2" ;:cases ((equal n1 1))
           :expand ((:free (x86 EFF-ADDR1) (WRITE-TO-SEGMENT N1 EFF-ADDR1 SEG-REG VAL1 x86))))
          ("Goal"
           :do-not '(fertilize)
           :induct (write-to-segment n1 eff-addr1 seg-reg val1 x86)
           :in-theory (e/d (sep-eff-addr-ranges-swap
                            write-to-segment
                            write-to-segment-of-write-byte-to-segment-2
                            bvlt
                            BVPLUS
                            bvuminus
                            bvminus
                            acl2::bvchop-of-sum-cases
                            UNSIGNED-BYTE-P)
                           (sep-eff-addr-ranges
                            ACL2::BVCAT-EQUAL-REWRITE-ALT
                            ACL2::BVPLUS-RECOLLAPSE
                            ACL2::BVCAT-EQUAL-REWRITE)))))

(defthmd write-to-segment-of-write-to-segment-diff-axe
  (implies (and (< eff-addr2 eff-addr1) ;or use axe-syntaxp
                (sep-eff-addr-ranges eff-addr1 n1 eff-addr2 n2)
                (integerp eff-addr1)
                (integerp eff-addr2)
                (unsigned-byte-p 32 n2)
                (unsigned-byte-p 32 n1)
                (x86p x86))
           (equal (write-to-segment n1 eff-addr1 seg-reg val1 (write-to-segment n2 eff-addr2 seg-reg val2 x86))
                  (write-to-segment n2 eff-addr2 seg-reg val2 (write-to-segment n1 eff-addr1 seg-reg val1 x86))))
  :hints (("Goal" :use write-to-segment-of-write-to-segment-diff
           :in-theory (disable write-to-segment-of-write-to-segment-diff))))

(defthm segment-is-32-bitsp-of-if
  (equal (segment-is-32-bitsp seg-reg (if test tp ep))
         (if test
             (segment-is-32-bitsp seg-reg tp)
           (segment-is-32-bitsp seg-reg ep))))

(defthm xr-of-if
  (equal (xr index fld (if test tp ep))
         (if test
             (xr index fld tp)
           (xr index fld ep))))

;;;
;;; read-stack-dword
;;;

;; Read 4 bytes (a double word, or dword) from the stack segment.
(defund read-stack-dword (eff-addr x86)
  (declare (xargs :stobjs x86
                  :guard (integerp eff-addr)))
  (read-from-segment 4 eff-addr *ss* x86))

(defthm read-stack-dword-of-xw
  (implies (and (not (equal :mem fld))
                (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (read-stack-dword eff-addr (xw fld index val x86))
                  (read-stack-dword eff-addr x86)))
  :hints (("Goal" :in-theory (enable read-stack-dword))))

;todo: enable
(defthmd read-stack-dword-intro
  (equal (read-from-segment 4 eff-addr *ss* x86)
         (read-stack-dword eff-addr x86))
  :hints (("Goal" :in-theory (enable read-stack-dword))))

;move
;can help when the inner if returns an error (a cons) or nil
(defthm if-of-if-of-cons-and-nil
  (equal (if (if test (cons a b) nil) tp ep)
         (if test tp ep)))
