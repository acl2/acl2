; 32-bit memory operations (segmented)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "portcullis")
(include-book "linear-memory")
(include-book "projects/x86isa/machine/segmentation" :dir :system)
(local (include-book "kestrel/bv/logapp" :dir :system)) ; todo
(local (include-book "kestrel/bv/rules" :dir :system)) ; for acl2::bvchop-+-cancel-seconds

(defthm integerp-of-mv-nth-0-of-segment-base-and-bounds
  (implies (x86p x86)
           (integerp (mv-nth 0 (segment-base-and-bounds proc-mode seg-reg x86))))
  :hints (("Goal" :in-theory (enable segment-base-and-bounds))))

(defthm unsigned-byte-p-64-of-mv-nth-0-of-segment-base-and-bounds
  (implies (x86p x86)
           (unsigned-byte-p 64 (mv-nth 0 (segment-base-and-bounds proc-mode seg-reg x86))))
  :hints (("Goal" :in-theory (enable segment-base-and-bounds))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defthm unsigned-byte-p-of-read-byte-from-segment
  (implies (x86p x86)
           (unsigned-byte-p 8 (read-byte-from-segment eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-byte-from-segment ifix))))

(defthm read-byte-from-segment-of-xw
  (implies (and (not (equal :mem fld))
                (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (read-byte-from-segment eff-addr seg-reg (xw fld index val x86))
                  (read-byte-from-segment eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-byte-from-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


(defthm x86p-of-write-byte-to-segment
  (implies (x86p x86)
           (x86p (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Read an N-byte chunk of data at effective address EFF-ADDR in the segment
;; indicated by SEG-REG.  Reads in a little-endian fashion: bytes with lower
;; addresses occupy less significant bits of the result.
;todo: disable
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

(defthm slice-of-read-from-segment-too-high
  (implies (and (<= (* 8 n) low)
                (natp n)
                (natp low))
           (equal (slice high low (read-from-segment n eff-addr seg-reg x86))
                  0))
  :hints (("Goal" :in-theory (enable acl2::slice-too-high-is-0))))

(defthm read-from-segment-of-xw
  (implies (and (not (equal :mem fld))
                (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (read-from-segment n eff-addr seg-reg (xw fld index val x86))
                  (read-from-segment n eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-from-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defthm read-byte-list-from-segment-of-xw
  (implies (and (not (equal :mem fld))
                (not (equal :seg-hidden-attr fld))
                (not (equal :seg-hidden-base fld))
                (not (equal :seg-hidden-limit fld))
                (not (equal fld :msr)))
           (equal (read-byte-list-from-segment n eff-addr seg-reg (xw fld index val x86))
                  (read-byte-list-from-segment n eff-addr seg-reg x86)))
  :hints (("Goal" :in-theory (enable read-byte-list-from-segment))))

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

;; do we need this?
(defthm read-byte-list-from-segment-of-1
  (equal (read-byte-list-from-segment 1 eff-addr seg-reg x86)
         (list (read-byte-from-segment eff-addr seg-reg x86)))
  :hints (("Goal" :expand (read-byte-list-from-segment 1 eff-addr seg-reg x86))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;; Resolves a read when we know the values stored in a memory chunk.
;; TODO: Require eff-addr and eff-addr2 to be constants?
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
