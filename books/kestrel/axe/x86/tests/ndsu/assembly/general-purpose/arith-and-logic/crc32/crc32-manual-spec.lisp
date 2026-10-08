; A restatement of the CRC32 instruction semantics directly from the Intel
; SDM Vol 2A CRC32 entry, independent of the ACL2 x86 model, for use in the
; statements of the correctness theorems in this directory.
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "kestrel/x86/portcullis" :dir :system)

;; This book restates, from the Intel SDM Vol 2A CRC32 operation section
;; alone, the CRC32 update computation:
;;
;;   TEMP1[SRCSZ-1:0] := BIT_REFLECT_SRCSZ(SRC[SRCSZ-1:0])
;;   TEMP2[31:0]      := BIT_REFLECT32(DEST[31:0])
;;   TEMP3[SRCSZ+31:0] := TEMP1[SRCSZ-1:0] << 32
;;   TEMP4[SRCSZ+31:0] := TEMP2[31:0] << SRCSZ
;;   TEMP5[SRCSZ+31:0] := TEMP3 XOR TEMP4
;;   TEMP6[31:0]       := TEMP5 MOD2 11EDC6F41H
;;   DEST[31:0]        := BIT_REFLECT(TEMP6[31:0])
;;
;; using only generic arithmetic (logxor, ash, logbit, logcons,
;; integer-length), not any function from the ACL2 x86 model
;; (projects/x86isa). This restatement is used in the statements of the
;; correctness theorems in this directory; its equivalence to the ACL2 x86
;; model's own CRC32 semantic function (x86isa::crc32, in
;; projects/x86isa/machine/instructions/crc32-spec.lisp) is established
;; below as a bridge lemma, for use only in hints.

;; centaur/bitops/ihs-extensions is not local: it is what defines LOGCONS
;; and LOGBIT, which spec-bit-reflect (below, exported) is built from.
(include-book "centaur/bitops/ihs-extensions" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))

;; As in the ACL2 x86 model's own crc32-spec.lisp, these two rules interfere
;; with direct reasoning about INTEGER-LENGTH below:
(local (in-theory (disable acl2::<-of-integer-length-arg1
                           acl2::<-of-integer-length-arg2)))

;; This book is used only to justify (via a bridge lemma, in hints) the
;; theorem statements in this directory; it is not itself part of the ACL2
;; x86 model, so it is fine for it to include the model's own CRC32
;; specification, purely to state and prove the bridge lemma. Not local:
;; the exported bridge lemmas' proofs (below) reference x86isa::bit-reflect,
;; x86isa::gf2-mod, and x86isa::crc32.
(include-book "projects/x86isa/machine/instructions/crc32-spec" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BIT_REFLECT_n: reverse the low n bits of x (Intel SDM Vol 2A CRC32 entry).
(defund spec-bit-reflect (n x)
  (declare (xargs :guard (and (natp n) (natp x))
                   :measure (nfix n)))
  (cond ((zp n) 0)
        (t (acl2::logcons (acl2::logbit (1- n) x)
                          (spec-bit-reflect (1- n) x)))))

;; Termination support for spec-mod2 below: XORing into the dividend a
;; shifted copy of the divisor (with matching leading bit) strictly
;; decreases the dividend's degree, mirroring the ACL2 x86 model's own
;; local lemma (of the same name) supporting the termination of gf2-mod.
(local
 (defthm integer-length-of-logxor-same-length
   (implies (and (posp x)
                 (natp y)
                 (equal (integer-length y) (integer-length x)))
            (< (integer-length (logxor x y))
               (integer-length x)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (acl2::enable* bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs)))))

;; MOD2: remainder of polynomial division over GF(2) (Intel SDM Vol 2A
;; CRC32 entry): while the dividend has degree at least that of the
;; divisor, subtract (i.e. XOR) the divisor, shifted to align its leading
;; coefficient with the dividend's.
(defund spec-mod2 (x y)
  (declare (xargs :guard (and (natp x) (posp y))
                   :measure (integer-length x)))
  (if (or (not (natp x)) (not (posp y)))
      0
    (let* ((deg-x (1- (integer-length x)))
           (deg-y (1- (integer-length y))))
      (if (< deg-x deg-y)
          x
        (spec-mod2 (logxor x (ash y (- deg-x deg-y))) y)))))

;; The CRC-32C (Castagnoli) generator polynomial, 11EDC6F41H, as given by
;; name in the Intel SDM Vol 2A CRC32 entry.
(defconst *crc32-polynomial-manual* #x11EDC6F41)

;; The CRC32 update, as specified by the Intel SDM Vol 2A CRC32 entry: for
;; an SRCSZ-bit SRC (data, data-width), absorb it into the 32-bit DEST
;; (crc).
(defund spec-crc32 (crc data data-width)
  (declare (xargs :guard (and (unsigned-byte-p 32 crc)
                              (natp data)
                              (natp data-width))))
  (spec-bit-reflect
   32
   (spec-mod2 (logxor (ash (spec-bit-reflect data-width data) 32)
                       (ash (spec-bit-reflect 32 crc) data-width))
              *crc32-polynomial-manual*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bridge lemmas (not from the Intel manual): these establish that the
;; restatement above computes the same result as the ACL2 x86 model's own
;; CRC32 specification function, x86isa::crc32. This is proved by simple
;; simultaneous induction, since spec-bit-reflect/spec-mod2 mirror the
;; recursive structure of x86isa::bit-reflect/x86isa::gf2-mod exactly. This
;; equivalence is for use only in proof hints, never in a theorem
;; statement.

(defthmd spec-bit-reflect-becomes-x86isa-bit-reflect
  (implies (natp n)
           (equal (spec-bit-reflect n x)
                  (x86isa::bit-reflect n x)))
  :hints (("Goal" :induct (spec-bit-reflect n x)
           :in-theory (enable spec-bit-reflect x86isa::bit-reflect))))

(defthmd spec-mod2-becomes-gf2-mod
  (implies (and (natp x) (posp y))
           (equal (spec-mod2 x y)
                  (x86isa::gf2-mod x y)))
  :hints (("Goal" :induct (spec-mod2 x y)
           :in-theory (enable spec-mod2 x86isa::gf2-mod))))

(defthmd spec-crc32-becomes-x86isa-crc32
  (implies (and (unsigned-byte-p 32 crc)
               (natp data)
               (natp data-width))
           (equal (spec-crc32 crc data data-width)
                  (x86isa::crc32 crc data data-width)))
  :hints (("Goal" :in-theory (enable spec-crc32 x86isa::crc32 x86isa::crc
                                     spec-bit-reflect-becomes-x86isa-bit-reflect
                                     spec-mod2-becomes-gf2-mod))))

;; The result of BIT_REFLECT_n always fits in n bits (Intel SDM Vol 2A
;; CRC32 entry).
(defthm unsigned-byte-p-of-spec-bit-reflect
  (implies (natp n)
           (unsigned-byte-p n (spec-bit-reflect n x)))
  :hints (("Goal" :induct (spec-bit-reflect n x)
           :in-theory (acl2::enable* spec-bit-reflect
                                     bitops::ihsext-bounds-thms))))

;; The CRC32 result always fits in 32 bits (Intel SDM Vol 2A CRC32 entry:
;; "DEST[31:0] := BIT_REFLECT(TEMP6[31:0])").
(defthm unsigned-byte-p-32-of-spec-crc32
  (unsigned-byte-p 32 (spec-crc32 crc data data-width))
  :hints (("Goal" :in-theory (enable spec-crc32)
           :use (:instance unsigned-byte-p-of-spec-bit-reflect
                           (n 32)
                           (x (spec-mod2 (logxor (ash (spec-bit-reflect data-width data) 32)
                                                  (ash (spec-bit-reflect 32 crc) data-width))
                                         *crc32-polynomial-manual*)))))
  :rule-classes (:rewrite :type-prescription))

;; Variant of the above for wider (e.g. 64-bit) locations, mirroring
;; x86isa::unsigned-byte-p-of-crc32.
(defthm unsigned-byte-p-of-spec-crc32
  (implies (and (integerp n) (<= 32 n))
           (unsigned-byte-p n (spec-crc32 crc data data-width)))
  :hints (("Goal" :use unsigned-byte-p-32-of-spec-crc32
           :in-theory (disable unsigned-byte-p-32-of-spec-crc32
                               spec-crc32
                               unsigned-byte-p))))
