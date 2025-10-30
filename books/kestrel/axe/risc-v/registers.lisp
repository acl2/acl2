; Normal forms for register operations
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; TODO: Consider adding 32 to the names of the functions in this file (or
;; making separate packages for 32-bit and 64-bit RISC-V proofs).  Note that
;; the functions defined in this file are analogous to the functions used by
;; Axe for x86 reasoning (except for the memory size).

(include-book "portcullis")
(include-book "risc-v-rules")
(include-book "kestrel/risc-v/specialized/rv32im-le/states" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system)
(include-book "kestrel/bv/bvif" :dir :system)
(include-book "kestrel/bv/trim" :dir :system)
(include-book "kestrel/axe/axe-syntax" :dir :system)
(include-book "kestrel/axe/axe-syntax-functions-bv" :dir :system)
(local (include-book "kestrel/bv/bvchop" :dir :system))

(local
  (defthm unsigned-byte-p-when-ubyte32p
    (implies (ubyte32p x)
             (unsigned-byte-p 32 x))
    :hints (("Goal" :in-theory (enable ubyte32p)))))

;; Gets the value of register N.
(defund reg (n stat)
  (declare (xargs :guard (and (natp n) ; allows 0, which is special
                              (< n 32)
                              (stat32p stat))
                  :guard-hints (("Goal" :in-theory (enable ubyte5p)))))
  (read32-xreg-unsigned n stat))

;; for axe
(defthmd integerp-of-reg (integerp (reg n stat)) :hints (("Goal" :in-theory (enable reg))))

(defthm unsigned-byte-p-of-reg (unsigned-byte-p 32 (reg n stat)) :hints (("Goal" :in-theory (enable reg))))

;; Introduces REG.
(defthmd read32-xreg-unsigned-becomes-reg
  (equal (read32-xreg-unsigned n stat)
         (reg n stat))
  :hints (("Goal" :in-theory (enable reg))))

(defthm reg-of-0
  (equal (reg 0 stat)
         0)
  :hints (("Goal" :in-theory (enable reg))))

(defthm reg-of-if
  (equal (reg n (if test tp ep))
         (bvif 32 test (reg n tp) (reg n ep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sets the value of register N.
(defund set-reg (n val stat)
  (declare (xargs :guard (and (natp n) ; allows 0, which is special
                              (< n 32)
                              (unsigned-byte-p 32 val)
                              (stat32p stat))
                  :guard-hints (("Goal" :in-theory (enable ubyte5p)))))
  (write32-xreg n val stat))

;; writing to "register 0" has no effect
(defthm set-reg-of-0
  (implies (stat32p stat) ; too bad
           (equal (set-reg 0 val stat)
                  stat))
  :hints (("Goal" :in-theory (enable set-reg))))

;; Introduces set-reg.
(defthmd write32-xreg-becomes-set-reg
  (equal (write32-xreg n val stat)
         (set-reg n val stat))
  :hints (("Goal" :in-theory (enable set-reg))))

(defthm error32p-of-set-reg (equal (error32p (set-reg n val stat)) (error32p stat)) :hints (("Goal" :in-theory (enable set-reg))))
(defthm read32-pc-of-set-reg (equal (read32-pc (set-reg n val stat)) (read32-pc stat)) :hints (("Goal" :in-theory (enable set-reg))))
(defthm stat32p-of-set-reg (implies (stat32p stat) (stat32p (set-reg n val stat))) :hints (("Goal" :in-theory (enable set-reg))))

(defthm set-reg-of-set-reg-same
  (equal (set-reg reg val1 (set-reg reg val2 stat))
         (set-reg reg val1 stat))
  :hints (("Goal" :in-theory (enable set-reg))))

(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/bv/bvchop" :dir :system))
(local (include-book "kestrel/bv/logapp" :dir :system)) ; todo: move loghead rule
;open less
(defthm set-reg-does-nothing
  (implies (equal val (reg reg stat))
           (equal (set-reg reg val stat)
                  (stat32-fix stat)))
  :hints (("Goal" :in-theory (e/d (set-reg reg
                                     write32-xreg
                                     read32-xreg-unsigned
                                     acl2::update-nth-when-equal-of-nth)
                                  (acl2::loghead$inline
                                   )))))

(defthm set-reg-of-set-reg-diff
  (implies (and (syntaxp (and (quotep reg1)
                              (quotep reg2)))
                (< reg2 reg1))
           (equal (set-reg reg1 val1 (set-reg reg2 val2 stat))
                  (set-reg reg2 val2 (set-reg reg1 val1 stat))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :use write32-xreg-of-write32-xreg-diff-helper
           :in-theory (enable set-reg))))

;; both cases (the register numbers should usually be constants)
(defthm reg-of-set-reg
  (implies (and (natp n1)
                (natp n2)
                (< n1 32)
                (< n2 32))
           (equal (reg n1 (set-reg n2 val stat))
                  (if (equal 0 n1)
                      0
                    (if (equal n1 n2)
                        (bvchop 32 val)
                      (reg n1 stat)))))
  :hints (("Goal" :in-theory (enable reg set-reg ubyte5-fix ubyte5p bvchop))))

(defthm reg-of-write32-pc (equal (reg n (write32-pc pc stat)) (reg n stat)) :hints (("Goal" :in-theory (enable reg))))

(defthmd set-reg-of-bvchop
  (equal (set-reg reg (bvchop 32 val) x)
         (set-reg reg val x))
  :hints (("Goal" :in-theory (enable set-reg write32-xreg))))

(defthmd set-reg-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp val nil dag-array))
           (equal (set-reg reg val x)
                  (set-reg reg (trim 32 val) x)))
  :hints (("Goal" :in-theory (enable trim set-reg write32-xreg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; register aliases (we plan to keep these enabled):
(defund x1 (stat) (declare (xargs :guard (stat32p stat))) (reg 1 stat))
(defund x2 (stat) (declare (xargs :guard (stat32p stat))) (reg 2 stat))
(defund x3 (stat) (declare (xargs :guard (stat32p stat))) (reg 3 stat))
(defund x4 (stat) (declare (xargs :guard (stat32p stat))) (reg 4 stat))
(defund x5 (stat) (declare (xargs :guard (stat32p stat))) (reg 5 stat))
(defund x6 (stat) (declare (xargs :guard (stat32p stat))) (reg 6 stat))
(defund x7 (stat) (declare (xargs :guard (stat32p stat))) (reg 7 stat))
(defund x8 (stat) (declare (xargs :guard (stat32p stat))) (reg 8 stat))
(defund x9 (stat) (declare (xargs :guard (stat32p stat))) (reg 9 stat))
(defund x10 (stat) (declare (xargs :guard (stat32p stat))) (reg 10 stat))
(defund x11 (stat) (declare (xargs :guard (stat32p stat))) (reg 11 stat))
(defund x12 (stat) (declare (xargs :guard (stat32p stat))) (reg 12 stat))
(defund x13 (stat) (declare (xargs :guard (stat32p stat))) (reg 13 stat))
(defund x14 (stat) (declare (xargs :guard (stat32p stat))) (reg 14 stat))
(defund x15 (stat) (declare (xargs :guard (stat32p stat))) (reg 15 stat))

(defund x16 (stat) (declare (xargs :guard (stat32p stat))) (reg 16 stat))
(defund x17 (stat) (declare (xargs :guard (stat32p stat))) (reg 17 stat))
(defund x18 (stat) (declare (xargs :guard (stat32p stat))) (reg 18 stat))
(defund x19 (stat) (declare (xargs :guard (stat32p stat))) (reg 19 stat))
(defund x20 (stat) (declare (xargs :guard (stat32p stat))) (reg 20 stat))
(defund x21 (stat) (declare (xargs :guard (stat32p stat))) (reg 21 stat))
(defund x22 (stat) (declare (xargs :guard (stat32p stat))) (reg 22 stat))
(defund x23 (stat) (declare (xargs :guard (stat32p stat))) (reg 23 stat))
(defund x24 (stat) (declare (xargs :guard (stat32p stat))) (reg 24 stat))
(defund x25 (stat) (declare (xargs :guard (stat32p stat))) (reg 25 stat))
(defund x26 (stat) (declare (xargs :guard (stat32p stat))) (reg 26 stat))
(defund x27 (stat) (declare (xargs :guard (stat32p stat))) (reg 27 stat))
(defund x28 (stat) (declare (xargs :guard (stat32p stat))) (reg 28 stat))
(defund x29 (stat) (declare (xargs :guard (stat32p stat))) (reg 29 stat))
(defund x30 (stat) (declare (xargs :guard (stat32p stat))) (reg 30 stat))
(defund x31 (stat) (declare (xargs :guard (stat32p stat))) (reg 31 stat))

;; register aliases (we plan to keep these enabled):
;; (defun zero (stat) (declare (xargs :guard (stat32p stat))) (x0 stat))
(defun ra (stat) (declare (xargs :guard (stat32p stat))) (x1 stat))
(defun sp (stat) (declare (xargs :guard (stat32p stat))) (x2 stat))
(defun gp (stat) (declare (xargs :guard (stat32p stat))) (x3 stat))
(defun tp (stat) (declare (xargs :guard (stat32p stat))) (x4 stat))

(defun t0 (stat) (declare (xargs :guard (stat32p stat))) (x5 stat))
(defun t1 (stat) (declare (xargs :guard (stat32p stat))) (x6 stat))
(defun t2 (stat) (declare (xargs :guard (stat32p stat))) (x7 stat))

(defun s0 (stat) (declare (xargs :guard (stat32p stat))) (x8 stat)) ; 2 aliases for x8
(defun fp (stat) (declare (xargs :guard (stat32p stat))) (x8 stat))
(defun s1 (stat) (declare (xargs :guard (stat32p stat))) (x9 stat))

(defun a0 (stat) (declare (xargs :guard (stat32p stat))) (x10 stat))
(defun a1 (stat) (declare (xargs :guard (stat32p stat))) (x11 stat))
(defun a2 (stat) (declare (xargs :guard (stat32p stat))) (x12 stat))
(defun a3 (stat) (declare (xargs :guard (stat32p stat))) (x13 stat))
(defun a4 (stat) (declare (xargs :guard (stat32p stat))) (x14 stat))
(defun a5 (stat) (declare (xargs :guard (stat32p stat))) (x15 stat))
(defun a6 (stat) (declare (xargs :guard (stat32p stat))) (x16 stat))
(defun a7 (stat) (declare (xargs :guard (stat32p stat))) (x17 stat))

(defun s2 (stat) (declare (xargs :guard (stat32p stat))) (x18 stat))
(defun s3 (stat) (declare (xargs :guard (stat32p stat))) (x19 stat))
(defun s4 (stat) (declare (xargs :guard (stat32p stat))) (x20 stat))
(defun s5 (stat) (declare (xargs :guard (stat32p stat))) (x21 stat))
(defun s6 (stat) (declare (xargs :guard (stat32p stat))) (x22 stat))
(defun s7 (stat) (declare (xargs :guard (stat32p stat))) (x23 stat))
(defun s8 (stat) (declare (xargs :guard (stat32p stat))) (x24 stat))
(defun s9 (stat) (declare (xargs :guard (stat32p stat))) (x25 stat))
(defun s10 (stat) (declare (xargs :guard (stat32p stat))) (x26 stat))
(defun s11 (stat) (declare (xargs :guard (stat32p stat))) (x27 stat))

(defun t3 (stat) (declare (xargs :guard (stat32p stat))) (x28 stat))
(defun t4 (stat) (declare (xargs :guard (stat32p stat))) (x29 stat))
(defun t5 (stat) (declare (xargs :guard (stat32p stat))) (x30 stat))
(defun t6 (stat) (declare (xargs :guard (stat32p stat))) (x31 stat))
