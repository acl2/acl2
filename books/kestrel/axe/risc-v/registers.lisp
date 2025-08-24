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
(include-book "kestrel/risc-v/specialized/states32" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system)
(local (include-book "kestrel/bv/bvchop" :dir :system))

(local
  (defthm unsigned-byte-p-when-ubyte32p
    (implies (ubyte32p x)
             (unsigned-byte-p 32 x))
    :hints (("Goal" :in-theory (enable ubyte32p)))))

;; Gets the value of register N.
(defund reg (n stat)
  (declare (xargs :guard (and (posp n)
                              (< n 31)
                              (stat32ip stat))
                  :guard-hints (("Goal" :in-theory (enable ubyte5p)))))
  (read32-xreg-unsigned n stat))

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

;; todo: reg-of-0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sets the value of register N.
(defund set-reg (n val stat)
  (declare (xargs :guard (and (posp n)
                              (< n 31)
                              (unsigned-byte-p 32 val)
                              (stat32ip stat))
                  :guard-hints (("Goal" :in-theory (enable ubyte5p)))))
  (write32-xreg n val stat))

;; writing to "register 0" has no effect
(defthm set-reg-of-0
  (implies (stat32ip stat) ; too bad
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
(defthm stat32ip-of-set-reg (implies (stat32ip stat) (stat32ip (set-reg n val stat))) :hints (("Goal" :in-theory (enable set-reg))))

(defthm set-reg-of-set-reg-same
  (equal (set-reg reg val1 (set-reg reg val2 stat))
         (set-reg reg val1 stat))
  :hints (("Goal" :in-theory (enable set-reg))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; register aliases (we plan to keep these enabled):
(defund x1 (stat) (declare (xargs :guard (stat32ip stat))) (reg 1 stat))
(defund x2 (stat) (declare (xargs :guard (stat32ip stat))) (reg 2 stat))
(defund x8 (stat) (declare (xargs :guard (stat32ip stat))) (reg 8 stat))
(defund x10 (stat) (declare (xargs :guard (stat32ip stat))) (reg 10 stat))
(defund x11 (stat) (declare (xargs :guard (stat32ip stat))) (reg 11 stat))

;; register aliases (we plan to keep these enabled):
(defun ra (stat) (declare (xargs :guard (stat32ip stat))) (x1 stat))
(defun sp (stat) (declare (xargs :guard (stat32ip stat))) (x2 stat))
(defun a0 (stat) (declare (xargs :guard (stat32ip stat))) (x10 stat))
(defun a1 (stat) (declare (xargs :guard (stat32ip stat))) (x11 stat))
