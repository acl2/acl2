; Rules about the RISC-V model
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

(include-book "portcullis")
(include-book "kestrel/risc-v/specialized/execution32" :dir :system)
(local (include-book "kestrel/lists-light/repeat" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable floor ash logand)))

;; Non-local because this prevents out-of-memory errors
(in-theory (disable (:e repeat)))

(defthm nth-of-memory32i-fix
  (implies (unsigned-byte-p 32 n)
           (equal (nth n (memory32i-fix x))
                  (ubyte8-fix (nth n x))))
  :hints (("Goal" :in-theory (enable memory32i-fix memory32ip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm ubyte5-fix-upper-bound-linear
  (<= (ubyte5-fix x) 31)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ubyte5-fix ubyte5p))))

(defthm read32-xreg-unsigned-upper-bound-linear
  (<= (read32-xreg-unsigned riscv::reg stat) 4294967295)
  :rule-classes :linear
  :hints (("Goal" :use (:instance riscv::ubyte32p-of-read32-xreg-unsigned)
           :in-theory (e/d (ubyte32p) (riscv::ubyte32p-of-read32-xreg-unsigned)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read32-xreg-unsigned-of-write32-pc
  (equal (read32-xreg-unsigned reg (write32-pc pc stat))
         (read32-xreg-unsigned reg stat))
  :hints (("Goal" :in-theory (enable write32-pc read32-xreg-unsigned))))

(defthm read32-xreg-unsigned-of-write32-mem-ubyte8
  (equal (read32-xreg-unsigned reg (write32-mem-ubyte8 addr val stat))
         (read32-xreg-unsigned reg stat))
  :hints (("Goal" :in-theory (enable read32-xreg-unsigned write32-mem-ubyte8))))

(defthm read32-xreg-unsigned-of-write32-mem-ubyte32-lendian
  (equal (read32-xreg-unsigned reg (write32-mem-ubyte32-lendian addr val stat))
         (read32-xreg-unsigned reg stat))
  :hints (("Goal" :in-theory (enable write32-mem-ubyte32-lendian))))

;; read of write same reg
(defthm read32-xreg-unsigned-of-write32-xreg-same
  (equal (read32-xreg-unsigned reg (write32-xreg reg val stat))
         (if (equal (ubyte5-fix reg) 0)
             0
           (loghead 32 val)))
  :hints (("Goal" :in-theory (enable read32-xreg-unsigned write32-xreg xregs32i-fix xregs32ip UBYTE32-FIX ubyte32p))))

(defthm read32-xreg-unsigned-of-write32-xreg-diff
  (implies (not (equal (ubyte5-fix reg1) (ubyte5-fix reg2)))
           (equal (read32-xreg-unsigned reg1 (write32-xreg reg2 val stat))
                  (read32-xreg-unsigned reg1 stat)))
  :hints (("Goal" :in-theory (enable read32-xreg-unsigned write32-xreg xregs32i-fix xregs32ip))))

(defthm read32-xreg-unsigned-of-write32-xreg-both
  (equal (read32-xreg-unsigned reg1 (write32-xreg reg2 val stat))
         (if (equal (ubyte5-fix reg1) (ubyte5-fix reg2))
             ;; same register:
             (if (equal (ubyte5-fix reg1) 0)
                 0
               (loghead 32 val))
           ;; different registers:
           (read32-xreg-unsigned reg1 stat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read32-pc-of-write32-xreg
  (equal (read32-pc (write32-xreg reg val stat))
         (read32-pc stat))
  :hints (("Goal" :in-theory (enable write32-xreg read32-pc))))

(defthm read32-pc-of-write32-pc
  (equal (read32-pc (write32-pc pc stat))
         (loghead 32 pc))
  :hints (("Goal" :in-theory (enable write32-pc read32-pc UBYTE32-FIX UBYTE32P))))

(defthm read32-pc-of-write32-mem-ubyte8
  (equal (read32-pc (write32-mem-ubyte8 addr val stat))
         (read32-pc stat))
  :hints (("Goal" :in-theory (enable read32-pc write32-mem-ubyte8))))

(defthm read32-pc-of-write32-mem-ubyte32-lendian
  (equal (read32-pc (write32-mem-ubyte32-lendian addr val stat))
         (read32-pc stat))
  :hints (("Goal" :in-theory (enable write32-mem-ubyte32-lendian))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm error32p-of-write32-pc
  (equal (error32p (write32-pc pc stat))
         (error32p stat))
  :hints (("Goal" :in-theory (enable write32-pc error32p))))

(defthm error32p-of-write32-xreg
  (equal (error32p (write32-xreg reg val stat))
         (error32p stat))
  :hints (("Goal" :in-theory (enable write32-xreg error32p))))

(defthm error32p-of-write32-mem-ubyte8
  (equal (error32p (write32-mem-ubyte8 addr val stat))
         (error32p stat))
  :hints (("Goal" :in-theory (enable error32p write32-mem-ubyte8))))

(defthm error32p-of-write32-mem-ubyte32-lendian
  (equal (error32p (write32-mem-ubyte32-lendian addr val stat))
         (error32p stat))
  :hints (("Goal" :in-theory (enable write32-mem-ubyte32-lendian))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read32-mem-ubyte8-of-write32-pc
  (equal (read32-mem-ubyte8 addr (write32-pc pc stat))
         (read32-mem-ubyte8 addr stat))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte8 write32-pc))))

(defthm read32-mem-ubyte8-of-write32-xreg
  (equal (read32-mem-ubyte8 addr (write32-xreg reg val stat))
         (read32-mem-ubyte8 addr stat))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte8 write32-xreg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read32-mem-ubyte8-of-write32-mem-ubyte8-same
  (equal (read32-mem-ubyte8 addr (write32-mem-ubyte8 addr val stat))
         (mod (ifix val) 256))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte8
                                     write32-mem-ubyte8
                                     ubyte8-fix
                                     ubyte8p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read32-mem-ubyte32-lendian-of-write32-pc
  (equal (read32-mem-ubyte32-lendian addr (write32-pc pc stat))
         (read32-mem-ubyte32-lendian addr stat))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte32-lendian))))

(defthm read32-mem-ubyte32-lendian-of-write32-xreg
  (equal (read32-mem-ubyte32-lendian addr (write32-xreg reg val stat))
         (read32-mem-ubyte32-lendian addr stat))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte32-lendian))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; brings the write of the PC forward
(defthm write32-mem-ubyte32-lendian-of-write32-pc
  (equal (write32-mem-ubyte32-lendian addr val (write32-pc pc stat))
         (write32-pc pc (write32-mem-ubyte32-lendian addr val stat)))
  :hints (("Goal" :in-theory (enable write32-pc write32-mem-ubyte32-lendian
                                     write32-mem-ubyte8
                                     ;stat32i
                                     ))))

;; brings the write of the register forward
(defthm write32-mem-ubyte32-lendian-of-write32-xreg
  (equal (write32-mem-ubyte32-lendian addr val (write32-xreg reg val2 stat))
         (write32-xreg reg val2 (write32-mem-ubyte32-lendian addr val stat)))
  :hints (("Goal" :in-theory (enable write32-xreg write32-mem-ubyte32-lendian
                                     write32-mem-ubyte8
                                     ;stat32i
                                     ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; writing to register 0 has no effect
(defthm write32-xreg-of-0-arg1
  (equal (write32-xreg 0 val stat)
         (stat32i-fix stat))
  :hints (("Goal" :in-theory (enable write32-pc write32-xreg
                                     write32-mem-ubyte8))))

(defthm write32-pc-of-write32-pc
  (equal (write32-pc pc1 (write32-pc pc2 stat))
         (write32-pc pc1 stat))
  :hints (("Goal" :in-theory (enable write32-pc))))

(defthm write32-xreg-of-write32-pc
  (equal (write32-xreg reg val (write32-pc pc stat))
         (write32-pc pc (write32-xreg reg val stat)))
  :hints (("Goal" :in-theory (enable write32-pc write32-xreg
                                     write32-mem-ubyte8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm write32-xreg-of-write32-xreg-same
  (equal (write32-xreg reg val1 (write32-xreg reg val2 stat))
         (write32-xreg reg val1 stat))
  :hints (("Goal" :in-theory (enable write32-xreg xregs32i-fix acl2::ubyte32-list-fix xregs32ip ubyte32p))))
