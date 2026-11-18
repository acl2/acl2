; Alternate definitions of RISC-V instruction semantic functions
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; This book recharacterizes the semantic functions of the RISC-V instructions
;; (the exec32-XXX functions in the rv32im-le model) in terms of our normal
;; forms: BV functions (instead of logops and raw arithmetic like +), and
;; getters and setters such as REG, SET-REG, PC, SET-PC, READ, and WRITE.

;; Notes on the forms used:
;; - Immediates are assumed to have the right sizes (they are constants from
;;   decoding, so the hyps get relieved by evaluation).  The PC argument
;;   (passed in by exec32-instr) is assumed to be a 32-bit value.
;; - Comparison results (SLT, etc.) use (bvif 32 test 1 0).
;; - In branches, the test is put in positive form (e.g., BGE tests (sbvlt
;;   ...) and has the fall-through case first).
;; - Error cases (misaligned jump or branch targets) use ERROR32, as in the
;;   model.

;; See tests/alt-defs-tests.lisp for tests that lift code for each instruction
;; using these rules (instead of opening the exec32-XXX functions).

(include-book "registers")
(include-book "pc")
(include-book "read-and-write")
(include-book "kestrel/bv/bvplus-def" :dir :system)
(include-book "kestrel/bv/bvminus-def" :dir :system)
(include-book "kestrel/bv/bvmult-def" :dir :system)
(include-book "kestrel/bv/bvand-def" :dir :system)
(include-book "kestrel/bv/bvor-def" :dir :system)
(include-book "kestrel/bv/bvxor-def" :dir :system)
(include-book "kestrel/bv/bvshl-def" :dir :system)
(include-book "kestrel/bv/bvshr-def" :dir :system)
(include-book "kestrel/bv/bvashr-def" :dir :system)
(include-book "kestrel/bv/bvsx-def" :dir :system)
(include-book "kestrel/bv/bvlt-def" :dir :system)
(include-book "kestrel/bv/sbvlt-def" :dir :system)
(include-book "kestrel/bv/bvif-def" :dir :system)
(include-book "kestrel/bv/bvcat-def" :dir :system)
(include-book "kestrel/bv/slice-def" :dir :system)
(include-book "kestrel/bv/getbit-def" :dir :system)
(include-book "kestrel/bv/bvdiv" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)
(include-book "kestrel/bv/sbvdiv-def" :dir :system)
(include-book "kestrel/bv/sbvrem" :dir :system)
(local (include-book "read-over-write-rules"))
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/bv/ash" :dir :system))
(local (include-book "kestrel/bv/bvand" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/bv/rules3" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/rem" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Local rules that turn the model's state accessors into our normal forms.
;; The remaining work in each proof is then about the BV values.

(local
  (defthm write32-xreg-becomes-set-reg-of-bvchop
    (equal (write32-xreg n val stat)
           (set-reg n (bvchop 32 val) stat))
    :hints (("Goal" :in-theory (enable set-reg write32-xreg)))))

(local
  (defthm write32-pc-becomes-set-pc-of-bvchop
    (equal (write32-pc pc stat)
           (set-pc (bvchop 32 pc) stat))
    :hints (("Goal" :in-theory (enable set-pc write32-pc)))))

(local
  (defthm inc32-pc-becomes-set-pc
    (equal (inc32-pc stat)
           (set-pc (bvplus 32 4 (pc stat)) stat))
    :hints (("Goal" :in-theory (enable inc32-pc pc bvplus)))))

(local
  (defthm read32-xreg-signed-becomes-logext-of-reg
    (equal (read32-xreg-signed n stat)
           (logext 32 (reg n stat)))
    :hints (("Goal" :in-theory (enable read32-xreg-signed reg)))))

(local (in-theory (enable read32-xreg-unsigned-becomes-reg
                          read32-pc-becomes-pc
                          acl2::bvchop-of-+-becomes-bvplus
                          acl2::ubyte5-fix acl2::ubyte5p
                          acl2::ubyte12-fix acl2::ubyte12p
                          acl2::ubyte20-fix acl2::ubyte20p
                          acl2::ubyte32-fix acl2::ubyte32p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Local rules about the values computed by the instructions.

(local
  (defthm bvchop-32-of-ash-becomes-bvshl
    (implies (and (natp n) (< n 32))
             (equal (bvchop 32 (ash x n))
                    (bvshl 32 x n)))
    :hints (("Goal" :in-theory (e/d (bvshl) (ash))))))

(local
  (defthm bvchop-32-of-ash-of-minus-becomes-bvshr
    (implies (and (natp n) (< n 32) (unsigned-byte-p 32 x))
             (equal (bvchop 32 (ash x (- n)))
                    (bvshr 32 x n)))
    :hints (("Goal" :cases ((equal n 0)) :in-theory (e/d (bvshr) (ash))))))

(local
  (defthm bvchop-32-of-ash-of-logext-becomes-bvashr
    (implies (and (natp n) (< n 32))
             (equal (bvchop 32 (ash (logext 32 x) (- n)))
                    (bvashr 32 x n)))
    :hints (("Goal" :in-theory (e/d (bvashr bvshr acl2::ash-becomes-logtail acl2::bvchop-of-logext-becomes-bvsx-gen) (ash))))))

(local
  (defthm bvchop-32-of-ash-of-*-of-logext-and-logext
    (implies (and (integerp a) (integerp b))
             (equal (bvchop 32 (ash (* (logext 32 a) (logext 32 b)) -32))
                    (slice 63 32 (bvmult 64 (bvsx 64 32 a) (bvsx 64 32 b)))))
    :hints (("Goal" :in-theory (e/d (bvmult bvshr acl2::bvsx-rewrite) (ash acl2::bvchop-of-logext-becomes-bvsx))))))

(local
  (defthm bvchop-32-of-ash-of-*-becomes-slice-of-bvmult
    (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
             (equal (bvchop 32 (ash (* a b) -32))
                    (slice 63 32 (bvmult 64 a b))))
    :hints (("Goal" :in-theory (e/d (bvmult bvshr) (ash))))))

(local
  (defthm bvchop-32-of-ash-of-*-of-logext
    (implies (and (integerp a) (unsigned-byte-p 32 b))
             (equal (bvchop 32 (ash (* (logext 32 a) b) -32))
                    (slice 63 32 (bvmult 64 (bvsx 64 32 a) b))))
    :hints (("Goal" :in-theory (e/d (bvmult bvshr acl2::bvsx-rewrite) (ash acl2::bvchop-of-logext-becomes-bvsx))))))

(local
  (defthm bvchop-32-of-ash-of-*-of-logext-alt
    (implies (and (integerp a) (unsigned-byte-p 32 b))
             (equal (bvchop 32 (ash (* b (logext 32 a)) -32))
                    (slice 63 32 (bvmult 64 (bvsx 64 32 a) b))))
    :hints (("Goal" :use bvchop-32-of-ash-of-*-of-logext
                    :in-theory (disable bvchop-32-of-ash-of-*-of-logext)))))

;; N is a free variable, bound by an unsigned-byte-p hyp in the context.
(local
  (defthm ash-becomes-bvcat-when-unsigned-byte-p
    (implies (and (unsigned-byte-p n x)
                  (natp k))
             (equal (ash x k)
                    (bvcat n x k 0)))
    :hints (("Goal" :in-theory (enable bvcat acl2::logapp ash)))))

(local
  (defthm getbit-1-of-bvand-2-4294967294
    (equal (getbit 1 (bvand 2 4294967294 z))
           (getbit 1 z))))

(local
  (defthm bvand-32-of-+-becomes-bvand-of-bvplus
    (implies (and (integerp a) (integerp b))
             (equal (bvand 32 k (+ a b))
                    (bvand 32 k (bvplus 32 a b))))
    :hints (("Goal" :in-theory (e/d (bvplus) (acl2::bvchop-of-+-becomes-bvplus))))))

(local
  (defthm getbit-1-of-+-becomes-getbit-1-of-bvplus
    (implies (and (integerp a) (integerp b))
             (equal (getbit 1 (+ a b))
                    (getbit 1 (bvplus 32 a b))))
    :hints (("Goal" :in-theory (e/d (bvplus) (acl2::bvchop-of-+-becomes-bvplus))))))

;; For JALR: the target, with its low bit cleared, is 4-byte aligned iff bit 1 is 0.
(local
  (defthm equal-of-0-and-mod-of-logand-4294967294-and-4
    (implies (integerp z)
             (equal (equal (mod (logand 4294967294 z) 4) 0)
                    (equal 0 (getbit 1 z))))
    :hints (("Goal" :use (getbit-1-of-bvand-2-4294967294
                          (:instance acl2::split-bv (x (bvand 2 4294967294 z)) (n 2) (m 1)))
                    :in-theory (e/d (acl2::mod-becomes-bvchop-when-power-of-2p
                                     acl2::bvchop-of-logand-becomes-bvand)
                                    (getbit-1-of-bvand-2-4294967294))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules for 16-bit memory accesses, like the ones for 32-bit accesses in
;; read-and-write.lisp (these could move there).

(defthm read32-mem-ubyte16-lendian-becomes-read
  (implies (integerp addr)
           (equal (riscv32im-le::read32-mem-ubyte16-lendian addr stat)
                  (read 2 addr stat)))
  :hints (("Goal" :expand ((:free (n addr) (read n addr stat)))
           :in-theory (e/d (riscv32im-le::read32-mem-ubyte16-lendian
                            read
                            bvcat acl2::logapp
                            unsigned-byte-p
                            read32-mem-ubyte8-becomes-read-byte
                            read-byte-of-+)
                           (acl2::bvcat-equal-rewrite
                            acl2::bvcat-equal-rewrite-alt
                            acl2::logapp-equal-rewrite
                            acl2::logapp-equal-rewrite-8
                            acl2::logapp-equal-rewrite-16
                            acl2::logapp-equal-rewrite-24)))))

(local
  (defthmd write32-mem-ubyte16-lendian-alt-def
    (implies (integerp addr)
             (equal (riscv32im-le::write32-mem-ubyte16-lendian addr val stat)
                    (write32-mem-ubyte8 (+ 1 addr)
                                        (slice 15 8 val)
                                        (write32-mem-ubyte8 addr (bvchop 8 val) stat))))
    :hints (("Goal" :in-theory (enable riscv32im-le::write32-mem-ubyte16-lendian
                                       acl2::logand-becomes-bvand
                                       acl2::bvchop-of-logtail
                                       acl2::ash-becomes-logtail
                                       acl2::bvchop-of-logtail-becomes-slice
                                       acl2::logtail-of-bvchop-becomes-slice)))))

(defthmd write32-mem-ubyte16-lendian-becomes-write
  (implies (integerp addr)
           (equal (riscv32im-le::write32-mem-ubyte16-lendian addr val stat)
                  (write 2 addr val stat)))
  :hints (("Goal" :expand ((:free (n addr val stat) (write n addr val stat)))
           :in-theory (enable write32-mem-ubyte16-lendian-alt-def
                              acl2::bvchop-of-logtail-becomes-slice
                              write
                              write32-mem-ubyte8-becomes-write-byte
                              write-byte-of-+))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Register-immediate instructions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ADDI: rd := rs1 + sext(imm)
(defthm exec32-addi-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-addi rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm)) stat))))
  :hints (("Goal" :in-theory (enable exec32-addi))))

;; SLTI: rd := (rs1 <s sext(imm)) ? 1 : 0
(defthm exec32-slti-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-slti rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvif 32 (sbvlt 32 (reg rs1 stat) (bvsx 32 12 imm)) 1 0) stat))))
  :hints (("Goal" :in-theory (enable exec32-slti sbvlt bvlt acl2::bool-to-bit))))

;; SLTIU: rd := (rs1 <u sext(imm)) ? 1 : 0
(defthm exec32-sltiu-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-sltiu rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvif 32 (bvlt 32 (reg rs1 stat) (bvsx 32 12 imm)) 1 0) stat))))
  :hints (("Goal" :in-theory (enable exec32-sltiu sbvlt bvlt acl2::bool-to-bit))))

;; ANDI: rd := rs1 & sext(imm)
(defthm exec32-andi-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-andi rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvand 32 (reg rs1 stat) (bvsx 32 12 imm)) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-andi acl2::bvchop-of-logand-becomes-bvand acl2::bvchop-of-logior-becomes-bvor acl2::bvchop-of-logxor-becomes-bvxor) (binary-logior binary-logxor)))))

;; ORI: rd := rs1 | sext(imm)
(defthm exec32-ori-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-ori rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvor 32 (reg rs1 stat) (bvsx 32 12 imm)) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-ori acl2::bvchop-of-logand-becomes-bvand acl2::bvchop-of-logior-becomes-bvor acl2::bvchop-of-logxor-becomes-bvxor) (binary-logior binary-logxor)))))

;; XORI: rd := rs1 ^ sext(imm)
(defthm exec32-xori-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-xori rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvxor 32 (reg rs1 stat) (bvsx 32 12 imm)) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-xori acl2::bvchop-of-logand-becomes-bvand acl2::bvchop-of-logior-becomes-bvor acl2::bvchop-of-logxor-becomes-bvxor) (binary-logior binary-logxor)))))

;; SLLI: rd := rs1 << imm
(defthm exec32-slli-alt-def
  (implies (unsigned-byte-p 5 imm)
           (equal (exec32-slli rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvshl 32 (reg rs1 stat) imm) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-slli) (ash)))))

;; SRLI: rd := rs1 >>u imm
(defthm exec32-srli-alt-def
  (implies (unsigned-byte-p 5 imm)
           (equal (exec32-srli rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvshr 32 (reg rs1 stat) imm) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-srli) (ash)))))

;; SRAI: rd := rs1 >>s imm
(defthm exec32-srai-alt-def
  (implies (unsigned-byte-p 5 imm)
           (equal (exec32-srai rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvashr 32 (reg rs1 stat) imm) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-srai) (ash)))))

;; LUI: rd := imm << 12
(defthm exec32-lui-alt-def
  (implies (unsigned-byte-p 20 imm)
           (equal (exec32-lui rd imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvcat 20 imm 12 0) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-lui bvshl) (ash)))))

;; AUIPC: rd := pc + (imm << 12)
(defthm exec32-auipc-alt-def
  (implies (and (unsigned-byte-p 20 imm)
                (unsigned-byte-p 32 pc))
           (equal (exec32-auipc rd imm pc stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvplus 32 pc (bvcat 20 imm 12 0)) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-auipc) (ash)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Register-register instructions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ADD: rd := rs1 + rs2
(defthm exec32-add-alt-def
  (equal (exec32-add rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvplus 32 (reg rs1 stat) (reg rs2 stat)) stat)))
  :hints (("Goal" :in-theory (enable exec32-add))))

;; SUB: rd := rs1 - rs2
(defthm exec32-sub-alt-def
  (equal (exec32-sub rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvminus 32 (reg rs1 stat) (reg rs2 stat)) stat)))
  :hints (("Goal" :in-theory (enable exec32-sub bvminus))))

;; SLT: rd := (rs1 <s rs2) ? 1 : 0
(defthm exec32-slt-alt-def
  (equal (exec32-slt rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvif 32 (sbvlt 32 (reg rs1 stat) (reg rs2 stat)) 1 0) stat)))
  :hints (("Goal" :in-theory (enable exec32-slt sbvlt bvlt acl2::bool-to-bit))))

;; SLTU: rd := (rs1 <u rs2) ? 1 : 0
(defthm exec32-sltu-alt-def
  (equal (exec32-sltu rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvif 32 (bvlt 32 (reg rs1 stat) (reg rs2 stat)) 1 0) stat)))
  :hints (("Goal" :in-theory (enable exec32-sltu sbvlt bvlt acl2::bool-to-bit))))

;; AND: rd := rs1 & rs2
(defthm exec32-and-alt-def
  (equal (exec32-and rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvand 32 (reg rs1 stat) (reg rs2 stat)) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-and acl2::bvchop-of-logand-becomes-bvand acl2::bvchop-of-logior-becomes-bvor acl2::bvchop-of-logxor-becomes-bvxor) (binary-logior binary-logxor)))))

;; OR: rd := rs1 | rs2
(defthm exec32-or-alt-def
  (equal (exec32-or rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvor 32 (reg rs1 stat) (reg rs2 stat)) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-or acl2::bvchop-of-logand-becomes-bvand acl2::bvchop-of-logior-becomes-bvor acl2::bvchop-of-logxor-becomes-bvxor) (binary-logior binary-logxor)))))

;; XOR: rd := rs1 ^ rs2
(defthm exec32-xor-alt-def
  (equal (exec32-xor rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvxor 32 (reg rs1 stat) (reg rs2 stat)) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-xor acl2::bvchop-of-logand-becomes-bvand acl2::bvchop-of-logior-becomes-bvor acl2::bvchop-of-logxor-becomes-bvxor) (binary-logior binary-logxor)))))

;; SLL: rd := rs1 << rs2[4:0]
(defthm exec32-sll-alt-def
  (equal (exec32-sll rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvshl 32 (reg rs1 stat) (bvchop 5 (reg rs2 stat))) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-sll) (ash)))))

;; SRL: rd := rs1 >>u rs2[4:0]
(defthm exec32-srl-alt-def
  (equal (exec32-srl rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvshr 32 (reg rs1 stat) (bvchop 5 (reg rs2 stat))) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-srl) (ash)))))

;; SRA: rd := rs1 >>s rs2[4:0]
(defthm exec32-sra-alt-def
  (equal (exec32-sra rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvashr 32 (reg rs1 stat) (bvchop 5 (reg rs2 stat))) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-sra) (ash)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Multiplication and division (the M extension)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; MUL: rd := low 32 bits of rs1 * rs2
(defthm exec32-mul-alt-def
  (equal (exec32-mul rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvmult 32 (reg rs1 stat) (reg rs2 stat)) stat)))
  :hints (("Goal" :in-theory (enable exec32-mul bvmult))))

;; MULH: rd := high 32 bits of the signed product
(defthm exec32-mulh-alt-def
  (equal (exec32-mulh rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (slice 63 32 (bvmult 64 (bvsx 64 32 (reg rs1 stat)) (bvsx 64 32 (reg rs2 stat)))) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-mulh) (ash)))))

;; MULHU: rd := high 32 bits of the unsigned product
(defthm exec32-mulhu-alt-def
  (equal (exec32-mulhu rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (slice 63 32 (bvmult 64 (reg rs1 stat) (reg rs2 stat))) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-mulhu) (ash)))))

;; MULHSU: rd := high 32 bits of the product of signed rs1 and unsigned rs2
(defthm exec32-mulhsu-alt-def
  (equal (exec32-mulhsu rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (slice 63 32 (bvmult 64 (bvsx 64 32 (reg rs1 stat)) (reg rs2 stat))) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-mulhsu) (ash)))))

;; DIV: rd := rs1 /s rs2 (rounding toward 0), or all ones if rs2 is 0
(defthm exec32-div-alt-def
  (equal (exec32-div rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvif 32 (equal 0 (reg rs2 stat))
                                   4294967295
                                   (sbvdiv 32 (reg rs1 stat) (reg rs2 stat)))
                          stat)))
  :hints (("Goal" :in-theory (e/d (exec32-div sbvdiv bvif) (truncate)))))

;; DIVU: rd := rs1 /u rs2, or all ones if rs2 is 0
(defthm exec32-divu-alt-def
  (equal (exec32-divu rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvif 32 (equal 0 (reg rs2 stat))
                                   4294967295
                                   (bvdiv 32 (reg rs1 stat) (reg rs2 stat)))
                          stat)))
  :hints (("Goal" :in-theory (e/d (exec32-divu bvdiv bvif acl2::truncate-becomes-floor) (truncate floor)))))

;; REM: rd := signed remainder (rs1 if rs2 is 0, which sbvrem gives too)
(defthm exec32-rem-alt-def
  (equal (exec32-rem rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (sbvrem 32 (reg rs1 stat) (reg rs2 stat)) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-rem sbvrem) (rem truncate)))))

;; REMU: rd := unsigned remainder (rs1 if rs2 is 0, which bvmod gives too)
(defthm exec32-remu-alt-def
  (equal (exec32-remu rd rs1 rs2 stat)
         (set-pc (bvplus 32 4 (pc stat))
                 (set-reg rd (bvmod 32 (reg rs1 stat) (reg rs2 stat)) stat)))
  :hints (("Goal" :in-theory (e/d (exec32-remu bvmod acl2::rem-becomes-mod) (rem mod truncate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Jumps
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; JAL: rd := pc + 4, then jump to pc + sext(imm << 1), which must be 4-byte aligned
(defthm exec32-jal-alt-def
  (implies (and (unsigned-byte-p 20 imm)
                (unsigned-byte-p 32 pc))
           (equal (exec32-jal rd imm pc stat)
                  (if (equal 0 (bvchop 2 (bvplus 32 pc (bvsx 32 21 (bvcat 20 imm 1 0)))))
                      (set-pc (bvplus 32 pc (bvsx 32 21 (bvcat 20 imm 1 0)))
                              (set-reg rd (bvplus 32 4 pc) stat))
                    (error32 stat))))
  :hints (("Goal" :in-theory (e/d (exec32-jal sbvlt bvlt acl2::mod-becomes-bvchop-when-power-of-2p) (ash)))))

;; JALR: rd := pc + 4, then jump to (rs1 + sext(imm)) with its low bit
;; cleared, which must be 4-byte aligned (so bit 1 of the sum must be 0)
(defthm exec32-jalr-alt-def
  (implies (and (unsigned-byte-p 12 imm)
                (unsigned-byte-p 32 pc))
           (equal (exec32-jalr rd rs1 imm pc stat)
                  (if (equal 0 (getbit 1 (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm))))
                      (set-pc (bvand 32 4294967294 (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm)))
                              (set-reg rd (bvplus 32 4 pc) stat))
                    (error32 stat))))
  :hints (("Goal" :in-theory (e/d (exec32-jalr acl2::bvchop-of-logand-becomes-bvand) (ash)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Branches
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In each branch, the target is pc + sext(imm << 1), which must be 4-byte
;; aligned if the branch is taken.

;; BEQ: branch if rs1 = rs2
(defthm exec32-beq-alt-def
  (implies (and (unsigned-byte-p 12 imm)
                (unsigned-byte-p 32 pc))
           (equal (exec32-beq rs1 rs2 imm pc stat)
                  (if (equal (reg rs1 stat) (reg rs2 stat))
                      (if (equal 0 (bvchop 2 (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0)))))
                          (set-pc (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0))) stat)
                        (error32 stat))
                    (set-pc (bvplus 32 4 (pc stat)) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-beq sbvlt bvlt acl2::mod-becomes-bvchop-when-power-of-2p) (ash)))))

;; BNE: branch if rs1 /= rs2
(defthm exec32-bne-alt-def
  (implies (and (unsigned-byte-p 12 imm)
                (unsigned-byte-p 32 pc))
           (equal (exec32-bne rs1 rs2 imm pc stat)
                  (if (equal (reg rs1 stat) (reg rs2 stat))
                      (set-pc (bvplus 32 4 (pc stat)) stat)
                    (if (equal 0 (bvchop 2 (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0)))))
                        (set-pc (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0))) stat)
                      (error32 stat)))))
  :hints (("Goal" :in-theory (e/d (exec32-bne sbvlt bvlt acl2::mod-becomes-bvchop-when-power-of-2p) (ash)))))

;; BLT: branch if rs1 <s rs2
(defthm exec32-blt-alt-def
  (implies (and (unsigned-byte-p 12 imm)
                (unsigned-byte-p 32 pc))
           (equal (exec32-blt rs1 rs2 imm pc stat)
                  (if (sbvlt 32 (reg rs1 stat) (reg rs2 stat))
                      (if (equal 0 (bvchop 2 (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0)))))
                          (set-pc (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0))) stat)
                        (error32 stat))
                    (set-pc (bvplus 32 4 (pc stat)) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-blt sbvlt bvlt acl2::mod-becomes-bvchop-when-power-of-2p) (ash)))))

;; BLTU: branch if rs1 <u rs2
(defthm exec32-bltu-alt-def
  (implies (and (unsigned-byte-p 12 imm)
                (unsigned-byte-p 32 pc))
           (equal (exec32-bltu rs1 rs2 imm pc stat)
                  (if (bvlt 32 (reg rs1 stat) (reg rs2 stat))
                      (if (equal 0 (bvchop 2 (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0)))))
                          (set-pc (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0))) stat)
                        (error32 stat))
                    (set-pc (bvplus 32 4 (pc stat)) stat))))
  :hints (("Goal" :in-theory (e/d (exec32-bltu sbvlt bvlt acl2::mod-becomes-bvchop-when-power-of-2p) (ash)))))

;; BGE: branch if rs1 >=s rs2, i.e., unless rs1 <s rs2
(defthm exec32-bge-alt-def
  (implies (and (unsigned-byte-p 12 imm)
                (unsigned-byte-p 32 pc))
           (equal (exec32-bge rs1 rs2 imm pc stat)
                  (if (sbvlt 32 (reg rs1 stat) (reg rs2 stat))
                      (set-pc (bvplus 32 4 (pc stat)) stat)
                    (if (equal 0 (bvchop 2 (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0)))))
                        (set-pc (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0))) stat)
                      (error32 stat)))))
  :hints (("Goal" :in-theory (e/d (exec32-bge sbvlt bvlt acl2::mod-becomes-bvchop-when-power-of-2p) (ash)))))

;; BGEU: branch if rs1 >=u rs2, i.e., unless rs1 <u rs2
(defthm exec32-bgeu-alt-def
  (implies (and (unsigned-byte-p 12 imm)
                (unsigned-byte-p 32 pc))
           (equal (exec32-bgeu rs1 rs2 imm pc stat)
                  (if (bvlt 32 (reg rs1 stat) (reg rs2 stat))
                      (set-pc (bvplus 32 4 (pc stat)) stat)
                    (if (equal 0 (bvchop 2 (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0)))))
                        (set-pc (bvplus 32 pc (bvsx 32 13 (bvcat 12 imm 1 0))) stat)
                      (error32 stat)))))
  :hints (("Goal" :in-theory (e/d (exec32-bgeu sbvlt bvlt acl2::mod-becomes-bvchop-when-power-of-2p) (ash)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Loads
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In each load and store, the address is rs1 + sext(imm).

;; LB: rd := sext(byte at address)
(defthm exec32-lb-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-lb rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvsx 32 8 (read 1 (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm)) stat)) stat))))
  :hints (("Goal" :in-theory (enable exec32-lb eff32-addr read32-mem-ubyte8-becomes-read-byte read-byte-becomes-read read-of-+ write32-mem-ubyte8-becomes-write-byte write-byte-becomes-write write-of-+ write32-mem-ubyte16-lendian-becomes-write write32-mem-ubyte32-lendian-becomes-write))))

;; LBU: rd := byte at address
(defthm exec32-lbu-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-lbu rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (read 1 (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm)) stat) stat))))
  :hints (("Goal" :in-theory (enable exec32-lbu eff32-addr read32-mem-ubyte8-becomes-read-byte read-byte-becomes-read read-of-+ write32-mem-ubyte8-becomes-write-byte write-byte-becomes-write write-of-+ write32-mem-ubyte16-lendian-becomes-write write32-mem-ubyte32-lendian-becomes-write))))

;; LH: rd := sext(halfword at address)
(defthm exec32-lh-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-lh rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (bvsx 32 16 (read 2 (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm)) stat)) stat))))
  :hints (("Goal" :in-theory (enable exec32-lh eff32-addr read32-mem-ubyte8-becomes-read-byte read-byte-becomes-read read-of-+ write32-mem-ubyte8-becomes-write-byte write-byte-becomes-write write-of-+ write32-mem-ubyte16-lendian-becomes-write write32-mem-ubyte32-lendian-becomes-write))))

;; LHU: rd := halfword at address
(defthm exec32-lhu-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-lhu rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (read 2 (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm)) stat) stat))))
  :hints (("Goal" :in-theory (enable exec32-lhu eff32-addr read32-mem-ubyte8-becomes-read-byte read-byte-becomes-read read-of-+ write32-mem-ubyte8-becomes-write-byte write-byte-becomes-write write-of-+ write32-mem-ubyte16-lendian-becomes-write write32-mem-ubyte32-lendian-becomes-write))))

;; LW: rd := word at address
(defthm exec32-lw-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-lw rd rs1 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (set-reg rd (read 4 (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm)) stat) stat))))
  :hints (("Goal" :in-theory (enable exec32-lw eff32-addr read32-mem-ubyte8-becomes-read-byte read-byte-becomes-read read-of-+ write32-mem-ubyte8-becomes-write-byte write-byte-becomes-write write-of-+ write32-mem-ubyte16-lendian-becomes-write write32-mem-ubyte32-lendian-becomes-write))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SB: store the low byte of rs2 at the address
(defthm exec32-sb-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-sb rs1 rs2 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (write 1 (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm)) (reg rs2 stat) stat))))
  :hints (("Goal" :in-theory (enable exec32-sb eff32-addr read32-mem-ubyte8-becomes-read-byte read-byte-becomes-read read-of-+ write32-mem-ubyte8-becomes-write-byte write-byte-becomes-write write-of-+ write32-mem-ubyte16-lendian-becomes-write write32-mem-ubyte32-lendian-becomes-write))))

;; SH: store the low halfword of rs2 at the address
(defthm exec32-sh-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-sh rs1 rs2 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (write 2 (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm)) (reg rs2 stat) stat))))
  :hints (("Goal" :in-theory (enable exec32-sh eff32-addr read32-mem-ubyte8-becomes-read-byte read-byte-becomes-read read-of-+ write32-mem-ubyte8-becomes-write-byte write-byte-becomes-write write-of-+ write32-mem-ubyte16-lendian-becomes-write write32-mem-ubyte32-lendian-becomes-write))))

;; SW: store rs2 at the address
(defthm exec32-sw-alt-def
  (implies (unsigned-byte-p 12 imm)
           (equal (exec32-sw rs1 rs2 imm stat)
                  (set-pc (bvplus 32 4 (pc stat))
                          (write 4 (bvplus 32 (reg rs1 stat) (bvsx 32 12 imm)) (reg rs2 stat) stat))))
  :hints (("Goal" :in-theory (enable exec32-sw eff32-addr read32-mem-ubyte8-becomes-read-byte read-byte-becomes-read read-of-+ write32-mem-ubyte8-becomes-write-byte write-byte-becomes-write write-of-+ write32-mem-ubyte16-lendian-becomes-write write32-mem-ubyte32-lendian-becomes-write))))
