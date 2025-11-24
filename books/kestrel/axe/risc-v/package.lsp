; The "R" package for RISC-V Axe proofs
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; to support LDing this book, since in this dir, ACL2 starts in the "R" package

(include-book "kestrel/axe/imported-symbols" :dir :system)
(include-book "kestrel/risc-v/portcullis" :dir :system)
(include-book "kestrel/risc-v/specialized/rv32im-le/portcullis" :dir :system)

;; Users of the RISC-V variant of Axe can use this "R" package for their books
;; that use Axe to lift/verify RISC-V code.

;; This is similar to the "X" package used by the x86 variant of Axe.

;; In general, we import function names, but not theorem names, from other
;; packages into this package.

(defconst *risc-v-symbols*
  '(riscv32im-le::memory-fix
    riscv32im-le::memoryp

    riscv::ubyte5p
    riscv::ubyte5-fix
    riscv::ubyte8p
    riscv::ubyte8-fix
    riscv::ubyte32p
    riscv::ubyte32-fix

    riscv32im-le::step32
    riscv32im-le::step32n
    riscv32im-le::step32n-base-1
    riscv32im-le::step32n-base-2
    riscv32im-le::step32n-unroll

    riscv32im-le::stat32p
    riscv32im-le::stat32-fix
    riscv32im-le::stat32->xregs

    riscv32im-le::xregs-fix
    riscv32im-le::xregsp

    riscv32im-le::read32-mem-ubyte8
    riscv32im-le::write32-mem-ubyte8
    riscv32im-le::read32-mem-ubyte32-lendian
    riscv32im-le::write32-mem-ubyte32-lendian

    riscv32im-le::read32-xreg-unsigned
    riscv32im-le::read32-xreg-signed
    riscv32im-le::write32-xreg
    riscv32im-le::error32
    riscv32im-le::error32p
    riscv32im-le::read32-pc
    riscv32im-le::write32-pc

    riscv32im-le::exec32-instr
    riscv32im-le::exec32-instr-base ; bad name

    riscv32im-le::exec32-add
    riscv32im-le::exec32-addi
    riscv32im-le::exec32-and
    riscv32im-le::exec32-andi
    riscv32im-le::exec32-auipc
    riscv32im-le::exec32-beq
    riscv32im-le::exec32-bge
    riscv32im-le::exec32-bgeu
    riscv32im-le::exec32-blt
    riscv32im-le::exec32-bltu
    riscv32im-le::exec32-bne
    riscv32im-le::exec32-branch
    riscv32im-le::exec32-div
    riscv32im-le::exec32-divu
    riscv32im-le::exec32-instr
    riscv32im-le::exec32-jal
    riscv32im-le::exec32-jalr
    riscv32im-le::exec32-lb
    riscv32im-le::exec32-lbu
    riscv32im-le::exec32-lh
    riscv32im-le::exec32-lhu
    riscv32im-le::exec32-load
    riscv32im-le::exec32-lui
    riscv32im-le::exec32-lw
    riscv32im-le::exec32-mul
    riscv32im-le::exec32-mulh
    riscv32im-le::exec32-mulhsu
    riscv32im-le::exec32-mulhu
    riscv32im-le::exec32-op
    riscv32im-le::exec32-op-imm
    riscv32im-le::exec32-op-imms
    riscv32im-le::exec32-or
    riscv32im-le::exec32-ori
    riscv32im-le::exec32-rem
    riscv32im-le::exec32-remu
    riscv32im-le::exec32-sb
    riscv32im-le::exec32-sh
    riscv32im-le::exec32-sll
    riscv32im-le::exec32-slli
    riscv32im-le::exec32-slt
    riscv32im-le::exec32-slti
    riscv32im-le::exec32-sltiu
    riscv32im-le::exec32-sltu
    riscv32im-le::exec32-sra
    riscv32im-le::exec32-srai
    riscv32im-le::exec32-srl
    riscv32im-le::exec32-srli
    riscv32im-le::exec32-store
    riscv32im-le::exec32-sub
    riscv32im-le::exec32-sw
    riscv32im-le::exec32-xor
    riscv32im-le::exec32-xori

    riscv32im-le::inc32-pc

    riscv32im-le::eff32-addr
    riscv32im-le::equal-of-stat32

    riscv32im-le::change-stat32
    riscv32im-le::stat32->memory

    ;; var names:
    riscv32im-le::stat
    riscv32im-le::instr
    riscv32im-le::instr.kind
    riscv32im-le::instr.funct
    riscv32im-le::instr.rd
    riscv32im-le::instr.rs1
    riscv32im-le::instr.rs2
    riscv32im-le::instr.imm
    ))

(defconst *risc-v-symbols-in-acl2-package*
  '(ubyte32-list-fix))

(defpkg "R"
  (append '(packbv-little

            bv-list-read-chunk-little

            repeat

            smaller-termp

            unsigned-byte-listp

            defpun

            in-region32p ; todo: move to mem package?
            subregion32p
            disjoint-regions32p
            memory-regionp
            memory-regionsp
            memory-region-addresses-and-lens
            )
          *arithmetic-symbols*
          *risc-v-symbols*
          *risc-v-symbols-in-acl2-package*
          *logops-symbols*
          *axe-term-symbols*
          *axe-tools*
          *axe-implementation-symbols*
          *axe-rule-symbols*
          (set-difference-eq *acl2-exports*
                             '(pc ; we need this name for accessing the program counter
                               ))))
