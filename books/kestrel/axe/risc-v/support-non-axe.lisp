; Top-level support book for non-Axe code proofs
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; This book supports lifts that use the ACL2 rewriter.  Most lifts will
;; instead use the Axe Rewriter and should instead include unroll.lisp.

(include-book "kestrel/executable-parsers/parse-executable" :dir :system)
(include-book "read-over-write-rules")
(include-book "write-over-write-rules")
(include-book "assumptions")
(include-book "run-until-return")
(include-book "alt-defs")

;; Set up the theory for code proofs:
(in-theory (e/d (step32n-base-1
                 step32n-base-2
                 step32n-unroll
                 step32-opener
                 ;; step32 ; causes loops

                 ;; instructions:

                 exec32-addi-alt-def
                 exec32-slti-alt-def
                 exec32-sltiu-alt-def
                 exec32-andi-alt-def
                 exec32-ori-alt-def
                 exec32-xori-alt-def
                 exec32-slli-alt-def
                 exec32-srli-alt-def
                 exec32-srai-alt-def
                 exec32-lui-alt-def
                 exec32-auipc-alt-def
                 exec32-add-alt-def
                 exec32-sub-alt-def
                 exec32-slt-alt-def
                 exec32-sltu-alt-def
                 exec32-and-alt-def
                 exec32-or-alt-def
                 exec32-xor-alt-def
                 exec32-sll-alt-def
                 exec32-srl-alt-def
                 exec32-sra-alt-def
                 exec32-mul-alt-def
                 exec32-mulh-alt-def
                 exec32-mulhu-alt-def
                 exec32-mulhsu-alt-def
                 exec32-div-alt-def
                 exec32-divu-alt-def
                 exec32-rem-alt-def
                 exec32-remu-alt-def
                 exec32-jal-alt-def
                 exec32-jalr-alt-def
                 exec32-beq-alt-def
                 exec32-bne-alt-def
                 exec32-blt-alt-def
                 exec32-bltu-alt-def
                 exec32-bge-alt-def
                 exec32-bgeu-alt-def
                 exec32-lb-alt-def
                 exec32-lbu-alt-def
                 exec32-lh-alt-def
                 exec32-lhu-alt-def
                 exec32-lw-alt-def
                 exec32-sb-alt-def
                 exec32-sh-alt-def
                 exec32-sw-alt-def

                 exec32-op-imm ; dispatch function
                 exec32-op ; dispatch function
                 exec32-store ; dispatch function
                 exec32-load ; dispatch function

                 inc32-pc ; todo: alt-def
                 exec32-instr-base ; todo: improve name in defopeners call
                 eff32-addr ; for now
                 write32-mem-ubyte8-of-+-arg1
                 write32-mem-ubyte32-lendian-of-+-arg1
                 acl2::bvplus-of-+-arg3
                 in-region32p-of-+-arg3
                 write32-xreg-of-+-arg2
                 read32-mem-ubyte32-lendian-of-+-arg1

                 disjoint-regions32p-of-+-arg4
                 write32-xreg-when-equal-of-read32-xreg-unsigned
                 (:e riscv32im-le::feat-rv32im-le) ; needed for code proofs

                 read32-xreg-signed ; exposes read32-xreg-unsigned
                 read32-xreg-unsigned-becomes-reg ; introduces reg
                 write32-xreg-becomes-set-reg ; introduces set-reg

                 read32-mem-ubyte8-becomes-read-byte
                 write32-mem-ubyte8-becomes-write-byte
                 write32-mem-ubyte32-lendian-becomes-write
                 ;; read32-xreg-unsigned-becomes-x1
                 ;; read32-xreg-unsigned-becomes-x2
                 ;; read32-xreg-unsigned-becomes-x8
                 ;; read32-xreg-unsigned-becomes-x10
                 ;; read32-xreg-unsigned-becomes-x10
                 ;; write32-xreg-becomes-set-x1
                 ;; write32-xreg-becomes-set-x2
                 ;; write32-xreg-becomes-set-x8
                 ;; write32-xreg-becomes-set-x10
                 ;; write32-xreg-becomes-set-x11
                 ;; write32-xreg-becomes-set-x14
                 read-of-+ ; introduces bvplus
                 write-of-+ ; introduces bvplus
                 acl2::bvchop-of-+-becomes-bvplus

                 acl2::mod-becomes-bvchop-when-power-of-2p

                 read32-pc-becomes-pc
                 write32-pc-becomes-set-pc

                 run-subroutine
                 run-until-return
                 run-until-return-aux-opener
                 run-until-return-aux-base
                 ;; sp-is-abovep
                 ;; run-until-sp-is-above-opener
                 ;; run-until-sp-is-above-base
                 ;; run-until-sp-is-above-of-if-arg2
                 update-call-stack-height
                 riscv::instr-option-some->val$inline
                 riscv::instr-fix$inline

                 ;; Expand syntactic sugar for registers:
                 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
                 ;; zero
                 ra sp gp tp t0 t1 t2 s0 fp s1 a0 a1 a2 a3 a4 a5
                 )
                (equal-of-stat32
                 logext)))
