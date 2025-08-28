; Top-level support book for non-Axe code proofs
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; This book supports lifts that use the ACL2 rewriter.  Most lifts will
;; instead use the Axe Rewriter and should instead include unroll.lisp.

(include-book "read-over-write-rules")
(include-book "write-over-write-rules")
(include-book "assumptions")
(include-book "run-until-return")

;; Set up the theory for code proofs:
(in-theory (e/d (step32n-base-1
                 step32n-base-2
                 step32n-unroll
                 step32-opener
                 ;; step32 ; causes loops
                 exec32-op-imm
                 exec32-op
                 exec32-add
                 exec32-addi
                 exec32-store
                 exec32-sw
                 exec32-load
                 exec32-lw
                 exec32-jalr
                 inc32-pc
                 exec32-instr-base ; todo: improve name in defopeners call
                 eff32-addr ; for now
                 write32-mem-ubyte8-of-+-arg1
                 write32-mem-ubyte32-lendian-of-+-arg1
                 acl2::bvplus-of-+-arg3
                 in-region32p-of-+-arg3
                 write32-xreg-of-+-arg2
                 read32-mem-ubyte32-lendian-of-+-arg1
                 read32-xreg-signed
                 disjoint-regions32p-of-+-arg4
                 write32-xreg-when-equal-of-read32-xreg-unsigned
                 (:e riscv::feat-rv32im-le) ; needed for code proofs
                 )
                (equal-of-stat32i)))

;; Introduce new normal forms:
(in-theory (enable read32-xreg-unsigned-becomes-reg
                   write32-xreg-becomes-set-reg

                   x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
                   ;; register aliases:
                   ;; zero
                   ra sp gp tp t0 t1 t2 s0 fp s1 a0 a1 a2 a3 a4 a5
                   ))

;; Introduce new normal forms:
(in-theory (enable read32-mem-ubyte8-becomes-read-byte
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
                   read-of-+
                   write-of-+
                   acl2::bvchop-of-+-becomes-bvplus))

(in-theory (enable acl2::mod-becomes-bvchop-when-power-of-2p))

(in-theory (disable logext))

(in-theory (enable run-subroutine
                   run-until-return
                   run-until-return-aux-opener
                   run-until-return-aux-base
                   run-subroutine
                   ;; sp-is-abovep
                   ;; run-until-sp-is-above-opener
                   ;; run-until-sp-is-above-base
                   ;; run-until-sp-is-above-of-if-arg2
                   update-call-stack-height
                   riscv::instr-option-some->val$inline
                   riscv::instr-fix$inline
                   ))

(in-theory (enable read32-pc-becomes-pc
                   write32-pc-becomes-set-pc))
