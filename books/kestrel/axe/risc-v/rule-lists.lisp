; Rule lists for use by the RISC-V Axe tools
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

(include-book "portcullis")
(include-book "../rule-lists")

(defun symbolic-execution-rules ()
  (declare (xargs :guard t))
  '(run-until-return
    run-subroutine
    sp-is-abovep
    run-until-sp-is-above-opener
    run-until-sp-is-above-base
    run-until-sp-is-above-of-if-arg2
    step32-opener))

(defun lifter-rules ()
  (declare (xargs :guard t))
  (append
   (acl2::core-rules-bv)
   (acl2::unsigned-byte-p-forced-rules)
   (acl2::type-rules) ; rename
   (acl2::bvchop-of-bv-rules)
   (acl2::convert-to-bv-rules) ; todo: may just need the trim-elim rules
   '(error32p-of-set-reg
     error32p-of-write
     error32p-of-set-pc

     read32-mem-ubyte32-lendian-becomes-read
     read32-mem-ubyte8-becomes-read-byte
     read-byte-becomes-read
     read-of-bvchop-32 ; todo: say which arg
     write-of-bvchop-32-arg2
     write-of-bvchop-arg3
     write-of-logext-arg3
     write32-mem-ubyte8-becomes-write-byte
     write32-mem-ubyte32-lendian-becomes-write
     read-of-+
     integerp-of-read
     natp-of-read
     unsigned-byte-p-of-read
     write-of-+
     read-of-write-same
     read-of-write-1-within
     read-1-of-write-within
     read-when-equal-of-read-bytes-and-subregion32p
     read-of-write-when-disjoint-regions32p
     read-of-write-when-disjoint-regions32p-gen
     read-of-write-when-disjoint-regions32p-gen-alt
     bvchop-of-read
     disjoint-regions32p-when-disjoint-regions32p-and-subregion32p-and-subregion32p
     disjoint-regions32p-when-disjoint-regions32p-and-subregion32p-and-subregion32p-alt

     subregion32p-of-1-arg1     ;; trying
     disjoint-regions32p-of-1-and-1 ; trying
     acl2::equal-of-bvplus-constant-and-constant-alt
     acl2::equal-of-bvplus-constant-and-constant
     not-equal-of-read-and-constant
     not-equal-of-constant-and-read
     acl2::equal-of-bvplus-and-bvplus-reduce-constants
     disjoint-regions32p-byte-special
     acl2::bv-array-read-chunk-little-of-1
     acl2::bv-array-read-of-bvplus-of-constant-no-wrap
     <-of-read ; for an array pattern rule
     bv-array-read-shorten-8
     acl2::bv-array-read-of-bvplus-of-constant-no-wrap
     acl2::not-equal-of-constant-and-bv-term-axe
     acl2::not-equal-of-constant-and-bv-term-alt-axe
     acl2::equal-of-bvchop-and-bvplus-of-same
     acl2::equal-of-bvchop-and-bvplus-of-same-alt
     acl2::logext-identity-when-usb-smaller-axe
     acl2::bvxor-of-logext-arg3
     acl2::bvxor-of-logext-arg2

     in-region32p-cancel-constants-1-1+
    in-region32p-cancel-constants-1+-1
    in-region32p-cancel-constants-1+-1+
    in-region32p-cancel-1-1+
    in-region32p-cancel-1+-1
    in-region32p-cancel-1+-1+
    in-region32p-cancel-1-2
    in-region32p-cancel-2-1
    in-region32p-cancel-1+-2
    in-region32p-cancel-2-1+
    in-region32p-cancel-2+-1
    in-region32p-cancel-1-3
    in-region32p-cancel-3-1
    in-region32p-cancel-2-2
    in-region32p-when-non-negative-and-negative-range
    ;in-region32p-of-0-arg3 ; introduces bvlt
    in-region32p-of-bvchop-arg1
    in-region32p-of-bvchop-arg3
    in-region32p-of-bvsx-arg1
    in-region32p-of-bvsx-arg3
    in-region32p-same


     in-region32p-byte-special ; have the memory machinery generate this?

     write-byte-becomes-write
     read-normalize-constant-arg2
     write-normalize-constant-arg2
     write-normalize-constant-arg3

     disjoint-regions32p-cancel-1-1+
     disjoint-regions32p-cancel-1+-1
     disjoint-regions32p-cancel-1+-1+
     disjoint-regions32p-cancel-1-2
     disjoint-regions32p-cancel-2-1
     disjoint-regions32p-cancel-1+-2
     disjoint-regions32p-cancel-2-1+
     disjoint-regions32p-cancel-2-2
     disjoint-regions32p-cancel-2+-2
     disjoint-regions32p-of-bvplus-of-constant-and-constant

     subregion32p-cancel-1-1
     subregion32p-cancel-1+-1
     subregion32p-cancel-1-1+
     subregion32p-cancel-2-1
     subregion32p-cancel-2-1+
     subregion32p-cancel-1-2
     subregion32p-cancel-1+-2
     subregion32p-cancel-2-2
     subregion32p-cancel-constants-1+-1
     subregion32p-cancel-constants-1+-1+

     set-pc-convert-arg1-to-bv-axe
     set-reg-convert-arg2-to-bv-axe

     acl2::bvplus-convert-arg2-to-bv-axe
     acl2::bvplus-convert-arg3-to-bv-axe
     acl2::bvplus-of-logext-arg2
     acl2::bvplus-of-logext-arg3
     acl2::bvchop-of-logext

     acl2::bvplus-associative

     ;; add some of these to core-rules?:
     acl2::boolif-of-nil-and-t
     acl2::not-of-not

     acl2::bvplus-commute-constant ; hope these are ok -- want it for addresses but nore for giant nests of crypto ops.  so limit the size of the nests?
     acl2::bvplus-commute-constant2

     acl2::equal-of-bvif-safe ; add to core-rules-bv
     acl2::equal-of-bvif-safe-alt
     acl2::equal-of-bvif-constants
     acl2::equal-of-bvif-constants2
     acl2::bvchop-of-if-becomes-bvif
     acl2::<-becomes-bvlt-axe-bind-free-arg1 ; or use stronger rules?
     acl2::<-becomes-bvlt-axe-bind-free-arg2

     read32-pc-becomes-pc
     write32-pc-becomes-set-pc
     read32-xreg-unsigned-becomes-reg
     write32-xreg-becomes-set-reg

     read32-xreg-signed ; open to the unsigned one

     integerp-of-reg
     reg-of-set-reg
     set-reg-of-set-reg-same
     set-reg-of-set-reg-diff
     reg-of-write
     ;; reg-of-write-byte
     reg-of-set-pc
     reg-of-if

     set-reg-of-bvchop
     set-reg-does-nothing

     acl2::equal-same ; !!

     set-reg-of-0 ; setting register 0 has no effect!

     pc-of-set-pc
     set-pc-of-set-pc
     pc-of-set-reg
     pc-of-write
     write-of-set-reg

     read-of-set-pc
     read-of-set-reg

     set-reg-of-set-pc
     write-of-set-pc

     stat32ip-of-set-reg
     stat32ip-of-write

     x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
     ;; register aliases:
     ;; zero
     ra sp gp tp t0 t1 t2 s0 fp s1 a0 a1 a2 a3 a4 a5

     acl2::subregion32p-constant-opener
     acl2::in-region32p-constant-opener
     acl2::disjoint-regions32p-constant-opener

     acl2::bv-array-read-chunk-little-constant-opener
     riscv::feat-rv32im-le ; todo: use constant-openers more for these?
     riscv::feat-endian-little
     riscv::feat-base-rv32i
     riscv::feat
     riscv::feat-endian-fix$inline
     riscv::feat-endian-kind$inline
     riscv::feat-base-fix$inline
     riscv::feat-base-kind$inline
     riscv::feat-mp
     riscv::feat-embedp
     riscv::feat->base$inline

     riscv::branch-funct-fix$inline
     riscv::branch-funct-kind$inline

     riscv::op-imms-funct-fix$inline
     riscv::op-imms-funct-kind$inline

     riscv::decodex-constant-opener
     acl2::ubyte32-fix-constant-opener
     acl2::ubyte32p-constant-opener
     riscv::get-fields-itype-constant-opener
     riscv::get-fields-jtype-constant-opener
     riscv::get-rd-constant-opener
     riscv::get-rs1-constant-opener
     riscv::get-rs2-constant-opener
     riscv::get-funct3-constant-opener
     riscv::get-funct7-constant-opener

     riscv::get-opcode-constant-opener
     riscv::get-imm-btype-constant-opener
     riscv::get-imm-itype-constant-opener
     riscv::get-imm-jtype-constant-opener
     riscv::get-imm-stype-constant-opener
     riscv::get-imm-utype-constant-opener
     bitops::part-select-low-high$inline-constant-opener
     bitops::part-select-width-low$inline-constant-opener
     riscv::feat-64p-constant-opener
     riscv::get-fields-btype-constant-opener
     riscv::get-fields-rtype-constant-opener
     riscv::get-fields-utype-constant-opener
     riscv::get-fields-stype-constant-opener
     riscv::feat->m$inline-constant-opener

     riscv::instr-op-imm-constant-opener

     acl2::logtail$inline-constant-opener
     acl2::expt2$inline-constant-opener
;     acl2::binary-logand-constant-opener ; todo: led to stack overflow -- need to make a safe opener?  and eval zip and evenp
     acl2::ifloor$inline-constant-opener
     acl2::logapp-constant-opener
     common-lisp::ash-constant-opener ; todo: use acl2 package
     acl2::ash-becomes-logtail ; do better?
     acl2::bvchop-of-ash
     acl2::logtail-of-logext
     ;acl2::logtail-of-bvcat
     acl2::logtail-becomes-slice-bind-free-axe
     acl2::bvcat-of-logext-arg2
     acl2::bvcat-of-logext-arg4

     acl2::loghead-becomes-bvchop

     ubyte5-fix
     acl2::ubyte12-fix
     acl2::ubyte20-fix

     ubyte5p
     acl2::ubyte12p
     acl2::ubyte20p

     riscv::op-imm-funct-fix$inline
     riscv::instr-kind$inline

     riscv::instr-op-constant-opener

     riscv::store-funct-fix$inline
     riscv::store-funct-kind$inline

     riscv::load-funct-fix$inline
     riscv::load-funct-kind$inline

     riscv::op-funct-fix$inline
     riscv::op-funct-kind$inline

     riscv::instr-op-imm->imm$inline
     riscv::instr-op-imm->rs1$inline
     riscv::instr-op-imm->funct$inline
     riscv::instr-op-imm->rd$inline

     riscv::instr-op-imms32->funct$inline
     riscv::instr-op-imms32->rd$inline
     riscv::instr-op-imms32->rs1$inline
     riscv::instr-op-imms32->imm$inline

     riscv::instr-load->funct$inline
     riscv::instr-load->rs1$inline
     riscv::instr-load->rd$inline
     riscv::instr-load->imm$inline

     riscv::instr-store->funct$inline
     riscv::instr-store->rs1$inline
     riscv::instr-store->rs2$inline
     riscv::instr-store->imm$inline

     riscv::instr-op->funct$inline
     riscv::instr-op->rd$inline
     riscv::instr-op->rs1$inline
     riscv::instr-op->rs2$inline

     riscv::instr-jalr->rd$inline
     riscv::instr-jalr->rs1$inline
     riscv::instr-jalr->imm$inline

     riscv::instr-jal->imm$inline
     riscv::instr-jal->rd$inline

     riscv::instr-branch->funct$inline
     riscv::instr-branch->rs1$inline
     riscv::instr-branch->rs2$inline
     riscv::instr-branch->imm$inline

     riscv::instr-auipc->rd$inline
     riscv::instr-auipc->imm$inline

     riscv::instr-lui->rd$inline
     riscv::instr-lui->imm$inline

     exec32-instr-base
     exec32-store
     exec32-load
     exec32-lw
     riscv::exec32-lb
     riscv::exec32-lbu
     exec32-sw
     exec32-op
     exec32-add
     exec32-jalr
     riscv::exec32-jal
     riscv::exec32-sb
     riscv::exec32-branch
     riscv::exec32-bgeu
     riscv::exec32-blt
     riscv::exec32-bne
     riscv::exec32-beq
     riscv::exec32-bge
     riscv::exec32-auipc
     riscv::exec32-lui
     riscv::exec32-op-imms
     riscv::exec32-srli
     riscv::exec32-slli
     riscv::exec32-andi
     riscv::exec32-xor
     riscv::exec32-srai
     riscv::exec32-sub
     riscv::exec32-sltiu
     riscv::exec32-sltu
     riscv::exec32-or


     /= ;; !!
     = ; todo: try base-rules


     ;; these should be 0-ary and thus safe to open:
     riscv::op-imm-funct-addi
     riscv::op-imm-funct-kind$inline-constant-opener
     riscv::store-funct-sw
     riscv::store-funct-sb
     riscv::load-funct-lw
     riscv::load-funct-lb
     riscv::load-funct-lbu
     riscv::instr-store-constant-opener
     riscv::instr-load-constant-opener

     riscv::op-funct-add
     riscv::op-funct-xor
     riscv::op-funct-sub
     riscv::op-funct-or
     riscv::op-funct-sltu

     riscv::instr-op-imms32
     riscv::op-imms-funct-srli
     riscv::op-imms-funct-slli
     riscv::op-imms-funct-srai
     riscv::op-imm-funct-andi
     riscv::op-imm-funct-sltiu
     riscv::branch-funct-bne
     riscv::branch-funct-beq
     riscv::branch-funct-blt
     riscv::branch-funct-bge
     riscv::branch-funct-bltu

     riscv::instr-jalr
     riscv::instr-jal
     riscv::instr-branch
     riscv::instr-auipc
     riscv::instr-lui

     riscv::branch-funct-bgeu

     riscv::exec32-op-imm-base

     exec32-addi

     inc32-pc ; increments by 4

     acl2::bvchop-of-+-becomes-bvplus
     acl2::bvminus-of-bvplus-and-bvplus-same
     acl2::bvminus-of-bvplus-same
     acl2::bvminus-of-bvplus-same-arg2
     acl2::bvminus-of-bvplus-of-constant-and-bvplus-of-constant
     acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version

     eff32-addr

     acl2::integerp-of-+-when-integerp-1
     acl2::integerp-of-+-when-integerp-2
     acl2::fix-when-integerp
     acl2::integerp-of-bvplus
     acl2::integerp-of-logext

     riscv::stat32i-fix-when-stat32ip

     acl2::ifix-when-integerp
     acl2::mod-becomes-bvchop-when-power-of-2p
     )))

(defun debug-rules ()
  (declare (xargs :guard t))
  '(step32-opener
    run-until-sp-is-above-opener
    read-when-equal-of-read-bytes-and-subregion32p))
