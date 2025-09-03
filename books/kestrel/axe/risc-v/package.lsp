; Package for RISC-V proofs
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "kestrel/risc-v/portcullis" :dir :system)
(include-book "kestrel/x86/portcullis" :dir :system)

;move this list?
(defconst *axe-implementation-functions*
  '(erp-nil
    erp-t
    myquotep
    step-incrementp
    print-levelp
    count-hits-argp
    normalize-xors-optionp
    rule-alistp
    pseudo-dagp
    this-step-increment
    add-limit-for-rules
    limit-for-rule
    simplify-dag-basic
    known-booleans
    real-time-since
    maybe-prune-dag-approximately
    maybe-prune-dag-precisely

    dag-fns ; todo: collect into *axe-tools* list
    dag-vars
    dag-size
    dag-info
    dag-to-term
    dag-node-to-term
    add-known-boolean

    remove-assumptions-about
    *non-stp-assumption-functions*
    equivalent-dagsp2
    print-to-hundredths
    print-dag-nicely
    print-dag-nicely-with-base
    print-level-at-least-tp
    nat-to-string
    dag-or-quotep-size
    dag-or-quotep-fns
    dag-or-quotep-vars
    dag-or-quotep-to-term
    defmacrodoc

    dargs
    darg1
    darg2
    darg3
    darg4
    pseudo-dag-arrayp
    syntactic-call-of

    dag-array ; for axe-syntaxp rules

    ;; todo: organize

    def-constant-opener
    fargs
    ffn-symb
    farg1
    farg2
    farg3

    lookup-equal
    lookup-eq

    make-rule-alist

    translate-term

    parse-elf-file-bytes

    _ ;; used to print non-pure patterns

    symbolic-array
    ;; symbolic-list
    symbolic-byte-list
    byte-types-for-vars
    make-var-names
    ))

(defpkg "R"
  (append '(loghead
            logapp
            logtail
            logtail$inline
            logext
            binary-logand

            expt2$inline
            ifloor$inline

            boolif
            booland
            boolor
            bool-fix
            bool-fix$inline

            bvplus
            bvminus
            bvuminus
            bvchop
            slice
            getbit
            bvcat
            bvcat2
            bvlt
            bvle
            bvgt
            bvge
            bvand
            bvor
            bvxor
            bvnot
            bvif

            trim

            putbyte

            power-of-2p
            lg

            axe-syntaxp
            axe-bind-free
            term-should-be-converted-to-bvp

            packbv-little

            list-to-bv-array
            list-to-bv-array-aux
            bv-arrayp
            bv-array-read
            bv-array-read-chunk-little
            bv-array-write
            array-of-zeros

            bv-list-read-chunk-little

            repeat

            smaller-termp

            b*
            patbind-when

            unsigned-byte-listp
            defopeners


            ubyte32-list-fix

            defpun

            in-region32p ; todo: move to mem package?
            subregion32p
            disjoint-regions32p
            memory-regionp
            memory-regionsp
            memory-region-addresses-and-lens

            riscv::memory32i-fix
            riscv::memory32ip

            riscv::ubyte5p
            riscv::ubyte5-fix
            riscv::ubyte8p
            riscv::ubyte8-fix
            riscv::ubyte32p
            riscv::ubyte32-fix

            riscv::step32
            riscv::step32n
            riscv::step32n-base-1
            riscv::step32n-base-2
            riscv::step32n-unroll

            riscv::stat32ip
            riscv::stat32i-fix
            riscv::stat32i->xregs

            riscv::xregs32i-fix
            riscv::xregs32ip

            riscv::read32-mem-ubyte8
            riscv::write32-mem-ubyte8
            riscv::read32-mem-ubyte32-lendian
            riscv::write32-mem-ubyte32-lendian

            riscv::read32-xreg-unsigned
            riscv::read32-xreg-signed
            riscv::write32-xreg
            riscv::error32
            riscv::error32p
            riscv::read32-pc
            riscv::write32-pc

            riscv::exec32-instr
            riscv::exec32-instr-base ; bad name

            riscv::exec32-add
            riscv::exec32-addi
            riscv::exec32-and
            riscv::exec32-andi
            riscv::exec32-auipc
            riscv::exec32-beq
            riscv::exec32-bge
            riscv::exec32-bgeu
            riscv::exec32-blt
            riscv::exec32-bltu
            riscv::exec32-bne
            riscv::exec32-branch
            riscv::exec32-div
            riscv::exec32-divu
            riscv::exec32-instr
            riscv::exec32-jal
            riscv::exec32-jalr
            riscv::exec32-lb
            riscv::exec32-lbu
            riscv::exec32-lh
            riscv::exec32-lhu
            riscv::exec32-load
            riscv::exec32-lui
            riscv::exec32-lw
            riscv::exec32-mul
            riscv::exec32-mulh
            riscv::exec32-mulhsu
            riscv::exec32-mulhu
            riscv::exec32-op
            riscv::exec32-op-imm
            riscv::exec32-op-imms
            riscv::exec32-or
            riscv::exec32-ori
            riscv::exec32-rem
            riscv::exec32-remu
            riscv::exec32-sb
            riscv::exec32-sh
            riscv::exec32-sll
            riscv::exec32-slli
            riscv::exec32-slt
            riscv::exec32-slti
            riscv::exec32-sltiu
            riscv::exec32-sltu
            riscv::exec32-sra
            riscv::exec32-srai
            riscv::exec32-srl
            riscv::exec32-srli
            riscv::exec32-store
            riscv::exec32-sub
            riscv::exec32-sw
            riscv::exec32-xor
            riscv::exec32-xori

            riscv::inc32-pc

            riscv::eff32-addr
            riscv::equal-of-stat32i

            riscv::change-stat32i
            riscv::stat32i->memory

            ;; var names:
            riscv::stat
            riscv::instr
            riscv::instr.kind
            riscv::instr.funct
            riscv::instr.rd
            riscv::instr.rs1
            riscv::instr.rs2
            riscv::instr.imm
            )
          *axe-implementation-functions*
          (set-difference-eq *acl2-exports*
                             '(pc ; we need this name for accessing the program counter
                               ))))
