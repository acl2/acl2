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

            bv-array-read
            bv-array-read-chunk-little
            bv-array-write

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

            riscv::exec32-op-imm
            riscv::exec32-op
            riscv::exec32-add
            riscv::exec32-addi
            riscv::exec32-store
            riscv::exec32-sw
            riscv::exec32-load
            riscv::exec32-lw
            riscv::exec32-jalr
            riscv::inc32-pc

            riscv::exec32-instr-base ; bad name

            riscv::eff32-addr
            riscv::equal-of-stat32i

            riscv::change-stat32i
            riscv::stat32i->memory

            ;; var names:
            riscv::stat
            )
          *axe-implementation-functions*
          (set-difference-eq *acl2-exports*
                             '(pc ; we need this name for accessing the program counter
                               ))))
