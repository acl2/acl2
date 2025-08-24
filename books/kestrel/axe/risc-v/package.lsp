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

(defpkg "R"
  (append '(acl2::loghead
            acl2::logapp
            acl2::logtail
            acl2::logext

            acl2::bvplus
            acl2::bvminus
            acl2::bvuminus
            acl2::bvchop
            acl2::slice
            acl2::bvcat
            acl2::bvcat2
            acl2::bvlt

            acl2::repeat

            acl2::b*
            acl2::patbind-when

            acl2::unsigned-byte-listp
            acl2::defopeners

            acl2::bv-array-read
            acl2::bv-array-read-chunk-little

            acl2::ubyte32-list-fix

            x::disjoint-regionsp ; todo: move these
            x::disjoint-regions32p
            x::memory-regionp
            x::memory-regionsp

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
          *acl2-exports*))
