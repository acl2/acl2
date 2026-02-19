; Rule lists for use by the ARM Axe tools
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "A")

(include-book "portcullis")
(include-book "../rule-lists")
(include-book "kestrel/arm/encodings" :dir :system)

(defun symbolic-execution-rules32-common ()
  (declare (xargs :guard t))
  '(update-call-stack-height
    update-call-stack-height-aux-base
    update-call-stack-height-aux-of-if-arg1
    arm::step-opener
    arm::execute-inst-base ; requires the instruction to be known
    arm::step-of-if
    arm::read-of-if-arg2
    arm::read-of-if-arg3
    arm::reg-of-if-arg2))

(defun symbolic-execution-rules32 ()
  (declare (xargs :guard t))
  (append (symbolic-execution-rules32-common)
          '(run-until-return-aux-base-axe
            run-until-return-aux-opener-axe
            run-until-return-aux-of-if-arg2
            run-until-return
            run-subroutine)))

(defun symbolic-execution-rules-with-stop-pcs32 ()
  (declare (xargs :guard t))
  (append (symbolic-execution-rules32-common)
          '(run-until-return-or-reach-pc-aux-base-axe
            run-until-return-or-reach-pc-aux-opener-axe
            run-until-return-or-reach-pc-aux-of-if-arg2
            run-until-return-or-reach-pc
            acl2::memberp-constant-opener ; for resolving the stop-pcs check (when non-position-independent)
            )))

(defun debug-rules32 ()
  (declare (xargs :guard t))
  '(arm::step-opener
    run-until-return-aux-opener-axe
    run-until-return-or-reach-pc-aux-opener-axe
    ;;run-until-sp-is-above-opener
    read-when-equal-of-read-bytes-and-subregion32p
    read-when-equal-of-read-bytes-and-subregion32p-alt
    read-when-equal-of-read-bytes
    read-when-equal-of-read-bytes-alt
    ))

;; ;; sophisticated scheme for removing inner, shadowed writes
;; (defund shadowed-write-rules32 ()
;;   (declare (xargs :guard t))
;;   '(write-becomes-write-of-clear-extend-axe
;;     clear-extend-of-write-continue-axe
;;     clear-extend-of-write-finish
;;     clear-extend-of-write-of-clear-retract
;;     write-of-clear-retract))

(defun execute-function-names (mnemonics)
  (declare (xargs :guard (keyword-listp mnemonics)))
  (if (endp mnemonics)
      nil
    (let* ((mnemonic (first mnemonics)))
      (cons (acl2::pack-in-package "ARM" 'execute- (symbol-name mnemonic))
            (execute-function-names (rest mnemonics))))))

(make-event
 `(defund semantic-functions-for-mnemonics ()
    (declare (xargs :guard t))
    ',(execute-function-names (strip-cars *patterns*))))

(defund instruction-semantic-functions ()
  (declare (xargs :guard t))
  (append (semantic-functions-for-mnemonics)
          '(arm::mov-common
            arm::mov-register-core
            arm::pop-encoding-a2-core
            arm::pop-common
            arm::pop-loop-base
            arm::pop-loop-unroll
            arm::push-encoding-a1-core
            arm::push-encoding-a2-core
            arm::push-common
            arm::push-loop-base
            arm::push-loop-unroll
            arm::ldm-loop-base
            arm::ldm-loop-unroll
            arm::stm-loop-base
            arm::stm-loop-unroll)))

(defun lifter-rules32 ()
  (declare (xargs :guard t))
  (append
   (instruction-semantic-functions)
   '(arm::lookup-eq2

     arm::r0
     arm::r1
     arm::r2
     arm::r3
     arm::r4
     arm::r5
     arm::r6
     arm::r7
     arm::r8
     arm::r9
     arm::r10
     arm::r11
     arm::r12
     arm::r13
     arm::r14
     arm::r15

     acl2::lookup-eq-becomes-lookup-equal
     arm::==$inline
     arm::ldr-literal-core
     arm::conditionpassed
     arm::uint
     arm::zeroextend
     arm::nullcheckifthumbee
     arm::pcvalue
     arm::align ; redef?
     arm::div
     arm::memu
     arm::advance-pc
     arm::pc ; should we open this? if so, do it in the assumptions too
     arm::reg-of-set-reg
     arm::register-numberp
     arm::add-to-address
     arm::read-of-set-reg
     arm::error-of-set-reg
     arm::arch-version-of-set-reg
     arm::isetstate-of-set-reg

     arm::isetstate-of-set-apsr.n
     arm::isetstate-of-set-apsr.z
     arm::isetstate-of-set-apsr.c
     arm::isetstate-of-set-apsr.v
     arm::isetstate-of-set-apsr.q

     arm::apsr.n-of-set-apsr.n
     arm::apsr.n-of-set-apsr.z
     arm::apsr.n-of-set-apsr.c
     arm::apsr.n-of-set-apsr.v
     arm::apsr.n-of-set-apsr.q

     arm::apsr.z-of-set-apsr.n
     arm::apsr.z-of-set-apsr.z
     arm::apsr.z-of-set-apsr.c
     arm::apsr.z-of-set-apsr.v
     arm::apsr.z-of-set-apsr.q

     arm::apsr.c-of-set-apsr.n
     arm::apsr.c-of-set-apsr.z
     arm::apsr.c-of-set-apsr.c
     arm::apsr.c-of-set-apsr.v
     arm::apsr.c-of-set-apsr.q

     arm::apsr.v-of-set-apsr.n
     arm::apsr.v-of-set-apsr.z
     arm::apsr.v-of-set-apsr.c
     arm::apsr.v-of-set-apsr.v
     arm::apsr.v-of-set-apsr.q

     arm::apsr.q-of-set-apsr.n
     arm::apsr.q-of-set-apsr.z
     arm::apsr.q-of-set-apsr.c
     arm::apsr.q-of-set-apsr.v
     arm::apsr.q-of-set-apsr.q

     arm::apsr.n-of-set-reg
     arm::apsr.z-of-set-reg
     arm::apsr.c-of-set-reg
     arm::apsr.v-of-set-reg
     arm::apsr.q-of-set-reg

     arm::set-apsr.n-of-set-reg
     arm::set-apsr.z-of-set-reg
     arm::set-apsr.c-of-set-reg
     arm::set-apsr.v-of-set-reg
     arm::set-apsr.q-of-set-reg

     arm::error-of-set-apsr.n
     arm::error-of-set-apsr.z
     arm::error-of-set-apsr.c
     arm::error-of-set-apsr.v
     arm::error-of-set-apsr.q

     arm::arch-version-of-set-apsr.n
     arm::arch-version-of-set-apsr.z
     arm::arch-version-of-set-apsr.c
     arm::arch-version-of-set-apsr.v
     arm::arch-version-of-set-apsr.q

     arm::read-of-set-apsr.n
     arm::read-of-set-apsr.z
     arm::read-of-set-apsr.c
     arm::read-of-set-apsr.v
     arm::read-of-set-apsr.q

     arm::reg-of-set-apsr.n
     arm::reg-of-set-apsr.z
     arm::reg-of-set-apsr.c
     arm::reg-of-set-apsr.v
     arm::reg-of-set-apsr.q

     arm::branchto
     arm::pcstorevalue
     arm::loadwritepc
     arm::bxwritepc
     arm::branchwritepc

     arm::armexpandimm_c
     arm::armexpandimm
     arm::shift_c
     arm::ror_c
     arm::lsr
     arm::lsr_c
     arm::lsl
     arm::bitcount
     arm::write_memu
     arm::write_mema
     arm::!=$inline
     arm::zeros

     arm::archversion
     arm::currentinstrset
     arm::unalignedsupport ; why?

     acl2::bvcount-constant-opener
     arm::integerp-of-reg
     arm::unsigned-byte-p-32-of-reg
     arm::reg-of-write
     ;; arm::write-byte-of-set-reg ; we always use write as the normal form
     arm::write-of-set-reg
     arm::set-reg-of-set-reg-same
     arm::set-reg-of-set-reg-diff-2
     arm::error-of-write
     arm::arch-version-of-write
     arm::isetstate-of-write
     arm::decodeimmshift
     arm::mv-nth-0-of-AddWithCarry ;;     arm::addwithcarry
     arm::mv-nth-1-of-AddWithCarry ;;     arm::addwithcarry
     arm::mv-nth-2-of-AddWithCarry ; todo: 32-bit only!
     arm::shift
     arm::lsl_c
     arm::iszerobit
     arm::iszero
     )
;   (shadowed-write-rules32)
   (acl2::base-rules) ; gets us if-same-branches, for example
   (acl2::core-rules-bv)
   (acl2::unsigned-byte-p-forced-rules)
   (acl2::type-rules) ; rename
   (acl2::bvchop-of-bv-rules)
   (acl2::convert-to-bv-rules) ; todo: may just need the trim-elim rules
   (acl2::boolean-rules-safe)
   (acl2::list-to-bv-array-rules) ;; unrolling seemed bad for large sections?
   '(;acl2::list-to-bv-array-constant-opener
     ;acl2::list-to-bv-array-aux-constant-opener ; slow?!
     acl2::bv-list-read-chunk-little-constant-opener
     acl2::packbv-little-constant-opener
     )
   '(arm::len-of-read-bytes arm::nth-of-read-bytes) ; for output-indicator handling
   '(;; error32p-of-set-reg
     ;; error32p-of-write
     ;; error32p-of-set-pc

     ;; Rules about read:
     arm::integerp-of-read
     arm::natp-of-read
     arm::unsigned-byte-p-of-read
     arm::read-of-bvchop-32 ; todo: say which arg
     arm::read-of-+

     ;; UNCOMMENT:
     ;; bvchop-of-read
     ;; <-of-read ; for an array pattern rule
     ;; not-equal-of-read-and-constant
     ;; not-equal-of-constant-and-read

     ;; UNCOMMENT:
     ;; Rules to introduce READ:
     arm::read-byte-becomes-read ; we use READ as the normal form, even when writing just one byte

     ;; UNCOMMENT:
     ;; ;; Rules about write:
     arm::write-of-bvchop-32-arg2
     arm::write-of-bvchop-arg3
     ;; write-of-logext-arg3
     ;; write32-mem-ubyte8-becomes-write-byte ; todo: go directly to write
     ;; write32-mem-ubyte32-lendian-becomes-write
     ;; write-of-+
     ;; write-of-write-same
     ;; Rules about reading and writing:
     arm::read-of-write-same
     arm::read-of-write-1-within
     arm::read-1-of-write-within
     arm::read-of-write-when-disjoint-regions32p
     arm::read-of-write-when-disjoint-regions32p-gen
     arm::read-of-write-when-disjoint-regions32p-gen-alt

     arm::disjoint-regions32p-when-disjoint-regions32p-and-subregion32p-and-subregion32p
     arm::disjoint-regions32p-when-disjoint-regions32p-and-subregion32p-and-subregion32p-alt

     ;; UNCOMMENT
     arm::read-when-equal-of-read-bytes-and-subregion32p ; for when the bytes are a constant
     arm::read-when-equal-of-read-bytes-and-subregion32p-alt ; for when the bytes are not a constant
     arm::read-when-equal-of-read-bytes ; note rule priority
     arm::read-when-equal-of-read-bytes-alt
     ;; acl2::len-of-cons ;  for when read-when-equal-of-read-bytes-and-subregion32p-alt introduces a cons nest

     arm::subregion32p-of-1-arg1     ;; trying
     arm::disjoint-regions32p-of-1-and-1 ; trying

     acl2::equal-of-bvplus-constant-and-constant-alt
     acl2::equal-of-bvplus-constant-and-constant
     acl2::equal-of-bvplus-and-bvplus-reduce-constants
     disjoint-regions32p-byte-special
     acl2::bv-array-read-chunk-little-of-1
     acl2::bv-array-read-chunk-little-unroll
     acl2::bv-array-read-of-bvplus-of-constant-no-wrap

     acl2::bv-list-read-chunk-little-of-cons-irrel
     acl2::bv-list-read-chunk-little-of-bvplus-of-constant
     acl2::bv-list-read-chunk-little-opener
     acl2::nth-of-cons-constant-version ; for handling (equal (read-bytes ..) <cons-nest>)
     acl2::unsigned-byte-listp-of-cons
     acl2::unsigned-byte-listp-constant-opener

     ;;bv-array-read-shorten-8
     acl2::bv-array-read-of-bvplus-of-constant-no-wrap
     acl2::not-equal-of-constant-and-bv-term-axe
     acl2::not-equal-of-constant-and-bv-term-alt-axe
     acl2::equal-of-bvchop-and-bvplus-of-same
     acl2::equal-of-bvchop-and-bvplus-of-same-alt
     acl2::logext-identity-when-usb-smaller-axe
     acl2::bvxor-of-logext-arg3
     acl2::bvxor-of-logext-arg2

     arm::not-bvlt-when-not-in-region32p ; backchains from bvlt to in-region32p

     not-in-region32p-when-disjoint-regions32p-special
     ;; not-in-region32p-when-disjoint-regions32p-one ; looped -- why?
     ;; not-in-region32p-when-disjoint-regions32p-two
     acl2::bvlt-of-1
     ;acl2::bvlt-of-bvplus-constant-and-constant-gen ; bad?
     bvlt-of-read-and-constant

    arm::in-region32p-cancel-constants-1-1+
    arm::in-region32p-cancel-constants-1+-1
    arm::in-region32p-cancel-constants-1+-1+
    arm::in-region32p-cancel-1-1+
    arm::in-region32p-cancel-1+-1
    arm::in-region32p-cancel-1+-1+
    arm::in-region32p-cancel-1-2
    arm::in-region32p-cancel-2-1
    arm::in-region32p-cancel-1+-2
    arm::in-region32p-cancel-2-1+
    arm::in-region32p-cancel-2+-1
    arm::in-region32p-cancel-1-3
    arm::in-region32p-cancel-3-1
    arm::in-region32p-cancel-2-2
    arm::in-region32p-when-non-negative-and-negative-range
    ;; arm::in-region32p-of-0-arg3 ; introduces bvlt
    arm::in-region32p-of-bvchop-arg1
    arm::in-region32p-of-bvchop-arg3
    arm::in-region32p-of-bvsx-arg1
    arm::in-region32p-of-bvsx-arg3
    arm::in-region32p-same

     ;in-region32p-byte-special ; have the memory machinery generate this?

;;     arm::write-byte-becomes-write UNCOMMENT
     arm::read-normalize-constant-arg2
     ;; arm::write-normalize-constant-arg2 UNCOMMENT
     ;; arm::write-normalize-constant-arg3

     arm::disjoint-regions32p-cancel-1-1+
     arm::disjoint-regions32p-cancel-1+-1
     arm::disjoint-regions32p-cancel-1+-1+
     arm::disjoint-regions32p-cancel-1-2
     arm::disjoint-regions32p-cancel-2-1
     arm::disjoint-regions32p-cancel-1+-2
     arm::disjoint-regions32p-cancel-2-1+
     arm::disjoint-regions32p-cancel-2-2
     arm::disjoint-regions32p-cancel-2+-2
     arm::disjoint-regions32p-of-bvplus-of-constant-and-constant

     arm::subregion32p-cancel-1-1
     arm::subregion32p-cancel-1+-1
     arm::subregion32p-cancel-1-1+
     arm::subregion32p-cancel-2-1
     arm::subregion32p-cancel-2-1+
     arm::subregion32p-cancel-1-2
     arm::subregion32p-cancel-1+-2
     arm::subregion32p-cancel-2-2
     arm::subregion32p-cancel-constants-1+-1
     arm::subregion32p-cancel-constants-1+-1+

     ;; todo: UNCOMMENT
     ;set-pc-convert-arg1-to-bv-axe
     ;set-reg-convert-arg2-to-bv-axe

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

     ;; read32-pc-becomes-pc ; introduces PC, our normal form
     ;; write32-pc-becomes-set-pc ; introduces SET-PC, our normal form
     ;; read32-xreg-unsigned-becomes-reg ; introduces REG, our normal form
     ;; write32-xreg-becomes-set-reg ; introduces SET-REG, our normal form

     ;; read32-xreg-signed ; open to the unsigned one

     ;; reg-of-set-reg
     ;; set-reg-of-set-reg-same
     ;; set-reg-of-set-reg-diff
     ;; reg-of-write
     ;; ;; reg-of-write-byte
     ;; reg-of-set-pc
     ;; reg-of-if

     ;; set-reg-of-bvchop
     ;; set-reg-does-nothing
     ;; set-reg-of-0 ; setting register 0 has no effect!

     ;; pc-of-set-pc
     ;; set-pc-of-set-pc
     ;; pc-of-set-reg
     ;; pc-of-write
     ;; write-of-set-reg

     ;; read-of-set-pc
     ;; read-of-set-reg

     ;; ;; normalizing nests of writes:
     ;; set-reg-of-set-pc
     ;; write-of-set-pc

     ;; stat32p-of-set-reg
     ;; stat32p-of-write
     ;; stat32p-of-set-pc ; uncomment?

     ;; regiseter names (we expand these to REG):
;     x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
     ;; register aliases:
     ;; zero
;     ra sp gp tp t0 t1 t2 s0 fp s1 a0 a1 a2 a3 a4 a5

     arm::subregion32p-constant-opener ; todo: think about package on these
     arm::in-region32p-constant-opener
     arm::disjoint-regions32p-constant-opener

     acl2::bv-array-write-of-if-arg4 ; introduces bvif

     acl2::bv-array-read-chunk-little-constant-opener

     ;; riscv::feat
     ;; riscv::feat->base$inline
     ;; riscv::feat->m$inline-constant-opener ; should all of these be constant-openers?


     ;; riscv32im-le::feat-rv32im-le ; todo: use constant-openers more for these?

     ;; riscv::feat-endian-little
     ;; riscv::feat-endian-fix$inline
     ;; riscv::feat-endian-kind$inline

     ;; riscv::feat-base-rv32i

     ;; riscv::feat-base-fix$inline
     ;; riscv::feat-base-kind$inline
     ;; riscv::feat-mp
     ;; riscv::feat-embedp

     ;; riscv::branch-funct-fix$inline
     ;; riscv::branch-funct-kind$inline

     ;; riscv::op-imms-funct-fix$inline
     ;; riscv::op-imms-funct-kind$inline

     arm::arm32-decode-constant-opener ;; ;; riscv::decodex-constant-opener ; not needed since the evaluator knows about this function
     ;; acl2::ubyte32-fix-constant-opener
     ;; acl2::ubyte32p-constant-opener
     ;; riscv::get-fields-itype-constant-opener
     ;; riscv::get-fields-jtype-constant-opener
     ;; riscv::get-rd-constant-opener
     ;; riscv::get-rs1-constant-opener
     ;; riscv::get-rs2-constant-opener
     ;; riscv::get-funct3-constant-opener
     ;; riscv::get-funct7-constant-opener

     ;; riscv::get-opcode-constant-opener
     ;; riscv::get-imm-btype-constant-opener
     ;; riscv::get-imm-itype-constant-opener
     ;; riscv::get-imm-jtype-constant-opener
     ;; riscv::get-imm-stype-constant-opener
     ;; riscv::get-imm-utype-constant-opener
     ;; bitops::part-select-low-high$inline-constant-opener
     ;; bitops::part-select-width-low$inline-constant-opener
     ;; riscv::feat-64p-constant-opener
     ;; riscv::get-fields-btype-constant-opener
     ;; riscv::get-fields-rtype-constant-opener
     ;; riscv::get-fields-utype-constant-opener
     ;; riscv::get-fields-stype-constant-opener

     ;; riscv::instr-op-imm-constant-opener

     acl2::logtail$inline-constant-opener
     acl2::expt2$inline-constant-opener
;     acl2::binary-logand-constant-opener ; todo: led to stack overflow -- need to make a safe opener?  and eval zip and evenp
     acl2::ifloor$inline-constant-opener
     acl2::logapp-constant-opener
     common-lisp::ash-constant-opener ; todo: use acl2 package
     acl2::ash-becomes-logtail ; do better?
     acl2::bvchop-of-ash-left-shift ; move
     acl2::logtail-of-logext
     ;acl2::logtail-of-bvcat
     acl2::logtail-becomes-slice-bind-free-axe
     acl2::bvcat-of-logext-arg2
     acl2::bvcat-of-logext-arg4

     ;acl2::bvcat-of-if-arg2
     ;acl2::bvcat-of-if-arg4
     acl2::bvcat-of-if-becomes-bvcat-of-bvif-arg2 ; these could be convert-to-bv rules
     acl2::bvcat-of-if-becomes-bvcat-of-bvif-arg4

     acl2::loghead-becomes-bvchop



     acl2::bvchop-of-+-becomes-bvplus
     acl2::bvminus-of-bvplus-and-bvplus-same
     acl2::bvminus-of-bvplus-same
     acl2::bvminus-of-bvplus-same-arg2
     acl2::bvminus-of-bvplus-of-constant-and-bvplus-of-constant
     acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version

;     eff32-addr

     acl2::integerp-of-+-when-integerp-1
     acl2::integerp-of-+-when-integerp-2
     acl2::fix-when-integerp
     acl2::integerp-of-bvplus
     acl2::integerp-of-logext

;     riscv32im-le::stat32-fix-when-stat32p

     acl2::ifix-when-integerp
     acl2::mod-becomes-bvchop-when-power-of-2p

     myif ; always expand to IF
     )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; try late
(acl2::set-axe-rule-priority arm::not-bvlt-when-not-in-region32p 1)

;; try after the one for constant bytes:
(acl2::set-axe-rule-priority arm::read-when-equal-of-read-bytes 1)

;; split before trying to open if the state is an IF:
(acl2::set-axe-rule-priority run-until-return-aux-of-if-arg2 -1)
