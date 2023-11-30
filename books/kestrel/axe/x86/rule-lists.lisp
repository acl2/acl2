; Rule Lists used by the x86 Axe tools
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "kestrel/axe/rule-lists" :dir :system)
(include-book "kestrel/utilities/defconst-computed" :dir :system)

(include-book "projects/x86isa/machine/instructions/top" :dir :system) ;needed to get the full ruleset instruction-decoding-and-spec-rules

;; TODO: Use union-equal instead of append?  Or even, in some cases, a version that detects duplicates.

;todo: add a variant of get-ruleset that complains if the ruleset doesn't exist..
(acl2::defconst-computed-simple *instruction-decoding-and-spec-rules*
  (acl2::get-ruleset 'x86isa::instruction-decoding-and-spec-rules (w state)))

;; Most of these are just names of functions to open
(defun instruction-rules ()
  (append '(x86isa::gpr-arith/logic-spec-1 ;; dispatches based on operation
            x86isa::gpr-arith/logic-spec-2 ;; dispatches based on operation
            x86isa::gpr-arith/logic-spec-4 ;; dispatches based on operation
            x86isa::gpr-arith/logic-spec-8 ;; dispatches based on operation

;            x86isa::jcc/cmovcc/setcc-spec ;case dispatch ;;disabling this to produce better results

            x86isa::gpr-or-spec-1$inline
            x86isa::gpr-or-spec-2$inline
            x86isa::gpr-or-spec-4$inline
            x86isa::gpr-or-spec-8$inline

            x86isa::gpr-and-spec-1$inline
            x86isa::gpr-and-spec-2$inline
            x86isa::gpr-and-spec-4$inline
            x86isa::gpr-and-spec-8$inline

            x86isa::gpr-adc-spec-1$inline
            x86isa::gpr-adc-spec-2$inline
            x86isa::gpr-adc-spec-4$inline
            x86isa::gpr-adc-spec-8$inline

            ;; x86isa::gpr-sub-spec-1$inline
            ;; x86isa::gpr-sub-spec-2$inline
            ;; x86isa::gpr-sub-spec-4$inline
            ;; x86isa::gpr-sub-spec-8$inline
            x86isa::gpr-sub-spec-1-alt-def
            x86isa::gpr-sub-spec-2-alt-def
            x86isa::gpr-sub-spec-4-alt-def
            x86isa::gpr-sub-spec-8-alt-def

            x86isa::gpr-xor-spec-1$inline
            x86isa::gpr-xor-spec-2$inline
            x86isa::gpr-xor-spec-4$inline
            x86isa::gpr-xor-spec-8$inline

            x86isa::shr-spec$inline ;; dispatches based on size
            x86isa::shr-spec-8
            x86isa::shr-spec-16
            x86isa::shr-spec-32
            x86isa::shr-spec-64

            x86isa::rol-spec$inline ;; dispatches based on size
            x86isa::rol-spec-8
            x86isa::rol-spec-16
            x86isa::rol-spec-32
            x86isa::rol-spec-64

            x86isa::sal/shl-spec$inline ;; dispatches based on size
            x86isa::sal/shl-spec-8
            x86isa::sal/shl-spec-16
            x86isa::sal/shl-spec-32
            x86isa::sal/shl-spec-64

            ;; unsigned multiply
            x86isa::mul-spec$inline ;; dispatches based on size
            x86isa::mul-spec-8
            x86isa::mul-spec-16
            x86isa::mul-spec-32
            x86isa::mul-spec-64

            ;; signed multiply
            x86isa::imul-spec$inline ;; dispatches based on size
            x86isa::imul-spec-8
            x86isa::imul-spec-16
            x86isa::imul-spec-32
            x86isa::imul-spec-64

            x86isa::gpr-add-spec-8$inline
            x86isa::gpr-add-spec-4$inline

            x86isa::idiv-spec$inline
            ;;X86ISA::IDIV-SPEC-64 ;need to re-characterize this as something nice
            x86isa::idiv-spec-64-trim-arg1-axe-all

            x86isa::sar-spec$inline
            x86isa::sar-spec-32-nice ;x86isa::sar-spec-32
            x86isa::sar-spec-64-nice ;x86isa::sar-spec-32

            ;; These recharacterize divide in terms of bvops:
            x86isa::mv-nth-0-of-div-spec-8
            x86isa::mv-nth-1-of-div-spec-8
            x86isa::mv-nth-2-of-div-spec-8
            x86isa::mv-nth-0-of-div-spec-16
            x86isa::mv-nth-1-of-div-spec-16
            x86isa::mv-nth-2-of-div-spec-16
            x86isa::mv-nth-0-of-div-spec-32
            x86isa::mv-nth-1-of-div-spec-32
            x86isa::mv-nth-2-of-div-spec-32
            x86isa::mv-nth-0-of-div-spec-64
            x86isa::mv-nth-1-of-div-spec-64
            x86isa::mv-nth-2-of-div-spec-64)
          *instruction-decoding-and-spec-rules*))

(defun list-rules-x86 ()
  '(atom ;open to expose consp
    car-cons
    acl2::consp-of-cons
    cdr-cons
    ;; lists as sets:
    x86isa::subset-p-of-singleton-arg1
    x86isa::disjoint-p-subset-p ;has free vars, somewhat aggressive
    x86isa::subset-p-reflexive  ;strengthen?
    x86isa::disjoint-p-nil-1
    ;;disjoint-p-cons-1 ;this may require more rules (e.g., (disjointp y z) and (subsetp x y) and (memberp a z) => (not (memberp a x)))
    ;;not-member-p-when-disjoint-p ;todo: make an alt version
    x86isa::subset-p-reflexive
    ))

(defun linear-memory-rules ()
  '(
    ;; Open these read operations to RB, which then gets turned into READ (TODO: Turn these into READ directly?)
    x86isa::rml08
    x86isa::rml16
    x86isa::rml32
    x86isa::rml64           ;shilpi leaves this enabled
    x86isa::rml-size$inline ;shilpi leaves this enabled ;todo: consider rml-size-becomes-rb

    x86isa::riml08
    x86isa::riml16
    x86isa::riml32
    x86isa::riml64               ;shilpi leaves this enabled
    x86isa::riml-size$inline ;shilpi leaves this enabled -- could restrict to constant

    x86isa::wml08
    x86isa::wml16
    x86isa::wml32
    x86isa::wml64           ;shilpi leaves this enabled, but this is big!
    x86isa::wml-size$inline ;shilpi leaves this enabled

    x86isa::wiml08
    x86isa::wiml16
    x86isa::wiml32
    x86isa::wiml64
    x86isa::wiml-size$inline
    ))

(defun read-introduction-rules ()
  '(mv-nth-1-of-rb-becomes-read
    mv-nth-1-of-rb-1-becomes-read))

(defun write-introduction-rules ()
  '(mv-nth-1-of-wb-1-becomes-write
    mv-nth-1-of-wb-becomes-write))

(defun read-byte-rules ()
  '(read-byte-of-xw-irrel
    read-byte-when-program-at
    read-byte-of-set-flag
    read-byte-of-write-byte
    read-byte-of-logext
    ))

(defun read-rules ()
  '(unsigned-byte-p-of-read
    integerp-of-read
    <-of-read-and-non-positive
    read-of-xw-irrel
    read-of-set-flag
    read-in-terms-of-nth-and-pos-eric ; read-when-program-at
    read-of-logext
    read-when-equal-of-read
    read-when-equal-of-read-alt
    <-of-constant-and-read ; in case we backchain to < to try to resolve a bvlt
    <-of-read-and-constant ; in case we backchain to < to try to resolve a bvlt
    ))

(defun write-rules ()
  '(write-of-bvchop-arg3-gen
    xr-of-write-when-not-mem
    x86p-of-write
    64-bit-modep-of-write
    app-view-of-write
    alignment-checking-enabled-p-of-write
    write-of-xw-irrel
    set-flag-of-write
    get-flag-of-write
    read-of-write-same
    read-of-write-disjoint
    read-of-write-disjoint2
    program-at-of-write
    ;; todo: uncomment these but first organize rules:
    ;;write-of-write-same
    ;;write-of-write-of-write-same
    ;;write-of-write-of-write-of-write-same
    ;; I guess we are not normalizing write nests, perhaps due to partial overlap?  could sort when known disjoint...
    ))

;; 'Read Over Write' and similar rules for state components. Our normal form
;; (at least for 64-bit code) includes 3 kinds of state changes, namely calls
;; to XW, WRITE, and SET-FLAG.
(defun state-rules ()
  '(
    ;x86isa::x86p-set-flag
    force ;todo: think about this
    x86isa::x86p-xw ;big rule with forced hyps
    x86isa::x86p-of-wb ;  wb-returns-x86p ;targets x86p-of-mv-nth-1-of-wb ;drop if WB will always be rewritten to WRITE

    ;; Flags:
    x86p-of-set-flag
    get-flag-of-xw
    xr-of-set-flag
    set-flag-of-xw
    get-flag-of-set-flag
    set-flag-of-set-flag-diff-axe
    set-flag-of-set-flag-same
    x86isa::alignment-checking-enabled-p-of-set-flag
    X86ISA::XW-RGF-OF-XR-RGF-SAME

    ;; Rules about get-flag
    get-flag-of-set-eip
    get-flag-of-write-byte-to-segment
    get-flag-of-write-to-segment
    get-flag-of-set-eax
    get-flag-of-set-ebx
    get-flag-of-set-ecx
    get-flag-of-set-edx
    get-flag-of-set-esp
    get-flag-of-set-ebp


;;     ;; x86isa::get-flag-set-flag ;covers both cases, with a twist for a 2-bit flag
;;     ;; x86isa::set-flag-set-flag-same
;;     ;; x86isa::set-flag-set-flag-different-concrete-indices
;;     x86isa::rflagsbits-fix$inline

;;     x86isa::rflagsbits->ac$inline
;;     x86isa::rflagsbits->af$inline
;;     x86isa::rflagsbits->cf$inline
;;     x86isa::rflagsbits->of$inline
;;     x86isa::rflagsbits->pf$inline
;;     x86isa::rflagsbits->sf$inline
;;     x86isa::rflagsbits->zf$inline

    x86isa::rflagsbits->ac$inline-constant-opener
    x86isa::rflagsbits->af$inline-constant-opener
    x86isa::rflagsbits->cf$inline-constant-opener
    x86isa::rflagsbits->of$inline-constant-opener
    x86isa::rflagsbits->pf$inline-constant-opener
    x86isa::rflagsbits->sf$inline-constant-opener
    x86isa::rflagsbits->zf$inline-constant-opener
    ;todo: more like this?

    x86isa::rflagsbits-fix$inline-constant-opener
    unsigned-byte-p-of-rflagsbits

    ;; These introduce set-flag:
    !rflags-of-!rflagsbits->af
    !rflags-of-!rflagsbits->cf
    !rflags-of-!rflagsbits->of
    !rflags-of-!rflagsbits->pf
    !rflags-of-!rflagsbits->sf
    !rflags-of-!rflagsbits->zf

    X86ISA::RFLAGSBITS->aF-OF-RFLAGSBITS
    X86ISA::RFLAGSBITS->cF-OF-RFLAGSBITS
    X86ISA::RFLAGSBITS->OF-OF-RFLAGSBITS
    X86ISA::RFLAGSBITS->pF-OF-RFLAGSBITS
    X86ISA::RFLAGSBITS->sF-OF-RFLAGSBITS
    X86ISA::RFLAGSBITS->zF-OF-RFLAGSBITS

    rflagsbits->af$inline-of-bvchop-32
    rflagsbits->cf$inline-of-bvchop-32
    rflagsbits->pf$inline-of-bvchop-32
    rflagsbits->of$inline-of-bvchop-32
    rflagsbits->sf$inline-of-bvchop-32
    rflagsbits->zf$inline-of-bvchop-32

    flags-af-cf
    flags-af-pf
    flags-af-of
    flags-af-sf
    flags-af-zf

    flags-cf-af
    flags-cf-pf
    flags-cf-of
    flags-cf-sf
    flags-cf-zf

    flags-pf-af
    flags-pf-cf
    flags-pf-of
    flags-pf-sf
    flags-pf-zf

    flags-of-af
    flags-of-cf
    flags-of-pf
    flags-of-sf
    flags-of-zf

    flags-sf-af
    flags-sf-cf
    flags-sf-pf
    flags-sf-of
    flags-sf-zf

    flags-zf-af
    flags-zf-cf
    flags-zf-pf
    flags-zf-of
    flags-zf-sf

    flags-af-af
    flags-cf-cf
    flags-pf-pf
    flags-of-of
    flags-sf-sf
    flags-zf-zf

    !rflags-of-xr-rflags-of-set-flag
    xr-rflags-of-!rflags
    !rflags-of-xw
    x86isa::!rflags-of-write
    !rflags-of-set-flag
    !rflags-of-!rflags
    !rflags-does-nothing

;;     x86isa::!rflagsbits->ac$inline
;;     x86isa::!rflagsbits->af$inline
;;     x86isa::!rflagsbits->cf$inline ;it would be better if these called rflagsbits
;;     x86isa::!rflagsbits->of$inline
;;     x86isa::!rflagsbits->pf$inline
;;     x86isa::!rflagsbits->sf$inline
;;     x86isa::!rflagsbits->zf$inline

;;     x86isa::!rflags$inline


;;     x86isa::unsigned-byte-p-1-of-rflagsbits->res1$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->cf$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->pf$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->id$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->vip$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->vif$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->ac$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->vm$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->rf$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->res4$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->nt$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->of$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->df$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->intf$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->tf$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->sf$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->zf$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->res3$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->af$inline
;;     x86isa::unsigned-byte-p-1-of-rflagsbits->res2$inline
;;     x86isa::unsigned-byte-p-2-of-rflagsbits->iopl$inline ;this one is 2 bits

;;     ;x86isa::rflagsbits->ac$inline
;;     ;X86ISA::RFLAGSBITS$INLINE
;;     ;X86ISA::RFLAGSBITS->AC$INLINE-CONSTANT-OPENER
;;     x86isa::RFLAGSBITS-rewrite
;; ;    x86isa::get-flag-xw

    ;; These introduce get-flag:
    rflagsbits->cf$inline-of-xr
    rflagsbits->pf$inline-of-xr
    rflagsbits->af$inline-of-xr
    rflagsbits->zf$inline-of-xr
    rflagsbits->sf$inline-of-xr
    rflagsbits->tf$inline-of-xr
    rflagsbits->intf$inline-of-xr
    rflagsbits->df$inline-of-xr
    rflagsbits->of$inline-of-xr
    rflagsbits->iopl$inline-of-xr
    rflagsbits->nt$inline-of-xr
    rflagsbits->rf$inline-of-xr
    rflagsbits->vm$inline-of-xr
    rflagsbits->ac$inline-of-xr
    rflagsbits->vif$inline-of-xr
    rflagsbits->vip$inline-of-xr
    rflagsbits->id$inline-of-xr

;    x86isa::get-flag-wb-in-app-view
    x86isa::xr-ms-mv-nth-1-wb ;new  (see also xr-wb-in-app-view)

    ACL2::BFIX-WHEN-BITP ; move? or drop if we go to unsigned-byte-p
    x86isa::unsigned-byte-p-of-bfix
    ACL2::BITP-BECOMES-UNSIGNED-BYTE-P
    ))

(defun decoding-and-dispatch-rules ()
  '(x86isa::two-byte-opcode-execute ;todo: restrict to constants?  ;big case split
    x86isa::64-bit-mode-one-byte-opcode-modr/m-p-rewrite-quotep ; axe can't eval this
    x86isa::64-bit-mode-one-byte-opcode-modr/m-p$inline-of-if-when-constants
    x86isa::64-bit-mode-two-byte-opcode-modr/m-p-base ;;64-bit-mode-two-byte-opcode-modr/m-p-rewrite-quotep ;because axe can't eval this?
    x86isa::two-byte-opcode-decode-and-execute ;shilpi leaves this enabled
    aref1-rewrite
    ;; x86isa::compute-mandatory-prefix-for-two-byte-opcode$inline
    ;; x86isa::64-bit-compute-mandatory-prefix-for-two-byte-opcode
    x86isa::32-bit-compute-mandatory-prefix-for-two-byte-opcode$inline-constant-opener
    x86isa::32-bit-mode-two-byte-opcode-modr/m-p-constant-opener
    ;; x86isa::two-byte-opcode-modr/m-and-mandatory-prefix
    x86isa::compute-mandatory-prefix-for-two-byte-opcode$inline
    x86isa::64-bit-compute-mandatory-prefix-for-two-byte-opcode$inline
    x86isa::prefixes->lck$inline
    x86isa::prefixes->nxt$inline
    x86isa::prefixes->num$inline
    x86isa::!prefixes->nxt$inline
    x86isa::!prefixes->num$inline
    x86isa::!prefixes->opr$inline
;    x86isa::num-prefixes-fix$inline
    x86isa::prefixes-fix$inline
;    x86isa::next-byte-fix
;    x86isa::opr-fix
    x86isa::prefixes->opr$inline
    x86isa::prefixes->adr$inline
    x86isa::prefixes->seg$inline
    x86isa::modr/m->mod$inline
    x86isa::modr/m->reg$inline
    x86isa::modr/m->r/m$inline
    x86isa::modr/m-fix$inline
    x86isa::sib->scale$inline
    x86isa::sib->base$inline
    x86isa::sib->index$inline
    x86isa::sib-fix$inline
    x86isa::4bits-fix
    x86isa::8bits-fix
))

(defun x86-type-rules ()
  '(x86isa::n01p-pf-spec64 ;targets unsigned-byte-p-of-pf-spec64
    x86isa::n01p-of-spec64 ;targets unsigned-byte-p-of-of-spec64
    x86isa::n01p-sf-spec64 ;targets unsigned-byte-p-of-sf-spec64
    x86isa::n01p-sub-af-spec64 ;targets unsigned-byte-p-of-sub-af-spec64

    x86isa::n01p-cf-spec32 ;targets unsigned-byte-p-1-of-cf-spec32
    x86isa::n01p-pf-spec32 ;targets unsigned-byte-p-1-of-cp-spec32
    x86isa::n01p-of-spec32 ;targets unsigned-byte-p-1-of-cp-spec32
    x86isa::n01p-add-af-spec32 ;targets unsigned-byte-p-1-of-add-af-spec32

    x86isa::n01p-zf-spec ; targets unsigned-byte-p-of-zf-spec (maybe this is the same for sizes 32 and 64)

    ;x86isa::bitp-of-sf-spec32 ;todo: more like this
    x86isa::unsigned-byte-p-1-of-sf-spec32 ;todo: more like this
    x86isa::unsigned-byte-p-1-of-sub-af-spec32

    ;; todo: now we turn bitp into unsigned-byte-p, so these won't fire:
    x86isa::bitp-of-cf-spec-8
    x86isa::bitp-of-cf-spec-16
    x86isa::bitp-of-cf-spec-32
    x86isa::bitp-of-cf-spec-64
    x86isa::bitp-of-of-spec-8
    x86isa::bitp-of-of-spec-16
    x86isa::bitp-of-of-spec-32
    x86isa::bitp-of-of-spec-64
    x86isa::bitp-of-pf-spec-8
    x86isa::bitp-of-pf-spec-16
    x86isa::bitp-of-pf-spec-32
    x86isa::bitp-of-pf-spec-64
    x86isa::bitp-of-sf-spec-8
    x86isa::bitp-of-sf-spec-16
    x86isa::bitp-of-sf-spec-32
    x86isa::bitp-of-sf-spec-64
    x86isa::bitp-of-zf-spec
    x86isa::bitp-of-add-af-spec8
    x86isa::bitp-of-add-af-spec16
    x86isa::bitp-of-add-af-spec32
    x86isa::bitp-of-add-af-spec64
    x86isa::bitp-of-sub-cf-spec8
    x86isa::bitp-of-sub-cf-spec16
    x86isa::bitp-of-sub-cf-spec32
    x86isa::bitp-of-sub-cf-spec64
    x86isa::bitp-of-sub-of-spec8
    x86isa::bitp-of-sub-of-spec16
    x86isa::bitp-of-sub-of-spec32
    x86isa::bitp-of-sub-of-spec64
    x86isa::bitp-of-sub-pf-spec8
    x86isa::bitp-of-sub-pf-spec16
    x86isa::bitp-of-sub-pf-spec32
    x86isa::bitp-of-sub-pf-spec64
    x86isa::bitp-of-sub-sf-spec8
    x86isa::bitp-of-sub-sf-spec16
    x86isa::bitp-of-sub-sf-spec32
    x86isa::bitp-of-sub-sf-spec64
    x86isa::bitp-of-sub-zf-spec8
    x86isa::bitp-of-sub-zf-spec16
    x86isa::bitp-of-sub-zf-spec32
    x86isa::bitp-of-sub-zf-spec64

    x86isa::unsigned-byte-p-of-sub-cf-spec8
    x86isa::unsigned-byte-p-of-sub-cf-spec16
    x86isa::unsigned-byte-p-of-sub-cf-spec32 ;bitp becomes unsigned-byte-p 1 ?
    x86isa::unsigned-byte-p-of-sub-cf-spec64 ;bitp becomes unsigned-byte-p 1 ?

    x86isa::unsigned-byte-p-of-sub-of-spec8
    x86isa::unsigned-byte-p-of-sub-of-spec16
    x86isa::unsigned-byte-p-of-sub-of-spec32
    x86isa::unsigned-byte-p-of-sub-of-spec64

    x86isa::unsigned-byte-p-of-sub-pf-spec8
    x86isa::unsigned-byte-p-of-sub-pf-spec16
    x86isa::unsigned-byte-p-of-sub-pf-spec32
    x86isa::unsigned-byte-p-of-sub-pf-spec64

    x86isa::unsigned-byte-p-of-sub-sf-spec8
    x86isa::unsigned-byte-p-of-sub-sf-spec16
    x86isa::unsigned-byte-p-of-sub-sf-spec32
    x86isa::unsigned-byte-p-of-sub-sf-spec64

    x86isa::unsigned-byte-p-of-sub-zf-spec8
    x86isa::unsigned-byte-p-of-sub-zf-spec16
    x86isa::unsigned-byte-p-of-sub-zf-spec32
    x86isa::unsigned-byte-p-of-sub-zf-spec64

    x86isa::integerp-of-sub-cf-spec8
    x86isa::integerp-of-sub-cf-spec16
    x86isa::integerp-of-sub-cf-spec32
    x86isa::integerp-of-sub-cf-spec64

    x86isa::integerp-of-sub-of-spec8
    x86isa::integerp-of-sub-of-spec16
    x86isa::integerp-of-sub-of-spec32
    x86isa::integerp-of-sub-of-spec64

    x86isa::integerp-of-sub-pf-spec8
    x86isa::integerp-of-sub-pf-spec16
    x86isa::integerp-of-sub-pf-spec32
    x86isa::integerp-of-sub-pf-spec64

    x86isa::integerp-of-sub-sf-spec8
    x86isa::integerp-of-sub-sf-spec16
    x86isa::integerp-of-sub-sf-spec32
    x86isa::integerp-of-sub-sf-spec64

    x86isa::integerp-of-sub-zf-spec8
    x86isa::integerp-of-sub-zf-spec16
    x86isa::integerp-of-sub-zf-spec32
    x86isa::integerp-of-sub-zf-spec64


    ;;todo: not x86-specific
    acl2::integerp-of-logext
    acl2::integerp-of--))

(defund bv-intro-rules ()
  (declare (xargs :guard t))
  '(acl2::logxor-becomes-bvxor-axe ;todo: more like this!
    ))

;todo: classify these
(defun x86-bv-rules ()
  (declare (xargs :guard t))
  (append
   (bv-intro-rules)
  '(acl2::bvlt-of-0-arg3 ;todo: more like this?
    ACL2::LOGHEAD-BECOMES-BVCHOP
    acl2::logext-of-bvplus-64 ;somewhat unusual
    logior-becomes-bvor-axe
    x86isa::n08-to-i08$inline ;this is just logext
    x86isa::slice-of-part-install-width-low
    x86isa::bvchop-of-part-install-width-low-becomes-bvcat

    ;;todo: try core-runes-bv:
    acl2::slice-of-slice-gen-better ;figure out which bv rules to include
    acl2::bvcat-of-0-arg1
    acl2::bvcat-of-0-arg3

    bitops::rotate-left-32$inline-constant-opener ;todo: gen to a full rewrite
    acl2::rotate-left-constant-opener
    acl2::logext-trim-arg-axe-all

    acl2::bvuminus-of-logext
    acl2::bvchop-of-if-when-constants
    acl2::bvplus-recollapse ;rename

    ;; this is needed to handle a divide:
    acl2::bvcat-of-if-becomes-bvsx-64-64
    acl2::bvlt-of-bvplus-1-cancel
    acl2::bvlt-of-bvplus-1-cancel-alt)))

;not used?
(defun canonical-address-rules ()
  '(x86isa::not-member-p-canonical-address-listp ;drop the not and strengthen?
    x86isa::subset-p-two-create-canonical-address-lists-general ;strengthen?
    ;;not-member-p-canonical-address-listp-when-disjoint-p ;free vars? looped? ;why?
    ;;not-member-p-canonical-address-listp-when-disjoint-p-alt ;free vars? looped? ;why?
    ;;not-member-p-when-disjoint-p ;todo: make an alt version
    x86isa::canonical-address-listp-of-cdr
    x86isa::cdr-create-canonical-address-list
    x86isa::car-create-canonical-address-list
    x86isa::canonical-address-p-of-i48
    x86isa::i48-when-canonical-address-p))

;; These are about if but are not 'if lifting' rules.
(defun if-rules ()
  '(acl2::if-nil-t
    acl2::if-of-not
    x86isa::if-of-if-same-arg2
    x86isa::if-of-if-arg3-same
    ))

;todo: try always including these?  these help with conditional branches
(defun if-lifting-rules ()
  '(x86isa::mv-nth-of-if          ;could restrict to when both branches are cons nests
   x86isa::equal-of-if-constants ;seems safe
   x86isa::equal-of-if-constants-alt ;seems safe
   x86isa::canonical-address-p-of-if
   x86isa::combine-bytes-of-if-when-constants
   x86isa::member-p-of-if-arg1
   x86isa::+-of-if-arg1
   x86isa::+-of-if-arg2
   acl2::nth-of-if-arg1
   x86isa::cons-of-if-when-constants
   x86isa::one-byte-opcode-execute-of-if-arg1
   x86isa::if-of-one-byte-opcode-execute-of-if-arg2 ;do we need this?
   x86isa::if-of-one-byte-opcode-execute-of-if-arg5 ;do we need this?
   x86isa::<-of-if-arg2                              ;could be dangerous
   x86isa::logext-of-if-arg2
   run-until-stack-shorter-than-of-if-arg2 ;careful, this can cause splits:
   ))

(defun simple-opener-rules ()
  '(x86isa::n08p$inline ;just unsigned-byte-p
    ; 64-bit-modep ; using rules about this instead, since this is no longer just true
    ))

;; These open the branch conditions, without trying to make the expressions nice.
;; Instead, consider adding more rules like jle-condition-rewrite-1.
;; TODO: Some of these are only for 64 or only for 32 bit mode?
;; (defun branch-condition-openers ()
;;   '(jo-condition
;;     jno-condition
;;     jb-condition
;;     jnb-condition
;;     jz-condition
;;     jnz-condition
;;     jbe-condition
;;     jnbe-condition
;;     js-condition
;;     jns-condition
;;     jp-condition
;;     jnp-condition
;;     jl-condition
;;     jnl-condition
;;     jle-condition
;;     jnle-condition))

;; these are for functions axe can't evaluate
(defun constant-opener-rules ()
  '(x86isa::zf-spec$inline-constant-opener

    x86isa::cf-spec8$inline-constant-opener
    x86isa::of-spec8$inline-constant-opener
    x86isa::pf-spec8$inline-constant-opener
    x86isa::sf-spec8$inline-constant-opener
    x86isa::adc-af-spec8$inline-constant-opener
    x86isa::add-af-spec8$inline-constant-opener
    x86isa::sub-af-spec8$inline-constant-opener
    x86isa::sub-cf-spec8-constant-opener
    x86isa::sub-of-spec8-constant-opener
    x86isa::sub-pf-spec8-constant-opener
    x86isa::sub-sf-spec8-constant-opener
    x86isa::sub-zf-spec8-constant-opener

    x86isa::cf-spec16$inline-constant-opener
    x86isa::of-spec16$inline-constant-opener
    x86isa::pf-spec16$inline-constant-opener
    x86isa::sf-spec16$inline-constant-opener
    x86isa::adc-af-spec16$inline-constant-opener
    x86isa::add-af-spec16$inline-constant-opener
    x86isa::sub-af-spec16$inline-constant-opener
    x86isa::sub-cf-spec16-constant-opener
    x86isa::sub-of-spec16-constant-opener
    x86isa::sub-pf-spec16-constant-opener
    x86isa::sub-sf-spec16-constant-opener
    x86isa::sub-zf-spec16-constant-opener

    x86isa::cf-spec32$inline-constant-opener
    x86isa::of-spec32$inline-constant-opener
    x86isa::pf-spec32$inline-constant-opener
    x86isa::sf-spec32$inline-constant-opener
    x86isa::adc-af-spec32$inline-constant-opener
    x86isa::add-af-spec32$inline-constant-opener
    x86isa::sub-af-spec32$inline-constant-opener
    x86isa::sub-cf-spec32-constant-opener
    x86isa::sub-of-spec32-constant-opener
    x86isa::sub-pf-spec32-constant-opener
    x86isa::sub-sf-spec32-constant-opener
    x86isa::sub-zf-spec32-constant-opener

    x86isa::cf-spec64$inline-constant-opener
    x86isa::of-spec64$inline-constant-opener
    x86isa::pf-spec64$inline-constant-opener
    x86isa::sf-spec64$inline-constant-opener
    x86isa::adc-af-spec64$inline-constant-opener
    x86isa::add-af-spec64$inline-constant-opener
    x86isa::sub-af-spec64$inline-constant-opener
    x86isa::sub-cf-spec64-constant-opener
    x86isa::sub-of-spec64-constant-opener
    x86isa::sub-pf-spec64-constant-opener
    x86isa::sub-sf-spec64-constant-opener
    x86isa::sub-zf-spec64-constant-opener

    acl2::bool->bit$inline-constant-opener
;    byte-ify-base
;    x86isa::byte-listp-unroll ;todo: improve (the __function__ put in by define makes this gross)
;    x86isa::byte-listp-base-1

    jo-condition-constant-opener
    jno-condition-constant-opener
    jb-condition-constant-opener
    jnb-condition-constant-opener
    jz-condition-constant-opener
    jnz-condition-constant-opener
    jbe-condition-constant-opener
    jnbe-condition-constant-opener
    js-condition-constant-opener
    jns-condition-constant-opener
    jp-condition-constant-opener
    jnp-condition-constant-opener
    jl-condition-constant-opener
    jnl-condition-constant-opener
    jle-condition-constant-opener
    jnle-condition-constant-opener

    x86isa::one-byte-opcode-modr/m-p$inline-constant-opener
    x86isa::two-byte-opcode-modr/m-p$inline-constant-opener
    ))

(defun get-prefixes-openers ()
  (declare (xargs :guard t ))
  '(x86isa::get-prefixes-base-1
    x86isa::get-prefixes-base-2
    x86isa::get-prefixes-base-3
    x86isa::get-prefixes-base-4
    x86isa::get-prefixes-base-5
    x86isa::get-prefixes-base-6
    x86isa::get-prefixes-base-7
    x86isa::get-prefixes-base-8
    x86isa::get-prefixes-unroll-1
    x86isa::get-prefixes-unroll-2
    x86isa::get-prefixes-unroll-3
    x86isa::get-prefixes-unroll-4
    ;; x86isa::get-prefixes-opener-lemma-no-prefix-byte
    ;; x86isa::get-prefixes-opener-lemma-group-1-prefix-simple
    ;; x86isa::get-prefixes-opener-lemma-group-2-prefix-simple
    ;; x86isa::get-prefixes-opener-lemma-group-3-prefix-simple
    ;; x86isa::get-prefixes-opener-lemma-group-4-prefix-simple
    ))

;todo: separate out the 64 but rules
(defun segment-base-and-bounds-rules ()
  '(segment-base-and-bounds-of-set-rip
    segment-base-and-bounds-of-set-rsp
    segment-base-and-bounds-of-set-rbp
    segment-base-and-bounds-of-set-rax
    segment-base-and-bounds-of-set-rdx
    segment-base-and-bounds-of-set-rsi
    segment-base-and-bounds-of-set-rdi
    segment-base-and-bounds-of-set-flag
    segment-base-and-bounds-of-set-undef
    segment-base-and-bounds-of-write-byte
    segment-base-and-bounds-of-write
    ))

;; are these only for making failures clearer?
(defun get-prefixes-rules64 ()
  (declare (xargs :guard t))
  '(mv-nth-0-of-get-prefixes-of-set-rip
    mv-nth-0-of-get-prefixes-of-set-rax
    mv-nth-0-of-get-prefixes-of-set-rdx
    mv-nth-0-of-get-prefixes-of-set-rsi
    mv-nth-0-of-get-prefixes-of-set-rdi
    mv-nth-0-of-get-prefixes-of-set-rsp
    mv-nth-0-of-get-prefixes-of-set-rbp
    mv-nth-1-of-get-prefixes-of-set-rip
    mv-nth-1-of-get-prefixes-of-set-rax
    mv-nth-1-of-get-prefixes-of-set-rdx
    mv-nth-1-of-get-prefixes-of-set-rsi
    mv-nth-1-of-get-prefixes-of-set-rdi
    mv-nth-1-of-get-prefixes-of-set-rsp
    mv-nth-1-of-get-prefixes-of-set-rbp))

(defun float-rules ()
  (declare (xargs :guard t))
  '(is-nan-intro
    if-of-equal-of-indef-and-is-nan
    if-of-equal-of-qnan-and-is-nan
    if-of-equal-of-snan-and-is-nan
    booleanp-of-is-nan
    not-mv-nth-0-of-sse-cmp
    mxcsrbits->daz-of-bvchop-32
    mxcsrbits->daz-of-ifix
    mxcsrbits->dm-of-bvchop-32
    mxcsrbits->dm-of-ifix
    mxcsrbits->im-of-bvchop-32
    mxcsrbits->im-of-ifix
    mxcsrbits->daz-of-mv-nth-2-of-sse-cmp
    mxcsrbits->dm-of-mv-nth-2-of-sse-cmp
    mxcsrbits->im-of-mv-nth-2-of-sse-cmp
    sse-cmp-of-bvchop-arg2
    sse-cmp-of-bvchop-arg3
    sse-cmp-of-bvchop-arg4
    unsigned-byte-p-of-mv-nth-1-of-sse-cmp-32
    integerp-of-mv-nth-2-of-sse-cmp
    mv-nth-1-of-sse-cmp-of-mv-nth-2-of-sse-cmp
    sse-cmp-of-op-ucomi-same
    x86isa::sse-cmp-base ; when operation and operands are constant
    unsigned-byte-p-of-mv-nth-1-of-sse-cmp-of-OP-UCOMI
    ;; todo: some of these may be more general than just float rules:
    jb-condition-of-bv-if-1-0-1
    jb-condition-of-bv-if-1-1-0
    jnb-condition-of-bv-if-1-0-1
    jnb-condition-of-bv-if-1-1-0
    acl2::bool-fix-of-myif
    boolif-of-myif-arg1-true ; drop
    equal-of-0-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe ;equal-of-0-and-mv-nth-1-of-sse-cmp-of-ucomi
    equal-of-1-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe
    equal-of-7-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe
    not-equal-of-7-and-mv-nth-1-of-sse-cmp
    ))
;; Try to introduce is-nan as soon as possible:
(table axe-rule-priorities-table 'is-nan-intro -1)

;; todo: move some of these to lifter-rules32 or lifter-rules64
;; todo: should this include core-rules-bv (see below)?
(defun lifter-rules-common ()
  (append (acl2::base-rules)
          (acl2::type-rules)
          ;; (acl2::logext-rules) ;;caused problems ;;todo: there are also logext rules below
          ;; trying these, though they are not yet as clean as they could be:
          (acl2::trim-rules)
          (acl2::trim-helper-rules)
          (acl2::unsigned-byte-p-rules)
          (constant-opener-rules)
          (simple-opener-rules)
          (instruction-rules)
          (list-rules-x86)
          (state-rules)
          (if-rules)
          (decoding-and-dispatch-rules)
          (get-prefixes-openers)
          (x86-type-rules)
          (x86-bv-rules)
          (acl2::array-reduction-rules)
          (acl2::unsigned-byte-p-forced-rules)
          (if-lifting-rules)
          (acl2::convert-to-bv-rules)
          '(ACL2::BOOLOR-OF-NON-NIL)
          (segment-base-and-bounds-rules) ; I've seen these needed for 64-bit code
          (float-rules)
          ;;(acl2::core-rules-bv) ;acl2::not-equal-max-int-when-<= not defined
          '(
            ;; Reading/writing registers (or parts of registers).  We leave
            ;; these enabled to expose rgfi and !rgfi, which then get rewritten
            ;; to xr and xw.  Shilpi seems to do the same.
            x86isa::rr08$inline
            x86isa::rr16$inline
            x86isa::rr32$inline
            x86isa::rr64$inline
            x86isa::wr08$inline
            x86isa::wr16$inline
            x86isa::wr32$inline
            x86isa::wr64$inline
            x86isa::rgfi-size$inline ;dispatches to rr08, etc.
            x86isa::!rgfi-size$inline ; dispatches to wr08, etc.
            x86isa::rgfi X86ISA::RGFI$A ;expose the call to xr
            x86isa::!rgfi X86ISA::!RGFI$A ;expose the call to xw

            ;; Chopping operators (these are just bvchop):
            x86isa::n01$inline
            x86isa::n03$inline
            x86isa::n06$inline
            x86isa::n08$inline
            x86isa::n16$inline
            x86isa::n32$inline
            x86isa::n64$inline

            ;; This is just logext:
            x86isa::i64$inline

            ;; These are just logext:
            x86isa::n08-to-i08$inline
            x86isa::n16-to-i16$inline
            x86isa::n32-to-i32$inline
            x86isa::n64-to-i64$inline         ;shilpi leaves this enabled
            x86isa::n128-to-i128$inline

            ;; These turn jcc/cmovcc/setcc-spec into more specialized forms,
            ;; which can be either opened or, for some, turned into better
            ;; tests.
            jcc/cmovcc/setcc-spec-rewrite-jo
            jcc/cmovcc/setcc-spec-rewrite-jno
            jcc/cmovcc/setcc-spec-rewrite-jb
            jcc/cmovcc/setcc-spec-rewrite-jnb
            jcc/cmovcc/setcc-spec-rewrite-jz
            jcc/cmovcc/setcc-spec-rewrite-jnz
            jcc/cmovcc/setcc-spec-rewrite-jbe
            jcc/cmovcc/setcc-spec-rewrite-jnbe
            jcc/cmovcc/setcc-spec-rewrite-js
            jcc/cmovcc/setcc-spec-rewrite-jns
            jcc/cmovcc/setcc-spec-rewrite-jp
            jcc/cmovcc/setcc-spec-rewrite-jnp
            jcc/cmovcc/setcc-spec-rewrite-jl
            jcc/cmovcc/setcc-spec-rewrite-jnl
            jcc/cmovcc/setcc-spec-rewrite-jle
            jcc/cmovcc/setcc-spec-rewrite-jnle

            ;; Rules to introduce our BV operators:
            x86isa::part-select-width-low-becomes-slice

            ;; State component read-over-write rules:
;            x86isa::xr-set-flag ;this is the -diff rule

            ;; Flags:
            x86isa::sub-af-spec32-same ; rewrites to 0, so perhaps worth including this rule

            ;; todo: organize these:

            x86isa::app-view-of-xw
            app-view-of-set-flag

            x86isa::separate-normalize-r-w-x-1
            x86isa::separate-normalize-r-w-x-2
            x86isa::not-separate-self
            x86isa::separate-of-plus
            x86isa::separate-of-plus-alt
            x86isa::separate-below-and-above
            x86isa::separate-below-and-above-alt
            x86isa::separate-lemma-1
            x86isa::separate-lemma-1-alt
            x86isa::separate-lemma-1b
            x86isa::separate-lemma-1b-alt
            x86isa::separate-lemma-2b
            x86isa::separate-lemma-2b-alt
            x86isa::separate-lemma-3
            x86isa::separate-lemma-3-alt
            x86isa::separate-of-if-arg3
            x86isa::separate-of-if-arg6
            x86isa::separate-below-and-above-offset
            x86isa::separate-below-and-above-offset-alt
            x86isa::separate-same-lemma-1
            x86isa::separate-same-lemma-1-alt
            x86isa::separate-from-separate-lemma-1
            x86isa::separate-from-separate-lemma-1b
            x86isa::separate-from-separate-lemma-1c
            x86isa::separate-from-separate-lemma-1d
            x86isa::separate-from-separate-lemma-1-alt
            x86isa::separate-from-separate-lemma-1b-alt
            x86isa::separate-from-separate-lemma-1c-alt
            x86isa::separate-from-separate-lemma-1d-alt
            ;; these 2 may subsume much of the stuff above:
            x86isa::separate-when-separate
            x86isa::separate-when-separate-alt
            ;; these may be expensive but seem necessary in some cases
            ;; todo: led to a loop involving BECOMES-BVLT-DAG-ALT-GEN-BETTER2.
            ;x86isa::not-equal-when-separate
            ;x86isa::not-equal-when-separate-alt

            x86isa::rb-wb-equal
            x86isa::rb-of-if-arg2

;            x86isa::set-flag-of-mv-nth-1-of-wb

            return-last
            ;; symbolic execution (perhaps separate these out):
            run-until-return
            run-until-stack-shorter-than-opener
            run-until-stack-shorter-than-base
            stack-shorter-thanp

            ;; x86-fetch-decode-execute-opener ; this had binding hyps
            ;; x86-fetch-decode-execute ; this splits into too many cases when things can't be resolved
            x86isa::x86-fetch-decode-execute-base

            ms x86isa::ms$a                            ;expose the call to xr
            fault x86isa::fault$a                         ;expose the call to xr
            ;x86isa::rip
            ;x86isa::rip$a                           ;expose the call to xr
;            app-view$inline         ;expose the call to xr

            the-check
            ;; get-prefixes:
            ;; todo: drop these if we are no longer using xw:
            x86isa::get-prefixes-does-not-modify-x86-state-in-app-view-new ;targets mv-nth-3-of-get-prefixes
            x86isa::mv-nth-0-of-get-prefixes-of-xw-of-irrel
            x86isa::mv-nth-1-of-get-prefixes-of-xw-of-irrel

            x86isa::mv-nth-of-cons ;mv-nth ;or do mv-nth of cons.  rules like rb-in-terms-of-nth-and-pos-eric target mv-nth

            x86isa::canonical-address-p-of-logext-48
            x86isa::logext-48-does-nothing-when-canonical-address-p

            x86isa::create-canonical-address-list-1

            x86isa::rb-in-terms-of-nth-and-pos-eric-gen ;rb-in-terms-of-nth-and-pos-eric ;targets mv-nth-1-of-rb
            x86isa::rb-returns-no-error-app-view ;targets mv-nth-0-of-rb
            x86isa::rb-returns-x86-app-view ;targets mv-nth-2-of-rb

            x86isa::canonical-address-listp-of-cons
            x86isa::canonical-address-listp-of-nil ;wouldn't need this if we could evaluate it
            x86isa::member-p-of-create-canonical-address-list-same
            x86isa::canonical-address-listp-create-canonical-address-list
            x86isa::pos-and-create-canonical-address-list

            inverse-of-+
            x86isa::combine-bytes-when-singleton

            x86isa::get-one-byte-prefix-array-code-rewrite-quotep ;;get-one-byte-prefix-array-code ;this is applied to a constant (the function is gross because it uses an array)


            part-install-width-low-becomes-bvcat-axe
            x86isa::car-create-canonical-address-list
            ;;canonical-address-p-between ;this is involved in loops (other rules backchain from < to canonical-addressp but this does the reverse)
            ;;will axe try all free variable matches?
            x86isa::canonical-address-p-between-special1
            x86isa::canonical-address-p-between-special2
            x86isa::canonical-address-p-between-special3
            x86isa::canonical-address-p-between-special4

            acl2::<-of-+-cancel-2-2
            acl2::<-of-+-cancel-2-1
            acl2::integerp-of-+-when-integerp-1-cheap
            acl2::fix-when-integerp
            x86isa::integerp-when-canonical-address-p-cheap
            x86isa::member-p-canonical-address-listp
            acl2::fold-consts-in-+
            acl2::<-of-+-cancel-2-1
            ash-negative-becomes-slice-axe

            ;;one-byte-opcode-execute ;shilpi leaves this enabled, but it seems dangerous
            x86isa::one-byte-opcode-execute-base
            eql

            acl2::binary-+-bring-constant-forward ;improve to disallow the other arg to be constant

            x86isa::reg-index$inline ;not sure what this is, maybe restrict to ground terms?
            acl2::logbitp-to-getbit-equal-1

            associativity-of-+
            x86isa::integerp-of-xr-rgf
            x86isa::wb-returns-no-error-app-view ;targets mv-nth 0 of wb
;            addr-byte-alistp-create-addr-bytes-alist
;            byte-listp-byte-ify
            x86isa::!rip x86isa::!rip$a          ;expose xw
            x86isa::xr-of-xw-diff
            ;;x86isa::xr-xw-intra-simple-field
            ;;x86isa::xr-xw-intra-array-field
            X86ISA::XR-OF-XW-INTRA-FIELD
            X86ISA::XR-OF-XW-INTER-FIELD
            acl2::<-of-+-cancel-1-2
            x86isa::program-at-xw-in-app-view
            x86isa::xr-app-view-mv-nth-1-wb ;has a hyp of t
            x86isa::program-at-wb-disjoint
;            strip-cars-of-create-addr-bytes-alist
            x86isa::true-listp-create-canonical-address-list
            x86isa::len-of-create-canonical-address-list
;            len-of-byte-ify ;can we drop the integerp hyp?

            x86isa::signed-byte-p-64-when-canonical-address-p-cheap ;i guess axe ignores the backchain-limit-lst ;might loop (but maybe not anymore)?
            x86isa::xr-wb-in-app-view ;targets xr-of-mv-nth-1-of-wb
            x86isa::x86-decode-sib-p               ;restrict to ground terms?
            x86isa::x86-operand-to-reg/mem         ;shilpi leaves this enabled
            x86isa::mv-nth-becomes-nth-when-constants
            x86isa::canonical-address-p-becomes-signed-byte-p-when-constant
            acl2::distributivity-of-minus-over-+
            acl2::commutativity-2-of-+-when-constant

            acl2::signed-byte-p-of-logext
;these deal with instruction semantics?:

            x86isa::x86-effective-addr
            x86isa::x86-effective-addr-32/64
            x86isa::x86-effective-addr-from-sib

            x86isa::trunc$inline        ;shilpi leaves this enabled

            acl2::backchain-signed-byte-p-to-unsigned-byte-p-non-const
            acl2::slice-of-logext
            x86isa::alignment-checking-enabled-p-and-xw
            x86isa::alignment-checking-enabled-p-and-wb-in-app-view ;targets mv-nth-1-of-wb
            logand-becomes-bvand-axe-arg1-axe
            logand-becomes-bvand-axe-arg2-axe
            acl2::unicity-of-0         ;introduces a fix
            acl2::ash-of-0
            acl2::fix-when-acl2-numberp
            acl2::acl2-numberp-of-+    ;we also have acl2::acl2-numberp-of-sum
            x86isa::mv-nth-1-rb-xw-rip         ;targets mv-nth-1-of-rb
            x86isa::mv-nth-1-rb-xw-rgf         ;targets mv-nth-1-of-rb
            x86isa::rb-wb-disjoint-eric
            x86isa::disjoint-p-two-create-canonical-address-lists-thm-1
            x86isa::rb-wb-subset
            x86isa::subset-p-two-create-canonical-address-lists-same-base-address
            x86isa::canonical-address-p-of-logext-64
            ;;x86isa::xw-xw-intra-array-field-shadow-writes
            ;;x86isa::xw-xw-intra-simple-field-shadow-writes
            X86ISA::XW-XW-SHADOW-WRITES
            x86isa::xw-xw-inter-field-arrange-writes ;axe puts in a loop-stopper hyp
            x86isa::xw-xw-intra-field-arrange-writes ;axe puts in a loop-stopper hyp
;            assoc-list-of-rev-of-create-addr-bytes-alist
;            true-listp-of-byte-ify
            x86isa::no-duplicates-p-create-canonical-address-list
            acl2::slice-becomes-bvchop
            acl2::bvchop-of-bvchop
            acl2::bvchop-of-bvplus
            acl2::bvchop-identity
;            combine-bytes-and-byte-ify
            acl2::open-ash-positive-constants
            acl2::logext-of-bvchop-same
            acl2::logext-identity
            ;x86isa::rgfi-is-i64p ;targets signed-byte-of-xr
;            x86isa::xw-xr-same
            ;; acl2::bvplus-commutative-axe ;is this based on nodenum or term weight?

            x86isa::select-operand-size$inline ;shilpi leaves this enabled (could restrict to ground terms)
            x86isa::select-segment-register$inline
            x86isa::x86-operand-from-modr/m-and-sib-bytes
            x86isa::write-user-rflags-rewrite ;x86isa::write-user-rflags$inline ;shilpi leaves this enabled

            x86isa::check-instruction-length$inline

            acl2::bvchop-of-bvcat-cases
            acl2::slice-becomes-getbit
            acl2::getbit-of-bvcat-all
            ;; x86isa::program-at-set-flag
            ;; x86isa::alignment-checking-enabled-p-and-set-flag

;            x86isa::rb-set-flag-in-app-view
            acl2::getbit-of-slice-both

            acl2::bvplus-of-bvchop-arg2 ; drop, once we include core-rules-bv
            acl2::bvplus-of-bvchop-arg3 ; drop, once we include core-rules-bv
;            x86isa::set-flag-and-wb-in-app-view ;shilpi leaves this enabled

            acl2::getbit-identity ;might be slow
            acl2::getbit-of-if-two-constants ;this caused the execution to split? (or maybe not?)

            acl2::unsigned-byte-p-of-if-two-constants

            ;; stuff from the timessix example:
            acl2::bvchop-of-logext
            acl2::getbit-of-bvchop

            x86isa::canonical-address-p-becomes-signed-byte-p-when-constant
            x86isa::disjoint-p-cons-1 ;restrict to a singleton?
            x86isa::disjoint-p-nil-1
            x86isa::not-member-p-canonical-address-listp-when-disjoint-p
; looped! not-member-p-canonical-address-listp-when-disjoint-p-alt
            x86isa::not-memberp-of-+-when-disjoint-from-larger-chunk
            acl2::bvplus-of-logext
            acl2::bvplus-combine-constants
            x86isa::<-of-logext-and-bvplus-of-constant
;<-when-canonical-address-p

            acl2::logext-of-bvplus-64 ; a bit scary (instead, see todo #1 above)

            x86isa::disjoint-of-create-canonical-address-list-and-create-canonical-address-list-stack-and-text
            x86isa::write-canonical-address-to-memory
            x86isa::canonical-address-listp-of-cdr
            x86isa::car-create-canonical-address-list
            x86isa::cdr-create-canonical-address-list
            x86isa::combine-bytes-unroll
            x86isa::combine-bytes-base
            logior-becomes-bvor-axe
            x86isa::if-of-xr-app-view
            x86isa::disjoint-of-create-canonical-address-list-and-create-canonical-address-list-stack-and-text-special

;            x86isa::set-flag-undefined$inline ;trying this..
;            x86isa::xr-set-flag-undefined
 ;           x86isa::program-at-set-flag-undefined
            x86isa::mv-nth-1-rb-xw-rgf
;xr-rgf-mv-nth-2-rb
;xr-app-view-mv-nth-2-rb

;signed-byte-p-when-between-canonical-addresses
;            x86isa::x86p-of-set-flag-undefined-eric ;x86p-of-set-flag-undefined ;drop?
;            x86isa::alignment-checking-enabled-p-and-set-flag-undefined ;drop?
;            x86isa::rb-set-flag-undefined-in-app-view ;drop?


            x86isa::<-of-logext-and-+-of-constant
            x86isa::canonical-address-p-+-signed-byte-p-16-is-signed-byte-p-64 ;looped
            x86isa::<-when-canonical-address-p-impossible
;                    canonical-address-p-of-+-when-canonical-address-p-of-+ ;has a natp hyp that is problematic ;todo: drop?
;                    canonical-address-p-of-+-when-canonical-address-p-of-+-alt ;todo: drop?
            ;;signed-byte-p-of-+-between

            acl2::logext-of-+-of-constant
;            x86isa::alignment-checking-enabled-p-and-set-flag
            x86isa::unsigned-byte-p-of-bool->bit
;            x86isa::set-flag-of-set-flag-undefined-different-concrete-indices ;drop?

            x86isa::undef-flg$notinline
            x86isa::undef-flg-logic
            x86isa::undef-read$notinline
            x86isa::undef-read-logic
            x86isa::!undef x86isa::!undef$a

            x86isa::mv-nth-1-rb-xw-undef
            x86isa::wb-xw-in-app-view
            x86isa::undef x86isa::undef$a
            acl2::bvchop-of-*
            acl2::bvchop-of-bvmult
            acl2::bvmult-of-logext-gen-arg1
            acl2::bvmult-of-logext-gen-arg2
            acl2::bvchop-of-ash
            acl2::nfix-does-nothing
            acl2::natp-of-+
            acl2::natp-of-nfix
            ;;introduce-read64 ; does this mess up our normal form? need some rules about it!  also need to apply this to the assumptions if we use it here
            acl2::bvmult-commutative-axe
            acl2::bvmult-of-bvcat-of-0
            acl2::bvmult-of-bvchop-arg3

            x86isa::disjoint-p-two-create-canonical-address-lists-thm-0-gen
            x86isa::disjoint-p-two-create-canonical-address-lists-thm-1-gen
            x86isa::not-memberp-of-+-when-disjoint-from-larger-chunk-pos ;only needed for pe file?

            acl2::bvplus-of-unary-minus
            acl2::bvplus-of-logext-arg1
            acl2::bvplus-of-logext
            acl2::slice-of-bvchop-low
            x86isa::rflags x86isa::rflags$a ;exposes xr
;            x86isa::rflags-set-flag ;targets xr-of-set-flag ;drop?
            x86isa::part-install-width-low-becomes-bvcat-32
            x86isa::rflags-is-n32p-unforced
             ;targets unsigned-byte-p-of-rflags
;                    acl2::bvcat-trim-arg4-axe-all
 ;                   acl2::bvcat-trim-arg2-axe-all

            x86isa::64-bit-modep-of-xw
            x86isa::64-bit-modep-of-mv-nth-1-of-wb
            x86isa::64-bit-modep-of-set-flag

            ;;todo: include all of the lifter rules:
            x86isa::canonical-address-p-of-i48
            x86isa::i48-when-canonical-address-p
            x86isa::select-address-size$inline
            x86isa::mv-nth-of-if
            x86isa::canonical-address-p-of-if
            read-in-terms-of-nth-and-pos-eric-2-bytes
            read-in-terms-of-nth-and-pos-eric-4-bytes
            read-in-terms-of-nth-and-pos-eric-8-bytes

            ;; nice rules: fixme: add the rest!
            jb-condition-of-sub-cf-spec8
            jb-condition-of-sub-cf-spec16
            jb-condition-of-sub-cf-spec32
            jb-condition-of-sub-cf-spec64
            jnb-condition-of-sub-cf-spec8
            jnb-condition-of-sub-cf-spec16
            jnb-condition-of-sub-cf-spec32
            jnb-condition-of-sub-cf-spec64
            jbe-condition-of-sub-cf-spec8-and-sub-zf-spec8
            jbe-condition-of-sub-cf-spec16-and-sub-zf-spec16
            jbe-condition-of-sub-cf-spec32-and-sub-zf-spec32
            jbe-condition-of-sub-cf-spec64-and-sub-zf-spec64
            jnbe-condition-of-sub-cf-spec8-and-sub-zf-spec8
            jnbe-condition-of-sub-cf-spec16-and-sub-zf-spec16
            jnbe-condition-of-sub-cf-spec32-and-sub-zf-spec32
            jnbe-condition-of-sub-cf-spec64-and-sub-zf-spec64
            jl-condition-of-sub-sf-spec8-and-sub-of-spec8
            jl-condition-of-sub-sf-spec16-and-sub-of-spec16
            jl-condition-of-sub-sf-spec32-and-sub-of-spec32
            jl-condition-of-sub-sf-spec64-and-sub-of-spec64
            jnl-condition-of-sub-sf-spec8-and-sub-of-spec8-same
            jnl-condition-of-sub-sf-spec16-and-sub-of-spec16-same
            jnl-condition-of-sub-sf-spec32-and-sub-of-spec32-same
            jnl-condition-of-sub-sf-spec64-and-sub-of-spec64-same
            jle-condition-of-sub-zf-spec8-and-sub-sf-spec8-and-sub-of-spec8
            jle-condition-of-sub-zf-spec16-and-sub-sf-spec16-and-sub-of-spec16
            jle-condition-of-sub-zf-spec32-and-sub-sf-spec32-and-sub-of-spec32
            jle-condition-of-sub-zf-spec64-and-sub-sf-spec64-and-sub-of-spec64
            jnle-condition-of-sub-zf-spec8-and-sub-sf-spec8-and-sub-of-spec8
            jnle-condition-of-sub-zf-spec16-and-sub-sf-spec16-and-sub-of-spec16
            jnle-condition-of-sub-zf-spec32-and-sub-sf-spec32-and-sub-of-spec32
            jnle-condition-of-sub-zf-spec64-and-sub-sf-spec64-and-sub-of-spec64
            jz-condition-of-zf-spec
            jz-condition-of-sub-zf-spec8
            jz-condition-of-sub-zf-spec16
            jz-condition-of-sub-zf-spec32
            jz-condition-of-sub-zf-spec64
            jnz-condition-of-zf-spec
            jnz-condition-of-sub-zf-spec8
            jnz-condition-of-sub-zf-spec16
            jnz-condition-of-sub-zf-spec32
            jnz-condition-of-sub-zf-spec64
            js-condition-of-sub-sf-spec8
            js-condition-of-sub-sf-spec16
            js-condition-of-sub-sf-spec32
            js-condition-of-sub-sf-spec64
            jns-condition-of-sub-sf-spec8
            jns-condition-of-sub-sf-spec16
            jns-condition-of-sub-sf-spec32
            jns-condition-of-sub-sf-spec64
            ;;if-of-jz-condition-and-1-and-0
            ;;if-of-jnz-condition-and-1-and-0
            ;;jz-condition-of-if-of-1-and-0
            ;;jnbe-condition-of-BOOL->BIT-of-<-of-bvchop-and-ZF-SPEC-of-bvplus-of-bvuminus

            ;todo: drop some of these?
            jz-condition-of-bvif-1-0-1
            jz-condition-of-bvif-1-1-0
            jnz-condition-of-bvif-1-0-1
            jnz-condition-of-bvif-1-1-0
            jp-condition-of-bvif-1-0-1
            jp-condition-of-bvif-1-1-0
            jnp-condition-of-bvif-1-0-1
            jnp-condition-of-bvif-1-1-0
            jbe-condition-of-bvif-1-arg1
            jbe-condition-of-bvif-1-arg2
            jnbe-condition-of-bvif-1-arg1
            jnbe-condition-of-bvif-1-arg2

            ;; can we get rid of these?:
            ;; jle-condition-rewrite-1
            ;; jle-condition-rewrite-2
            ;; jle-condition-rewrite-3
            ;; jnle-condition-rewrite
            ;; jnle-condition-rewrite-2
            ;; jnle-condition-rewrite-2-alt
            ;; jnle-condition-rewrite-3-32
            ;; jnl-condition-rewrite-1
            ;; jnl-condition-rewrite-1-32
            ;; jnl-condition-rewrite-1-32-constant-version
            ;; jnle-condition-rewrite-3
            ;; jnz-condition-rule-2

            x86isa::memory-byte-accesses-are-always-aligned
            x86isa::address-aligned-p-of-8-and-nil
            x86isa::address-aligned-p-of-4-and-nil

            acl2::bvplus-trim-leading-constant
            acl2::bvplus-of-0-arg2
            acl2::bvchop-subst-constant
            x86isa::byte-listp-becomes-all-unsigned-byte-p
            acl2::lnfix$inline
            gl::gl-mbe-fn ;used by bitops.  yuck.

            x86isa::x86-operation-mode
            x86isa::alignment-checking-enabled-p-of-xw-irrel
            acl2::slice-of-bvcat-gen
            /= ;"not equal"

            acl2::truncate-becomes-floor-gen ;it might be better to avoid explosing truncate in the first place

            acl2::<-of-constant-when-<-of-constant-integer
            acl2::<-of-constant-when-<=-of-constant-integer
            acl2::bvplus-of-+-combine-constants

            common-lisp::logcount-constant-opener ; for flags
            common-lisp::evenp-constant-opener ; appears in parity flag
            acl2::nonnegative-integer-quotient-constant-opener ; appears in parity flag
            acl2::zip-constant-opener ; for flags

            X86ISA::X86-ELEM-FIX ;new
            X86ISA::ELEM-P-OF-XR-RGF
            SEG-HIDDEN-ATTRI
            X86ISA::SEG-HIDDEN-ATTRI$A
            SEG-HIDDEN-baseI
            x86isa::SEG-HIDDEN-baseI$A
            SEG-HIDDEN-LIMITI
            x86isa::SEG-HIDDEN-LIMITI$A
            X86ISA::!MS
            X86ISA::!MS$a

            acl2::bv-array-read-shorten-axe
            acl2::integerp-of-if-strong
            )))

;; This needs to fire before bvplus-convert-arg3-to-bv-axe to avoid loops on things like (bvplus 32 k (+ k (esp x86))).
;; Note that bvplus-of-constant-and-esp-when-overflow will turn a bvplus into a +.
(table axe-rule-priorities-table 'acl2::bvplus-of-+-combine-constants -1)

;; Not needed?:
;; (table axe-rule-priorities-table 'x86isa::separate-when-separate -1)
;; (table axe-rule-priorities-table 'x86isa::separate-when-separate-alt -1)

;; note: mv-nth-1-wb-and-set-flag-commute loops with set-flag-and-wb-in-app-view

;; Used in both versions of the lifter
;; TODO: Split into 32-bit and 64-bit rules:
(defun assumption-simplification-rules ()
  (append
   '(standard-state-assumption
     standard-assumptions-core-64
     standard-state-assumption-32
     standard-assumptions-mach-o-64
     standard-assumptions-elf-64
     standard-assumptions-pe-64
     bytes-loaded-at-address-64
     ;; Mach-O stuff:
     acl2::get-mach-o-code
     acl2::subroutine-address-mach-o
     acl2::get-mach-o-symbol-table
     acl2::get-mach-o-code-address
     acl2::get-mach-o-section-base-1
     acl2::get-mach-o-section-base-2
     acl2::get-mach-o-section-unroll
     acl2::get-mach-o-segment-base-1
     acl2::get-mach-o-segment-base-2
     acl2::get-mach-o-segment-unroll-1
     acl2::get-mach-o-segment-unroll-2
     acl2::get-symbol-entry-mach-o-base-1
     acl2::get-symbol-entry-mach-o-base-2
     acl2::get-symbol-entry-mach-o-unroll
     acl2::get-text-section-number-mach-o
     acl2::get-all-sections-from-mach-o
     acl2::get-all-sections-from-mach-o-load-commands-base
     acl2::get-all-sections-from-mach-o-load-commands-unroll
     acl2::get-all-sections-from-mach-o-load-command
     acl2::get-section-number-mach-o
     acl2::get-section-number-mach-o-aux-base-1
     acl2::get-section-number-mach-o-aux-base-2
     acl2::get-section-number-mach-o-aux-unroll
     acl2::get-mach-o-load-command-base-1
     acl2::get-mach-o-load-command-base-2
     acl2::get-mach-o-load-command-unroll
     ;; PE stuff:
     acl2::get-pe-sections
     acl2::get-pe-section
     acl2::get-pe-text-section
     acl2::get-pe-section-info-bytes
     acl2::get-pe-text-section-bytes
     acl2::get-pe-section-aux-base-1
     acl2::get-pe-section-aux-base-2
     acl2::get-pe-section-aux-unroll
     acl2::lookup-pe-symbol-base-1
     acl2::lookup-pe-symbol-base-2
     acl2::lookup-pe-symbol-unroll
     acl2::subroutine-address-within-text-section-pe-64
     ;; ELF stuff:
     acl2::lookup-equal-safe
     acl2::subroutine-address-elf
     acl2::get-elf-symbol-table
     acl2::get-elf-section-address
     acl2::get-elf-section-bytes
     acl2::get-elf-code
     acl2::get-elf-code-address
     acl2::get-elf-section-header-base-1
     acl2::get-elf-section-header-base-2
     acl2::get-elf-section-header-unroll
     acl2::get-elf-symbol-address-base-1
     acl2::get-elf-symbol-address-base-2
     acl2::get-elf-symbol-address-unroll

     ;;     read64
;     read-becomes-mv-nth-1-of-rb
     acl2::equal-of-0-and-mod ;acl2::mod-=-0 ;yuck
;     app-view$inline
     rml64
     x86isa::mv-nth-of-if
     x86isa::mv-nth-of-cons
     x86isa::canonical-address-p-of-if
     the-check
     acl2::lookup-eq-safe
     eql
     acl2::+-commutative-axe
     unicity-of-0
     ;; all-addreses-of-stack-slots
     ms X86ISA::ms$A
     fault X86ISA::fault$A
     rgfi X86ISA::RGFI$A ;expose xr
     x86isa::canonical-address-p$inline-constant-opener
     addresses-of-subsequent-stack-slots
     ;; addresses-of-subsequent-stack-slots-aux-base
     ;; addresses-of-subsequent-stack-slots-aux-unroll
     canonical-address-listp-of-addresses-of-subsequent-stack-slots-aux
     x86isa::canonical-address-listp-of-cons
     x86isa::canonical-address-p-between-special1
     x86isa::canonical-address-p-between-special2
     x86isa::canonical-address-p-between-special3
     acl2::fold-consts-in-+
     x86isa::canonical-address-listp-of-nil
     acl2::integerp-of-+-when-integerp-1-cheap
     x86isa::integerp-of-xr-rgf-4
     x86isa::fix-of-xr-rgf-4)
   (acl2::lookup-rules)))

;move?
(defun myif-rules ()
  (append '(acl2::myif-same-branches ;add to lifter-rules?
            acl2::myif-of-t-and-nil-when-booleanp
            acl2::myif-nil-t
            ;; acl2::boolif-of-nil-and-t ;redundant?
            )
          (acl2::boolean-rules)
          ;; '(acl2::boolif-x-x-y-becomes-boolor
          ;; acl2::boolif-x-y-x-becomes-booland
          ;; acl2::boolif-same-branches
          ;; acl2::boolif-when-quotep-arg1
          ;; acl2::boolif-when-quotep-arg2
          ;; acl2::boolif-when-quotep-arg3)
          ))

;; todo: move some of these to lifter-rules-common
(defun lifter-rules32 ()
  (append (lifter-rules-common)
          '(x86isa::rip ; todo: think about this
            x86isa::rip$a ; todo: think about this
            ;; x86isa::get-prefixes-opener-lemma-group-1-prefix-simple-32
            ;; x86isa::get-prefixes-opener-lemma-group-2-prefix-simple-32
            ;; x86isa::get-prefixes-opener-lemma-group-3-prefix-simple-32
            ;; x86isa::get-prefixes-opener-lemma-group-4-prefix-simple-32
            ;; x86isa::segment-base-and-bounds$inline ;todo: give a nicer body ;; trying to keep this closed
            acl2::bvplus-when-equal-of-constant-and-bvchop-arg3
            ;; wb-is-wb-1-for-app-view
            x86isa::i48$inline
            x86isa::<-of-if-arg2
            acl2::<-of-if-arg1
            x86isa::mv-nth-of-if
            x86isa::if-of-if-of-nil-and-consp
            acl2::ubp-longer-better
            x86isa::canonical-address-p-when-unsigned-byte-p
            x86isa::canonical-address-p-of-sum-when-unsigned-byte-p-32
            acl2::collect-constants-over-<-2
            acl2::<-of-negative-when-usbp
            x86isa::canonical-address-p-of-if
            acl2::<-becomes-bvlt-axe-both
            acl2::bvlt-of-bvplus-constant-and-constant-other
            acl2::bvlt-transitive-4-a
            acl2::bvlt-transitive-4-b
            acl2::bvlt-transitive-3-a
            acl2::bvlt-transitive-3-b
            acl2::bvlt-transitive-2-a
            acl2::bvlt-transitive-2-b
            acl2::bvlt-transitive-1-a
            acl2::bvlt-transitive-1-b
            acl2::collect-constants-over-<
            acl2::bvlt-of-bvplus-constant-and-constant-safe2
            acl2::<-of-bvplus-same-gen
            bvle
            acl2::+-of-bvplus-of-x-and-minus-x
            acl2::<-of-minus-and-constant
            acl2::equal-of-constant-when-bvlt-constant-1
            acl2::equal-of-constant-when-bvlt-constant-2
            acl2::acl2-numberp-when-unsigned-byte-p
            acl2::integerp-when-unsigned-byte-p-free
            x86isa::32-bit-mode-one-byte-opcode-modr/m-p-rewrite-quotep
            code-segment-readable-bit-of-xw-irrel
            code-segment-readable-bit-of-set-flag
            code-segment-readable-bit-of-write-byte-to-segment
            code-segment-readable-bit-of-write-to-segment
            code-segment-readable-bit-of-set-eip
            code-segment-readable-bit-of-set-eax
            code-segment-readable-bit-of-set-ebx
            code-segment-readable-bit-of-set-ecx
            code-segment-readable-bit-of-set-edx
            code-segment-readable-bit-of-set-esp
            code-segment-readable-bit-of-set-ebp
            data-segment-writeable-bit-of-xw-irrel
            data-segment-writeable-bit-of-set-flag
            data-segment-writeable-bit-of-write-byte-to-segment
            data-segment-writeable-bit-of-write-to-segment
            data-segment-writeable-bit-of-set-eip
            data-segment-writeable-bit-of-set-eax
            data-segment-writeable-bit-of-set-ebx
            data-segment-writeable-bit-of-set-ecx
            data-segment-writeable-bit-of-set-edx
            data-segment-writeable-bit-of-set-esp
            data-segment-writeable-bit-of-set-ebp
            code-segment-descriptor-attributesbits->r-of-bvchop
            data-segment-descriptor-attributesbits->w-of-bvchop
            data-segment-descriptor-attributesbits->e-of-bvchop
            data-segment-descriptor-attributesbits->d/b-of-bvchop

            seg-visible-not-equal-0-when-well-formed-32-bit-segmentp

            segment-base-and-bounds-of-set-eip
            segment-base-and-bounds-of-set-eax
            segment-base-and-bounds-of-set-ebx
            segment-base-and-bounds-of-set-ecx
            segment-base-and-bounds-of-set-edx
            segment-base-and-bounds-of-set-esp
            segment-base-and-bounds-of-set-ebp

            segment-base-and-bounds-of-write-to-segment
            segment-base-and-bounds-of-write-byte-to-segment
            x86isa::segment-base-and-bounds-of-xw
            segment-base-and-bounds-of-set-flag
            esp-of-write-to-segment

            ;; These are not strictly necessary but can help make failures more
            ;; clear / smaller:
            x86isa::mv-nth-0-of-rme-size-of-xw-when-app-view
            ;; todo: make 64-bit versions of these:
            mv-nth-0-of-rme-size-of-set-eip-when-app-view
            mv-nth-0-of-rme-size-of-set-esp-when-app-view
            mv-nth-0-of-rme-size-of-set-ebp-when-app-view
            mv-nth-0-of-rme-size-of-set-eax-when-app-view
            mv-nth-0-of-rme-size-of-set-ebx-when-app-view
            mv-nth-0-of-rme-size-of-set-ecx-when-app-view
            mv-nth-0-of-rme-size-of-set-edx-when-app-view
            mv-nth-1-of-rme-size-of-set-eip-when-app-view
            mv-nth-1-of-rme-size-of-set-esp-when-app-view
            mv-nth-1-of-rme-size-of-set-ebp-when-app-view
            mv-nth-1-of-rme-size-of-set-eax-when-app-view
            mv-nth-1-of-rme-size-of-set-ebx-when-app-view
            mv-nth-1-of-rme-size-of-set-ecx-when-app-view
            mv-nth-1-of-rme-size-of-set-edx-when-app-view

            write-to-segment-of-set-eip
            write-byte-to-segment-of-set-eip

            if-of-if-of-cons-and-nil
            )))

;; new batch of rules for the more abstract lifter (but move some of these elsewhere):
(defun lifter-rules32-new ()
  '(
    ACL2::BVCHOP-NUMERIC-BOUND
;    not-mv-nth-0-of-ea-to-la-of-cs
    not-mv-nth-0-of-rme08
    not-mv-nth-0-of-rme16

    return-address-okp-intro

    ;; Rules about writing:
    not-mv-nth-0-of-wme-size ;gets rid of error branch
    mv-nth-1-of-wme-size     ;introduces write-to-segment

    ;; Rules about reading:
    not-mv-nth-0-of-rme-size$inline ;; gets rid of error branch
    mv-nth-2-of-rme-size$inline ;; shows that reading does not change the state
    not-mv-nth-0-of-rime-size$inline ;; gets rid of error branch
    mv-nth-2-of-rime-size$inline ;; shows that reading does not change the state

    ;; Rules to introduce read-from-segment:
    mv-nth-1-of-rme08-becomes-read-from-segment
    mv-nth-1-of-rme16-becomes-read-from-segment
    mv-nth-1-of-rme-size$inline-becomes-read-from-segment
    mv-nth-1-of-rime-size$inline-becomes-read-from-segment-1
    mv-nth-1-of-rime-size$inline-becomes-read-from-segment-2
    mv-nth-1-of-rime-size$inline-becomes-read-from-segment-4
    mv-nth-1-of-rime-size$inline-becomes-read-from-segment-8
;    read-of-mv-nth-1-of-ea-to-la-becomes-read-from-segment

    ;; Type rules for read-from-segment:
    read-from-segment-not-negative
    unsigned-byte-p-of-read-from-segment
    integerp-of-read-from-segment

    ;; Read-over-write rules for read-from-segment:
    read-from-segment-of-write-to-segment-same
    read-from-segment-of-write-to-segment-irrel
    read-from-segment-of-write-to-segment-diff-segments
    read-from-segment-of-set-eip
    read-from-segment-of-set-eax
    read-from-segment-of-set-ebx
    read-from-segment-of-set-ecx
    read-from-segment-of-set-edx
    read-from-segment-of-set-esp
    read-from-segment-of-set-ebp
    read-from-segment-of-xw
    read-from-segment-of-set-flag

    read-from-segment-of-1 ;; simplifies to read-byte-from-segment

    write-to-segment-of-write-to-segment-same
    write-to-segment-of-write-to-segment-diff-axe

;    mv-nth-1-of-rme08-of-cs-becomes-read-byte-from-segment
;   mv-nth-1-of-rme08-of-cs-becomes-read-byte-from-segment-gen
    x86isa::rme08-does-not-affect-state-in-app-view ;; targets mv-nth-2-of-rme08
    x86isa::rme16-does-not-affect-state-in-app-view ;; targets mv-nth-2-of-rme16
    read-byte-from-segment-when-code-segment-assumptions32-for-code
    read-from-segment-when-code-segment-assumptions32-for-code

    acl2::fix-of-ifix

    ;; Rules about EIP/SET-EIP:
    xw-becomes-set-eip
    xw-of-set-eip-irrel
    xr-of-set-eip-irrel
    xr-of-set-eip-same ; or turn xr into eip or get-eip?
    set-eip-of-set-eip
    ;; bring eip to the front:
    set-eax-of-set-eip
    set-ebx-of-set-eip
    set-ecx-of-set-eip
    set-edx-of-set-eip
    set-esp-of-set-eip
    set-ebp-of-set-eip
    eip-of-set-eip
    eip-of-set-eax
    eip-of-set-ebx
    eip-of-set-ecx
    eip-of-set-edx
    eip-of-set-esp
    eip-of-set-ebp
    eip-of-xw-irrel
;eip-of-xw-of-rip ;drop?
    not-mv-nth-0-of-add-to-*ip
;mv-nth-1-of-add-to-*ip
    mv-nth-1-of-add-to-*ip-gen
    read-*ip-becomes-eip

    ;; Rules about add-to-*sp
    not-mv-nth-0-of-add-to-*sp
    mv-nth-1-of-add-to-*sp
    not-mv-nth-0-of-add-to-*sp-gen
    mv-nth-1-of-add-to-*sp-gen
    not-mv-nth-0-of-add-to-*sp-gen-special
    not-mv-nth-0-of-add-to-*sp-positive-offset

    ;; Rules about write-*sp
    x86isa::write-*sp-when-not-64-bit-modep

    ;; Rules about ESP:
    read-*sp-becomes-esp
    xr-becomes-esp ;do we need this?
    esp-bound-hack
    bvchop-of-decrement-esp-hack
    integerp-of-esp
    unsigned-byte-p-of-esp-when-stack-segment-assumptions32
    esp-bound

    xr-of-write-byte-to-segment
    xr-of-write-to-segment
    stack-segment-assumptions32-of-write-to-segment

    ;; Rules about read-byte-list-from-segment
    read-byte-list-from-segment-of-xw
    read-byte-list-from-segment-of-write-to-segment-diff-segments
    read-byte-list-from-segment-of-set-flag

    segment-expand-down-bit-of-cs-when-code-segment-well-formedp
    segment-expand-down-bit-of-ss-when-stack-segment-assumptions32
    ;; segment-is-32-bitsp-intro-1
    ;; segment-is-32-bitsp-intro-1-alt
    ;; segment-is-32-bitsp-intro-2
    ;; segment-is-32-bitsp-intro-2-alt
    segment-is-32-bitsp-when-code-segment-well-formedp
    code-segment-readable-bit-when-code-segment-well-formedp
    well-formed-32-bit-segmentp-when-code-segment-well-formedp
    segment-is-32-bitsp-when-stack-segment-assumptions32
    not-<-of-esp-when-stack-segment-assumptions32
    natp-of-+-of-esp-lemma
    not-<-of-32-bit-segment-size
    <-of-32-bit-segment-size
    eff-addrs-lemma
    well-formed-32-bit-segmentp-when-stack-segment-assumptions32

    read-byte-from-segment-of-write-to-segment-diff-segments
    eff-addr-okp-when-code-segment-assumptions32-for-code
    eff-addrs-okp-when-code-segment-assumptions32-for-code
    seg-regp-constant-opener
    acl2::integer-range-p-constant-opener
    signed-byte-p-of-+-of-esp
;    x86isa::ea-to-la-of-xw
;    ea-to-la-of-write-to-segment
;    canonical-address-p-of-mv-nth-1-of-ea-to-la-of-cs
;    canonical-address-p-of-mv-nth-1-of-ea-to-la-of-ss
    x86isa::mv-nth-0-rb-xw-rgf ;gen?
    x86isa::mv-nth-0-rb-xw-rip
;    fix-of-mv-nth-1-of-ea-to-la
;    read-of-ea-to-la-becomes-read-byte-from-segment
;    canonical-address-p-of-+-of-mv-nth-1-of-ea-to-la-of-ss
    acl2::if-x-x-y-when-booleanp
;    mv-nth-0-of-ea-to-la ; introduces eff-addrs-okp

    eff-addr-okp-of-set-flag
    eff-addr-okp-of-WRITE-TO-SEGMENT
    stack-segment-assumptions32-of-xw-of-rgf

    esp-of-xw-of-rgf-and-rsp
    eff-addr-okp-of-+-of-esp
    ea-to-la-of-set-flag
    ;fix-of-esp
    ;bvchop-32-of-esp
    signed-byte-p-64-of-esp
    eff-addr-okp-of-esp

    ;; Rules about x86p
    x86p-of-write-to-segment
    x86p-of-set-eip
    x86p-of-set-eax
    x86p-of-set-ebx
    x86p-of-set-ecx
    x86p-of-set-edx
    x86p-of-set-esp
    x86p-of-set-ebp

    ;; Rules about segment-is-32-bitsp
    segment-is-32-bitsp-of-write-byte-to-segment
    segment-is-32-bitsp-of-write-to-segment
    segment-is-32-bitsp-of-set-eip
    segment-is-32-bitsp-of-set-eax
    segment-is-32-bitsp-of-set-ebx
    segment-is-32-bitsp-of-set-ecx
    segment-is-32-bitsp-of-set-edx
    segment-is-32-bitsp-of-set-esp
    segment-is-32-bitsp-of-set-ebp
    segment-is-32-bitsp-of-set-flag
    segment-is-32-bitsp-of-xw-irrel

    ;;Rules about 32-bit-segment-size
    32-bit-segment-size-of-write-byte-to-segment
    32-bit-segment-size-of-write-to-segment
    32-bit-segment-size-of-set-eip
    32-bit-segment-size-of-set-eax
    32-bit-segment-size-of-set-ebx
    32-bit-segment-size-of-set-ecx
    32-bit-segment-size-of-set-edx
    32-bit-segment-size-of-set-esp
    32-bit-segment-size-of-set-ebp
    32-bit-segment-size-of-set-flag
    32-bit-segment-size-of-xw

    ;;Rules about 32-bit-segment-start
    32-bit-segment-start-of-write-byte-to-segment
    32-bit-segment-start-of-write-to-segment
    32-bit-segment-start-of-set-eip
    32-bit-segment-start-of-set-eax
    32-bit-segment-start-of-set-ebx
    32-bit-segment-start-of-set-ecx
    32-bit-segment-start-of-set-edx
    32-bit-segment-start-of-set-esp
    32-bit-segment-start-of-set-ebp
    32-bit-segment-start-of-set-flag
    32-bit-segment-start-of-xw

    ;; Rules about segment-expand-down-bit
    segment-expand-down-bit-of-write-byte-to-segment
    segment-expand-down-bit-of-write-to-segment
    segment-expand-down-bit-of-set-eip
    segment-expand-down-bit-of-set-eax
    segment-expand-down-bit-of-set-ebx
    segment-expand-down-bit-of-set-ecx
    segment-expand-down-bit-of-set-edx
    segment-expand-down-bit-of-set-esp
    segment-expand-down-bit-of-set-ebp
    segment-expand-down-bit-of-set-flag
    segment-expand-down-bit-of-xw-irrel

    ;; Rules about well-formed-32-bit-segmentp
    well-formed-32-bit-segmentp-of-write-byte-to-segment
    well-formed-32-bit-segmentp-of-write-to-segment
    well-formed-32-bit-segmentp-of-set-eip
    well-formed-32-bit-segmentp-of-set-eax
    well-formed-32-bit-segmentp-of-set-ebx
    well-formed-32-bit-segmentp-of-set-ecx
    well-formed-32-bit-segmentp-of-set-edx
    well-formed-32-bit-segmentp-of-set-esp
    well-formed-32-bit-segmentp-of-set-ebp
    well-formed-32-bit-segmentp-of-set-flag
    well-formed-32-bit-segmentp-of-xw

    ;; Rules about segments-separate
    segments-separate-of-write-byte-to-segment
    segments-separate-of-write-to-segment
    segments-separate-of-set-eip
    segments-separate-of-set-eax
    segments-separate-of-set-ebx
    segments-separate-of-set-ecx
    segments-separate-of-set-edx
    segments-separate-of-set-esp
    segments-separate-of-set-ebp
    segments-separate-of-set-flag
    segments-separate-of-xw-irrel

    ;; Rules about code-and-stack-segments-separate (todo: do we need these and the rules about segments-separate?)
    code-and-stack-segments-separate-of-write-byte-to-segment
    code-and-stack-segments-separate-of-write-to-segment
    code-and-stack-segments-separate-of-set-eip
    code-and-stack-segments-separate-of-set-eax
    code-and-stack-segments-separate-of-set-ebx
    code-and-stack-segments-separate-of-set-ecx
    code-and-stack-segments-separate-of-set-edx
    code-and-stack-segments-separate-of-set-esp
    code-and-stack-segments-separate-of-set-ebp
    code-and-stack-segments-separate-of-set-flag
    code-and-stack-segments-separate-of-xw-irrel

    ;; Rules about alignment-checking-enabled-p
    alignment-checking-enabled-p-of-write-byte-to-segment
    alignment-checking-enabled-p-of-write-to-segment
    alignment-checking-enabled-p-of-set-eip
    alignment-checking-enabled-p-of-set-eax
    alignment-checking-enabled-p-of-set-ebx
    alignment-checking-enabled-p-of-set-ecx
    alignment-checking-enabled-p-of-set-edx
    alignment-checking-enabled-p-of-set-esp
    alignment-checking-enabled-p-of-set-ebp

    eax-of-set-ebx
    eax-of-set-ecx
    eax-of-set-edx
    eax-of-set-esp
    eax-of-set-ebp
    ebx-of-set-eax
    ebx-of-set-ecx
    ebx-of-set-edx
    ebx-of-set-esp
    ebx-of-set-ebp
    ecx-of-set-eax
    ecx-of-set-ebx
    ecx-of-set-edx
    ecx-of-set-esp
    ecx-of-set-ebp
    edx-of-set-eax
    edx-of-set-ebx
    edx-of-set-ecx
    edx-of-set-esp
    edx-of-set-ebp
    esp-of-set-eax
    esp-of-set-ebx
    esp-of-set-ecx
    esp-of-set-edx
    esp-of-set-ebp
    ebp-of-set-eax
    ebp-of-set-ebx
    ebp-of-set-ecx
    ebp-of-set-edx
    ebp-of-set-esp

    ;; Rules about esp
    esp-of-set-eip
    esp-of-set-flag
    esp-of-xw-irrel
    natp-of-esp-when-stack-segment-assumptions32

    ;; Rules about read-byte-from-segment
    read-byte-from-segment-of-xw
    read-byte-from-segment-of-set-eip
    read-byte-from-segment-of-set-eax
    read-byte-from-segment-of-set-ebx
    read-byte-from-segment-of-set-ecx
    read-byte-from-segment-of-set-edx
    read-byte-from-segment-of-set-esp
    read-byte-from-segment-of-set-ebp
    read-byte-from-segment-of-set-flag

    ;; Rules about 64-bit-modep
    64-bit-modep-of-write-bytes-to-segment
    64-bit-modep-of-set-eip
    64-bit-modep-of-set-eax
    64-bit-modep-of-set-ebx
    64-bit-modep-of-set-ecx
    64-bit-modep-of-set-edx
    64-bit-modep-of-set-esp
    64-bit-modep-of-set-ebp

    ;; Rules about app-view
    app-view-of-write-to-segment
    app-view-of-set-eip
    app-view-of-set-eax
    app-view-of-set-ebx
    app-view-of-set-ecx
    app-view-of-set-edx
    app-view-of-set-esp
    app-view-of-set-ebp

    ;; Rules about code-segment-well-formedp
    code-segment-well-formedp-of-xw ;; lets us drop most state updates
    code-segment-well-formedp-of-set-eip
    code-segment-well-formedp-of-set-eax
    code-segment-well-formedp-of-set-ebx
    code-segment-well-formedp-of-set-ecx
    code-segment-well-formedp-of-set-edx
    code-segment-well-formedp-of-set-esp
    code-segment-well-formedp-of-set-ebp
    code-segment-well-formedp-of-write-to-segment
    code-segment-well-formedp-OF-set-flag

    ;; Rules about code-segment-assumptions32-for-code
    code-segment-assumptions32-for-code-of-xw
    code-segment-assumptions32-for-code-of-write-to-segment
    code-segment-assumptions32-for-code-of-set-eip
    code-segment-assumptions32-for-code-of-set-eax
    code-segment-assumptions32-for-code-of-set-ebx
    code-segment-assumptions32-for-code-of-set-ecx
    code-segment-assumptions32-for-code-of-set-edx
    code-segment-assumptions32-for-code-of-set-esp
    code-segment-assumptions32-for-code-of-set-ebp
    code-segment-assumptions32-for-code-of-set-flag

    unsigned-byte-p-of-+-of-esp
    eff-addr-okp-of-+-of-esp-positive-offset
    eff-addrs-okp-of-+-of-esp-positive-offset
    eff-addrs-okp-of-+-of-esp-negative-offset

    eff-addrs-okp-of-esp
    sep-eff-addr-ranges ;; we leave this enabled, at least for now

    unsigned-byte-p-of-+-of-esp-negative-offset-simple
    bvminus-cancel-2-2
    bvminus-cancel-2-all
    bvminus-cancel-all-2
    mv-nth-1-of-add-to-*sp-gen-special
    mv-nth-1-of-add-to-*sp-positive-offset
    segments-separate-of-code-and-stack
    write-*ip-inline-becomes-xw

;segment-min-eff-addr32-of-set-eip ;drop?
;segment-max-eff-addr32-of-set-eip ;drop?

;    ea-to-la-of-set-eip

    eff-addr-okp-of-xw-irrel
    eff-addr-okp-of-set-eip
    eff-addr-okp-of-set-eax
    eff-addr-okp-of-set-ebx
    eff-addr-okp-of-set-ecx
    eff-addr-okp-of-set-edx
    eff-addr-okp-of-set-esp
    eff-addr-okp-of-set-ebp

    eff-addrs-okp-of-xw-irrel
    eff-addrs-okp-of-write-to-segment
    eff-addrs-okp-of-set-flag
    eff-addrs-okp-of-set-eip
    eff-addrs-okp-of-set-eax
    eff-addrs-okp-of-set-ebx
    eff-addrs-okp-of-set-ecx
    eff-addrs-okp-of-set-edx
    eff-addrs-okp-of-set-esp
    eff-addrs-okp-of-set-ebp

    eff-addrs-okp-of-1 ;simplifies to just eff-addr-okp
    segment-is-32-bitsp-intro-code
    segment-is-32-bitsp-intro-data
    code-segment-readable-bit-intro
    data-segment-writeable-bit-intro
    data-segment-writeable-bit-when-stack-segment-assumptions32
    not-<-of-seg-hidden-limit-when-code-segment-assumptions32-for-code

    ;; normalizing nests of state updates:

    ;; push flag stuff inward:
    set-flag-of-write-to-segment
    set-flag-of-write-byte-to-segment
    set-flag-of-set-eip-irrel
    set-flag-of-set-eax
    set-flag-of-set-ebx
    set-flag-of-set-ecx
    set-flag-of-set-edx
    set-flag-of-set-esp
    set-flag-of-set-ebp
    ;; push memory writes inward:
    write-byte-to-segment-of-xw-rgf
    write-to-segment-of-xw-rgf

    ;; Introduce register writers
    xw-becomes-set-eax
    xw-becomes-set-ebx
    xw-becomes-set-ecx
    xw-becomes-set-edx
    xw-becomes-set-esp
    xw-becomes-set-ebp

    ;; Introduce register readers
    xr-becomes-eax
    xr-becomes-ebx
    xr-becomes-ecx
    xr-becomes-edx
    xr-becomes-ebp
    xr-becomes-esp

    eax-of-set-eax
    ebx-of-set-ebx
    ecx-of-set-ecx
    edx-of-set-edx
    esp-of-set-esp
    ebp-of-set-ebp

    eax-of-set-eip
    ebx-of-set-eip
    ecx-of-set-eip
    edx-of-set-eip
    ebp-of-set-eip
    ;esp-of-set-eip

    write-byte-to-segment-of-set-eax
    write-byte-to-segment-of-set-ebx
    write-byte-to-segment-of-set-ecx
    write-byte-to-segment-of-set-edx ;todo: more?
    write-byte-to-segment-of-set-esp
    write-byte-to-segment-of-set-ebp

    write-to-segment-of-set-eax
    write-to-segment-of-set-ebx
    write-to-segment-of-set-ecx
    write-to-segment-of-set-edx
    write-to-segment-of-set-esp
    write-to-segment-of-set-ebp

    set-ebx-of-set-eax
    set-ecx-of-set-eax
    set-edx-of-set-eax
    set-esp-of-set-eax
    set-ebp-of-set-eax
    set-ecx-of-set-ebx
    set-edx-of-set-ebx
    set-esp-of-set-ebx
    set-ebp-of-set-ebx
    set-edx-of-set-ecx
    set-esp-of-set-ecx
    set-ebp-of-set-ecx
    set-esp-of-set-edx
    set-ebp-of-set-edx
    set-ebp-of-set-esp

    xr-of-set-eax
    xr-of-set-ebx
    xr-of-set-ecx
    xr-of-set-edx
    xr-of-set-esp
    xr-of-set-ebp

    xr-of-set-esp-same ;todo hack
    xr-of-esp-and-set-eax
    xr-of-esp-and-set-ebx
    xr-of-esp-and-set-ecx
    xr-of-esp-and-set-edx
    xr-of-esp-and-set-ebp

    set-eax-of-set-eax
    set-ebx-of-set-ebx
    set-ecx-of-set-ecx
    set-edx-of-set-edx
    set-esp-of-set-esp
    set-ebp-of-set-ebp

    segment-is-32-bitsp-of-if
    esp-of-if
    xr-of-if

    eax-of-xw
    ebx-of-xw
    ecx-of-xw
    edx-of-xw
    esp-of-xw
    ebp-of-xw

    bvplus-of-constant-and-esp-when-overflow
    ;;acl2::bvplus-of-constant-when-overflow ;move?  targets things like (BVPLUS 32 4294967280 (ESP X86))

    read-stack-dword-of-write-to-segment-diff-segments
    write-to-segment-of-write-byte-to-segment-included
    write-to-segment-of-write-to-segment-included
    ))

(defun lifter-rules64 ()
  (append (lifter-rules-common)
          (read-introduction-rules)
          (write-introduction-rules)
          (read-rules)
          (write-rules)
          (read-byte-rules)
          (linear-memory-rules)
          (get-prefixes-rules64)
          '(x86isa::rme08-when-64-bit-modep-and-not-fs/gs ; puts in rml08, todo: rules for other sizes?
            x86isa::rme-size-when-64-bit-modep-and-not-fs/gs ; puts in rml-size
            ;; this is sometimes needed in 64-bit mode (e.g., when a stack
            ;; protection value is read via the FS segment register):
            x86isa::rme-size-when-64-bit-modep-fs/gs
            x86isa::wme-size-when-64-bit-modep-and-not-fs/gs ; puts in wml-size
            x86isa::rime-size-when-64-bit-modep-and-not-fs/gs
            x86isa::wime-size-when-64-bit-modep-and-not-fs/gs
            x86isa::read-*ip-when-64-bit-modep
            x86isa::mv-nth-0-of-add-to-*ip-when-64-bit-modep
            x86isa::mv-nth-1-of-add-to-*ip-when-64-bit-modep
            x86isa::write-*ip-when-64-bit-modep
            x86isa::read-*sp-when-64-bit-modep
            x86isa::mv-nth-0-of-add-to-*sp-when-64-bit-modep
            x86isa::mv-nth-1-of-add-to-*sp-when-64-bit-modep
            x86isa::write-*sp-when-64-bit-modep
            x86isa::program-at-of-set-flag)))

(defun lifter-rules64-new ()
  (declare (xargs :guard t))
  '(;; Rules about RIP/SET-RIP:
    xr-becomes-rip ; introduces rip
    xw-becomes-set-rip ; introduces set-rip
    xw-of-set-rip-irrel
    xr-of-set-rip-irrel
    set-rip-of-set-rip
    ;; bring rip to the front:
    set-rax-of-set-rip
    set-rbx-of-set-rip
    set-rcx-of-set-rip
    set-rdx-of-set-rip
    set-rsi-of-set-rip
    set-rdi-of-set-rip
    set-r8-of-set-rip
    set-r9-of-set-rip
    set-r10-of-set-rip
    set-r11-of-set-rip
    set-r12-of-set-rip
    set-r13-of-set-rip
    set-r14-of-set-rip
    set-r15-of-set-rip
    set-rsp-of-set-rip
    set-rbp-of-set-rip

    rax-of-set-rip
    rbx-of-set-rip
    rcx-of-set-rip
    rdx-of-set-rip
    rsi-of-set-rip
    rdi-of-set-rip
    r8-of-set-rip
    r9-of-set-rip
    r10-of-set-rip
    r11-of-set-rip
    r12-of-set-rip
    r13-of-set-rip
    r14-of-set-rip
    r15-of-set-rip
    rsp-of-set-rip
    rbp-of-set-rip

    rax-of-xw
    rbx-of-xw
    rcx-of-xw
    rdx-of-xw
    rsi-of-xw
    rdi-of-xw
    r8-of-xw
    r9-of-xw
    r10-of-xw
    r11-of-xw
    r12-of-xw
    r13-of-xw
    r14-of-xw
    r15-of-xw
    rsp-of-xw
    rbp-of-xw

    set-flag-of-set-rip
    set-flag-of-set-rax
    set-flag-of-set-rbx
    set-flag-of-set-rcx
    set-flag-of-set-rdx
    set-flag-of-set-rsi
    set-flag-of-set-rdi
    set-flag-of-set-r8
    set-flag-of-set-r9
    set-flag-of-set-r10
    set-flag-of-set-r11
    set-flag-of-set-r12
    set-flag-of-set-r13
    set-flag-of-set-r14
    set-flag-of-set-r15
    set-flag-of-set-rsp
    set-flag-of-set-rbp

    rip-of-set-rip
    rip-of-set-rax
    rip-of-set-rbx
    rip-of-set-rcx
    rip-of-set-rdx
    rip-of-set-rsi
    rip-of-set-rdi
    rip-of-set-r8
    rip-of-set-r9
    rip-of-set-r10
    rip-of-set-r11
    rip-of-set-r12
    rip-of-set-r13
    rip-of-set-r14
    rip-of-set-r15
    rip-of-set-rsp
    rip-of-set-rbp
    rip-of-set-undef
    rip-of-xw-irrel

    rax-of-set-rax
    rbx-of-set-rbx
    rcx-of-set-rcx
    rdx-of-set-rdx
    rsi-of-set-rsi
    rdi-of-set-rdi
    r8-of-set-r8
    r9-of-set-r9
    r10-of-set-r10
    r11-of-set-r11
    r12-of-set-r12
    r13-of-set-r13
    r14-of-set-r14
    r15-of-set-r15
    rsp-of-set-rsp
    rbp-of-set-rbp
    undef-of-set-undef
    undef-of-write-byte
    undef-of-write

    app-view-of-set-rip
    app-view-of-set-rax
    app-view-of-set-rbx
    app-view-of-set-rcx
    app-view-of-set-rdx
    app-view-of-set-rsi
    app-view-of-set-rdi
    app-view-of-set-r8
    app-view-of-set-r9
    app-view-of-set-r10
    app-view-of-set-r11
    app-view-of-set-r12
    app-view-of-set-r13
    app-view-of-set-r14
    app-view-of-set-r15
    app-view-of-set-rsp
    app-view-of-set-rbp
    app-view-of-set-undef

    x86p-of-set-rip
    x86p-of-set-rax
    x86p-of-set-rbx
    x86p-of-set-rcx
    x86p-of-set-rdx
    x86p-of-set-rsi
    x86p-of-set-rdi
    x86p-of-set-r8
    x86p-of-set-r9
    x86p-of-set-r10
    x86p-of-set-r11
    x86p-of-set-r12
    x86p-of-set-r13
    x86p-of-set-r14
    x86p-of-set-r15
    x86p-of-set-rsp
    x86p-of-set-rbp
    x86p-of-set-undef

    ;; needed to resolve (xr ':ms 'nil ...)
    xr-of-set-rip-irrel
    xr-of-set-rax-irrel
    xr-of-set-rbx-irrel
    xr-of-set-rcx-irrel
    xr-of-set-rdx-irrel
    xr-of-set-rsi-irrel
    xr-of-set-rdi-irrel
    xr-of-set-r8-irrel
    xr-of-set-r9-irrel
    xr-of-set-r10-irrel
    xr-of-set-r11-irrel
    xr-of-set-r12-irrel
    xr-of-set-r13-irrel
    xr-of-set-r14-irrel
    xr-of-set-r15-irrel
    xr-of-set-rsp-irrel
    xr-of-set-rbp-irrel
    xr-of-set-undef-irrel

    read-of-set-rip
    read-of-set-rax
    read-of-set-rbx
    read-of-set-rcx
    read-of-set-rdx
    read-of-set-rsi
    read-of-set-rdi
    read-of-set-r8
    read-of-set-r9
    read-of-set-r10
    read-of-set-r11
    read-of-set-r12
    read-of-set-r13
    read-of-set-r14
    read-of-set-r15
    read-of-set-rsp
    read-of-set-rbp
    read-of-set-undef
    read-of-set-undef

    get-flag-of-set-rip
    get-flag-of-set-rax
    get-flag-of-set-rbx
    get-flag-of-set-rcx
    get-flag-of-set-rdx
    get-flag-of-set-rsi
    get-flag-of-set-rdi
    get-flag-of-set-r8
    get-flag-of-set-r9
    get-flag-of-set-r10
    get-flag-of-set-r11
    get-flag-of-set-r12
    get-flag-of-set-r13
    get-flag-of-set-r14
    get-flag-of-set-r15
    get-flag-of-set-rsp
    get-flag-of-set-rbp
    get-flag-of-set-undef
    get-flag-of-!rflags-of-xr

    rax-of-set-rbx
    rax-of-set-rcx
    rax-of-set-rdx
    rax-of-set-rdi
    rax-of-set-r8
    rax-of-set-r9
    rax-of-set-r10
    rax-of-set-r11
    rax-of-set-r12
    rax-of-set-r13
    rax-of-set-r14
    rax-of-set-r15
    rax-of-set-rsi
    rax-of-set-rsp
    rax-of-set-rbp
    rax-of-set-undef
    rbx-of-set-rax
    rbx-of-set-rcx
    rbx-of-set-rdx
    rbx-of-set-rsi
    rbx-of-set-rdi
    rbx-of-set-r8
    rbx-of-set-r9
    rbx-of-set-r10
    rbx-of-set-r11
    rbx-of-set-r12
    rbx-of-set-r13
    rbx-of-set-r14
    rbx-of-set-r15
    rbx-of-set-rsp
    rbx-of-set-rbp
    rbx-of-set-undef
    rcx-of-set-rax
    rcx-of-set-rbx
    rcx-of-set-rdx
    rcx-of-set-rsi
    rcx-of-set-rdi
    rcx-of-set-r8
    rcx-of-set-r9
    rcx-of-set-r10
    rcx-of-set-r11
    rcx-of-set-r12
    rcx-of-set-r13
    rcx-of-set-r14
    rcx-of-set-r15
    rcx-of-set-rsp
    rcx-of-set-rbp
    rcx-of-set-undef
    rdx-of-set-rax
    rdx-of-set-rbx
    rdx-of-set-rcx
    rdx-of-set-rsi
    rdx-of-set-rdi
    rdx-of-set-r8
    rdx-of-set-r9
    rdx-of-set-r10
    rdx-of-set-r11
    rdx-of-set-r12
    rdx-of-set-r13
    rdx-of-set-r14
    rdx-of-set-r15
    rdx-of-set-rsp
    rdx-of-set-rbp
    rdx-of-set-undef
    rsi-of-set-rax
    rsi-of-set-rbx
    rsi-of-set-rcx
    rsi-of-set-rdx
    rsi-of-set-rdi
    rsi-of-set-r8
    rsi-of-set-r9
    rsi-of-set-r10
    rsi-of-set-r11
    rsi-of-set-r12
    rsi-of-set-r13
    rsi-of-set-r14
    rsi-of-set-r15
    rsi-of-set-rsp
    rsi-of-set-rbp
    rsi-of-set-undef
    rdi-of-set-rax
    rdi-of-set-rbx
    rdi-of-set-rcx
    rdi-of-set-rdx
    rdi-of-set-rsi
    rdi-of-set-r8
    rdi-of-set-r9
    rdi-of-set-r10
    rdi-of-set-r11
    rdi-of-set-r12
    rdi-of-set-r13
    rdi-of-set-r14
    rdi-of-set-r15
    rdi-of-set-rsp
    rdi-of-set-rbp
    rdi-of-set-undef
    r8-of-set-rax
    r8-of-set-rbx
    r8-of-set-rcx
    r8-of-set-rdx
    r8-of-set-rsi
    r8-of-set-rdi
    r8-of-set-r9
    r8-of-set-r10
    r8-of-set-r11
    r8-of-set-r12
    r8-of-set-r13
    r8-of-set-r14
    r8-of-set-r15
    r8-of-set-rsp
    r8-of-set-rbp
    r8-of-set-undef
    r9-of-set-rax
    r9-of-set-rbx
    r9-of-set-rcx
    r9-of-set-rdx
    r9-of-set-rsi
    r9-of-set-rdi
    r9-of-set-r8
    r9-of-set-r10
    r9-of-set-r11
    r9-of-set-r12
    r9-of-set-r13
    r9-of-set-r14
    r9-of-set-r15
    r9-of-set-rsp
    r9-of-set-rbp
    r9-of-set-undef
    r10-of-set-rax
    r10-of-set-rbx
    r10-of-set-rcx
    r10-of-set-rdx
    r10-of-set-rsi
    r10-of-set-rdi
    r10-of-set-r8
    r10-of-set-r9
    r10-of-set-r11
    r10-of-set-r12
    r10-of-set-r13
    r10-of-set-r14
    r10-of-set-r15
    r10-of-set-rsp
    r10-of-set-rbp
    r10-of-set-undef

    r11-of-set-rax
    r11-of-set-rbx
    r11-of-set-rcx
    r11-of-set-rdx
    r11-of-set-rsi
    r11-of-set-rdi
    r11-of-set-r8
    r11-of-set-r9
    r11-of-set-r10
    r11-of-set-r12
    r11-of-set-r13
    r11-of-set-r14
    r11-of-set-r15
    r11-of-set-rsp
    r11-of-set-rbp
    r11-of-set-undef

    r12-of-set-rax
    r12-of-set-rbx
    r12-of-set-rcx
    r12-of-set-rdx
    r12-of-set-rsi
    r12-of-set-rdi
    r12-of-set-r8
    r12-of-set-r9
    r12-of-set-r10
    r12-of-set-r11
    r12-of-set-r13
    r12-of-set-r14
    r12-of-set-r15
    r12-of-set-rsp
    r12-of-set-rbp
    r12-of-set-undef

    r13-of-set-rax
    r13-of-set-rbx
    r13-of-set-rcx
    r13-of-set-rdx
    r13-of-set-rsi
    r13-of-set-rdi
    r13-of-set-r8
    r13-of-set-r9
    r13-of-set-r10
    r13-of-set-r11
    r13-of-set-r12
    r13-of-set-r14
    r13-of-set-r15
    r13-of-set-rsp
    r13-of-set-rbp
    r13-of-set-undef

    r14-of-set-rax
    r14-of-set-rbx
    r14-of-set-rcx
    r14-of-set-rdx
    r14-of-set-rsi
    r14-of-set-rdi
    r14-of-set-r8
    r14-of-set-r9
    r14-of-set-r10
    r14-of-set-r11
    r14-of-set-r12
    r14-of-set-r13
    r14-of-set-r15
    r14-of-set-rsp
    r14-of-set-rbp
    r14-of-set-undef

    r15-of-set-rax
    r15-of-set-rbx
    r15-of-set-rcx
    r15-of-set-rdx
    r15-of-set-rsi
    r15-of-set-rdi
    r15-of-set-r8
    r15-of-set-r9
    r15-of-set-r10
    r15-of-set-r11
    r15-of-set-r12
    r15-of-set-r13
    r15-of-set-r14
    r15-of-set-rsp
    r15-of-set-rbp
    r15-of-set-undef

    rsp-of-set-rax
    rsp-of-set-rbx
    rsp-of-set-rcx
    rsp-of-set-rdx
    rsp-of-set-rsi
    rsp-of-set-rdi
    rsp-of-set-r8
    rsp-of-set-r9
    rsp-of-set-r10
    rsp-of-set-r11
    rsp-of-set-r12
    rsp-of-set-r13
    rsp-of-set-r14
    rsp-of-set-r15
    rsp-of-set-rbp
    rsp-of-set-undef
    rbp-of-set-rax
    rbp-of-set-rbx
    rbp-of-set-rcx
    rbp-of-set-rdx
    rbp-of-set-rsi
    rbp-of-set-rdi
    rbp-of-set-r8
    rbp-of-set-r9
    rbp-of-set-r10
    rbp-of-set-r11
    rbp-of-set-r12
    rbp-of-set-r13
    rbp-of-set-r14
    rbp-of-set-r15
    rbp-of-set-rsp
    rbp-of-set-undef

    rax-of-set-flag
    rbx-of-set-flag
    rcx-of-set-flag
    rdx-of-set-flag
    rsi-of-set-flag
    rdi-of-set-flag
    r8-of-set-flag
    r9-of-set-flag
    r10-of-set-flag
    r11-of-set-flag
    r12-of-set-flag
    r13-of-set-flag
    r14-of-set-flag
    r15-of-set-flag
    rsp-of-set-flag
    rbp-of-set-flag
    undef-of-set-flag

    alignment-checking-enabled-p-of-set-rip
    alignment-checking-enabled-p-of-set-rax
    alignment-checking-enabled-p-of-set-rbx
    alignment-checking-enabled-p-of-set-rcx
    alignment-checking-enabled-p-of-set-rdx
    alignment-checking-enabled-p-of-set-rsi
    alignment-checking-enabled-p-of-set-rdi
    alignment-checking-enabled-p-of-set-r8
    alignment-checking-enabled-p-of-set-r9
    alignment-checking-enabled-p-of-set-r10
    alignment-checking-enabled-p-of-set-r11
    alignment-checking-enabled-p-of-set-r12
    alignment-checking-enabled-p-of-set-r13
    alignment-checking-enabled-p-of-set-r14
    alignment-checking-enabled-p-of-set-r15
    alignment-checking-enabled-p-of-set-rsp
    alignment-checking-enabled-p-of-set-rbp
    alignment-checking-enabled-p-of-set-undef
    alignment-checking-enabled-p-of-!rflags-of-xr

    undef-of-set-rip
    undef-of-set-rax
    undef-of-set-rbx
    undef-of-set-rcx
    undef-of-set-rdx
    undef-of-set-rdi
    undef-of-set-r8
    undef-of-set-r9
    undef-of-set-r10
    undef-of-set-r11
    undef-of-set-r12
    undef-of-set-r13
    undef-of-set-r14
    undef-of-set-r15
    undef-of-set-rsi
    undef-of-set-rsp
    undef-of-set-rbp

    xw-becomes-set-rip
    xw-becomes-set-rax
    xw-becomes-set-rbx
    xw-becomes-set-rcx
    xw-becomes-set-rdx
    xw-becomes-set-rsi
    xw-becomes-set-rdi
    xw-becomes-set-r8
    xw-becomes-set-r9
    xw-becomes-set-r10
    xw-becomes-set-r11
    xw-becomes-set-r12
    xw-becomes-set-r13
    xw-becomes-set-r14
    xw-becomes-set-r15
    xw-becomes-set-rsp
    xw-becomes-set-rbp
    xw-becomes-set-undef
    xw-becomes-set-error

    ;xr-becomes-rip
    xr-becomes-rax
    xr-becomes-rbx
    xr-becomes-rcx
    xr-becomes-rdx
    xr-becomes-rsi
    xr-becomes-rdi
    xr-becomes-r8
    xr-becomes-r9
    xr-becomes-r10
    xr-becomes-r11
    xr-becomes-r12
    xr-becomes-r13
    xr-becomes-r14
    xr-becomes-r15
    xr-becomes-rsp
    xr-becomes-rbp
    xr-becomes-undef

    ;; Rules about 64-bit-modep
    64-bit-modep-of-set-rip
    64-bit-modep-of-set-rax
    64-bit-modep-of-set-rbx
    64-bit-modep-of-set-rcx
    64-bit-modep-of-set-rdx
    64-bit-modep-of-set-rsi
    64-bit-modep-of-set-rdi
    64-bit-modep-of-set-r8
    64-bit-modep-of-set-r9
    64-bit-modep-of-set-r10
    64-bit-modep-of-set-r11
    64-bit-modep-of-set-r12
    64-bit-modep-of-set-r13
    64-bit-modep-of-set-r14
    64-bit-modep-of-set-r15
    64-bit-modep-of-set-rsp
    64-bit-modep-of-set-rbp
    64-bit-modep-of-set-undef

    ctri-of-set-rip
    ctri-of-set-rax
    ctri-of-set-rbx
    ctri-of-set-rcx
    ctri-of-set-rdx
    ctri-of-set-rsi
    ctri-of-set-rdi
    ctri-of-set-r8
    ctri-of-set-r9
    ctri-of-set-r10
    ctri-of-set-r11
    ctri-of-set-r12
    ctri-of-set-r13
    ctri-of-set-r14
    ctri-of-set-r15
    ctri-of-set-rsp
    ctri-of-set-rbp
    ctri-of-set-undef
    ctri-of-!rflags

    rax-of-write
    rbx-of-write
    rcx-of-write
    rdx-of-write
    rsi-of-write
    rdi-of-write
    r8-of-write
    r9-of-write
    r10-of-write
    r11-of-write
    r12-of-write
    r13-of-write
    r14-of-write
    r15-of-write
    rsp-of-write
    rbp-of-write

    rip-of-myif
    rax-of-myif
    rbx-of-myif
    rcx-of-myif
    rdx-of-myif
    rsi-of-myif
    rdi-of-myif
    r8-of-myif
    r9-of-myif
    r10-of-myif ;todo: more?
    rsp-of-myif
    rbp-of-myif
    undef-of-myif

    rip-of-if
    rax-of-if
    rbx-of-if
    rcx-of-if
    rdx-of-if
    rsi-of-if
    rdi-of-if
    r8-of-if
    r9-of-if
    r10-of-if ; todo: more?
    rsp-of-if
    rbp-of-if
    undef-of-if

    set-rip-of-myif
    set-rax-of-myif
    set-rbx-of-myif
    set-rcx-of-myif
    set-rdx-of-myif
    set-rsi-of-myif
    set-rdi-of-myif
    set-r8-of-myif
    set-r9-of-myif
    set-r10-of-myif ; todo: more?
    set-rsp-of-myif
    set-rbp-of-myif
    set-undef-of-myif

    write-of-set-rip
    write-of-set-rax
    write-of-set-rbx
    write-of-set-rcx
    write-of-set-rdx
    write-of-set-rsi
    write-of-set-rdi
    write-of-set-r8
    write-of-set-r9
    write-of-set-r10
    write-of-set-r11
    write-of-set-r12
    write-of-set-r13
    write-of-set-r14
    write-of-set-r15
    write-of-set-rsp
    write-of-set-rbp

    write-byte-of-set-rip

    ;; bury set-undef deep in the term:
    set-undef-of-set-rip
    set-undef-of-set-rax
    set-undef-of-set-rbx
    set-undef-of-set-rcx
    set-undef-of-set-rdx
    set-undef-of-set-rdi
    set-undef-of-set-rsi
    set-undef-of-set-r8
    set-undef-of-set-r9
    set-undef-of-set-r10
    set-undef-of-set-r11
    set-undef-of-set-r12
    set-undef-of-set-r13
    set-undef-of-set-r14
    set-undef-of-set-r15
    set-undef-of-set-rsp
    set-undef-of-set-rbp
    set-undef-of-set-flag
    set-undef-of-write-byte
    set-undef-of-write
    set-undef-of-!rflags ; why is !rflags showing up?

    set-rbx-of-set-rax
    set-rcx-of-set-rax
    set-rdx-of-set-rax
    set-rsi-of-set-rax
    set-rdi-of-set-rax
    set-r8-of-set-rax
    set-r9-of-set-rax
    set-r10-of-set-rax
    set-r11-of-set-rax
    set-r12-of-set-rax
    set-r13-of-set-rax
    set-r14-of-set-rax
    set-r15-of-set-rax
    set-rsp-of-set-rax
    set-rbp-of-set-rax

    set-rcx-of-set-rbx
    set-rdx-of-set-rbx
    set-rsi-of-set-rbx
    set-rdi-of-set-rbx
    set-r8-of-set-rbx
    set-r9-of-set-rbx
    set-r10-of-set-rbx
    set-r11-of-set-rbx
    set-r12-of-set-rbx
    set-r13-of-set-rbx
    set-r14-of-set-rbx
    set-r15-of-set-rbx
    set-rsp-of-set-rbx
    set-rbp-of-set-rbx

    set-rdx-of-set-rcx
    set-rsi-of-set-rcx
    set-rdi-of-set-rcx
    set-r8-of-set-rcx
    set-r9-of-set-rcx
    set-r10-of-set-rcx
    set-r11-of-set-rcx
    set-r12-of-set-rcx
    set-r13-of-set-rcx
    set-r14-of-set-rcx
    set-r15-of-set-rcx
    set-rsp-of-set-rcx
    set-rbp-of-set-rcx

    set-rsi-of-set-rdx
    set-rdi-of-set-rdx
    set-r8-of-set-rdx
    set-r9-of-set-rdx
    set-r10-of-set-rdx
    set-r11-of-set-rdx
    set-r12-of-set-rdx
    set-r13-of-set-rdx
    set-r14-of-set-rdx
    set-r15-of-set-rdx
    set-rsp-of-set-rdx
    set-rbp-of-set-rdx

    set-rdi-of-set-rsi
    set-r8-of-set-rsi
    set-r9-of-set-rsi
    set-r10-of-set-rsi
    set-r11-of-set-rsi
    set-r12-of-set-rsi
    set-r13-of-set-rsi
    set-r14-of-set-rsi
    set-r15-of-set-rsi
    set-rsp-of-set-rsi
    set-rbp-of-set-rsi

    set-r8-of-set-rdi
    set-r9-of-set-rdi
    set-r10-of-set-rdi
    set-r11-of-set-rdi
    set-r12-of-set-rdi
    set-r13-of-set-rdi
    set-r14-of-set-rdi
    set-r15-of-set-rdi
    set-rsp-of-set-rdi
    set-rbp-of-set-rdi

    set-r9-of-set-r8
    set-r10-of-set-r8
    set-r11-of-set-r8
    set-r12-of-set-r8
    set-r13-of-set-r8
    set-r14-of-set-r8
    set-r15-of-set-r8
    set-rsp-of-set-r8
    set-rbp-of-set-r8

    set-r10-of-set-r9
    set-r11-of-set-r9
    set-r12-of-set-r9
    set-r13-of-set-r9
    set-r14-of-set-r9
    set-r15-of-set-r9
    set-rsp-of-set-r9
    set-rbp-of-set-r9

    set-r11-of-set-r10
    set-r12-of-set-r10
    set-r13-of-set-r10
    set-r14-of-set-r10
    set-r15-of-set-r10
    set-rsp-of-set-r10
    set-rbp-of-set-r10

    set-r12-of-set-r11
    set-r13-of-set-r11
    set-r14-of-set-r11
    set-r15-of-set-r11
    set-rsp-of-set-r11
    set-rbp-of-set-r11

    set-r13-of-set-r12
    set-r14-of-set-r12
    set-r15-of-set-r12
    set-rsp-of-set-r12
    set-rbp-of-set-r12

    set-r14-of-set-r13
    set-r15-of-set-r13
    set-rsp-of-set-r13
    set-rbp-of-set-r13

    set-r15-of-set-r14
    set-rsp-of-set-r14
    set-rbp-of-set-r14

    set-rsp-of-set-r15
    set-rbp-of-set-r15

    set-rbp-of-set-rsp

    ;; set of set of the same register:
    set-rax-of-set-rax
    set-rbx-of-set-rbx
    set-rcx-of-set-rcx
    set-rdx-of-set-rdx
    set-rdi-of-set-rdi
    set-rsi-of-set-rsi
    set-r8-of-set-r8
    set-r9-of-set-r9
    set-r10-of-set-r10
    set-r11-of-set-r11
    set-r12-of-set-r12
    set-r13-of-set-r13
    set-r14-of-set-r14
    set-r15-of-set-r15
    set-rsp-of-set-rsp
    set-rbp-of-set-rbp
    set-undef-of-set-undef

    !RFLAGS-OF-SET-RIP
    !RFLAGS-OF-SET-RAX
    !RFLAGS-OF-SET-RBX
    !RFLAGS-OF-SET-RCX
    !RFLAGS-OF-SET-RDX
    !RFLAGS-OF-SET-RDI
    !RFLAGS-OF-SET-RSI
    !RFLAGS-OF-SET-R8
    !RFLAGS-OF-SET-R9
    !RFLAGS-OF-SET-R10
    !RFLAGS-OF-SET-R11
    !RFLAGS-OF-SET-R12
    !RFLAGS-OF-SET-R13
    !RFLAGS-OF-SET-R14
    !RFLAGS-OF-SET-R15
    !RFLAGS-OF-SET-RSP
    !RFLAGS-OF-SET-RBP

    rsp-of-if

    rax-of-!rflags
    rbx-of-!rflags
    rcx-of-!rflags
    rdx-of-!rflags
    rsi-of-!rflags
    rdi-of-!rflags
    r8-of-!rflags
    r9-of-!rflags
    r10-of-!rflags
    r11-of-!rflags
    r12-of-!rflags
    r13-of-!rflags
    r14-of-!rflags
    r15-of-!rflags
    rsp-of-!rflags
    rbp-of-!rflags
    undef-of-!rflags ; why is !rflags not going away?

    xw-becomes-set-undef
    xr-becomes-undef

    integerp-of-rax
    integerp-of-rbx
    integerp-of-rcx
    integerp-of-rdx
    integerp-of-rsi
    integerp-of-rdi
    integerp-of-r8
    integerp-of-r9
    integerp-of-r10
    integerp-of-r11
    integerp-of-r12
    integerp-of-r13
    integerp-of-r14
    integerp-of-r15
    integerp-of-rsp
    integerp-of-rbp

    fix-of-rax
    fix-of-rbx
    fix-of-rcx
    fix-of-rdx
    fix-of-rsi
    fix-of-rdi
    fix-of-r8
    fix-of-r9
    fix-of-r10
    fix-of-r11
    fix-of-r12
    fix-of-r13
    fix-of-r14
    fix-of-r15
    fix-of-rsp
    fix-of-rbp

    msri-of-set-rip
    msri-of-set-rax
    msri-of-set-rbx
    msri-of-set-rcx
    msri-of-set-rdx
    msri-of-set-rsi
    msri-of-set-rdi
    msri-of-set-r8
    msri-of-set-r9
    msri-of-set-r10
    msri-of-set-r11
    msri-of-set-r12
    msri-of-set-r13
    msri-of-set-r14
    msri-of-set-r15
    msri-of-set-rsp
    msri-of-set-rbp
    msri-of-set-undef
    msri-of-write
    msri-of-set-flag

    ;; These help make failures more clear, by dropping irrelevant
    ;; state writes inside rme-size:
    mv-nth-0-of-rme-size-of-set-rip
    mv-nth-0-of-rme-size-of-set-rax
    mv-nth-0-of-rme-size-of-set-rbx
    mv-nth-0-of-rme-size-of-set-rcx
    mv-nth-0-of-rme-size-of-set-rdx
    mv-nth-0-of-rme-size-of-set-rsi
    mv-nth-0-of-rme-size-of-set-rdi
    mv-nth-0-of-rme-size-of-set-r8
    mv-nth-0-of-rme-size-of-set-r9
    mv-nth-0-of-rme-size-of-set-r10
    mv-nth-0-of-rme-size-of-set-r11
    mv-nth-0-of-rme-size-of-set-r12
    mv-nth-0-of-rme-size-of-set-r13
    mv-nth-0-of-rme-size-of-set-r14
    mv-nth-0-of-rme-size-of-set-r15
    mv-nth-0-of-rme-size-of-set-rsp
    mv-nth-0-of-rme-size-of-set-rbp
    mv-nth-0-of-rme-size-of-set-undef
    ))

;; Try this rule first
(table axe-rule-priorities-table 'read-of-write-disjoint -1)

;; These rules expand operations on effective addresses, exposing the
;; underlying operations on linear addresses.
(defun low-level-rules-32 ()
  (append (linear-memory-rules)
          (read-introduction-rules)
          (write-introduction-rules)
          (read-rules)
          (write-rules)
          '(x86isa::rme08$inline
            x86isa::rme16$inline
            x86isa::rme32$inline
            x86isa::rme64$inline
            x86isa::rme128$inline
            x86isa::rme-size$inline
            x86isa::rime08$inline
            x86isa::rime16$inline
            x86isa::rime32$inline
            x86isa::rime64$inline
            x86isa::rime-size$inline
            x86isa::wme08$inline
            x86isa::wme16$inline
            x86isa::wme32$inline
            x86isa::wme64$inline
            x86isa::wme128$inline
            x86isa::wme-size$inline
            ea-to-la$inline
            x86isa::read-*ip$inline
            x86isa::write-*ip$inline
            x86isa::add-to-*ip$inline
            x86isa::read-*sp$inline
            x86isa::write-*sp$inline
            x86isa::add-to-*sp$inline

            ;; x86isa::data-segment-descriptor-attributesbits->e$inline
            ;; x86isa::data-segment-descriptor-attributesbits->d/b$inline
            ;; x86isa::data-segment-descriptor-attributesbits->w$inline
            ;; x86isa::code-segment-descriptor-attributesbits->d$inline
            ;; x86isa::code-segment-descriptor-attributesbits->r$inline
            ;; x86isa::data-segment-descriptor-attributesbits-fix
            ;; x86isa::code-segment-descriptor-attributesbits-fix

            ;x86isa::rflagsbits->res1$inline
            ;x86isa::rflagsbits->res2$inline
            )))

;; some commonly monitored stuff:
;;   :monitor (acl2::get-prefixes-opener-lemma-no-prefix-byte-conjunct-1 ;todo: handle multi-conjunct rules better
;;             acl2::get-prefixes-opener-lemma-no-prefix-byte-conjunct-2
;; ;            rb-in-terms-of-nth-and-pos-eric-gen
;;             rb-returns-no-error-app-view
;;             part-install-width-low-becomes-bvcat-axe
;;             car-create-canonical-address-list
;;             ;;canonical-address-p-between
;;             wb-returns-no-error-app-view
;;             addr-byte-alistp-create-addr-bytes-alist
;; ;            program-at-xw-in-app-view
;;             program-at-wb-disjoint
;;             strip-cars-of-create-addr-bytes-alist
;;             len-of-byte-ify
;;             rb-returns-x86-app-view
;; ;            x86p-xw ;big rule with forced hyps
;;             rb-wb-disjoint
;;             disjoint-p-two-create-canonical-address-lists-thm-1
;;             assoc-list-of-rev-of-create-addr-bytes-alist
;;             acl2::bvchop-identity
;;             unsigned-byte-p-64-of-xr-of-rgf
;;             )
;; ;;more:
;;  (x86isa::x86-fetch-decode-execute-base mv-nth-1-of-add-to-*sp-positive-offset
;;             mv-nth-1-of-add-to-*sp-gen-special
;;             read-from-segment-of-write-to-segment-same
;;             read-from-segment-of-write-to-segment-irrel
;;             eff-addrs-okp-of-+-of-esp-positive-offset
;;             unsigned-byte-p-of-+-of-esp
;;             eff-addr-okp-of-+-of-esp-positive-offset
;;             read-of-mv-nth-1-of-ea-to-la-becomes-read-from-segment
;;             not-mv-nth-0-of-add-to-*sp-gen-special
;;             X86ISA::X86P-XW
;;             not-mv-nth-0-of-add-to-*sp-gen-special
;; ;;             x86isa::write-*sp-when-not-64-bit-modep-gen2
;;              mv-nth-1-of-add-to-*sp-gen
;;              not-mv-nth-0-of-add-to-*sp-gen
;; ;;             not-mv-nth-0-of-add-to-*sp
;; ;;             read-*sp-becomes-esp
;; ;;             x86isa::write-*sp-when-not-64-bit-modep-gen
;; ;;             read-of-ea-to-la-becomes-read-byte-from-segment
;; ;;             x86isa::rb-returns-no-error-app-view
;; ;;             x86isa::x86p-xw
;;              not-mv-nth-0-of-add-to-*ip
;; ;;             x86p-of-write-to-segment
;; ;;             ;eff-addr-okp-when-code-segment-assumptions32
;; ;;             ;read-byte-from-segment-of-write-to-segment-diff-segments
;; ;;             ;; mv-nth-1-of-rme08-of-cs-becomes-read-byte-from-segment
;; ;;             ;; not-mv-nth-0-of-rme08-of-cs-gen
;;             x86isa::get-prefixes-base-1
;;             x86isa::get-prefixes-base-2
;;             x86isa::get-prefixes-base-3
;;             x86isa::get-prefixes-base-4
;;             x86isa::get-prefixes-base-5
;;             x86isa::get-prefixes-base-6
;;             x86isa::get-prefixes-base-7
;;             x86isa::get-prefixes-base-8
;;             x86isa::get-prefixes-unroll-1
;;             x86isa::get-prefixes-unroll-2
;;             x86isa::get-prefixes-unroll-3
;;             x86isa::get-prefixes-unroll-4
;; ;;             ;;read-when-equal-of-read
;; ;;             ;;read-when-equal-of-read-alt
;; ;;             ;read-when-program-at
;; ;;             ;read-of-write-disjoint2
;; ;;             ;read-of-write-disjoint
;; ;; ;acl2::<-becomes-bvlt-axe-both
;; ;; ;            read-byte-from-segment-when-code-segment-assumptions32
;; ;;  ;           mv-nth-1-of-add-to-*sp
;; ;;   ;          not-mv-nth-0-of-add-to-*sp
;; ;;             ;x86isa::write-*sp-when-not-64-bit-modep-gen
;; ;;             read-*ip-becomes-eip-gen
;; ;;             code-segment-assumptions32-of-write-to-segment-of-ss
;;             )

(defun debug-rules-common ()
  (declare (xargs :guard t))
  '(run-until-stack-shorter-than-opener
    not-mv-nth-0-of-wme-size ;gets rid of error branch
    mv-nth-1-of-wme-size     ;introduces write-to-segment
    mv-nth-1-of-rb-becomes-read
    mv-nth-1-of-rb-1-becomes-read
    ))

(defun debug-rules32 ()
  (append (debug-rules-common)
          '(not-mv-nth-0-of-add-to-*sp-gen
            mv-nth-1-of-add-to-*sp-gen)))

(defun debug-rules64 ()
  (append (debug-rules-common)
          (get-prefixes-openers)
          ;; todo: flesh out this list:
          '(x86isa::wme-size-when-64-bit-modep-and-not-fs/gs
            x86isa::rme-size-when-64-bit-modep-and-not-fs/gs
            ;; could consider things like these:
            ;; READ-OF-WRITE-DISJOINT2
            )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Push many of these tester rules back into more fundamental rule sets

;; these are used both for lifting and proving
(defun extra-tester-rules ()
  (declare (xargs :guard t))
  (append '(acl2::bvchop-of-*
            acl2::integerp-of-expt
            acl2::integerp-of-*                 ; for array index calcs
            ACL2::<-OF-+-AND-+-CANCEL-CONSTANTS ; for array index calcs
            ACL2::MY-INTEGERP-<-NON-INTEGERP    ; for array index calcs
            acl2::bvsx-when-bvlt
            x86isa::canonical-address-p-between-special5
            x86isa::canonical-address-p-between-special5-alt
            x86isa::canonical-address-p-between-special6
            bitops::ash-is-expt-*-x acl2::natp-of-*
            acl2::<-of-constant-and-+-of-constant ; for address calcs
            <-of-15-and-*-of-4
            unsigned-byte-p-2-of-bvchop-when-bvlt-of-4
            acl2::bvlt-of-max-arg2
            <-of-*-when-constant-integers
            ;separate-when-separate-2 ; todo: drop? but that caused problems
            acl2::<-of-+-cancel-second-of-more-and-only ; more?
            acl2::<-of-+-cancel-1+-1+ ;; acl2::<-of-+-cancel-first-and-first
            acl2::collect-constants-over-<-2
            acl2::commutativity-of-*-when-constant
            <-of-*-of-constant-and-constant
            rationalp-when-integerp
            acl2::<-of-+-cancel-1+-1 ; todo: same as acl2::<-of-+-cancel.  kill that one
            acl2::+-of-+-of---same
            acl2::<-of-minus-and-constant ; ensure needed
            acl2::fix-when-acl2-numberp
            acl2-numberp-of--
            acl2::acl2-numberp-of-*
            bitops::ash-of-0-c ; at least for now
            ;;RFLAGSBITS->AF-of-myif
            ACL2::BVASHR-of-0-arg2
            ACL2::BVSHR-of-0-arg2
            acl2::eql ; drop soon?
            ACL2::EQUAL-OF-CONSTANT-AND-BVUMINUS
            ACL2::BVOR-OF-MYIF-ARG2 ; introduces bvif (myif can arise from expanding a shift into cases)
            ACL2::BVOR-OF-MYIF-ARG3 ; introduces bvif (myif can arise from expanding a shift into cases)
            ACL2::BVIF-OF-MYIF-ARG3 ; introduces bvif
            ACL2::BVIF-OF-MYIF-ARG4 ; introduces bvif
            ;; help to show that divisions don't overflow or underflow:
            not-sbvlt-of-constant-and-sbvdiv-32-64
            not-sbvlt-of-sbvdiv-and-minus-constant-32-64
            not-bvlt-of-constant-and-bvdiv-64-128
            not-bvlt-of-constant-and-bvdiv-32-64
            ACL2::BVDIV-SAME
            ACL2::SBVDIV-SAME
            ACL2::SBVDIV-OF-1-ARG3
            ACL2::BVSX-OF-BVSX
            ACL2::SLICE-OF-BVSX-HIGH
            bvcat-of-repeatbit-of-getbit-of-bvsx-same
            not-sbvlt-of-bvsx-of-constant-arg2-64-8
            not-sbvlt-of-bvsx-of-constant-arg2-64-16
            not-sbvlt-of-bvsx-of-constant-arg2-64-32
            not-sbvlt-of-bvsx-of-constant-arg2-128-64
            not-sbvlt-of-bvsx-of-constant-arg3-64-8
            not-sbvlt-of-bvsx-of-constant-arg3-64-16
            not-sbvlt-of-bvsx-of-constant-arg3-64-32
            not-sbvlt-of-bvsx-of-constant-arg3-128-64
            acl2::floor-of-1-when-integerp ; simplified something that showed up in an error case?
            unicity-of-1 ; simplified something that showed up in an error case
            bvcat-of-repeatbit-of-getbit-becomes-bvsx
            bvcat-of-repeatit-tighten-64-32 ;gen!
            ACL2::BVLT-OF-BVSX-ARG2
            sbvlt-of-bvsx-32-16-constant
            RFLAGSBITS->AF-OF-IF
            ACL2::SBVLT-FALSE-WHEN-SBVLT-GEN ; did nothing?
            if-of-sbvlt-and-not-sbvlt-helper
            if-of-set-flag-and-set-flag
            XR-OF-!RFLAGS-IRREL ; todo: better normal form?
            64-bit-modep-OF-!RFLAGS
            app-view-OF-!RFLAGS
            x86p-OF-!RFLAGS
            read-OF-!RFLAGS
            boolif-same-arg1-arg2
            logext-of-+-of-bvplus-same-size
            logext-of-+-of-+-of-mult-same-size
            ACL2::MINUS-CANCELLATION-ON-RIGHT ; todo: use an arithmetic-light rule
            ACL2::BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ2 ; needed for STP to see the array op
            BV-ARRAY-READ-of-*-arg3 ; introduces bvmult for the index
            BV-ARRAY-READ-of-+-arg3 ; introduces bvplus for the index
            ACL2::NTH-BECOMES-BV-ARRAY-READ-STRONG2
            ACL2::BVPLUS-OF-*-ARG2 ; introduces bvmult -- todo: alt version?
            not-equal-of-+-and-+-when-separate
            not-equal-of-+-of-+-and-+-when-separate
            not-equal-of-+-of-+-and-+-when-separate-gen
            acl2::<-of-negative-constant-and-bv
            READ-OF-WRITE-BOTH-SIZE-1
            ACL2::BVLT-OF-CONSTANT-WHEN-USB-DAG ; rename
            ;; separate-of-1-and-1 ; do we ever need this?
            <-of-+-and-+-arg3-and-arg1
            equal-of-bvshl-and-constant
            bvchop-of-bvshl-same
            acl2::equal-of-myif-arg1-safe
            acl2::equal-of-myif-arg2-safe
            write-of-write-same
            write-of-write-of-write-same
            write-of-write-of-write-of-write-same
            bvminus-of-+-arg2
            bvminus-of-+-arg3
            acl2::bvminus-of-bvplus-and-bvplus-same-2-2
            acl2::right-cancellation-for-+ ; todo: switch to an arithmetic-light rule
            acl2::bvplus-of-unary-minus
            acl2::bvplus-of-unary-minus-arg2
            acl2::if-becomes-bvif-1-axe
            ;; acl2::boolif-of-t-and-nil-when-booleanp
            slice-of-bvand-of-constant
            acl2::myif-becomes-boolif-axe ; since STP translation supports disjuncts that are calls to boolif but not if.
            acl2::equal-of-bvplus-constant-and-constant
            acl2::equal-of-bvplus-constant-and-constant-alt
            acl2::bvchop-of-bvshr-same
            ;bvand-of-lognot-arg2
            ;bvand-of-lognot-arg3
            ;bvxor-of-lognot-arg2
            ;bvxor-of-lognot-arg3
            acl2::bvchop-of-lognot
            acl2::getbit-of-lognot ; todo: handle all cases of logops inside bvops
            bvif-of-if-constants-nil-nonnil
            bvif-of-if-constants-nonnil-nil
            acl2::bvminus-of-0-arg3
            acl2::bvif-same-branches
            acl2::equal-of-1-and-bitand
            ACL2::BOOLIF-OF-NIL-AND-T
            ACL2::BVIF-OF-BOOL-FIX
            acl2::boolif-same-branches
            ACL2::BOOLEANP-OF-MYIF ; or convert myif to boolif when needed
            ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG1
            ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG2
            ;; these next few did seem needed after lifting (todo: either add the rest like this or drop these):
            booleanp-of-jp-condition
            booleanp-of-jnp-condition
            booleanp-of-jz-condition
            booleanp-of-jnz-condition
            ACL2::GETBIT-0-OF-BOOL-TO-BIT
            ACL2::EQUAL-OF-BOOL-TO-BIT-AND-0 ; alt version needed, or do equals get turned around?
            ACL2::EQUAL-OF-BOOL-TO-BIT-AND-1 ; alt version needed, or do equals get turned around?
            ACL2::EQUAL-OF-1-AND-BITNOT ; todo: add 0 version
            ;;ACL2::BVIF-OF-1-AND-0-BECOMES-BOOL-TO-BIT ; introduced bool-to-bit?  maybe bad.
            ;; todo: just include boolean-rules?:
            acl2::bool-fix-when-booleanp
            acl2::booland-of-constant-arg1
            acl2::booland-of-constant-arg2
            acl2::boolor-of-constant-arg1
            acl2::boolor-of-constant-arg2
            ;; acl2::bvmult-tighten-when-power-of-2p-axe ; todo: uncomment
            ;; acl2::bvplus-of-bvmult-when-power-of-2p-tighten ; todo: uncomment
            bvchop-of-bool-to-bit ;todo: drop
            logext-of-bool-to-bit
            acl2::bool-fix-when-booleanp
            acl2::<-of-if-arg1-safe
            ;; acl2::<-of-if-arg2-safe
            acl2::bvif-of-logext-1
            acl2::bvif-of-logext-2
            equal-of-bvif-safe2
            )
          (acl2::convert-to-bv-rules) ; turns things like logxor into things like bvxor
          (acl2::booleanp-rules)
          (acl2::boolean-rules-safe)
          (acl2::type-rules)))

;; beyond what def-unrolled uses
(defun extra-tester-lifting-rules ()
  (declare (xargs :guard t))
  (append (lifter-rules64-new)
          (extra-tester-rules)
          '(X86ISA::WX32$inline ; more?
            X86ISA::WZ32$inline ; more?
            <-of-fp-to-rat ; do we want this?
            X86ISA::!EVEX-PREFIXES->BYTE0$INLINE-CONSTANT-OPENER
            !RFLAGS-of-if-arg1
            !RFLAGS-of-if-arg2
            ;;xr-of-!rflags-irrel
            acl2::IF-X-X-Y-when-booleanp
            ;; ACL2::IF-OF-T-AND-NIL-WHEN-BOOLEANP
            ACL2::EQUAL-OF-IF-ARG1-WHEN-QUOTEP
            ACL2::EQUAL-OF-IF-ARG2-WHEN-QUOTEP
            eq
            X86ISA::SSE-CMP-SPECIAL ; scary
            X86ISA::FP-DECODE-CONSTANT-OPENER
            X86ISA::FP-to-rat-CONSTANT-OPENER
            RTL::BIAS-CONSTANT-OPENER
            RTL::expw-CONSTANT-OPENER
            unsigned-byte-p-32-of-!MXCSRBITS->IE
            unsigned-byte-p-32-of-!MXCSRBITS->DE
            ACL2::BVCHOP-OF-IF
            integerp-of-!MXCSRBITS->DE
            integerp-of-!MXCSRBITS->IE
            integerp-of-xr-mxcsr
            ifix-of-if
            MXCSRBITS->IM-of-!MXCSRBITS->IE
            MXCSRBITS->IM-of-!MXCSRBITS->DE
            MXCSRBITS->DM-of-!MXCSRBITS->DE
            MXCSRBITS->DM-of-!MXCSRBITS->IE
            MXCSRBITS->DAZ-of-!MXCSRBITS->DE
            MXCSRBITS->DAZ-of-!MXCSRBITS->IE
            X86ISA::MXCSRBITS->IM-of-if
            X86ISA::MXCSRBITS->DM-of-if
            X86ISA::MXCSRBITS->Daz-of-if
            sse-daz-of-nil
            X86ISA::N32P-XR-MXCSR
            ;X86ISA::SSE-CMP ; scary
            x86isa::dp-sse-cmp
            app-view-of-if
            program-at-of-if
            x86p-of-if
            ALIGNMENT-CHECKING-ENABLED-P-of-if
            get-flag-of-if
            ctri-of-if
            ;; feature-flag-of-if
            read-of-if
            bvle
            ACL2::INTEGERP-OF-BVPLUS ;todo: more
            ACL2::INTEGERP-OF-BVCHOP

            ;zf-spec$inline     ; needed for unsigned_add_associates -- but does this ruin rules about jle-condition? zf-spec seems to be used in more things that just the conditional branches?

            ;x86isa::sub-zf-spec32-same ; this can mess up the condition rules...
            ;x86isa::if-of-sub-zf-spec32-arg2
            ACL2::BFIX-WHEN-BITP
            ;;stuff related to flags changes:
            x86isa::GPR-SUB-SPEC-1-alt-def
            x86isa::GPR-SUB-SPEC-2-alt-def
            x86isa::GPR-SUB-SPEC-4-alt-def
            x86isa::GPR-SUB-SPEC-8-alt-def

            bvchop-of-sub-zf-spec32
            equal-of-sub-zf-spec32-and-1
            equal-of-1-and-sub-zf-spec32

            logand-of-1-arg2
            acl2::ifix-does-nothing
            of-spec-of-logext-32
            ACL2::LOGXOR-BVCHOP-BVCHOP        ; introduce bvxor
            ACL2::LOGXOR-of-BVCHOP-becomes-bvxor-arg1 ; introduce bvxor
;            bvplus-of-logxor-arg1                     ; introduce bvxor
;            bvxor-of-logxor-arg2                      ; introduce bvxor
            integerp-of-logxor                        ;todo: more
            acl2::unsigned-byte-p-of-if
            acl2::unsigned-byte-p-of-bvplus ;todo: more
            ACL2::BVCHOP-OF-MYIF
            XR-OF-IF ;restrict?
            ACL2::SLICE-OUT-OF-ORDER
            X86ISA::DIV-SPEC$inline ; just a dispatch on the size
            ACL2::BVCAT-OF-0-arg2
            bvmod-tighten-64-32
            bvdiv-tighten-64-32
            not-bvlt-of-max-when-unsiged-byte-p
            ;X86ISA::SF-SPEC32-REWRITE ; trying without...
            jle-condition-rewrite-1-with-bvif ; this one works on bvif
            jle-condition-rewrite-1-with-bvif-and-bvchop
            jle-condition-rewrite-1-with-bvchop
            jnl-condition-of-getbit-31-and-0
            jnl-condition-rewrite-16
            jnl-condition-rewrite-16b
            bvchop-of-logext-becomes-bvsx ; needed for jnl-condition-rewrite-16
            ACL2::BVSX-WHEN-SIZES-MATCH
            ACL2::BVCHOP-OF-BVSX
            ACL2::BVCHOP-OF-BVCHOP
            ACL2::BVPLUS-OF-BVCHOP-ARG2
            bvchop-of-zf-spec
            logext-of-zf-spec
            integerp-of-zf-spec
            sbvle ; expand to sbvlt
            ACL2::SBVLT-OF-BVCHOP-ARG2
            ACL2::BVUMINUS-OF-BVUMINUS
            ACL2::BVPLUS-OF-BVUMINUS-SAME
            ACL2::BVCHOP-NUMERIC-BOUND
            ACL2::BVCHOP-OF-LOGXOR-BECOMES-BVXOR
            ;acl2::bvuminus-of-bvsx-low ; todo: other cases? todo: push back
            SF-SPEC64-of-bvchop-64
            jnl-condition-of-sf-spec32-and-of-spec32-same
            jnl-condition-of-sf-spec64-and-of-spec64-same
            jnl-condition-of-sf-spec64-and-0
            of-spec64-of-logext-64
            ACL2::SBVLT-OF-BVSX-ARG2
            ACL2::BVSX-OF-BVCHOP
            X86ISA::!PREFIXES->REP$INLINE-CONSTANT-OPENER ; for floating point?
            X86ISA::PREFIXES->REP$INLINE-CONSTANT-OPENER ; for floating point?
            X86ISA::CHK-EXC-FN ; for floating point?
            ctri-of-xw-irrel
            ctri-of-write
            ctri-of-set-flag
            X86ISA::FEATURE-FLAGS-opener
            X86ISA::FEATURE-FLAGS-base
            eql
            integerp-of-ctri
            X86ISA::XMMI-SIZE$inline ;trying
            X86ISA::!XMMI-SIZE$inline
            X86ISA::X86-OPERAND-TO-XMM/MEM
            cr0bits->ts-of-bvchop
            cr0bits->em-of-bvchop
            cr4bits->OSFXSR-of-bvchop
            X86ISA::WX128$inline
            X86ISA::WZ128$inline
            X86ISA::RX32$inline
            X86ISA::RX64$inline
            X86ISA::RZ32$inline
            X86ISA::RZ64$inline
            X86ISA::RX128$INLINE
            X86ISA::RZ128$INLINE
            X86ISA::ZMMI
            X86ISA::ZMMI$A
            X86ISA::!ZMMI
            X86ISA::!ZMMI$A
            X86ISA::N128$inline
            integerp-of-PART-INSTALL-WIDTH-LOW$INLINE
            X86ISA::SP-SSE-CMP
            ;;X86ISA::SSE-CMP ;todo: limit?
            X86ISA::MXCSR
            X86ISA::MXCSR$A
            X86ISA::!MXCSR
            X86ISA::!MXCSR$A
            64-BIT-MODEP-of-if
            ;; FEATURE-FLAG-sse-of-xw
            ;; FEATURE-FLAG-sse-of-write
            ;; FEATURE-FLAG-sse-of-set-flag
            ;; FEATURE-FLAG-sse2-of-xw
            ;; FEATURE-FLAG-sse2-of-write
            ;; FEATURE-FLAG-sse2-of-set-flag
            ACL2::EQUAL-OF-IF-CONSTANTS
            ACL2::BVLT-OF-BVPLUS-1-CANCEL-ALT ; optional
            ;X86ISA::IDIV-SPEC-32 ; trying
            ACL2::BVCHOP-WHEN-SIZE-IS-NOT-POSP
            mv-nth-0-of-idiv-spec-32
            mv-nth-1-of-idiv-spec-32
            mv-nth-0-of-idiv-spec-64
            mv-nth-1-of-idiv-spec-64
            acl2::bvcat-of-if-arg2
            acl2::bvcat-of-if-arg4
            ACL2::BVIF-OF-0-ARG1
            ACL2::BVPLUS-WHEN-SIZE-IS-NOT-POSITIVE ; todo: more like this, make a rule-list
            x86isa::X86-CWD/CDQ/CQO-alt-def
            acl2::bvcat-of-slice-of-bvsx-same
            not-sbvlt-64-of-sbvdiv-64-of-bvsx-64-32-and--2147483648
            not-sbvlt-64-of-2147483647-and-sbvdiv-64-of-bvsx-64-32
            IF-OF-IF-OF-CONS-AND-NIL ; why not already included
            ACL2::BVPLUS-COMMUTATIVE-INCREASING-AXE
            ACL2::BVPLUS-COMMUTATIVE-2-INCREASING-AXE
            ;;acl2::equal-same
            ;; bvcat-of-minus-becomes-bvshl ; except STP doesn't support the shift operators
            acl2::<-lemma-for-known-operators
            acl2::bvlt-of-bvchop-arg2
            acl2::bvlt-of-bvchop-arg3
            acl2::sbvlt-of-bvchop-arg2
            acl2::sbvlt-of-bvchop-arg3
            ;; todo: more like this?:
            X86ISA::RFLAGSBITS->CF-of-if
            X86ISA::RFLAGSBITS->PF-of-if
            X86ISA::RFLAGSBITS->OF-of-if
            X86ISA::RFLAGSBITS->SF-of-if
            X86ISA::RFLAGSBITS->ZF-of-if
            acl2::bvand-of-bvchop-1 ;rename
            acl2::bvand-of-bvchop-2 ;rename
            ACL2::BVCHOP-OF-MINUS-BECOMES-BVUMINUS ; todo: or re-characterize the subl instruction
            ACL2::BVPLUS-OF-PLUS-ARG3 ; todo: drop once we characterize long negation?
            ACL2::BVUMINUS-OF-+
            X86ISA::INTEGERP-OF-XR-RGF
            ACL2::NATP-OF-+-OF-- ; trying, or simplify (NATP (BINARY-+ '32 (UNARY-- (BVCHOP '5 x))))
            min ; why is min arising?  or add min-same
            ACL2::<-BECOMES-BVLT-DAG-ALT-GEN-BETTER2
            ACL2::<-BECOMES-BVLT-DAG-GEN-BETTER2
            ;; after adding core-rules-bv:
            acl2::bvplus-of-logext-gen-arg1
            acl2::bvplus-of-logext-gen-arg2
            ACL2::BVPLUS-OF-LOGEXT ; rename
            ACL2::BVPLUS-OF-LOGEXT-arg1 ; rename
            ACL2::BVUMINUS-OF-LOGEXT
            acl2::bvlt-tighten-bind-and-bind-dag
            ACL2::UNSIGNED-BYTE-P-OF-0-ARG1 ; move to a more fundamental rule list
            ;; ACL2::BOOLIF-X-X-Y-BECOMES-BOOLOR ; introduces boolor
            boolor-becomes-boolif
            ;bvlt-hack-1-gen
            ACL2::BVCHOP-SUBST-CONSTANT
            ACL2::BVCHOP-SUBST-CONSTANT-alt
            ACL2::BOOL-FIX$INLINE-CONSTANT-OPENER
            boolif-of-bvlt-strengthen-to-equal
            bvlt-reduce-when-not-equal-one-less
            acl2::bvchop-of-logand-becomes-bvand
            read-of-write-1-4
            read-of-write-1-both
            not-equal-of-+-when-separate
            not-equal-of-+-when-separate-alt
            x86isa::canonical-address-p-of-sum-when-unsigned-byte-p-32
            x86isa::!prefixes->seg$inline-constant-opener
            read-of-2 ; splits into 2 reads
            )
          (acl2::core-rules-bv) ; trying
          (acl2::unsigned-byte-p-rules)
          (acl2::unsigned-byte-p-forced-rules)))

(defun tester-proof-rules ()
  (declare (xargs :guard t))
  (append '(myif-of-sub-zf-spec32-arg2
            myif-of-sub-zf-spec32-arg3
            ACL2::INTEGERP-OF-BVPLUS ;todo: more
            ACL2::INTEGERP-OF-BVCHOP
            equal-of-sub-zf-spec32-and-1
            equal-of-1-and-sub-zf-spec32
            acl2::if-of-t-and-nil-when-booleanp
            acl2::equal-of-if-constants
            acl2::if-becomes-myif ; todo: do we want this when lifting?
            ACL2::MYIF-BECOMES-BVIF-1-axe
            ACL2::BVCHOP-OF-MYIF
            ACL2::BVIF-OF-+-ARG4
            ACL2::BVIF-OF-+-ARG3
            ACL2::BVIF-OF---ARG3
            ACL2::BVIF-OF---ARG4
            ACL2::INTEGERP-OF-BVIF
            ACL2::INTEGERP-OF---when-integerp
            ACL2::EQUAL-OF-BVPLUS-MOVE-BVMINUS-BETTER
            ACL2::EQUAL-OF-BVPLUS-MOVE-BVMINUS-ALT-BETTER
            ACL2::BVPLUS-COMMUTATIVE-INCREASING-AXE
            ACL2::BVCHOP-OF-BVMOD
            ACL2::BVPLUS-OF-0-ARG2
            ACL2::BVMOD-OF-BVCHOP-ARG2
            ACL2::BVMOD-OF-BVCHOP-ARG3
            bvuminus-of-bvif-constants
            ACL2::BVPLUS-OF-BVIF-ARG2-SAFE
            ACL2::BVPLUS-OF-BVIF-ARG3-SAFE
            ACL2::EQUAL-OF-BVIF ;restrict to constant x?
            ACL2::EQUAL-OF-BVIF-alt ;restrict to constant x?
            ACL2::BVCHOP-OF-BVIF
            ;; just include boolean-rules?
            acl2::boolif-when-quotep-arg2
            acl2::boolif-when-quotep-arg3
            acl2::bvchop-1-becomes-getbit
            ACL2::BVCHOP-OF-BVSX
            ACL2::BVCHOP-OF-BVUMINUS-SAME
            ACL2::BVUMINUS-OF-BVUMINUS
            ACL2::BVSX-OF-BVCHOP
            ACL2::BVCHOP-OF-BVCHOP
            ACL2::BVPLUS-OF-BVCHOP-ARG2
            ACL2::EQUAL-OF-BVSX-AND-BVSX
            acl2::equal-same
            ACL2::BVPLUS-OF-LOGEXT ; rename
            ACL2::BVPLUS-OF-LOGEXT-arg1 ; rename
            ACL2::BVUMINUS-OF-LOGEXT
            ACL2::SIGNED-BYTE-P-OF-BVIF
            ACL2::LOGEXT-IDENTITY
            ACL2::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-ONE-LESS
            ;ACL2::BOOLIF-X-X-Y-BECOMES-BOOLOR ; introduces boolor
            ACL2::BVLT-OF-CONSTANT-WHEN-USB-DAG
            boolor-becomes-boolif
            ;bvlt-hack-1-gen
            ACL2::BVCHOP-SUBST-CONSTANT
            ACL2::BVCHOP-SUBST-CONSTANT-alt
            ;; acl2::boolif-of-t-and-nil-when-booleanp
            ACL2::BOOL-FIX$INLINE-CONSTANT-OPENER
            boolif-of-bvlt-strengthen-to-equal
            bvlt-reduce-when-not-equal-one-less
            ;; trying opening these up if they surive to the proof stage (TODO: Add the rest, or drop these?):
            jp-condition
            jnp-condition
            jz-condition
            jnz-condition)
          (float-rules) ; I need booleanp-of-isnan, at least
          (extra-tester-rules)
          (lifter-rules64-new) ; overkill?
          (acl2::base-rules)
          (acl2::core-rules-bv) ; trying
          (acl2::unsigned-byte-p-rules)
          (acl2::unsigned-byte-p-forced-rules)))
