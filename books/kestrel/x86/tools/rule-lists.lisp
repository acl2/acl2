; Rule lists used for x86 reasoning
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
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

            x86isa::gpr-sub-spec-1$inline
            x86isa::gpr-sub-spec-2$inline
            x86isa::gpr-sub-spec-4$inline
            x86isa::gpr-sub-spec-8$inline

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
            )
          *instruction-decoding-and-spec-rules*))

(defun list-rules2 ()
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

    x86isa::wml32
    x86isa::wml64           ;shilpi leaves this enabled, but this is big!
    x86isa::wml-size$inline ;shilpi leaves this enabled

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
    ))

(defun read-rules ()
  '(unsigned-byte-p-of-read
    integerp-of-read
    <-of-read-and-non-positive
    read-of-xw-irrel
    read-of-set-flag
    read-when-program-at
    read-of-logext-48
    read-when-equal-of-read
    read-when-equal-of-read-alt
    ))

(defun write-rules ()
  '(write-of-bvchop-arg3-gen
    xr-of-write
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
    program-at-of-write))

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
    x86isa::x86p-of-set-flag
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

    ACL2::BFIX-WHEN-BITP
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

    ;;todo: not x86-specific
    acl2::integerp-of-logext
    acl2::integerp-of--))

(defun x86-bv-rules ()
  '(acl2::bvlt-of-0-arg3 ;todo: more like this?
    ACL2::LOGHEAD-BECOMES-BVCHOP
    acl2::logext-of-bvplus-64 ;somewhat unusual
    logior-becomes-bvor-axe
    x86isa::n08-to-i08$inline ;this is just logext
    x86isa::slice-of-part-install-width-low
    x86isa::bvchop-of-part-install-width-low-becomes-bvcat

    ;;todo: try core-runes-bv:
    acl2::slice-of-slice-gen-better ;figure out which bv rules to include
    acl2::bvcat-when-lowsize-is-0
    acl2::bvcat-when-highsize-is-0

    bitops::rotate-left-32$inline-constant-opener ;todo: gen to a full rewrite
    acl2::rotate-left-constant-opener
    acl2::logext-trim-arg-axe-all

    acl2::bvuminus-of-logext
    acl2::bvchop-of-if-when-constants
    acl2::bvplus-recollapse ;rename
    ))

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
  '(x86isa::if-x-nil-t
    x86isa::if-of-not
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
   x86isa::run-until-rsp-greater-than-of-if-arg2 ;careful, this can cause splits:
   ))

(defun simple-opener-rules ()
  '(x86isa::n08p$inline ;just unsigned-byte-p
    ; 64-bit-modep ; using rules about this instead, since this is no longer just true
    ))

;; These open the branch conditions, without trying to make the expressions nice.
;; Instead, consider adding more rules like jle-condition-rewrite-1.
;; TODO: Some of these are only for 64 or only for 32 bit mode?
(defun branch-condition-openers ()
  '(jo-condition
    jno-condition
    jb-condition
    jnb-condition
    jz-condition
    jnz-condition
    jbe-condition
    jnbe-condition
    js-condition
    jns-condition
    jp-condition
    jnp-condition
    jl-condition
    jnl-condition
    jle-condition
    jnle-condition))

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

    x86isa::cf-spec16$inline-constant-opener
    x86isa::of-spec16$inline-constant-opener
    x86isa::pf-spec16$inline-constant-opener
    x86isa::sf-spec16$inline-constant-opener
    x86isa::adc-af-spec16$inline-constant-opener
    x86isa::add-af-spec16$inline-constant-opener
    x86isa::sub-af-spec16$inline-constant-opener

    x86isa::cf-spec32$inline-constant-opener
    x86isa::of-spec32$inline-constant-opener
    x86isa::pf-spec32$inline-constant-opener
    x86isa::sf-spec32$inline-constant-opener
    x86isa::adc-af-spec32$inline-constant-opener
    x86isa::add-af-spec32$inline-constant-opener
    x86isa::sub-af-spec32$inline-constant-opener

    acl2::bool->bit$inline-base
;    byte-ify-base
;    x86isa::byte-listp-unroll ;todo: improve (the __function__ put in by define makes this gross)
;    x86isa::byte-listp-base-1

    ;; These are needed just because Axe cannot evaluate calls to these
    ;; functions:
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

;; todo: move some of these to lifter-rules32 or lifter-rules64
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
          (list-rules2)
          (state-rules)
          (if-rules)
          (decoding-and-dispatch-rules)
          (x86-type-rules)
          (x86-bv-rules)
          (acl2::unsigned-byte-p-forced-rules)
          (if-lifting-rules)
          '(ACL2::BOOLOR-OF-NON-NIL)
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
            x86isa::n16$inline
            x86isa::n32$inline
            x86isa::n64$inline

            ;; This is just logext:
            x86isa::i64$inline

            ;; These are just logext:
            x86isa::n08-to-i08$inline
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
            sub-af-spec32-same ; rewrites to 0, so perhaps worth including this rule

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
            x86isa::rb-wb-equal
            x86isa::rb-of-if-arg2

;            x86isa::set-flag-of-mv-nth-1-of-wb

            return-last
            ;; symbolic execution (perhaps separate these out):
            run-until-return
            run-until-rsp-greater-than-opener
            run-until-rsp-greater-than-base
            rsp-greater-than

            ;; x86-fetch-decode-execute-opener ; this had binding hyps
            ;; x86-fetch-decode-execute ; this splits into too many cases when things can't be resolved
            x86isa::x86-fetch-decode-execute-base

            ms x86isa::ms$a                            ;expose the call to xr
            fault x86isa::fault$a                         ;expose the call to xr
            x86isa::rip x86isa::rip$a                           ;expose the call to xr
;            app-view$inline         ;expose the call to xr

            the-check
            ;; get-prefixes:
            x86isa::get-prefixes-does-not-modify-x86-state-in-app-view-new ;targets mv-nth-3-of-get-prefixes
            x86isa::mv-nth-0-of-get-prefixes-of-xw-of-irrel
            x86isa::mv-nth-1-of-get-prefixes-of-xw-of-irrel
            ;; get-prefixes openers:
            X86ISA::GET-PREFIXES-BASE-1
            X86ISA::GET-PREFIXES-BASE-2
            X86ISA::GET-PREFIXES-BASE-3
            X86ISA::GET-PREFIXES-BASE-4
            X86ISA::GET-PREFIXES-BASE-5
            X86ISA::GET-PREFIXES-BASE-6
            X86ISA::GET-PREFIXES-BASE-7
            X86ISA::GET-PREFIXES-BASE-8
            X86ISA::GET-PREFIXES-UNROLL-1
            X86ISA::GET-PREFIXES-UNROLL-2
            X86ISA::GET-PREFIXES-UNROLL-3
            X86ISA::GET-PREFIXES-UNROLL-4
            ;; x86isa::get-prefixes-opener-lemma-no-prefix-byte
            ;; x86isa::get-prefixes-opener-lemma-group-1-prefix-simple
            ;; x86isa::get-prefixes-opener-lemma-group-2-prefix-simple
            ;; x86isa::get-prefixes-opener-lemma-group-3-prefix-simple
            ;; x86isa::get-prefixes-opener-lemma-group-4-prefix-simple


            x86isa::mv-nth-of-cons ;mv-nth ;or do mv-nth of cons.  rules like rb-in-terms-of-nth-and-pos-eric target mv-nth

            x86isa::canonical-address-p-of-logext-48
            x86isa::logext-48-does-nothing-when-canonical-address-p

            x86isa::create-canonical-address-list-1

            x86isa::rb-in-terms-of-nth-and-pos-eric-gen ;rb-in-terms-of-nth-and-pos-eric
            x86isa::rb-returns-no-error-app-view ;targets mv-nth-0-of-rb
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

            acl2::hack-arith-cancel
            acl2::<-of-+-of-1-same-alt ;pretty specific
            acl2::integerp-of-+-when-integerp-1-cheap
            x86isa::fix-when-integerp
            x86isa::integerp-when-canonical-address-p-cheap
            x86isa::member-p-canonical-address-listp
            acl2::fold-consts-in-+
            acl2::cancel-<-+
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
            x86isa::rb-returns-x86-app-view ;targets mv-nth 2 of rb


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
            logand-becomes-bvand-axe-arg1
            logand-becomes-bvand-axe-arg2
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
            acl2::bvplus-recollapse ;rename
            acl2::bvchop-of-bvplus
            acl2::bvchop-identity
;            combine-bytes-and-byte-ify
            x86isa::open-ash-positive-constants
            acl2::logext-bvchop-better
            acl2::logext-identity
            ;x86isa::rgfi-is-i64p ;targets signed-byte-of-xr
;            x86isa::xw-xr-same
            ;; acl2::bvplus-commutative-dag ;is this based on nodenum or term weight?



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

            acl2::bvplus-of-bvchop-arg1
            acl2::bvplus-of-bvchop-arg2
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
            x86isa::rb-returns-x86-app-view
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

            acl2::logext-of-sum-trim-constant-big
            acl2::logext-of-sum-trim-constant
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
            acl2::bvmult-commutative-dag
            acl2::bvmult-of-bvcat-of-0
            acl2::bvmult-of-bvchop-arg3


            x86isa::disjoint-p-two-create-canonical-address-lists-thm-0-gen
            x86isa::disjoint-p-two-create-canonical-address-lists-thm-1-gen
            x86isa::not-memberp-of-+-when-disjoint-from-larger-chunk-pos ;only needed for pe file?

            acl2::bvplus-recollapse ;todo: rename
            acl2::bvplus-of-unary-minus
            acl2::bvplus-of-logext-arg1
            acl2::bvplus-of-logext
            acl2::slice-of-bvchop-low
            x86isa::rflags x86isa::rflags$a ;exposes xr
;            x86isa::rflags-set-flag ;targets xr-of-set-flag ;drop?
            x86isa::part-install-width-low-becomes-bvcat-32
            x86isa::rflags-is-n32p-unforced
             ;targets unsigned-byte-p-of-rflags
;                    acl2::bvcat-trim-arg2-dag-all
 ;                   acl2::bvcat-trim-arg1-dag-all

            x86isa::64-bit-modep-of-xw
            x86isa::64-bit-modep-of-mv-nth-1-of-wb
            x86isa::64-bit-modep-of-set-flag

            ;;todo: include all of the lifter rules:
            x86isa::canonical-address-p-of-i48
            x86isa::i48-when-canonical-address-p
            x86isa::select-address-size$inline
            x86isa::mv-nth-of-if
            x86isa::canonical-address-p-of-if
            read-in-terms-of-nth-and-pos-eric-4-bytes

            jle-condition-rewrite-1
            jle-condition-rewrite-2
            jle-condition-rewrite-3
            jnle-condition-rewrite
            jnle-condition-rewrite-2
            jnle-condition-rewrite-2-alt
            jnle-condition-rewrite-3-32
            jnl-condition-rewrite-1
            jnl-condition-rewrite-1-32
            jnl-condition-rewrite-1-32-constant-version
            jnle-condition-rewrite-3
            jnz-condition-rule-2

            x86isa::memory-byte-accesses-are-always-aligned
            x86isa::address-aligned-p-of-8-and-nil
            x86isa::address-aligned-p-of-4-and-nil

            acl2::bvplus-trim-leading-constant
            acl2::bvplus-of-0
            acl2::bvchop-subst-constant
            x86isa::byte-listp-becomes-all-unsigned-byte-p
            acl2::lnfix$inline
            gl::gl-mbe-fn ;used by bitops.  yuck.

            x86isa::x86-operation-mode
            x86isa::alignment-checking-enabled-p-of-xw-irrel
            return-last
            acl2::slice-of-bvcat-gen
            /= ;"not equal"

            acl2::truncate-becomes-floor-gen ;it might be better to avoid explosing truncate in the first place

            acl2::<-of-constant-when-<-of-constant-integer
            acl2::<-of-constant-when-<=-of-constant-integer
            acl2::bvplus-of-+-combine-constants

            common-lisp::logcount-constant-opener ; for flags
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

            )))

;; note: mv-nth-1-wb-and-set-flag-commute loops with set-flag-and-wb-in-app-view

;; Used in both versions of the lifter
;; TODO: Split into 32-bit and 64-bit rules:
(defun assumption-simplification-rules ()
  (append
   '(standard-state-assumption
     standard-assumptions-core-64
     standard-state-assumption-32
     standard-assumptions-mach-o-64
     standard-assumptions-pe-64
     bytes-loaded-in-text-section-64
     acl2::get-mach-o-code
     acl2::subroutine-address-mach-o
     acl2::get-mach-o-code-address
     acl2::get-mach-o-segment
     acl2::get-mach-o-section
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
     acl2::+-commutative-dag
     unicity-of-0
     all-addreses-of-stack-slots
     ms X86ISA::ms$A
     fault X86ISA::fault$A
     rgfi X86ISA::RGFI$A ;expose xr
     canonical-address-p-of-0
     addresses-of-subsequent-stack-slots
     addresses-of-subsequent-stack-slots-aux-base
     addresses-of-subsequent-stack-slots-aux-unroll
     x86isa::canonical-address-listp-of-cons
     x86isa::canonical-address-p-between-special1
     x86isa::canonical-address-p-between-special2
     x86isa::canonical-address-p-between-special3
     acl2::fold-consts-in-+
     x86isa::canonical-address-listp-of-nil
     )
   (acl2::lookup-rules)))

(defun myif-rules ()
  (append '(acl2::myif-same-branches ;add to lifter-rules?
            acl2::myif-t-nil
            acl2::myif-nil-t
            ;; acl2::boolif-of-nil-and-t ;redundant?
            )
          (acl2::boolean-rules)
          ;; '(acl2::boolif-x-x-y
          ;; acl2::boolif-x-y-x
          ;; acl2::boolif-same-branches
          ;; acl2::boolif-when-quotep-arg1
          ;; acl2::boolif-when-quotep-arg2
          ;; acl2::boolif-when-quotep-arg3)
          ))

(defun lifter-rules32 ()
  (append (lifter-rules-common)
          '(;; x86isa::get-prefixes-opener-lemma-group-1-prefix-simple-32
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
            acl2::<-becomes-bvlt-dag-both
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

(defun lifter-rules64 ()
  (append (lifter-rules-common)
          (read-introduction-rules)
          (write-introduction-rules)
          (read-rules)
          (write-rules)
          (read-byte-rules)
          (linear-memory-rules)
          '(x86isa::rme08-when-64-bit-modep-and-not-fs/gs
            x86isa::rme-size-when-64-bit-modep-and-not-fs/gs
            x86isa::wme-size-when-64-bit-modep-and-not-fs/gs
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

    fix-of-ifix

    ;; Rules about EIP/SET-EIP:
    xw-becomes-set-eip
    xw-of-set-eip-irrel
    xr-of-set-eip-irrel
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
    integerp-of-if
;    canonical-address-p-of-+-of-mv-nth-1-of-ea-to-la-of-ss
    x86isa::if-x-x-y
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
    write-byte-to-segment-of-set-edx
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

    acl2::bvplus-of-constant-when-overflow ;move?  targets things like (BVPLUS 32 4294967280 (ESP X86))
    read-stack-dword-of-write-to-segment-diff-segments
    write-to-segment-of-write-byte-to-segment-included
    write-to-segment-of-write-to-segment-included
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
;;   :monitor (run-until-rsp-greater-than-opener
;;             acl2::get-prefixes-opener-lemma-no-prefix-byte-conjunct-1 ;todo: handle multi-conjunct rules better
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
;;             run-until-rsp-greater-than-opener
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
;; ;; ;acl2::<-becomes-bvlt-dag-both
;; ;; ;            read-byte-from-segment-when-code-segment-assumptions32
;; ;;  ;           mv-nth-1-of-add-to-*sp
;; ;;   ;          not-mv-nth-0-of-add-to-*sp
;; ;;             ;x86isa::write-*sp-when-not-64-bit-modep-gen
;; ;; ;            run-until-rsp-greater-than-opener
;; ;;             read-*ip-becomes-eip-gen
;; ;;             code-segment-assumptions32-of-write-to-segment-of-ss
;;             )

(defun debug-rules32 ()
  '(run-until-rsp-greater-than-opener
    not-mv-nth-0-of-wme-size ;gets rid of error branch
    mv-nth-1-of-wme-size     ;introduces write-to-segment
    not-mv-nth-0-of-add-to-*sp-gen
    mv-nth-1-of-add-to-*sp-gen))
