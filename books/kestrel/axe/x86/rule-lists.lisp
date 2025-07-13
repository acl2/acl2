; Rule Lists used by the x86 Axe tools
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "kestrel/axe/rule-lists" :dir :system)
(include-book "kestrel/utilities/defconst-computed" :dir :system)
(include-book "../priorities")

(include-book "projects/x86isa/machine/instructions/top" :dir :system) ;needed to get the full ruleset instruction-decoding-and-spec-rules

;; TODO: Use union-equal instead of append?  Or even, in some cases, a version that detects duplicates.

;todo: add a variant of get-ruleset that complains if the ruleset doesn't exist..
(acl2::defconst-computed-simple *instruction-decoding-and-spec-rules*
  (acl2::get-ruleset 'x86isa::instruction-decoding-and-spec-rules (w state)))

(defun map-add-suffix (syms str)
  (declare (xargs :guard (and (symbol-listp syms)
                              (stringp str))))
  (if (endp syms)
      nil
    (cons (add-suffix (first syms) str)
          (map-add-suffix (rest syms) str))))

;; todo: some of these should be added to the X86 package:

;; n08$inline and many more
;; todo: go directly to bvchop?
(acl2::defconst-computed-simple *unsigned-choppers* (map-add-suffix (acl2::get-ruleset 'x86isa::nw-defs (w state)) "$INLINE"))

;; i08$inline and many more
(acl2::defconst-computed-simple *signed-choppers* (map-add-suffix (acl2::get-ruleset 'x86isa::iw-defs (w state)) "$INLINE"))

;; n08p$inline and many more
(acl2::defconst-computed-simple *unsigned-recognizers* (map-add-suffix (acl2::get-ruleset 'x86isa::nwp-defs (w state)) "$INLINE"))

;; i08p$inline and many more
(acl2::defconst-computed-simple *signed-recognizers* (map-add-suffix (acl2::get-ruleset 'x86isa::iwp-defs (w state)) "$INLINE"))

;; Most of these are just names of functions to open
(defund instruction-rules ()
  (declare (xargs :guard t))
  (append '(x86isa::gpr-arith/logic-spec-1 ;; dispatches based on operation
            x86isa::gpr-arith/logic-spec-2 ;; dispatches based on operation
            x86isa::gpr-arith/logic-spec-4 ;; dispatches based on operation
            x86isa::gpr-arith/logic-spec-8 ;; dispatches based on operation

            x86isa::gpr-and-spec-1-alt-def
            x86isa::gpr-and-spec-2-alt-def
            x86isa::gpr-and-spec-4-alt-def
            x86isa::gpr-and-spec-8-alt-def

            x86isa::gpr-or-spec-1-alt-def
            x86isa::gpr-or-spec-2-alt-def
            x86isa::gpr-or-spec-4-alt-def
            x86isa::gpr-or-spec-8-alt-def

            x86isa::gpr-adc-spec-1-alt-def
            x86isa::gpr-adc-spec-2-alt-def
            x86isa::gpr-adc-spec-4-alt-def
            x86isa::gpr-adc-spec-8-alt-def ;x86isa::gpr-adc-spec-8$inline
            x86isa::open-carry-of-rflagsbits->cf
            ;; open-carry-of-cf-spec8 ; open the cf function when used in certain places, like gpr-adc-spec-8
            ;; open-carry-of-cf-spec16
            ;; open-carry-of-cf-spec32
            ;; open-carry-of-cf-spec64
            open-carry-constant-opener ; also open when applied to a constant (or refrain from even this?)
            integerp-of-open-carry

            x86isa::gpr-xor-spec-1-alt-def
            x86isa::gpr-xor-spec-2-alt-def
            x86isa::gpr-xor-spec-4-alt-def
            gpr-xor-spec-8-alt-def-axe

            x86isa::gpr-add-spec-1-alt-def
            x86isa::gpr-add-spec-2-alt-def
            x86isa::gpr-add-spec-4-better ; $inline ; todo: make better rules for the rest
            ;;x86isa::gpr-add-spec-4-alt-def
            x86isa::gpr-add-spec-8-alt-def

            ;; x86isa::gpr-sub-spec-1$inline
            ;; x86isa::gpr-sub-spec-2$inline
            ;; x86isa::gpr-sub-spec-4$inline
            ;; x86isa::gpr-sub-spec-8$inline
            x86isa::gpr-sub-spec-1-alt-def
            x86isa::gpr-sub-spec-2-alt-def
            x86isa::gpr-sub-spec-4-alt-def-better
            ;;x86isa::gpr-sub-spec-4-alt-def ;; todo: make better versions of all of these, and of more ops
            x86isa::gpr-sub-spec-8-alt-def

            ;; unsigned multiply
            x86isa::mul-spec$inline ;; dispatches based on size
            x86isa::mul-spec-8 ; todo: make alt-defs with better rflags handling?
            x86isa::mul-spec-16
            x86isa::mul-spec-32
            x86isa::mul-spec-64

            ;; signed multiply
            x86isa::imul-spec$inline ;; dispatches based on size
            x86isa::imul-spec-8
            x86isa::imul-spec-16
            x86isa::imul-spec-32
            x86isa::imul-spec-64

            x86isa::div-spec$inline ; just a dispatch on the size
            ;; These recharacterize divide in terms of bvops:
            mv-nth-0-of-div-spec-8
            mv-nth-1-of-div-spec-8
            mv-nth-2-of-div-spec-8
            mv-nth-0-of-div-spec-16
            mv-nth-1-of-div-spec-16
            mv-nth-2-of-div-spec-16
            mv-nth-0-of-div-spec-32
            mv-nth-1-of-div-spec-32
            mv-nth-2-of-div-spec-32
            mv-nth-0-of-div-spec-64
            mv-nth-1-of-div-spec-64
            mv-nth-2-of-div-spec-64

            x86isa::idiv-spec$inline
            ;;X86ISA::IDIV-SPEC-64 ;need to re-characterize this as something nice
            x86isa::idiv-spec-64-trim-arg1-axe-all
            mv-nth-0-of-idiv-spec-32 ; more?
            mv-nth-1-of-idiv-spec-32
            mv-nth-0-of-idiv-spec-64
            mv-nth-1-of-idiv-spec-64

            x86isa::shr-spec$inline ;; dispatches based on size
            ;; x86isa::shr-spec-8
            ;; x86isa::shr-spec-16
            ;; x86isa::shr-spec-32
            ;; x86isa::shr-spec-64
            x86isa::shr-spec-8-alt-def
            x86isa::shr-spec-16-alt-def
            x86isa::shr-spec-32-alt-def
            x86isa::shr-spec-64-alt-def
            acl2::bvshr-rewrite-for-constant-shift-amount ; puts in slice, since we don't translate bvshr to stp

            x86isa::sal/shl-spec$inline ;; dispatches based on size
            ;; x86isa::sal/shl-spec-8
            ;; x86isa::sal/shl-spec-16
            ;; x86isa::sal/shl-spec-32
            ;; x86isa::sal/shl-spec-64
            x86isa::sal/shl-spec-8-alt-def
            x86isa::sal/shl-spec-16-alt-def
            x86isa::sal/shl-spec-32-alt-def
            x86isa::sal/shl-spec-64-alt-def
            ;; ACL2::BVSHL-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT ; todo: consider this since we don't translate bvshl to stp

            x86isa::shlx-spec$inline ; just a dispatch
            x86isa::shlx-spec-32-alt-def
            x86isa::shlx-spec-64-alt-def

            x86isa::shrx-spec$inline ; just a dispatch
            x86isa::shrx-spec-32-alt-def
            x86isa::shrx-spec-64-alt-def

            x86isa::sarx-spec$inline ; just a dispatch
            x86isa::sarx-spec-32-alt-def
            x86isa::sarx-spec-64-alt-def

            x86isa::sar-spec$inline
            ;x86isa::sar-spec-32-nice
            ;x86isa::sar-spec-64-nice
            x86isa::sar-spec-8-alt-def
            x86isa::sar-spec-16-alt-def
            x86isa::sar-spec-32-alt-def
            x86isa::sar-spec-64-alt-def

            x86isa::rol-spec$inline ;; dispatches based on size
            x86isa::rol-spec-8
            x86isa::rol-spec-16
            x86isa::rol-spec-32
            x86isa::rol-spec-64

            x86isa::ror-spec$inline ; just a dispatch
            x86isa::ror-spec-8
            x86isa::ror-spec-16
            x86isa::ror-spec-32
            ror-spec-64-alt-def ; x86isa::ror-spec-64

            x86isa::x86-operand-to-xmm/mem

            x86isa::simd-add-spec-base-1 x86isa::simd-add-spec-base-2 x86isa::simd-add-spec-unroll
            x86isa::simd-sub-spec-base-1 x86isa::simd-sub-spec-base-2 x86isa::simd-sub-spec-unroll

            ;; Improved versions of instruction semantic functions:
            x86isa::x86-cbw/cwd/cdqe-alt-def
            x86isa::x86-cwd/cdq/cqo-alt-def)
          (set-difference-equal *instruction-decoding-and-spec-rules*
                                ;; We remove these because we have better versions:
                                '(x86isa::x86-cbw/cwd/cdqe
                                  x86isa::x86-cwd/cdq/cqo))))

;; todo: can we just use list-rules?
(defund list-rules-x86 ()
  (declare (xargs :guard t))
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

;; For 64-bit mode and low-level 32-bit mode proofs.
;; When using these, also include (read-rules) and (write-rules).
(defund linear-memory-rules ()
  (declare (xargs :guard t))
  '(;; Rules about reads:

    x86isa::rime-size-when-64-bit-modep-and-not-fs/gs ; introduces riml-size
    x86isa::rime-size-when-64-bit-modep-fs/gs ; introduces segment-base-and-bounds and riml-size

    rme08-of-0-when-not-fs/gs-becomes-read ;; x86isa::rme08-when-64-bit-modep-and-not-fs/gs ; puts in rml08
    x86isa::rme16-when-64-bit-modep-and-not-fs/gs ; todo: go to read like we do for rme08? at least make strong versions that put the canonical hyp in the conclusion
    x86isa::rme32-when-64-bit-modep-and-not-fs/gs
    x86isa::rme48-when-64-bit-modep-and-not-fs/gs
    x86isa::rme64-when-64-bit-modep-and-not-fs/gs
    x86isa::rme80-when-64-bit-modep-and-not-fs/gs
    x86isa::rme128-when-64-bit-modep-and-not-fs/gs
    x86isa::rme256-when-64-bit-modep-and-not-fs/gs

    ;; rme-size can arize in 64-bit mode (e.g., when a stack protection value is read via the FS segment register):
    x86isa::rme-size-when-64-bit-modep-and-not-fs/gs-strong ; puts in rml-size
    x86isa::rme-size-when-64-bit-modep-fs/gs ; exposes segment-base-and-bounds and rml-size

    ;; Rules about rimlXX (there are only 4 of these):
    ;; We open these to expose RML08, etc (handled below):
    ;; TODO: go directly to logext of read
    riml08
    riml16
    riml32
    riml64
    riml-size$inline ; dispatches to riml08, etc.
    ;; riml-size-of-1-becomes-read ; todo: try these (for which proofs?)
    ;; riml-size-of-2-becomes-read
    ;; riml-size-of-4-becomes-read
    ;; riml-size-of-8-becomes-read

    rml-size$inline ;; dispatches to rml08, etc.  can become RB but only for ill-guarded calls.
    ;; rml-size-of-1-becomes-read ;; todo: try these, or combine them
    ;; rml-size-of-2-becomes-read
    ;; rml-size-of-4-becomes-read
    ;; rml-size-of-6-becomes-read
    ;; rml-size-of-8-becomes-read
    ;; rml-size-of-10-becomes-read
    ;; rml-size-of-16-becomes-read
    ;; rml-size-of-32-becomes-read
    ;; Or we could open these to expose RB and turn that into READ:
    rml08-becomes-read
    rml16-becomes-read
    rml32-becomes-read
    rml48-becomes-read
    rml64-becomes-read
    rml80-becomes-read
    rml128-becomes-read ;; x86isa::rml128-when-app-view ; introduces rb (handled below)
    rml256-becomes-read ;; x86isa::rml256-when-app-view ; introduces rb
    rml512-becomes-read ;;

    ;; rb-becomes-read ; could uncomment if RB ever shows up ; no need to target mv-nth-1-of-rb, etc. since this rewrites the entire rb
    ;; These just clarify failures to turn RB into READ: ; TODO: Only use when debugging?
    ;mv-nth-1-of-rb-of-set-rip
    ;mv-nth-1-of-rb-of-set-rax ; could add more like this
    ;; x86isa::mv-nth-0-of-rb-of-1 ; todo: gen
    ;; x86isa::rb-returns-no-error-app-view ;targets mv-nth-0-of-rb
    ;; x86isa::rb-in-terms-of-nth-and-pos-eric-gen ;rb-in-terms-of-nth-and-pos-eric ;targets mv-nth-1-of-rb ; todo: or do we just always go to read?
    ;;x86isa::rb-returns-x86-app-view ;targets mv-nth-2-of-rb

    ;; Rules about writes:

    x86isa::wme-size-when-64-bit-modep-and-not-fs/gs-strong ; puts in wml-size
    x86isa::wime-size-when-64-bit-modep-and-not-fs/gs

    ;; Rules about wimlXX (there are only 4 of these):
    ;; We open these to expose WML08, etc (handled below)::
    ;; TODO: Go directly to WRITE
    wiml08
    wiml16
    wiml32
    wiml64
    wiml-size$inline ; dispatches to wiml08, etc.

    wml-size$inline ; dispatches to wml08, etc.  can go to wb but only for ill-guarded calls.
    ;; TODO: Go directly to WRITE?
    wml08
    wml16
    wml32
    wml48
    wml64
    wml80
    x86isa::wml128-when-app-view
    x86isa::wml256-when-app-view
    x86isa::wml512-when-app-view

    wb-becomes-write-when-app-view
    ))

;; (set-axe-rule-priority rb-becomes-read -1) ; get rid of RB immediately


;; Now we just go to read
;; (defun read-byte-rules ()
;;   (declare (xargs :guard t))
;;   '(read-byte-of-xw-irrel
;;     ;;read-byte-when-program-at read-byte-when-program-at-gen
;;     read-byte-of-set-flag
;;     read-byte-of-write-byte
;;     read-byte-of-logext
;;     ))

;todo: some are only needed with the new normal forms
(defund read-rules ()
  (declare (xargs :guard t))
  '(unsigned-byte-p-of-read
    integerp-of-read
    natp-of-read
    <-of-read-and-non-positive
    read-of-xw-irrel
    read-of-set-flag
    read-of-!rflags
    read-of-set-undef
    read-of-set-mxcsr

    read-when-program-at ; trying just this one
    ;; since read-when-program-at can introduce bv-array-read-chunk-little
    ;; acl2::bv-array-read-chunk-little-constant-opener ; drop now that we can eval it
    acl2::bv-array-read-chunk-little-base ; todo: try to do better than these in some cases (try the other rules first)
    acl2::bv-array-read-chunk-little-unroll
    ;; read-when-program-at-1-byte-simple
    ;; read-when-program-at-2-bytes
    ;; read-when-program-at-4-bytes
    ;; read-when-program-at-8-bytes
    read-of-logext
    read-when-equal-of-read
    read-when-equal-of-read-alt
    <-of-constant-and-read ; in case we backchain to < to try to resolve a bvlt
    <-of-read-and-constant ; in case we backchain to < to try to resolve a bvlt
    bvchop-of-read
    trim-of-read
    slice-of-read
    svblt-of-read-trim-arg2
    svblt-of-read-trim-arg3

    ;; we will just unroll read-chunks (at least for now):
    read-chunks-base
    read-chunks-unroll))

;; Mostly for 64-bit mode
;todo: some are only needed with the new normal forms
(defund write-rules ()
  (declare (xargs :guard t))
  '(xr-of-write-when-not-mem
    x86p-of-write
    64-bit-modep-of-write
    app-view-of-write
    alignment-checking-enabled-p-of-write
    get-flag-of-write
    ctri-of-write ; may be needed for lifter, which does not use the new-normal-form-rules64 (todo: move other similar rules here?)
    undef-of-write
    mxcsr-of-write
    ms-of-write
    fault-of-write
    set-undef-of-write
    msri-of-write

    write-of-xw-irrel
    set-flag-of-write

    ;; I guess we are not normalizing write nests, perhaps due to partial overlap?  could sort when known disjoint...
    write-of-write-same
    write-of-write-of-write-same
    write-of-write-of-write-of-write-same
    ;; write-of-write-of-write-of-write-of-write-same

    write-of-bvchop-arg3-gen
    ))

(defund region-rules ()
  (declare (xargs :guard t))
  '( ;; WARNING: Keep in sync with the list for 64 bits below
    in-region48p-cancel-constants-1-1+
    in-region48p-cancel-constants-1+-1
    in-region48p-cancel-constants-1+-1+
    in-region48p-cancel-1-1+
    in-region48p-cancel-1+-1
    in-region48p-cancel-1+-1+
    in-region48p-cancel-1-2
    in-region48p-cancel-2-1
    in-region48p-cancel-2+-1
    in-region48p-cancel-1+-2
    in-region48p-cancel-2-1+
    in-region48p-cancel-2+-1
    in-region48p-cancel-1-3
    in-region48p-cancel-3-1
    in-region48p-cancel-2-2
    in-region48p-when-non-negative-and-negative-range
    in-region48p-of-0-arg3 ; introduces bvlt
    in-region48p-of-bvchop-arg1
    in-region48p-of-bvchop-arg3
    in-region48p-same

    ;; Seems ok to always have these on: ; todo: add more
    disjoint-regions48p-cancel-1-1+
    disjoint-regions48p-cancel-1+-1
    disjoint-regions48p-cancel-1+-1+
    disjoint-regions48p-cancel-1-2
    disjoint-regions48p-cancel-2-1
    disjoint-regions48p-cancel-1+-2
    disjoint-regions48p-cancel-2-1+
    disjoint-regions48p-cancel-2-2
    disjoint-regions48p-cancel-2+-2
    disjoint-regions48p-of-bvplus-of-constant-and-constant
    subregion48p-cancel-1-1
    subregion48p-cancel-1+-1
    subregion48p-cancel-1-1+
    subregion48p-cancel-2-1
    subregion48p-cancel-2-1+
    subregion48p-cancel-1-2
    subregion48p-cancel-1+-2
    subregion48p-cancel-2-2
    subregion48p-cancel-constants-1+-1
    subregion48p-cancel-constants-1+-1+
    subregion48p-reduce-sizes
    ;; subregion48p-same-ads-same-lens ; consider this
    subregion48p-when-non-negative-and-negative-range
    subregion48p-of-1-arg1 ; introduces in-region48p
    acl2::bvminus-of-bvplus-and-bvplus-same-2-2 ; move?  open bvminus?
    acl2::bvminus-of-bvplus-same
    subregion48p-of-bvchop-arg2
    subregion48p-of-bvchop-arg4
    disjoint-regions48p-of-bvchop-arg2
    disjoint-regions48p-of-bvchop-arg4
    acl2::bvmult-tighten-when-power-of-2p-axe ; helps rules like in-region48p-when-non-negative-and-negative-range fire
    ))

;; Non-SMT-amendable read-of-write rules:
(defund read-and-write-rules-non-bv ()
  (declare (xargs :guard t))
  '(read-of-write-irrel
    read-of-write-when-separate ; todo: rename to have separate in the name
    ))

;; SMT-amendable read-of-write rules:
(defund read-and-write-rules-bv ()
  (declare (xargs :guard t))
  '(read-of-write-when-disjoint-regions48p-gen
    read-of-write-when-disjoint-regions48p-gen-alt
    read-of-write-when-disjoint-regions48p ; for different regions with the same base address?
    read-of-write-of-write-irrel-inner-bv ; can clarify failures
    read-of-write-of-write-of-write-same-middle-bv ; can clarify failures
    in-region48p-of-+-arg1
    in-region48p-of-+-arg3
    in-region48p-of-logext-arg1
    in-region48p-of-logext-arg3
    in-region48p-of-bvplus-tighten-arg1
    in-region48p-of-bvplus-tighten-arg3
    subregion48p-of-+-arg2
    subregion48p-of-+-arg4
    disjoint-regions48p-of-+-arg2
    disjoint-regions48p-of-+-arg4
    read-of-+-arg2
    write-of-+-arg2
    read-when-equal-of-read-and-subregion48p ; for a program-at-like hyp
    read-when-equal-of-read-bytes-and-subregion48p ; for a program-at-like hyp todo: add alt version?
    read-when-equal-of-read-and-subregion48p
    read-when-equal-of-read-and-subregion48p-alt
    acl2::bvchop-of-+-becomes-bvplus
    acl2::bvplus-of-*-arg1
    acl2::bvplus-of-*-arg2
    acl2::bvminus-of-bvplus-tighten-arg2
    acl2::bvminus-of-bvplus-tighten-arg3
    ))

;; Rules about the actual functions READ and WRITE.
(defund read-and-write-rules ()
  (declare (xargs :guard t))
  (append
  '(read-1-of-write-1-diff
    ;read-1-of-write-1-both-alt ; trying
    read-of-write-same
    ;; read-of-write-within-same-address  ;todo: uncomment but first simplify the assumptions we give about RSP
    ;; todo: more variants of these:
    ;; todo: uncomment:
    ;;read-of-write-of-set-flag ; these just make terms nicer (todo: these break proofs -- why?)
    ;;read-of-write-of-write-of-set-flag
    ;;read-of-write-of-write-of-write-of-set-flag
    read-1-of-write-within-new
    )
  (region-rules)))

;; For both 32-bit and 64-bit
(defund new-normal-form-rules-common ()
  (declare (xargs :guard t))
  '(;; Introduce fault, etc:
    xr-becomes-fault
    xr-becomes-ms
    xr-becomes-mxcsr
    xr-becomes-undef
    ;; Introduce set-fault, etc:
    xw-becomes-set-fault
    xw-becomes-set-ms
    xw-becomes-set-mxcsr
    xw-becomes-set-undef
    !fault-becomes-set-fault
    !ms-becomes-set-ms
    !mxcsr-becomes-set-mxcsr
    !undef-becomes-set-undef))

;; todo: some of these are write-over-write rules
;; These are used for both 32 and 64 bit modes.
;; Most of these are for the new normal form (fault, etc.)
(defund read-over-write-rules-common ()
  (declare (xargs :guard t))
  '( ; rule to intro app-view?
    x86isa::app-view-of-xw ; needed?
    app-view-of-set-flag
    ;; app-view-of-set-ms ;; we don't want to continue once a branch has a call of set-ms
    app-view-of-set-mxcsr
    app-view-of-set-undef
    app-view-of-!rflags

    ;; Rules about x86p:
    x86isa::x86p-xw
    x86p-of-set-flag
    ;; x86p-of-set-ms
    x86p-of-set-mxcsr
    x86p-of-set-undef
    x86p-of-!rflags

    ;; Rules about fault:
    fault-of-xw ; currently needed at least for writes to float registers
    fault-of-set-flag
    ;; fault-of-set-ms
    fault-of-set-mxcsr
    fault-of-set-undef
    fault-of-!rflags ; why is !rflags not going away?

    xr-of-set-undef-irrel
    xr-of-set-mxcsr-irrel
    ;; xr-of-set-ms-irrel

    get-flag-of-set-undef
    get-flag-of-set-mxcsr
    ;; get-flag-of-set-ms

    ;; Rules about set-fault:
    ;; we probably don't need read-over-write rules for set-fault, because a fault means the symbolic execution will stop (on that branch)

    ;; Rules about ms:

    ;; ms-of-set-ms
    ms-of-set-flag
    ;; ms-of-myif
    ms-of-!rflags         ; why is !rflags not going away?
    ms-of-set-rip         ; move to 64 rules?
    ms-of-set-undef
    ms-of-set-mxcsr
    ms-of-xw ; currently needed at least for writes to float registers

    ctri-of-!rflags          ; rename !rflags?
    ctri-of-xw-irrel         ; why?
    ctri-of-set-flag
    ctri-of-set-undef
    ctri-of-set-mxcsr
    integerp-of-ctri

    ;; Rules about set-ms:
    ;; set-ms-of-set-rip ; move to 64 rules?

    ;; x86isa::undef x86isa::undef$a
    undef-of-xw
    undef-of-set-undef
    undef-of-set-mxcsr
    undef-of-set-flag
    ;; undef-of-myif
    undef-of-!rflags         ; why is !rflags not going away?
    undef-of-set-rip         ; move to 64 rules?

    mxcsr-of-xw
    mxcsr-of-set-flag
    mxcsr-of-set-mxcsr ; read-of-write
    mxcsr-of-set-undef
    ;; mxcsr-of-myif
    mxcsr-of-!rflags         ; why is !rflags not going away?
    mxcsr-of-set-rip         ; move to 64 rules?

    x86isa::64-bit-modep-of-xw
    64-bit-modep-of-set-flag
    64-bit-modep-of-set-mxcsr
    64-bit-modep-of-set-undef
    ;; 64-bit-modep-of-set-ms ; could omit (since set-ms means the run will stop, but this can help clarify things)
    64-bit-modep-of-!rflags

    x86isa::alignment-checking-enabled-p-and-xw ; targets alignment-checking-enabled-p-of-xw
    x86isa::alignment-checking-enabled-p-of-xw-irrel ; todo: compare to x86isa::alignment-checking-enabled-p-and-xw
    x86isa::alignment-checking-enabled-p-of-set-flag ; todo: change package
    alignment-checking-enabled-p-of-set-mxcsr
    alignment-checking-enabled-p-of-set-undef
    alignment-checking-enabled-p-of-!rflags

    msri-of-set-flag
    msri-of-set-mxcsr
    msri-of-set-undef

    set-undef-of-undef-same

    set-undef-of-set-undef
    ;;            set-undef-of-set-mxcsr
    set-undef-of-set-flag
    ;; set-undef-of-myif
    set-undef-of-!rflags         ; why is !rflags showing up?
    set-undef-of-set-rip         ; move to 64 rules?

    set-mxcsr-of-set-mxcsr
    set-mxcsr-of-set-flag
    ;; set-mxcsr-of-myif
    set-mxcsr-of-!rflags         ; why is !rflags showing up?
    set-mxcsr-of-set-rip         ; move to 64 rules?

    rip-of-set-undef         ; also used in 32-bit mode?  or not?
    rip-of-set-mxcsr         ; also used in 32-bit mode?  or not?
    ;; rip-of-set-ms            ; also used in 32-bit mode?  or not?
    ))

(defund read-over-write-rules32 ()
  (declare (xargs :guard t))
  '(get-flag-of-write-to-segment
    get-flag-of-write-byte-to-segment

    ms-of-write-to-segment
    ms-of-write-byte-to-segment

    fault-of-write-to-segment
    fault-of-write-byte-to-segment

    undef-of-write-to-segment
    undef-of-write-byte-to-segment

    set-rax-high-of-write-to-segment
    set-rbx-high-of-write-to-segment
    set-rcx-high-of-write-to-segment
    set-rdx-high-of-write-to-segment
    set-rsp-high-of-write-to-segment
    set-rbp-high-of-write-to-segment

    set-rax-high-of-write-byte-to-segment
    set-rbx-high-of-write-byte-to-segment
    set-rcx-high-of-write-byte-to-segment
    set-rdx-high-of-write-byte-to-segment
    set-rsp-high-of-write-byte-to-segment
    set-rbp-high-of-write-byte-to-segment

    mxcsr-of-write-to-segment
    mxcsr-of-write-byte-to-segment
    ))

;; sophisticated scheme for removing inner, shadowed writes
(defund shadowed-write-rules ()
  (declare (xargs :guard t))
  '(write-becomes-write-of-clear-extend-axe
    clear-extend-of-write-continue-axe
    clear-extend-of-write-finish
    clear-extend-of-write-of-clear-retract
    write-of-clear-retract))

(defund read-write-set-flag-rules ()
  (declare (xargs :guard t))
  '(read-of-write-becomes-read-of-write-of-clear-flags-extend-axe
    clear-flags-extend-of-write-continue-axe
    clear-flags-extend-of-set-flag-finish
    clear-flags-extend-of-write-of-clear-flags-retract
    read-of-write-of-clear-flags-retract))

;; Rules that require the rewriter-x86, due to axe-syntaxp or axe-bind-free functions.
;; To be excluded when pruning (with the non-x86 rewriter)
(defund x86-rewriter-rules ()
  (declare (xargs :guard t))
  (append (shadowed-write-rules)
          (read-write-set-flag-rules)))

;; 'Read Over Write' and similar rules for state components. Our normal form
;; (at least for 64-bit code) includes 3 kinds of state changes, namely calls
;; to XW, WRITE, and SET-FLAG (todo: update this comment).
(defund state-rules ()
  (declare (xargs :guard t))
  '(
    force ;todo: think about this, could only open force on a constant arg
    ;x86isa::x86p-of-wb ;  wb-returns-x86p ;targets x86p-of-mv-nth-1-of-wb ;drop if WB will always be rewritten to WRITE

    ;; Flags:
    unsigned-byte-p-of-get-flag-one-bit ; todo: other case
    get-flag-of-xw
    xr-of-set-flag
    set-flag-of-xw
    get-flag-of-set-flag
    set-flag-of-set-flag-diff-axe
    set-flag-of-set-flag-same
    set-flag-of-get-flag-same-gen ;; set-flag-of-get-flag-same

    acl2::expt2$inline-constant-opener

;;     ;; x86isa::get-flag-set-flag ;covers both cases, with a twist for a 2-bit flag
;;     ;; x86isa::set-flag-set-flag-same
;;     ;; x86isa::set-flag-set-flag-different-concrete-indices

    x86isa::rflagsbits$inline-constant-opener

    x86isa::!rflagsbits->ac$inline-constant-opener
    x86isa::!rflagsbits->af$inline-constant-opener
    x86isa::!rflagsbits->cf$inline-constant-opener
    x86isa::!rflagsbits->of$inline-constant-opener
    x86isa::!rflagsbits->pf$inline-constant-opener
    x86isa::!rflagsbits->sf$inline-constant-opener
    x86isa::!rflagsbits->zf$inline-constant-opener

    x86isa::rflagsbits->ac$inline-constant-opener
    x86isa::rflagsbits->af$inline-constant-opener
    x86isa::rflagsbits->cf$inline-constant-opener
    x86isa::rflagsbits->of$inline-constant-opener
    x86isa::rflagsbits->pf$inline-constant-opener
    x86isa::rflagsbits->sf$inline-constant-opener
    x86isa::rflagsbits->zf$inline-constant-opener
    x86isa::rflagsbits->res1$inline-constant-opener
    x86isa::rflagsbits->res2$inline-constant-opener
    x86isa::rflagsbits->res3$inline-constant-opener
    x86isa::rflagsbits->tf$inline-constant-opener
    x86isa::rflagsbits->intf$inline-constant-opener
    x86isa::rflagsbits->df$inline-constant-opener
    x86isa::rflagsbits->iopl$inline-constant-opener
    x86isa::rflagsbits->nt$inline-constant-opener
    x86isa::rflagsbits->res4$inline-constant-opener
    x86isa::rflagsbits->rf$inline-constant-opener
    x86isa::rflagsbits->vm$inline-constant-opener
    x86isa::rflagsbits->vif$inline-constant-opener
    x86isa::rflagsbits->vip$inline-constant-opener
    x86isa::rflagsbits->id$inline-constant-opener
    x86isa::rflagsbits->res5$inline-constant-opener    ;todo: more like this, or do we have them all?

    x86isa::rflagsbits-fix$inline-constant-opener

    unsigned-byte-p-of-rflagsbits

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

    ;; These introduce set-flag:
    !rflags-of-!rflagsbits->af
    !rflags-of-!rflagsbits->cf
    !rflags-of-!rflagsbits->of
    !rflags-of-!rflagsbits->pf
    !rflags-of-!rflagsbits->sf
    !rflags-of-!rflagsbits->zf

    x86isa::rflagsbits->af-of-rflagsbits ; these are generated by defbitstruct
    x86isa::rflagsbits->cf-of-rflagsbits
    x86isa::rflagsbits->of-of-rflagsbits
    x86isa::rflagsbits->pf-of-rflagsbits
    x86isa::rflagsbits->sf-of-rflagsbits
    x86isa::rflagsbits->zf-of-rflagsbits    ;; todo: more?

    rflagsbits->af$inline-of-bvchop-32
    rflagsbits->cf$inline-of-bvchop-32
    rflagsbits->pf$inline-of-bvchop-32
    rflagsbits->of$inline-of-bvchop-32
    rflagsbits->sf$inline-of-bvchop-32
    rflagsbits->zf$inline-of-bvchop-32    ;; todo: more?

    ;; Or perhaps instead of these we should recharacterize
    ;; some instruction semantic functions so as not to need these:
    ;; x86isa::rflagsbits->af$inline-of-if-safe
    ;; x86isa::rflagsbits->cf$inline-of-if-safe
    ;; x86isa::rflagsbits->of$inline-of-if-safe
    ;; x86isa::rflagsbits->pf$inline-of-if-safe
    ;; x86isa::rflagsbits->sf$inline-of-if-safe
    ;; x86isa::rflagsbits->zf$inline-of-if-safe
    x86isa::rflagsbits->af$inline-of-if
    x86isa::rflagsbits->cf$inline-of-if
    x86isa::rflagsbits->of$inline-of-if
    x86isa::rflagsbits->pf$inline-of-if
    x86isa::rflagsbits->sf$inline-of-if
    x86isa::rflagsbits->zf$inline-of-if    ;; todo: more?

    rflagsbits->af-of-bvif
    rflagsbits->cf-of-bvif
    rflagsbits->of-of-bvif
    rflagsbits->pf-of-bvif
    rflagsbits->sf-of-bvif
    rflagsbits->zf-of-bvif    ;; todo: more?

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
    !rflags-of-write
    !rflags-of-set-flag
    !rflags-of-!rflags
    !rflags-does-nothing
;;     x86isa::!rflags$inline

    ;; For these, we can look inside !rflagsbits->cf, because it is not an argument to !rflags
    getbit-of-!rflagsbits->af
    getbit-of-!rflagsbits->cf
    getbit-of-!rflagsbits->pf
    getbit-of-!rflagsbits->of
    getbit-of-!rflagsbits->sf
    getbit-of-!rflagsbits->zf
    getbit-of-!rflagsbits->res1
    getbit-of-!rflagsbits->res2
    getbit-of-!rflagsbits->res3

;;     x86isa::!rflagsbits->ac$inline
;;     x86isa::!rflagsbits->af$inline
;;     x86isa::!rflagsbits->cf$inline ;it would be better if these called rflagsbits?
;;     x86isa::!rflagsbits->of$inline
;;     x86isa::!rflagsbits->pf$inline
;;     x86isa::!rflagsbits->sf$inline
;;     x86isa::!rflagsbits->zf$inline

    x86isa::unsigned-byte-p-1-of-rflagsbits->res1$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->cf$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->pf$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->id$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->vip$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->vif$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->ac$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->vm$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->rf$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->res4$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->nt$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->of$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->df$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->intf$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->tf$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->sf$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->zf$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->res3$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->af$inline
    x86isa::unsigned-byte-p-1-of-rflagsbits->res2$inline
    x86isa::unsigned-byte-p-2-of-rflagsbits->iopl$inline ;this one is 2 bits

;;     ;x86isa::rflagsbits->ac$inline
;;     ;X86ISA::RFLAGSBITS$INLINE
;;     ;X86ISA::RFLAGSBITS->AC$INLINE-CONSTANT-OPENER
;;     x86isa::RFLAGSBITS-rewrite
;; ;    x86isa::get-flag-xw

;    x86isa::get-flag-wb-in-app-view
    ;x86isa::xr-wb
    ;;x86isa::xr-ms-mv-nth-1-wb ;new  (see also xr-wb-in-app-view)

    acl2::bfix-when-bitp ; move? or drop if we go to unsigned-byte-p
    x86isa::unsigned-byte-p-of-bfix
    acl2::bitp-becomes-unsigned-byte-p

    ;; Just for making terms in failures more readable:
    ;; mv-nth-1-of-rb-1-of-set-rip
    ))

(defund decoding-and-dispatch-rules ()
  (declare (xargs :guard t))
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

    x86isa::prefixes-fix$inline ; or use constant-openers for these
    x86isa::prefixes->num$inline
    x86isa::prefixes->lck$inline
    x86isa::prefixes->rep$inline
    x86isa::prefixes->seg$inline
    x86isa::prefixes->opr$inline
    x86isa::prefixes->adr$inline
    x86isa::prefixes->nxt$inline
    ;; x86isa::prefixes->rep$inline-constant-opener ; for floating point?
    x86isa::!prefixes->num$inline ; why are these needed?
    x86isa::!prefixes->lck$inline
    x86isa::!prefixes->rep$inline
    x86isa::!prefixes->seg$inline
    x86isa::!prefixes->opr$inline
    x86isa::!prefixes->adr$inline
    x86isa::!prefixes->nxt$inline

    ;; are constant-openers better than enabling these funtions? todo: remove once built into x86 evaluator and other evaluators no longer used
    X86ISA::!PREFIXES->REP$INLINE-CONSTANT-OPENER ; for floating point?
    x86isa::!prefixes->seg$inline-constant-opener

    x86isa::vex-prefixes-fix$inline-constant-opener
    x86isa::vex-prefixes->byte0$inline-constant-opener
    x86isa::vex-prefixes->byte1$inline-constant-opener
    x86isa::vex-prefixes->byte2$inline-constant-opener
    x86isa::!vex-prefixes->byte0$inline-constant-opener ; kind of surprised that we are writing into such a struct
    x86isa::!vex-prefixes->byte1$inline-constant-opener
    x86isa::!vex-prefixes->byte2$inline-constant-opener

    x86isa::vex2-byte1-fix$inline-constant-opener
    x86isa::vex2-byte1->pp$inline-constant-opener
    x86isa::vex2-byte1->l$inline-constant-opener
    x86isa::vex2-byte1->vvvv$inline-constant-opener
    x86isa::vex2-byte1->r$inline-constant-opener

    x86isa::vex3-byte1-fix$inline-constant-opener
    x86isa::vex3-byte1->m-mmmm$inline-constant-opener
    x86isa::vex3-byte1->b$inline-constant-opener
    x86isa::vex3-byte1->x$inline-constant-opener
    x86isa::vex3-byte1->r$inline-constant-opener

    x86isa::vex3-byte2-fix$inline-constant-opener
    x86isa::vex3-byte2->pp$inline-constant-opener
    x86isa::vex3-byte2->l$inline-constant-opener
    x86isa::vex3-byte2->vvvv$inline-constant-opener
    x86isa::vex3-byte2->w$inline-constant-opener

    x86isa::evex-prefixes->byte0$inline-constant-opener
    x86isa::evex-prefixes->byte1$inline-constant-opener
    x86isa::evex-prefixes->byte2$inline-constant-opener
    x86isa::evex-prefixes->byte3$inline-constant-opener
    x86isa::!evex-prefixes->byte0$inline-constant-opener

    x86isa::evex-byte1->mmm$inline-constant-opener
    x86isa::evex-byte1->res$inline-constant-opener
    x86isa::evex-byte1->r-prime$inline-constant-opener
    x86isa::evex-byte1->b$inline-constant-opener
    x86isa::evex-byte1->x$inline-constant-opener
    x86isa::evex-byte1->r$inline-constant-opener

    x86isa::evex-byte2->pp$inline-constant-opener
    x86isa::evex-byte2->res$inline-constant-opener
    x86isa::evex-byte2->vvvv$inline-constant-opener
    x86isa::evex-byte2->w$inline-constant-opener

    x86isa::evex-byte3->aaa$inline-constant-opener
    x86isa::evex-byte3->v-prime$inline-constant-opener
    x86isa::evex-byte3->b$inline-constant-opener
    x86isa::evex-byte3->vl/rc$inline-constant-opener
    x86isa::evex-byte3->z$inline-constant-opener

    x86isa::rex-byte-from-vex-prefixes-constant-opener

    x86isa::vex-vvvv-reg-index-constant-opener

;    x86isa::num-prefixes-fix$inline

;    x86isa::next-byte-fix
;    x86isa::opr-fix
    ;; todo: just use constant openers for these?
    modr/m-fix$inline
    modr/m->mod$inline
    modr/m->reg$inline
    modr/m->r/m$inline
    sib-fix$inline
    sib->scale$inline
    sib->base$inline
    sib->index$inline

    x86isa::vex-opcode-modr/m-p$inline-constant-opener
    x86isa::vex-prefixes-map-p$inline-constant-opener

    x86isa::vex->vvvv$inline-constant-opener
    x86isa::vex->l$inline-constant-opener
    x86isa::vex->pp$inline-constant-opener
    x86isa::vex->r$inline-constant-opener
    x86isa::vex->w$inline-constant-opener
    x86isa::vex->b$inline-constant-opener
    x86isa::vex->x$inline-constant-opener

    ;; todo: more constant-openers for the bitstructs (or add to evaluator)

    x86isa::vex-decode-and-execute ; restrict to when we can resolve the instruction?
    x86isa::vex-0f38-execute  ; move?
    x86isa::vex-0f-execute
))

(defund x86-type-rules ()
  (declare (xargs :guard t))
  '(x86isa::unsigned-byte-p-of-cf-spec8
    x86isa::unsigned-byte-p-of-cf-spec16
    x86isa::unsigned-byte-p-of-cf-spec32
    x86isa::unsigned-byte-p-of-cf-spec64
    x86isa::bitp-of-cf-spec8
    x86isa::bitp-of-cf-spec16
    x86isa::bitp-of-cf-spec32
    x86isa::bitp-of-cf-spec64
    integerp-of-cf-spec64 ; todo: more

    x86isa::unsigned-byte-p-of-of-spec8
    x86isa::unsigned-byte-p-of-of-spec16
    x86isa::unsigned-byte-p-of-of-spec32
    x86isa::unsigned-byte-p-of-of-spec64
    x86isa::bitp-of-of-spec8
    x86isa::bitp-of-of-spec16
    x86isa::bitp-of-of-spec32
    x86isa::bitp-of-of-spec64

    x86isa::unsigned-byte-p-of-pf-spec8
    x86isa::unsigned-byte-p-of-pf-spec16
    x86isa::unsigned-byte-p-of-pf-spec32
    x86isa::unsigned-byte-p-of-pf-spec64
    x86isa::bitp-of-pf-spec8
    x86isa::bitp-of-pf-spec16
    x86isa::bitp-of-pf-spec32
    x86isa::bitp-of-pf-spec64

    x86isa::unsigned-byte-p-of-sf-spec8
    x86isa::unsigned-byte-p-of-sf-spec16
    x86isa::unsigned-byte-p-of-sf-spec32
    x86isa::unsigned-byte-p-of-sf-spec64
    x86isa::bitp-of-sf-spec8
    x86isa::bitp-of-sf-spec16
    x86isa::bitp-of-sf-spec32
    x86isa::bitp-of-sf-spec64

    x86isa::unsigned-byte-p-of-zf-spec ; zf-spec is not size-specific (32, 64, etc)
    ;; todo: now we turn bitp into unsigned-byte-p, so these won't fire:
    x86isa::bitp-of-zf-spec
    x86isa::integerp-of-zf-spec

    x86isa::unsigned-byte-p-of-add-af-spec8
    x86isa::unsigned-byte-p-of-add-af-spec16
    x86isa::unsigned-byte-p-of-add-af-spec32
    x86isa::unsigned-byte-p-of-add-af-spec64
    x86isa::bitp-of-add-af-spec8
    x86isa::bitp-of-add-af-spec16
    x86isa::bitp-of-add-af-spec32
    x86isa::bitp-of-add-af-spec64

    x86isa::unsigned-byte-p-of-sub-af-spec8
    x86isa::unsigned-byte-p-of-sub-af-spec16
    x86isa::unsigned-byte-p-of-sub-af-spec32
    x86isa::unsigned-byte-p-of-sub-af-spec64

    x86isa::unsigned-byte-p-of-sub-cf-spec8
    x86isa::unsigned-byte-p-of-sub-cf-spec16
    x86isa::unsigned-byte-p-of-sub-cf-spec32 ;bitp becomes unsigned-byte-p 1 ?
    x86isa::unsigned-byte-p-of-sub-cf-spec64 ;bitp becomes unsigned-byte-p 1 ?
    x86isa::bitp-of-sub-cf-spec8
    x86isa::bitp-of-sub-cf-spec16
    x86isa::bitp-of-sub-cf-spec32
    x86isa::bitp-of-sub-cf-spec64
    x86isa::integerp-of-sub-cf-spec8
    x86isa::integerp-of-sub-cf-spec16
    x86isa::integerp-of-sub-cf-spec32
    x86isa::integerp-of-sub-cf-spec64

    x86isa::unsigned-byte-p-of-sub-of-spec8
    x86isa::unsigned-byte-p-of-sub-of-spec16
    x86isa::unsigned-byte-p-of-sub-of-spec32
    x86isa::unsigned-byte-p-of-sub-of-spec64
    x86isa::bitp-of-sub-of-spec8
    x86isa::bitp-of-sub-of-spec16
    x86isa::bitp-of-sub-of-spec32
    x86isa::bitp-of-sub-of-spec64
    x86isa::integerp-of-sub-of-spec8
    x86isa::integerp-of-sub-of-spec16
    x86isa::integerp-of-sub-of-spec32
    x86isa::integerp-of-sub-of-spec64

    x86isa::unsigned-byte-p-of-sub-pf-spec8
    x86isa::unsigned-byte-p-of-sub-pf-spec16
    x86isa::unsigned-byte-p-of-sub-pf-spec32
    x86isa::unsigned-byte-p-of-sub-pf-spec64
    x86isa::bitp-of-sub-pf-spec8
    x86isa::bitp-of-sub-pf-spec16
    x86isa::bitp-of-sub-pf-spec32
    x86isa::bitp-of-sub-pf-spec64
    x86isa::integerp-of-sub-pf-spec8
    x86isa::integerp-of-sub-pf-spec16
    x86isa::integerp-of-sub-pf-spec32
    x86isa::integerp-of-sub-pf-spec64

    x86isa::unsigned-byte-p-of-sub-sf-spec8
    x86isa::unsigned-byte-p-of-sub-sf-spec16
    x86isa::unsigned-byte-p-of-sub-sf-spec32
    x86isa::unsigned-byte-p-of-sub-sf-spec64
    x86isa::bitp-of-sub-sf-spec8
    x86isa::bitp-of-sub-sf-spec16
    x86isa::bitp-of-sub-sf-spec32
    x86isa::bitp-of-sub-sf-spec64
    x86isa::integerp-of-sub-sf-spec8
    x86isa::integerp-of-sub-sf-spec16
    x86isa::integerp-of-sub-sf-spec32
    x86isa::integerp-of-sub-sf-spec64

    x86isa::unsigned-byte-p-of-sub-zf-spec8
    x86isa::unsigned-byte-p-of-sub-zf-spec16
    x86isa::unsigned-byte-p-of-sub-zf-spec32
    x86isa::unsigned-byte-p-of-sub-zf-spec64
    x86isa::bitp-of-sub-zf-spec8
    x86isa::bitp-of-sub-zf-spec16
    x86isa::bitp-of-sub-zf-spec32
    x86isa::bitp-of-sub-zf-spec64
    x86isa::integerp-of-sub-zf-spec8
    x86isa::integerp-of-sub-zf-spec16
    x86isa::integerp-of-sub-zf-spec32
    x86isa::integerp-of-sub-zf-spec64

    acl2::unsigned-byte-p-of-+ ; can work with cf-spec64-becomes-getbit

    integerp-of-!rflagsbits->af
    integerp-of-!rflagsbits->cf
    integerp-of-!rflagsbits->of
    integerp-of-!rflagsbits->pf
    integerp-of-!rflagsbits->sf
    integerp-of-!rflagsbits->zf
    integerp-of-!rflagsbits->res1
    integerp-of-!rflagsbits->res2
    integerp-of-!rflagsbits->res3

    ;;todo: not x86-specific
    acl2::integerp-of-logext
    acl2::signed-byte-p-of-logext
    acl2::integerp-of--))

(defund arith-to-bv-rules ()
  (declare (xargs :guard t))
  '(acl2::bvchop-of-*-becomes-bvmult
    acl2::getbit-of-*-becomes-getbit-of-bvmult
    acl2::slice-of-*-becomes-slice-of-bvmult
    acl2::bvuminus-of-+
    acl2::bvminus-of-+-arg2 ; caused loops with bvplus-of-constant-and-esp-when-overflow.  probably want to go to bvuminus anyway?
    acl2::bvminus-of-+-arg3
    acl2::bvif-of-+-arg4
    acl2::bvif-of-+-arg3
    acl2::bvif-of---arg3
    acl2::bvif-of---arg4
    ;; todo: more
    ))

;; Rules to introduce our BV operators (todo: move these):
;rename bv-intro-rules-logops?
;move?  maybe only needed for x86 (for now?)
(defund logops-to-bv-rules ()
  (declare (xargs :guard t))
  '(acl2::logand-becomes-bvand-arg1-axe
    acl2::logand-becomes-bvand-arg2-axe
    acl2::logior-becomes-bvor-arg1-axe ; based on the form of arg1
    acl2::logior-becomes-bvor-arg1-axe ; based on the form of arg2
    acl2::logxor-becomes-bvxor-arg1-axe ; based on the form of arg1
    acl2::logxor-becomes-bvxor-arg1-axe ; based on the form of arg2
    ;acl2::logxor-bvchop-bvchop        ; introduce bvxor
    ;acl2::logxor-of-bvchop-becomes-bvxor-arg1 ; introduce bvxor
    ;;            acl2::bvplus-of-logxor-arg1                     ; introduce bvxor
    ;;            acl2::bvxor-of-logxor-arg2                      ; introduce bvxor

    acl2::loghead-becomes-bvchop
    acl2::bvchop-of-lognot-becomes-bvnot
    acl2::bvchop-of-logand-becomes-bvand
    acl2::bvchop-of-logior-becomes-bvor
    acl2::bvchop-of-logxor-becomes-bvxor
    acl2::bvchop-of-+-becomes-bvplus

    acl2::logapp-becomes-bvcat-bind-free-axe
    acl2::logtail-becomes-slice-bind-free-axe
    acl2::logtail-of-bvchop-becomes-slice ; todo: other way?

    ;; Can help get rid of an intervening ifix:
    acl2::integerp-of-logand
    acl2::integerp-of-logior ; useful for mxcsr bits
    acl2::integerp-of-logxor
    ))

;; combine with the logops-to-bv-rules rules?
(defund logops-rules ()
  (declare (xargs :guard t))
  '(acl2::logapp-constant-opener
    common-lisp::lognot-constant-opener
    common-lisp::logcount-constant-opener))

;; These are x86-specific since they know about READ:
(defund logops-to-bv-rules-x86 ()
  (declare (xargs :guard t))
  '(logtail-of-read-becomes-slice
    logapp-of-read-becomes-bvcat))

;; Rules to introduce our BV operators (todo: move these):
(defund bitops-to-bv-rules ()
  (declare (xargs :guard t))
  '(acl2::part-select-width-low-becomes-slice

    acl2::slice-of-part-install-width-low ; introduces bvcat
    acl2::bvchop-of-part-install-width-low-becomes-bvcat
    acl2::part-install-width-low-becomes-bvcat ; gets the size of X from an assumption
    acl2::part-install-width-low-becomes-bvcat-axe ; gets the size of X from the form of X
    acl2::part-install-width-low-becomes-bvcat-32
    acl2::part-install-width-low-becomes-bvcat-64
    acl2::part-install-width-low-becomes-bvcat-128
    acl2::part-install-width-low-becomes-bvcat-256
    acl2::part-install-width-low-becomes-bvcat-512
    acl2::integerp-of-part-install-width-low$inline ; needed?

    acl2::rotate-right-becomes-rightrotate
    acl2::rotate-left-becomes-leftrotate
    acl2::logbit-becomes-getbit
    acl2::b-and-becomes-bitand
    acl2::b-ior-becomes-bitor
    acl2::b-xor-becomes-bitxor))

;; See also bitops-to-bv-rules.
;; todo: add more constant openers
(defund bitops-rules ()
  (declare (xargs :guard t))
  '(bitops::rotate-left-8$inline ; rewrites to the non-fast rotate
    bitops::rotate-left-9$inline ; rewrites to the non-fast rotate
    bitops::rotate-left-16$inline ; rewrites to the non-fast rotate
    bitops::rotate-left-17$inline ; rewrites to the non-fast rotate
    bitops::rotate-left-32$inline ; rewrites to the non-fast rotate
    bitops::rotate-left-33$inline ; rewrites to the non-fast rotate
    bitops::rotate-left-64$inline ; rewrites to the non-fast rotate
    bitops::rotate-left-65$inline ; rewrites to the non-fast rotate
    bitops::rotate-right-8$inline ; rewrites to the non-fast rotate
    bitops::rotate-right-9$inline ; rewrites to the non-fast rotate
    bitops::rotate-right-16$inline ; rewrites to the non-fast rotate
    bitops::rotate-right-17$inline ; rewrites to the non-fast rotate
    bitops::rotate-right-32$inline ; rewrites to the non-fast rotate
    bitops::rotate-right-33$inline ; rewrites to the non-fast rotate
    bitops::rotate-right-64$inline ; rewrites to the non-fast rotate
    bitops::rotate-right-65$inline ; rewrites to the non-fast rotate
    acl2::rotate-left-constant-opener
    acl2::rotate-right-constant-opener))

;todo: classify these
(defund x86-bv-rules ()
  (declare (xargs :guard t))
  '( ;acl2::bvlt-of-0-arg3 ;todo: more like this?

    acl2::logext-of-bvplus-64 ;somewhat unusual

    acl2::bvlt-of-constant-when-unsigned-byte-p-tighter

    acl2::logext-trim-arg-axe-all

    acl2::bvchop-of-if-when-constants

    ;; this is needed to handle a divide:
    acl2::bvcat-of-if-becomes-bvsx-64-64
    acl2::bvlt-of-bvplus-1-cancel
    acl2::bvlt-of-bvplus-1-cancel-alt
    acl2::bvsx-when-unsigned-byte-p ; without this, we'd need rules like bvsx-of-read (when the read is small)

    acl2::bvlt-trim-arg1-axe-all
    acl2::bvlt-trim-arg2-axe-all

    acl2::bvlt-of-bvmult-of-expt-arg2-constant-version2
    acl2::bvlt-of-bvmult-of-expt-arg3-constant-version

    acl2::bvplus-of-bvplus-tighten-arg3 ; new
    acl2::bvsx-of-logext
    acl2::logext-of-+-of-logext-arg2
    ))

;; ;not used?
;; (defund canonical-address-rules ()
;;  (declare (xargs :guard t))
;;   '(x86isa::not-member-p-canonical-address-listp ;drop the not and strengthen?
;;     x86isa::subset-p-two-create-canonical-address-lists-general ;strengthen?
;;     ;;not-member-p-canonical-address-listp-when-disjoint-p ;free vars? looped? ;why?
;;     ;;not-member-p-canonical-address-listp-when-disjoint-p-alt ;free vars? looped? ;why?
;;     ;;not-member-p-when-disjoint-p ;todo: make an alt version
;;     x86isa::canonical-address-listp-of-cdr
;;     x86isa::cdr-create-canonical-address-list
;;     x86isa::car-create-canonical-address-list
;;     x86isa::canonical-address-p-of-i48
;;     x86isa::i48-when-canonical-address-p))

;; These are about if but are not 'if lifting' rules.
(defund if-rules ()
  (declare (xargs :guard t))
  '(acl2::if-nil-t
    acl2::if-of-t-and-nil-becomes-bool-fix
    acl2::if-of-not
    acl2::if-of-if-same-arg2
    acl2::if-of-if-same-arg3
    acl2::if-of-if-t-nil
    acl2::if-of-if-of-cons-arg1-arg2
    acl2::if-of-if-of-cons-arg1-arg3
    ))

;; For this strategy, we lower the IF when the 2 states have the same PC and no
;; faults. This allows the symbolic execution to continue with just the single
;; merged state.  (The need for this may be due to an instruction semantic
;; function, or a rewrite rule, that introduces an unnecessary IF on states.)
;; TODO: If the stack height is different, we might want to refrain (but then
;; it would be a bit odd to have the same RIP).
(defund if-lowering-rules64 ()
  (declare (xargs :guard t))
  '(mergeable-states64p
    if-of-set-rip-and-set-rip-same

    if-of-set-rax-arg2-64
    if-of-set-rbx-arg2-64
    if-of-set-rcx-arg2-64
    if-of-set-rdx-arg2-64 ; todo: more

    if-of-set-rax-arg3-64
    if-of-set-rbx-arg3-64
    if-of-set-rcx-arg3-64
    if-of-set-rdx-arg3-64

    if-of-set-flag-arg2-64
    if-of-set-flag-arg3-64
    if-of-set-undef-arg2-64
    if-of-set-undef-arg3-64
    if-of-set-mxcsr-arg2-64
    if-of-set-mxcsr-arg3-64
;    if-of-write-byte-arg2-64
;    if-of-write-byte-arg3-64
    if-of-write-arg2-64
    if-of-write-arg3-64 ; todo: more?
    ))

;these help with conditional branches
;but see if-lifting strategies below for ifs on state transformers.
(defund if-lifting-rules ()
  (declare (xargs :guard t))
  '(x86isa::app-view-of-if
    ;x86isa::program-at-of-if
    x86isa::x86p-of-if
    x86isa::alignment-checking-enabled-p-of-if
    x86isa::64-bit-modep-of-if
    x86isa::ctri-of-if
    x86isa::canonical-address-p-of-if
    get-flag-of-if
    ;; feature-flag-of-if
    read-of-if
    undef-of-if
    mxcsr-of-if
    ms-of-if
    fault-of-if
    acl2::mv-nth-of-if ;could restrict to when both branches are cons nests
    x86isa::equal-of-if-constants    ;seems safe
    x86isa::equal-of-if-constants-alt ;seems safe
    x86isa::combine-bytes-of-if-when-constants
    x86isa::member-p-of-if-arg1
    x86isa::+-of-if-arg1
    x86isa::+-of-if-arg2
    acl2::nth-of-if-arg1
    x86isa::cons-of-if-when-constants
    ;; x86isa::one-byte-opcode-execute-of-if-arg1 ; drop?
    ;; x86isa::if-of-one-byte-opcode-execute-of-if-arg2 ;do we need this?
    ;; x86isa::if-of-one-byte-opcode-execute-of-if-arg5 ;do we need this?
    x86isa::<-of-if-arg2 ;could be dangerous
    x86isa::logext-of-if-arg2))

;; if-lifting strategy: where we lift the ifs (todo: restrict to provably different pcs or fault statuses?):
;; set-rax-of-if-arg2
;; set-rdi-of-if-arg2
;; set-rip-of-if
;; set-undef-of-if
;; set-flag-of-if
;; ;xr-of-if ; overkill?  also one in the x86isa pkg?

;; ;; Strategy 2b: don't lift or lower the if because the states all have the same pc (instead, we just try to resolve the next instruction).  warning: if some of these rules are missing, very large terms can result:
;; ;; x86isa::xr-of-if-special-case-for-ms
;; ;; x86isa::xr-of-if-special-case-for-fault ; this was bad without x86isa::64-bit-modep-of-if.  why?  maybe lets us expand fetch-decode-execute when we shouldn't?  may also need rb-of-if and such to help get-prefixes.  maybe only open fetch-code-execute when we can resolve the get-prefixes.  but that might cause work to be redone, unless we add support for binding hyps
;; ;; ;x86isa::rb-of-if-arg2
;;   ;; x86isa::app-view-of-if x86isa::x86p-of-if read-of-if
;;   ;;acl2::<-minus-zero
;;   x86isa::64-bit-modep-of-if
;;   x86isa::app-view-of-if
;;   x86isa::x86p-of-if
;;   read-of-if
;;   ;; or lower ifs with if-of-write
;;   xr-of-if ; too much?  need ms
;;   x86isa::alignment-checking-enabled-p-of-if

(defund simple-opener-rules ()
  (declare (xargs :guard t))
  '(; 64-bit-modep ; using rules about this instead, since this is no longer just true
    ))

;; These open the branch conditions, without trying to make the expressions nice.
;; Instead, consider adding more rules like jle-condition-rewrite-1.
;; TODO: Some of these are only for 64 or only for 32 bit mode?
;; (defund branch-condition-openers ()
;;  (declare (xargs :guard t))
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
(defund constant-opener-rules ()
  (declare (xargs :guard t))
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

    ;; acl2::bool->bit$inline-constant-opener
    ;; byte-ify-base
    ;; x86isa::byte-listp-unroll ;todo: improve (the __function__ put in by define makes this gross)
    ;; x86isa::byte-listp-base-1

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

    acl2::logmask$inline-constant-opener ; add to evaluator?
    ;;acl2::binary-logand-constant-opener

    subregion48p-constant-opener
    in-region48p-constant-opener
    disjoint-regions48p-constant-opener))

;; too: update this list
(defund get-prefixes-openers ()
  (declare (xargs :guard t))
  '(;; x86isa::get-prefixes-base-1; error case
    ;; x86isa::get-prefixes-base-2 ; error case
    ;; x86isa::get-prefixes-base-3 ; error case
    x86isa::get-prefixes-base-4
    ;; x86isa::get-prefixes-base-5 ; error case
    ;; x86isa::get-prefixes-base-6 ; error case
    ;; x86isa::get-prefixes-base-7 ; error case
    ;; x86isa::get-prefixes-base-8 ; error case
    ;; x86isa::get-prefixes-base-9 ; error case
    x86isa::get-prefixes-unroll-1
    x86isa::get-prefixes-unroll-2
    x86isa::get-prefixes-unroll-3
    x86isa::get-prefixes-unroll-4
    x86isa::get-prefixes-unroll-5
    ;; x86isa::get-prefixes-opener-lemma-no-prefix-byte
    ;; x86isa::get-prefixes-opener-lemma-group-1-prefix-simple
    ;; x86isa::get-prefixes-opener-lemma-group-2-prefix-simple
    ;; x86isa::get-prefixes-opener-lemma-group-3-prefix-simple
    ;; x86isa::get-prefixes-opener-lemma-group-4-prefix-simple
    ))

(set-axe-rule-priority x86isa::get-prefixes-base-1 1) ; try late (unusual case)

;todo: separate out the 64-bit rules
(defund segment-base-and-bounds-rules-general ()
  (declare (xargs :guard t))
  '(x86isa::segment-base-and-bounds-of-xw ; needed?
    segment-base-and-bounds-of-set-flag
    segment-base-and-bounds-of-set-undef
    segment-base-and-bounds-of-set-mxcsr
    ;; segment-base-and-bounds-of-set-ms
    integerp-of-mv-nth-0-of-segment-base-and-bounds-gen
    ))

(defund segment-base-and-bounds-rules-64 ()
  (declare (xargs :guard t))
  '(segment-base-and-bounds-of-set-rip
    segment-base-and-bounds-of-set-rsp
    segment-base-and-bounds-of-set-rbp
    segment-base-and-bounds-of-set-rax
    segment-base-and-bounds-of-set-rbx
    segment-base-and-bounds-of-set-rcx
    segment-base-and-bounds-of-set-rdx
    segment-base-and-bounds-of-set-rsi
    segment-base-and-bounds-of-set-rdi
    segment-base-and-bounds-of-set-r8
    segment-base-and-bounds-of-set-r9
    segment-base-and-bounds-of-set-r10
    segment-base-and-bounds-of-set-r11
    segment-base-and-bounds-of-set-r12
    segment-base-and-bounds-of-set-r13
    segment-base-and-bounds-of-set-r14
    segment-base-and-bounds-of-set-r15

    segment-base-and-bounds-of-set-flag
;    segment-base-and-bounds-of-write-byte
    segment-base-and-bounds-of-write
    ))

(defund segment-base-and-bounds-rules-32 ()
  (declare (xargs :guard t))
  '(segment-base-and-bounds-of-set-eip
    segment-base-and-bounds-of-set-eax
    segment-base-and-bounds-of-set-ebx
    segment-base-and-bounds-of-set-ecx
    segment-base-and-bounds-of-set-edx
    segment-base-and-bounds-of-set-esp
    segment-base-and-bounds-of-set-ebp
    segment-base-and-bounds-of-set-rax-high
    segment-base-and-bounds-of-set-rbx-high
    segment-base-and-bounds-of-set-rcx-high
    segment-base-and-bounds-of-set-rdx-high
    segment-base-and-bounds-of-set-rsp-high
    segment-base-and-bounds-of-set-rbp-high
    segment-base-and-bounds-of-write-to-segment
    segment-base-and-bounds-of-write-byte-to-segment))

;; are these only for making failures clearer?
;; todo: more?
(defund get-prefixes-rules64 ()
  (declare (xargs :guard t))
  '(mv-nth-0-of-get-prefixes-of-set-rip
    mv-nth-0-of-get-prefixes-of-set-rax
    mv-nth-0-of-get-prefixes-of-set-rbx
    mv-nth-0-of-get-prefixes-of-set-rcx
    mv-nth-0-of-get-prefixes-of-set-rdx
    mv-nth-0-of-get-prefixes-of-set-rsi
    mv-nth-0-of-get-prefixes-of-set-rdi
    mv-nth-0-of-get-prefixes-of-set-rsp
    mv-nth-0-of-get-prefixes-of-set-rbp
    mv-nth-1-of-get-prefixes-of-set-rip
    mv-nth-1-of-get-prefixes-of-set-rax
    mv-nth-1-of-get-prefixes-of-set-rbx
    mv-nth-1-of-get-prefixes-of-set-rcx
    mv-nth-1-of-get-prefixes-of-set-rdx
    mv-nth-1-of-get-prefixes-of-set-rsi
    mv-nth-1-of-get-prefixes-of-set-rdi
    mv-nth-1-of-get-prefixes-of-set-rsp
    mv-nth-1-of-get-prefixes-of-set-rbp))

(defund float-rules ()
  (declare (xargs :guard t))
  '(is-nan-intro ; targets an IF
    is-nan-intro-from-boolif
    if-of-equal-of-indef-and-is-nan
    if-of-equal-of-qnan-and-is-nan
    if-of-equal-of-snan-and-is-nan
    booleanp-of-is-nan
    not-mv-nth-0-of-sse-cmp

    integerp-of-mxcsr
    ;; maybe drop these:
    ;;integerp-of-xr-mxcsr
    ;;x86isa::n32p-xr-mxcsr ; targets unsigned-byte-p-of-mxcsr

    x86isa::mxcsrbits-fix-constant-opener
    x86isa::mxcsrbits->ie$inline-constant-opener
    x86isa::mxcsrbits->de$inline-constant-opener
    x86isa::mxcsrbits->ze$inline-constant-opener
    x86isa::mxcsrbits->oe$inline-constant-opener
    x86isa::mxcsrbits->ue$inline-constant-opener
    x86isa::mxcsrbits->pe$inline-constant-opener
    x86isa::mxcsrbits->daz$inline-constant-opener
    x86isa::mxcsrbits->im$inline-constant-opener
    x86isa::mxcsrbits->dm$inline-constant-opener
    x86isa::mxcsrbits->zm$inline-constant-opener
    x86isa::mxcsrbits->om$inline-constant-opener
    x86isa::mxcsrbits->um$inline-constant-opener
    x86isa::mxcsrbits->pm$inline-constant-opener
    x86isa::mxcsrbits->rc$inline-constant-opener
    x86isa::mxcsrbits->ftz$inline-constant-opener

    mxcsrbits->ie-of-bvor
    mxcsrbits->de-of-bvor
    mxcsrbits->ze-of-bvor
    mxcsrbits->oe-of-bvor
    mxcsrbits->ue-of-bvor
    mxcsrbits->pe-of-bvor
    mxcsrbits->daz-of-bvor
    mxcsrbits->im-of-bvor
    mxcsrbits->dm-of-bvor
    mxcsrbits->zm-of-bvor
    mxcsrbits->om-of-bvor
    mxcsrbits->um-of-bvor
    mxcsrbits->pm-of-bvor
    mxcsrbits->rc-of-bvor
    mxcsrbits->ftz-of-bvor
    mxcsrbits->reserved-of-bvor

    mxcsrbits->ie-of-logior
    mxcsrbits->de-of-logior
    mxcsrbits->ze-of-logior
    mxcsrbits->oe-of-logior
    mxcsrbits->ue-of-logior
    mxcsrbits->pe-of-logior
    mxcsrbits->daz-of-logior
    mxcsrbits->im-of-logior
    mxcsrbits->dm-of-logior
    mxcsrbits->zm-of-logior
    mxcsrbits->om-of-logior
    mxcsrbits->um-of-logior
    mxcsrbits->pm-of-logior
    mxcsrbits->rc-of-logior
    mxcsrbits->ftz-of-logior
    mxcsrbits->reserved-of-logior

    ;todo: more
    mxcsrbits->daz-of-bvchop
    mxcsrbits->dm-of-bvchop
    mxcsrbits->im-of-bvchop
    mxcsrbits->ie-of-bvchop

    mxcsrbits->daz-of-ifix
    mxcsrbits->dm-of-ifix
    mxcsrbits->im-of-ifix
    mxcsrbits->ie-of-ifix

    ;; more?  or make rules about bvif
    x86isa::mxcsrbits->im-of-if
    x86isa::mxcsrbits->dm-of-if
    x86isa::mxcsrbits->daz-of-if

    mxcsrbits->daz-of-mv-nth-2-of-sse-cmp
    mxcsrbits->dm-of-mv-nth-2-of-sse-cmp
    mxcsrbits->im-of-mv-nth-2-of-sse-cmp

    unsigned-byte-p-32-of-!mxcsrbits->ie
    unsigned-byte-p-32-of-!mxcsrbits->de
    integerp-of-!mxcsrbits->de
    integerp-of-!mxcsrbits->ie
    mxcsrbits->im-of-!mxcsrbits->ie
    mxcsrbits->im-of-!mxcsrbits->de
    mxcsrbits->dm-of-!mxcsrbits->de
    mxcsrbits->dm-of-!mxcsrbits->ie
    mxcsrbits->daz-of-!mxcsrbits->de
    mxcsrbits->daz-of-!mxcsrbits->ie

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
    jb-condition-of-bvif-1-0-1
    jb-condition-of-bvif-1-1-0
    jnb-condition-of-bvif-1-0-1
    jnb-condition-of-bvif-1-1-0
    ;;acl2::bool-fix-of-myif
    ;;boolif-of-myif-arg1-true ; drop
    equal-of-0-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe ;equal-of-0-and-mv-nth-1-of-sse-cmp-of-ucomi
    equal-of-1-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe
    equal-of-7-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe
    not-equal-of-7-and-mv-nth-1-of-sse-cmp

    sse-daz-of-nil

    ;sse-cmp ; scary
    sp-sse-cmp ; single precision wrapper for sse-cmp
    dp-sse-cmp ; double precision wrapper for sse-cmp
    dazify-of-0-arg2
    unmasked-excp-p-of-63-arg2 ; may help a lot
    mxcsr-rc-redef
    mxcsr-masks-redef

    acl2::bitn-becomes-getbit ; the rules below target getbit
    getbit-of-daz-becomes-mxcsrbits->daz
    getbit-of-omsk-becomes-mxcsrbits->-om
    getbit-of-umsk-becomes-mxcsrbits->-um
    getbit-of-ftz-becomes-mxcsrbits->-ftz
    natp-of-omsk
    natp-of-umsk
    natp-of-ftz
    natp-of-daz

    x86isa::fp-decode-constant-opener
    x86isa::fp-to-rat-constant-opener
    rtl::bias-constant-opener
    rtl::expw-constant-opener))

;; Try to introduce is-nan as soon as possible:
(set-axe-rule-priority is-nan-intro -1)

;; Do this late, to give the bitp rules a chance to fire first:
(set-axe-rule-priority acl2::bitp-becomes-unsigned-byte-p 1)

;; Fire very early to remove bvchop from things like (+ 4 (ESP X86)), at least for now:
(set-axe-rule-priority bvchop-of-+-of-esp-becomes-+-of-esp -2)

;; Careful, this one broke things by introducing bvplus into esp expressions.  So we added bvchop-of-+-of-esp-becomes-+-of-esp.
;; Ensures that rules targetting things like (bvchop 32 (+ x y)) have a chance to fire first.
;; Or we could recharacterize things like X86ISA::GPR-ADD-SPEC-8 to just use bvplus.
(set-axe-rule-priority acl2::bvchop-identity 1)

;; for 32-bit mode, with no stop-pcs
(defund symbolic-execution-rules32 ()
  (declare (xargs :guard t))
  '(    ;; newer scheme, 32-bit:
    run-until-return4
    run-until-esp-is-above-opener-axe ; not for IFs
    run-until-esp-is-above-base-axe ; not for IFs
    run-until-esp-is-above-of-if-arg2 ;careful, this can cause splits, todo: add support for smart IF handling
    esp-is-abovep
    ))

;; for 64-bit mode, with no stop-pcs
(defund symbolic-execution-rules64 ()
  (declare (xargs :guard t))
  '(run-until-return ; we always open this, to expose run-until-stack-shorter-than
    run-until-stack-shorter-than-opener-axe ; not for IFs
    run-until-stack-shorter-than-base-axe ; not for IFs
    run-until-stack-shorter-than-of-if-arg2 ;careful, this can cause splits, todo: add support for smart IF handling
    stack-shorter-thanp

    ;; new scheme:
    run-until-return32
    run-until-return64
    run-until-rsp-is-opener-axe ; not for IFs
    run-until-rsp-is-base-axe ; not for IFs
    run-until-rsp-is-of-if-arg2 ;careful, this can cause splits, todo: add support for smart IF handling
    acl2::equal-of-+-cancel-2

    ;; newer scheme:
    run-until-return3
    run-until-rsp-is-above-opener-axe ; not for IFs
    run-until-rsp-is-above-base-axe ; not for IFs
    run-until-rsp-is-above-of-if-arg2 ;careful, this can cause splits, todo: add support for smart IF handling
    rsp-is-abovep
    acl2::bvminus-of-bvplus-same-arg2 ; more like this?
    ;; acl2::bvminus-of-+-arg2 ; disabled later due to problems?
    ;; acl2::bvminus-of-+-arg3
    acl2::bvminus-of-+-cancel-arg3))

;; Extra rules to support the :stop-pcs option:
;;newer-scheme, 32-bits:
(defund symbolic-execution-rules-with-stop-pcs32 ()
  (declare (xargs :guard t))
  '(run-until-return-or-reach-pc4
    run-until-esp-is-above-or-reach-pc-opener-axe
    run-until-esp-is-above-or-reach-pc-base-axe
    run-until-esp-is-above-or-reach-pc-of-if-arg2
    esp-is-abovep))

;; Extra rules to support the :stop-pcs option:
(defund symbolic-execution-rules-with-stop-pcs64 ()
  (declare (xargs :guard t))
  '(run-until-return-or-reach-pc ; we always open this, to expose run-until-stack-shorter-than
    run-until-stack-shorter-than-or-reach-pc-opener-axe ; not for IFs
    run-until-stack-shorter-than-or-reach-pc-base-axe ; not for IFs
    ;; stack-shorter-thanp
    run-until-stack-shorter-than-or-reach-pc-of-if-arg2 ;careful, this can cause splits, todo: add support for smart IF handling

    ;; new scheme:
    run-until-return-or-reach-pc32
    run-until-return-or-reach-pc64
    run-until-rsp-is-or-reach-pc-opener-axe ; not for IFs
    run-until-rsp-is-or-reach-pc-base-axe ; not for IFs
    ;; stack-shorter-thanp
    run-until-rsp-is-or-reach-pc-of-if-arg2 ;careful, this can cause splits, todo: add support for smart IF handling

    ;;newer-scheme:
    run-until-return-or-reach-pc3
    run-until-rsp-is-above-or-reach-pc-opener-axe
    run-until-rsp-is-above-or-reach-pc-base-axe
    run-until-rsp-is-above-or-reach-pc-of-if-arg2
    rsp-is-abovep
    acl2::bvminus-of-bvplus-same-arg2
    ;; acl2::bvminus-of-+-arg2 ; disabled later due to problems?
    ;; acl2::bvminus-of-+-arg3
    acl2::bvminus-of-+-cancel-arg3))

(defund separate-rules ()
  (declare (xargs :guard t))
  '(x86isa::separate-normalize-r-w-x-1
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
    ;; todo: led to loops (involving <-BECOMES-BVLT-DAG-ALT-GEN-BETTER2?)
    ;;x86isa::not-equal-when-separate
    ;;x86isa::not-equal-when-separate-alt
    x86isa::not-equal-constant-when-separate-of-constants ; these are needed when we agressively turn address claims into BV claims
    x86isa::not-equal-constant-when-separate-of-constants-alt
    acl2::equal-of-+-combine-constants
    acl2::equal-of-+-combine-constants-alt
    acl2::equal-of-+-and-+-cancel-constants
    ))

(defund canonical-rules-non-bv ()
  (declare (xargs :guard t))
  '(booleanp-of-canonical-address-p
    x86isa::canonical-address-p-of-logext-48
    x86isa::logext-48-does-nothing-when-canonical-address-p
    ;; x86isa::create-canonical-address-list-1
    ;; x86isa::canonical-address-listp-of-cons
    ;; x86isa::canonical-address-listp-of-nil ;wouldn't need this if we could evaluate it
    ;; x86isa::member-p-of-create-canonical-address-list-same
    ;; x86isa::canonical-address-listp-create-canonical-address-list
    ;; x86isa::pos-and-create-canonical-address-list
    ;; x86isa::car-create-canonical-address-list
    x86isa::canonical-address-p-between ;this was involved in loops (other rules backchained from < to canonical-address-p but this does the reverse)
    ;;will axe try all free variable matches?
    ;; x86isa::canonical-address-p-between-special1
    ;; x86isa::canonical-address-p-between-special2
    ;; x86isa::canonical-address-p-between-special3
    ;; x86isa::canonical-address-p-between-special4
    x86isa::canonical-address-p-of-+-of-constant-when-natp ; useful for non-PIE code
    x86isa::integerp-when-canonical-address-p-cheap ; requires acl2::equal-same
    ;; x86isa::member-p-canonical-address-listp
    ;; x86isa::true-listp-create-canonical-address-list
    ;; x86isa::len-of-create-canonical-address-list
    x86isa::signed-byte-p-64-when-canonical-address-p-cheap ;i guess axe ignores the backchain-limit-lst ;might loop (but maybe not anymore)?
    x86isa::canonical-address-p-becomes-signed-byte-p-when-constant
    ;; x86isa::disjoint-p-two-create-canonical-address-lists-thm-1
    ;; x86isa::subset-p-two-create-canonical-address-lists-same-base-address
    x86isa::canonical-address-p-of-logext-64
    ;; x86isa::no-duplicates-p-create-canonical-address-list
    ;; x86isa::not-member-p-canonical-address-listp-when-disjoint-p
    ;; looped! not-member-p-canonical-address-listp-when-disjoint-p-alt
    ;; <-when-canonical-address-p
    ;; x86isa::disjoint-of-create-canonical-address-list-and-create-canonical-address-list-stack-and-text
    x86isa::write-canonical-address-to-memory
    ;; x86isa::canonical-address-listp-of-cdr
    ;; x86isa::car-create-canonical-address-list
    ;; x86isa::cdr-create-canonical-address-list
    ;; x86isa::disjoint-of-create-canonical-address-list-and-create-canonical-address-list-stack-and-text-special
    ;; signed-byte-p-when-between-canonical-addresses
    x86isa::canonical-address-p-+-signed-byte-p-16-is-signed-byte-p-64 ;looped
    ;;signed-byte-p-of-+-when-canonical-and-canonical ; todo: remove the one just above?
    logext-64-of-+-when-canonical-and-canonical
    ;; x86isa::not-<-when-canonical-address-p ;looped with the between lemma?
    ;; canonical-address-p-of-+-when-canonical-address-p-of-+ ;has a natp hyp that is problematic ;todo: drop?
    ;; canonical-address-p-of-+-when-canonical-address-p-of-+-alt ;todo: drop?
    ;; x86isa::disjoint-p-two-create-canonical-address-lists-thm-0-gen
    ;; x86isa::disjoint-p-two-create-canonical-address-lists-thm-1-gen
    x86isa::canonical-address-p-of-i48
    x86isa::i48-when-canonical-address-p
    ;; x86isa::canonical-address-p-of-if
    acl2::logext-of-bvplus-64 ; new, to get rid of bvplus
    ))

(defund unsigned-canonical-rules ()
  (declare (xargs :guard t))
  '(canonical-address-p-becomes-unsigned-canonical-address-p-of-bvchop
    unsigned-canonical-address-p-when-canonical-regionp-and-in-region64p
    canonical-regionp-of-+-arg2
    unsigned-canonical-address-p-of-bvif
    unsigned-canonical-address-p-of-if
    unsigned-canonical-address-p-of-bvsx-64-48
    unsigned-canonical-address-p-of-bvchop
    bvsx-64-48-of-bvplyus-48-when-unsigned-canonical-address-p
    unsigned-canonical-address-p-constant-opener
    write-of-logext-arg2 ; move?
    unsigned-canonical-address-p-of-+-when-small
    unsigned-canonical-address-p-of-bvplus-when-small
    acl2::bvplus-associative-when-constant-arg1 ; hope this is ok (had to turn it off for a blake proof).  for cancellation rules for in-region64p.  use an alias, or just a better, general cancellation rule that doesn't enforce any normal form?
    ))

(defund canonical-rules-bv ()
  (declare (xargs :guard t))
  '(
    ;; these are for the full, 64-bit address space:
    ;; WARNING: Keep in sync with the list for 48 bits above
    in-region64p-of-bvchop-arg1
    in-region64p-of-bvchop-arg3
    in-region64p-same
    in-region64p-cancel-constants-1-1+
    in-region64p-cancel-constants-1+-1
    in-region64p-cancel-constants-1+-1+
    in-region64p-cancel-1-1+
    in-region64p-cancel-1+-1
    in-region64p-cancel-1+-1+
    in-region64p-cancel-1-2
    in-region64p-cancel-2-1
    in-region64p-cancel-2+-1
    in-region64p-cancel-1+-2
    in-region64p-cancel-2-1+
    in-region64p-cancel-2+-1
    in-region64p-cancel-1-3
    in-region64p-cancel-3-1
    in-region64p-cancel-2-2
    in-region64p-when-non-negative-and-negative-range
    in-region64p-of-0-arg3 ; introduces bvlt
    in-region64p-of-+-arg1
    in-region64p-of-+-arg3

    subregion64p-constant-opener
    in-region64p-constant-opener
    disjoint-regions64p-constant-opener

    ;; some of these might become unnecesary after we switch to hiding the signed values
    ;x86isa::add-to-*ip-of-*64-bit-mode*-safe
    x86isa::canonical-address-p-+-signed-byte-p-16-is-signed-byte-p-64 ; could generalize
    ;;acl2::logext-of-plus-of-logext
    ;;write-of-logext-arg2
    ;;set-rip-of-+-of-logext
    set-rip-of-+-of-bvplus
    ;;x86isa::logext-48-does-nothing-when-canonical-address-p
    acl2::bvplus-of-logext-arg3-convert-to-bv ; crucial
    acl2::bvsx-convert-arg3-to-bv-axe ; crucial

    x86isa::integerp-when-canonical-address-p-cheap ; also in the non-bv case!
    ))

;; These are for both 32 and 64 bit modes.
;; todo: move some of these to lifter-rules32 or lifter-rules64
;; todo: should this include core-rules-bv (see below)?
(defund lifter-rules-common ()
  (declare (xargs :guard t))
  (append (read-over-write-rules-common) ; todo: don't use all these?
          (shadowed-write-rules) ; requires the x86 rewriter ; todo: not needed for 32-bit?
          (read-write-set-flag-rules) ; requires the x86 rewriter ; todo: not needed for 32-bit?
          (acl2::base-rules)
          (acl2::type-rules)
          ;; (acl2::logext-rules) ;;caused problems ;;todo: there are also logext rules below
          ;; trying these, though they are not yet as clean as they could be:
          ;; (acl2::trim-rules) ;; without these, float-macho-64 is not as nice (but better safe trim rules may help with that (e.g., when both branches of a bvif are safe to trim))
          (acl2::unsigned-byte-p-rules)
          (constant-opener-rules)
          (simple-opener-rules)
          (instruction-rules)
          (list-rules-x86)
          (state-rules)
          (if-rules)
          (decoding-and-dispatch-rules)
          (get-prefixes-openers)
          (separate-rules) ; todo: don't always use these
          (x86-type-rules)
          (logops-to-bv-rules)
          (logops-to-bv-rules-x86)
          (logops-rules)
          (acl2::bv-of-logext-rules)
          (arith-to-bv-rules)
          (bitops-to-bv-rules)
          (x86-bv-rules)
          (acl2::reassemble-bv-rules) ; add to core-rules-bv?
          (acl2::array-reduction-rules)
          (if-lifting-rules)
          (acl2::convert-to-bv-rules) ; turns things like logxor into things like bvxor
          '(acl2::boolor-of-non-nil)
          (segment-base-and-bounds-rules-general)
          (float-rules)
          (acl2::core-rules-bv)
          (acl2::bvif-rules)
          (bitops-rules)
          (acl2::if-becomes-bvif-rules)
          (acl2::list-to-bv-array-rules) ; for simplifying output-extractors
          '(acl2::len-of-cons acl2::nth-of-cons-constant-version) ; add to list-to-bv-array-rules?
          *unsigned-choppers* ;; these are just logead, aka bvchop
          *signed-choppers* ;; these are just logext
          *unsigned-recognizers* ;; these are just unsigned-byte-p
          *signed-recognizers* ;; these are just signed-byte-p
          '(;; It would be nice is all uses of !rflags could become calls to set-flag, but sometimes we seem to set all of the flags?
            ;; !rflags-becomes-xw ; todo: now get rid of rules about !rflags and rflags
            ;; rflags-becomes-xr
            ;; xw-of-rflags-and-set-flag
            ;; x86isa::xw-of-xr
            ;; xw-of-rflags-does-nothing ; use a more general rule?
            ;; alignment-checking-enabled-p-of-xw-rflags-of-xr-rflags

            ;; get-flag-of-xw-rflags-of-xr-rflags
            get-flag-of-!rflags-of-xr
            ;; xw-of-rflags-of-xw
            ;; xw-rflags-of-set-flag

            myif ; trying this, so that we only have to deal with if ; todo: remove all other rules aboute myif.  todo: try this first

            ;; These are just logext: ; todo: more!
            x86isa::n08-to-i08$inline
            x86isa::n16-to-i16$inline
            x86isa::n32-to-i32$inline
            x86isa::n64-to-i64$inline
            x86isa::n128-to-i128$inline
            x86isa::n256-to-i256$inline
            x86isa::n512-to-i512$inline

            ;; x86isa::jcc/cmovcc/setcc-spec ;case dispatch ;;disabling this to produce better results
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

            ;; State component read-over-write rules:
;            x86isa::xr-set-flag ;this is the -diff rule

            ;; Flags:
            x86isa::sub-af-spec32-same ; rewrites to 0, so perhaps worth including this rule

            ;; todo: organize these:

            ;; x86isa::rb-wb-equal
            ;; x86isa::rb-of-if-arg2

;            x86isa::set-flag-of-mv-nth-1-of-wb

            poor-mans-quotep-constant-opener

            the-check
            ;; get-prefixes:
            ;; todo: drop these if we are no longer using xw:
            x86isa::get-prefixes-does-not-modify-x86-state-in-app-view-new ;targets mv-nth-3-of-get-prefixes
            x86isa::mv-nth-0-of-get-prefixes-of-xw-of-irrel
            x86isa::mv-nth-1-of-get-prefixes-of-xw-of-irrel

            ;x86isa::mv-nth-of-cons ;mv-nth ;or do mv-nth of cons.  rules like rb-in-terms-of-nth-and-pos-eric target mv-nth

            inverse-of-+
            x86isa::combine-bytes-when-singleton

            x86isa::get-one-byte-prefix-array-code-rewrite-quotep ;;get-one-byte-prefix-array-code ;this is applied to a constant (the function is gross because it uses an array)

            ;; some of these can be needed for x86isa::canonical-address-p-between: ; move to canonical-rules-non-bv?
            acl2::<-of-+-cancel-1-2
            acl2::<-of-+-cancel-2-1
            acl2::<-of-+-cancel-2-2
            acl2::<-of-+-cancel-second-of-more-and-only ; more? rename
            acl2::<-of-+-cancel-1+-1+ ;; acl2::<-of-+-cancel-first-and-first
            acl2::<-of-+-cancel-1+-1 ; todo: same as acl2::<-of-+-cancel.  kill that one
            acl2::<-of-+-cancel-1-3
            acl2::<-of-+-cancel-3-1

            acl2::<-of-+-and-+-cancel-constants ; for array index calcs, and separateness ; todo: make these 3 names more similar?
            acl2::<-of-+-combine-constants-1
            acl2::<-of-+-combine-constants-2

            acl2::integerp-of-+-when-integerp-1-cheap
            acl2::fix-when-integerp
            acl2::integerp-when-signed-byte-p

            ;; acl2::acl2-numberp-when-signed-byte-p

            acl2::fold-consts-in-+
            acl2::ash-negative-becomes-slice-axe ; move?

            ;;one-byte-opcode-execute ;shilpi leaves this enabled, but it seems dangerous
            x86isa::one-byte-opcode-execute-base

            acl2::binary-+-bring-constant-forward ;improve to disallow the other arg to be constant

            x86isa::reg-index$inline ;not sure what this is, maybe restrict to ground terms?
            acl2::logbitp-to-getbit-equal-1 ;rename to use 'becomes'

            associativity-of-+
            x86isa::integerp-of-xr-rgf ; drop if we always use a different normal form
            ;x86isa::wb-returns-no-error-app-view ;targets mv-nth 0 of wb
;            addr-byte-alistp-create-addr-bytes-alist
;            byte-listp-byte-ify
            x86isa::xr-of-xw-diff
            ;;x86isa::xr-xw-intra-simple-field
            ;;x86isa::xr-xw-intra-array-field
            x86isa::xr-of-xw-intra-field
            x86isa::xr-of-xw-inter-field
            x86isa::program-at-xw-in-app-view
            ;x86isa::xr-wb
            ;x86isa::xr-app-view-mv-nth-1-wb ;has a hyp of t
            ;x86isa::program-at-wb-disjoint ;drop?
;            strip-cars-of-create-addr-bytes-alist
;            len-of-byte-ify ;can we drop the integerp hyp?


            ;x86isa::xr-wb-in-app-view ;targets xr-of-mv-nth-1-of-wb
            x86isa::x86-decode-sib-p               ;restrict to ground terms?
            x86isa::x86-operand-to-reg/mem         ;shilpi leaves this enabled
            x86isa::mv-nth-becomes-nth-when-constants
            acl2::distributivity-of-minus-over-+
            acl2::commutativity-2-of-+-when-constant

            acl2::signed-byte-p-of-logext
;these deal with instruction semantics?:

            x86isa::x86-effective-addr
            x86isa::x86-effective-addr-32/64
            x86isa::x86-effective-addr-from-sib

            x86isa::trunc$inline        ;shilpi leaves this enabled

            acl2::backchain-signed-byte-p-to-unsigned-byte-p-non-const
            ;x86isa::alignment-checking-enabled-p-and-wb-in-app-view ;targets alignment-checking-enabled-p-of-mv-nth-1-of-wb
            acl2::unicity-of-0         ;introduces a fix
            acl2::ash-of-0
            ;acl2::acl2-numberp-of-+    ;we also have acl2::acl2-numberp-of-sum
            ;; x86isa::rb-xw-values ; targets mv-nth-0-of-rb-of-xw and mv-nth-1-of-rb-of-xw
            ;x86isa::mv-nth-1-rb-xw-rip         ;targets mv-nth-1-of-rb
            ;x86isa::mv-nth-1-rb-xw-rgf         ;targets mv-nth-1-of-rb
            ;x86isa::mv-nth-1-rb-xw-undef

            ;; x86isa::rb-wb-disjoint-eric
            ;; x86isa::rb-wb-subset
            ;;x86isa::xw-xw-intra-array-field-shadow-writes
            ;;x86isa::xw-xw-intra-simple-field-shadow-writes
            x86isa::xw-xw-shadow-writes
            x86isa::xw-xw-inter-field-arrange-writes ;axe puts in a loop-stopper hyp
            x86isa::xw-xw-intra-field-arrange-writes ;axe puts in a loop-stopper hyp
;            assoc-list-of-rev-of-create-addr-bytes-alist
;            true-listp-of-byte-ify
            ;acl2::slice-becomes-bvchop
            ;acl2::bvchop-of-bvchop
            ;acl2::bvchop-of-bvplus
            acl2::bvchop-identity
;            combine-bytes-and-byte-ify
            acl2::open-ash-positive-constants
            acl2::logext-of-bvchop-same
            acl2::logext-identity
            acl2::logext-of-+-of-logext-arg1
            acl2::logext-of-+-of-logext-arg2
;            x86isa::xw-xr-same
            ;; acl2::bvplus-commutative-axe ;is this based on nodenum or term weight?

            x86isa::select-operand-size$inline ;shilpi leaves this enabled (could restrict to ground terms)
            x86isa::select-segment-register$inline
            x86isa::x86-operand-from-modr/m-and-sib-bytes
            ;; x86isa::write-user-rflags-rewrite ;x86isa::write-user-rflags$inline ;shilpi leaves this enabled
            x86isa::write-user-rflags-rewrite-better

            x86isa::check-instruction-length$inline

            ;acl2::bvchop-of-bvcat-cases
            ;acl2::slice-becomes-getbit
            ;acl2::getbit-of-bvcat-all
            ;; x86isa::program-at-set-flag

;            x86isa::rb-set-flag-in-app-view
            acl2::getbit-of-slice-both

;            x86isa::set-flag-and-wb-in-app-view ;shilpi leaves this enabled

            acl2::getbit-identity ;might be slow
            acl2::getbit-of-if-two-constants ;this caused the execution to split? (or maybe not?)

            acl2::unsigned-byte-p-of-if-two-constants

            ;; stuff from the timessix example:
            ;acl2::getbit-of-bvchop

            x86isa::disjoint-p-cons-1 ;restrict to a singleton?
            ;x86isa::disjoint-p-nil-1
            x86isa::not-memberp-of-+-when-disjoint-from-larger-chunk
            ;acl2::bvplus-combine-constants
            x86isa::<-of-logext-and-bvplus-of-constant

            ;acl2::logext-of-bvplus-64 ; a bit scary (instead, see todo #1 above)

            x86isa::combine-bytes-unroll
            x86isa::combine-bytes-base
            x86isa::if-of-xr-app-view

;            x86isa::set-flag-undefined$inline ;trying this..
;            x86isa::xr-set-flag-undefined
 ;           x86isa::program-at-set-flag-undefined
;xr-rgf-mv-nth-2-rb
;xr-app-view-mv-nth-2-rb

;            x86isa::x86p-of-set-flag-undefined-eric ;x86p-of-set-flag-undefined ;drop?
;            x86isa::rb-set-flag-undefined-in-app-view ;drop?

            x86isa::<-of-logext-and-+-of-constant
            ;;signed-byte-p-of-+-between

            acl2::logext-of-+-of-constant
            x86isa::unsigned-byte-p-of-bool->bit
;            x86isa::set-flag-of-set-flag-undefined-different-concrete-indices ;drop?

            x86isa::undef-flg$notinline
            x86isa::undef-flg-logic
            x86isa::undef-read$notinline
            x86isa::undef-read-logic
            ;x86isa::!undef x86isa::!undef$a

            ;x86isa::wb-xw-in-app-view

            ;acl2::bvchop-of-bvmult
            acl2::bvchop-of-ash
            acl2::nfix-does-nothing
            acl2::natp-of-+
            acl2::natp-of-nfix
            acl2::bvmult-commutative-axe
            acl2::bvmult-of-bvcat-of-0
            acl2::bvmult-of-bvchop-arg3

            x86isa::not-memberp-of-+-when-disjoint-from-larger-chunk-pos ;only needed for pe file?

            acl2::bvplus-of-unary-minus
            acl2::slice-of-bvchop-low
            x86isa::rflags x86isa::rflags$a ;exposes xr
;            x86isa::rflags-set-flag ;targets xr-of-set-flag ;drop?
            x86isa::elem-p-of-xr-rflags ; unsigned-byte-p-32-of-rflags
             ;targets unsigned-byte-p-of-rflags
            ;; acl2::bvcat-trim-arg4-axe-all
            ;; acl2::bvcat-trim-arg2-axe-all

            ;x86isa::64-bit-modep-of-mv-nth-1-of-wb

            ;;todo: include all of the lifter rules:

            x86isa::select-address-size$inline

            cf-spec64-when-unsigned-byte-p

            ;; nice rules: fixme: add the rest!
            jb-condition-of-sub-cf-spec8
            jb-condition-of-sub-cf-spec16
            jb-condition-of-sub-cf-spec32
            jb-condition-of-sub-cf-spec64
            jb-condition-of-cf-spec8
            jb-condition-of-cf-spec16
            jb-condition-of-cf-spec32
            jb-condition-of-cf-spec64
            ;jb-condition-of-getbit ; for when we turn a cf-spec function into getbit (do we still do that?)
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

            ;; jnl-condition-of-sf-spec32-and-of-spec32-same
            ;; jnl-condition-of-sf-spec64-and-of-spec64-same
            ;; jnl-condition-of-sf-spec64-and-0
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
            jo-condition-of-of-spec8
            jo-condition-of-of-spec16
            jo-condition-of-of-spec32
            jo-condition-of-of-spec64
            jo-condition-of-sub-of-spec8
            jo-condition-of-sub-of-spec16
            jo-condition-of-sub-of-spec32
            jo-condition-of-sub-of-spec64
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
            ;;jnbe-condition-of-bool->bit-of-<-of-bvchop-and-zf-spec-of-bvplus-of-bvuminus

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

            ;; more like this?
            bvchop-of-zf-spec
            logext-of-zf-spec

            ;; more like this?
            bvchop-of-sub-zf-spec32
            equal-of-sub-zf-spec32-and-1
            equal-of-1-and-sub-zf-spec32

            x86isa::memory-byte-accesses-are-always-aligned
            x86isa::address-aligned-p-of-8-and-nil
            x86isa::address-aligned-p-of-4-and-nil

            ;acl2::bvplus-trim-leading-constant
            ;acl2::bvplus-of-0-arg2
            acl2::bvchop-subst-constant
            x86isa::byte-listp-becomes-all-unsigned-byte-p
            acl2::lnfix$inline
            gl::gl-mbe-fn ;used by bitops.  yuck.

            x86isa::x86-operation-mode

            ;acl2::slice-of-bvcat-gen

            acl2::truncate-becomes-floor-gen ;it might be better to avoid explosing truncate in the first place

            acl2::<-of-constant-when-<-of-constant-integer
            acl2::<-of-constant-when-<=-of-constant-integer
            acl2::bvplus-of-+-combine-constants

            ;common-lisp::logcount-constant-opener ; for flags
            common-lisp::evenp-constant-opener ; appears in parity flag
            acl2::nonnegative-integer-quotient-constant-opener ; appears in parity flag
            acl2::zip-constant-opener ; for flags

            x86isa::x86-elem-fix ;new
            x86isa::elem-p-of-xr-rgf ; drop?
            seg-hidden-attri
            x86isa::seg-hidden-attri$a
            seg-hidden-basei
            x86isa::seg-hidden-basei$a
            seg-hidden-limiti
            x86isa::seg-hidden-limiti$a
            x86isa::!ms ; todo: use set-ms?
            x86isa::!ms$a

            acl2::bv-array-read-shorten-axe
            acl2::integerp-of-if-strong

            x86isa::feature-flags-constant-opener  ; move

            acl2::lookup-becomes-lookup-equal ; or try just executing lookup itself

            ;; Can help resolve overflow conditions in rust code:
            acl2::unsigned-byte-p-of-+-becomes-unsigned-byte-p-of-bvplus-axe

            acl2::not-of-cons

            cr0bits->ts-of-bvchop
            cr0bits->em-of-bvchop
            cr4bits->osfxsr-of-bvchop

            x86isa::chk-exc-fn ; for floating point and/or avx/vex?

            x86isa::n512p-xr-zmm ; targets unsigned-byte-p-of-xr-of-zmm

            xmmi-size$inline ; dispatches to rx32, etc
            !xmmi-size$inline ; dispatched to wx32, etc

            zmmi-size$inline ; dispatches to rz32, etc
            !zmmi-size$inline ; dispatches to wz32, etc

            rx32$inline ; these expose the rz variants ; there seem to be only 3 of these
            rx64$inline
            rx128$inline

            wx32$inline ; these expose the wz variants  ; there seem to be only 3 of these
            wx64$inline
            wx128$inline

            rz32$inline ; these expose zmmi ; there seem to be only 5 of these
            rz64$inline
            rz128$inline
            rz256$inline
            rz512$inline

            wz32$inline ; these do zmmi and then !zmmi to write part of the register ; there seem to be only 5 of these
            wz64$inline
            wz128$inline
            wz256$inline
            wz512$inline

            zmmi ; exposes zmmi$a
            zmmi$a ; exposes xr

            !zmmi ; exposes !zmmi$a
            !zmmi$a ; exposes xw

            x86isa::x86-operand-to-zmm/mem

            acl2::integerp-of-ash
            acl2::bvplus-of-bvmult-when-power-of-2p-tighten

            ;; See books/projects/x86isa/utils/basic-structs.lisp
            ;; x86isa::2bits-fix-constant-opener
            ;; x86isa::3bits-fix-constant-opener
            ;; x86isa::4bits-fix-constant-opener
            ;; x86isa::5bits-fix-constant-opener
            ;; x86isa::6bits-fix-constant-opener
            ;; x86isa::7bits-fix-constant-opener
            ;; x86isa::8bits-fix-constant-opener
            ;; x86isa::10bits-fix-constant-opener
            ;; x86isa::11bits-fix-constant-opener
            ;; x86isa::12bits-fix-constant-opener
            ;; x86isa::13bits-fix-constant-opener
            ;; x86isa::16bits-fix-constant-opener
            ;; x86isa::17bits-fix-constant-opener
            ;; x86isa::19bits-fix-constant-opener
            ;; x86isa::22bits-fix-constant-opener
            ;; x86isa::24bits-fix-constant-opener
            ;; x86isa::31bits-fix-constant-opener
            ;; x86isa::32bits-fix-constant-opener
            ;; x86isa::36bits-fix-constant-opener
            ;; x86isa::40bits-fix-constant-opener
            ;; x86isa::45bits-fix-constant-opener
            ;; x86isa::54bits-fix-constant-opener
            ;; x86isa::64bits-fix-constant-opener
            2bits-fix
            3bits-fix
            4bits-fix
            5bits-fix
            6bits-fix
            7bits-fix
            8bits-fix
            10bits-fix
            11bits-fix
            12bits-fix
            13bits-fix
            16bits-fix
            17bits-fix
            19bits-fix
            22bits-fix
            24bits-fix
            31bits-fix
            32bits-fix
            36bits-fix
            40bits-fix
            45bits-fix
            54bits-fix
            64bits-fix

            ;; maybe eventually remove, but needed for the loop lifter (at least remove other mentions)
            x86isa::integerp-when-canonical-address-p-cheap
            )))

;; This needs to fire before bvplus-convert-arg3-to-bv-axe-restricted to avoid loops on things like (bvplus 32 k (+ k (esp x86))).
;; Note that bvplus-of-constant-and-esp-when-overflow will turn a bvplus into a +.
(set-axe-rule-priority acl2::bvplus-of-+-combine-constants -1)

;; Not needed?:
;; (set-axe-rule-priority x86isa::separate-when-separate -1)
;; (set-axe-rule-priority x86isa::separate-when-separate-alt -1)

;; note: mv-nth-1-wb-and-set-flag-commute loops with set-flag-and-wb-in-app-view

;; Used in both versions of the lifter
;; TODO: Split into 32-bit and 64-bit rules:
(defund assumption-simplification-rules ()
  (declare (xargs :guard t))
  (append
   '(standard-state-assumption
     standard-state-assumption-32
     standard-assumptions-core-64
     standard-state-assumption-64
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
     lookup-equal-safe
     acl2::subroutine-address-elf
     acl2::parsed-elf-symbol-table
     acl2::get-elf-section-address
     acl2::get-elf-section-bytes
     acl2::get-elf-code
     acl2::get-elf-code-address
     acl2::get-elf-section-header-base-1
     acl2::get-elf-section-header-base-2
     acl2::get-elf-section-header-unroll
     acl2::get-elf-symbol-address
     acl2::get-elf-symbol-address-aux-base-1
     acl2::get-elf-symbol-address-aux-base-2
     acl2::get-elf-symbol-address-aux-unroll

     acl2::equal-of-0-and-mod ;acl2::mod-=-0 ;yuck
     acl2::mv-nth-of-if
     acl2::mv-nth-of-cons-safe
     x86isa::canonical-address-p-of-if
     the-check
     lookup-eq-safe
     eql ; just include base-rules?
     acl2::+-commutative-axe
     unicity-of-0
     ;; all-addreses-of-stack-slots

     rgfi rgfi$a ;expose xr -- why?  shouldn't we then turn these into get-rax, set-rax, etc?  we could use the (get-register-intro-rules64) but only for the non-loop-lifter
     x86isa::integerp-of-xr-rgf ; drop if we are not using this normal form?
     x86isa::fix-of-xr-rgf-4 ; drop if we are not using this normal form?

     x86isa::canonical-address-p$inline-constant-opener
     addresses-of-subsequent-stack-slots
     ;; addresses-of-subsequent-stack-slots-aux-base
     ;; addresses-of-subsequent-stack-slots-aux-unroll
     canonical-address-listp-of-addresses-of-subsequent-stack-slots-aux ; seems needed, for assumption simplification
     x86isa::canonical-address-listp-of-cons
     x86isa::canonical-address-p-between-special1
     x86isa::canonical-address-p-between-special2
     x86isa::canonical-address-p-between-special3
     acl2::fold-consts-in-+
     x86isa::canonical-address-listp-of-nil
     acl2::integerp-of-+-when-integerp-1-cheap
     x86isa::integerp-when-canonical-address-p-cheap ; requires acl2::equal-same
     acl2::fix-when-integerp
     acl2::equal-same
     acl2::if-of-nil
     acl2::if-of-t

     acl2::bvplus-of-logext-arg2
     acl2::bvplus-of-logext-arg3
     acl2::signed-byte-p-logext)
   (region-rules)
   (acl2::lookup-rules)
   (constant-opener-rules)
   ;; needed for BV-mode:
   '(acl2::bvchop-of-+-becomes-bvplus
     acl2::bvplus-trim-leading-constant)))

;move?
;todo: most of these are not myif rules
;; only used in loop-lifter
(defund myif-rules ()
  (declare (xargs :guard t))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Used to add limits
(defund step-opener-rules32 ()
  (declare (xargs :guard t))
  '(;; x86-fetch-decode-execute-opener ; this had binding hyps
    ;; x86-fetch-decode-execute ; this splits into too many cases when things can't be resolved
    ;; x86isa::x86-fetch-decode-execute-base ; even this can introduce confusing cases when things can't be resolved
    ;; todo: support using this one only when debugging:
    ;;x86isa::x86-fetch-decode-execute-base-new ; prevents opening when we can't resolve the pc
    ;; just use one of these 2:
    ;; x86isa::x86-fetch-decode-execute-base
    x86isa::x86-fetch-decode-execute-base-new ; todo: make a faster version, like we do for 64 bit
    ))

;; Used to add limits
(defund step-opener-rules64 ()
  (declare (xargs :guard t))
  '(x86-fetch-decode-execute-opener-safe-64))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Used in loop-lifter (old normal form) and unroller (new normal form)
;; todo: move some of these to lifter-rules-common
(defund lifter-rules32 ()
  (declare (xargs :guard t))
  (set-difference-equal
   (append (lifter-rules-common)
           (read-over-write-rules32)
           (segment-base-and-bounds-rules-32)
           (step-opener-rules32)
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
            x86isa::if-of-if-of-nil-and-consp
            acl2::unsigned-byte-p-when-unsigned-byte-p-smaller
            x86isa::canonical-address-p-when-unsigned-byte-p
            x86isa::canonical-address-p-of-sum-when-unsigned-byte-p-32
            acl2::collect-constants-over-<-2
            acl2::<-of-negative-when-usbp
            x86isa::canonical-address-p-of-if
            acl2::<-becomes-bvlt-axe-bind-free-and-bind-free
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
            acl2::+-of-bvplus-of-x-and-minus-x
            acl2::<-of-minus-and-constant
            acl2::not-equal-of-constant-when-bvlt-constant-1
            acl2::not-equal-of-constant-when-bvlt-constant-2
            acl2::acl2-numberp-when-unsigned-byte-p
            acl2::integerp-when-unsigned-byte-p-free
            x86isa::32-bit-mode-one-byte-opcode-modr/m-p-rewrite-quotep
            code-segment-readable-bit-of-xw-irrel
            code-segment-readable-bit-of-set-flag
            code-segment-readable-bit-of-write-byte-to-segment
            code-segment-readable-bit-of-write-to-segment

            data-segment-writeable-bit-of-xw-irrel
            data-segment-writeable-bit-of-set-flag
            data-segment-writeable-bit-of-set-mxcsr
            data-segment-writeable-bit-of-set-undef
            data-segment-writeable-bit-of-write-byte-to-segment
            data-segment-writeable-bit-of-write-to-segment

            code-segment-descriptor-attributesbits->r-of-bvchop
            data-segment-descriptor-attributesbits->w-of-bvchop
            data-segment-descriptor-attributesbits->e-of-bvchop
            data-segment-descriptor-attributesbits->d/b-of-bvchop

            seg-visible-not-equal-0-when-well-formed-32-bit-segmentp

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
            ))
   '(; caused loops with bvplus-of-constant-and-esp-when-overflow.  probably want to go to bvuminus anyway?:
     acl2::bvminus-of-+-arg2
     acl2::bvminus-of-+-arg3)))

(defund new-memory-rules32 ()
  (declare (xargs :guard t))
  '(;; Rules to introduce read-from-segment:
    mv-nth-1-of-rme08-becomes-read-from-segment
    mv-nth-1-of-rme16-becomes-read-from-segment
    mv-nth-1-of-rme-size$inline-becomes-read-from-segment
    mv-nth-1-of-rime-size$inline-becomes-read-from-segment-1
    mv-nth-1-of-rime-size$inline-becomes-read-from-segment-2
    mv-nth-1-of-rime-size$inline-becomes-read-from-segment-4
    mv-nth-1-of-rime-size$inline-becomes-read-from-segment-8
;    read-of-mv-nth-1-of-ea-to-la-becomes-read-from-segment

    ;; Type rules, etc for read-from-segment:
    read-from-segment-not-negative
    unsigned-byte-p-of-read-from-segment
    integerp-of-read-from-segment
    slice-of-read-from-segment-too-high

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
    read-from-segment-of-set-rax-high
    read-from-segment-of-set-rbx-high
    read-from-segment-of-set-rcx-high
    read-from-segment-of-set-rdx-high
    read-from-segment-of-set-rsp-high
    read-from-segment-of-set-rbp-high
    read-from-segment-of-xw
    read-from-segment-of-set-flag
    read-from-segment-of-set-undef
    read-from-segment-of-set-mxcsr
    ;; read-from-segment-of-set-ms

    read-from-segment-of-1 ;; simplifies to read-byte-from-segment

    ;; write-to-segment-of-bvchop ; todo: rename and uncomment here
    write-to-segment-of-bvchop-arg4

    write-to-segment-of-write-to-segment-same
    write-to-segment-of-write-to-segment-diff-axe

    ;; mv-nth-1-of-rme08-of-cs-becomes-read-byte-from-segment
    ;; mv-nth-1-of-rme08-of-cs-becomes-read-byte-from-segment-gen

    read-byte-from-segment-when-code-segment-assumptions32-for-code
    read-from-segment-when-code-segment-assumptions32-for-code

    xr-of-write-byte-to-segment
    xr-of-write-to-segment
    stack-segment-assumptions32-of-write-to-segment

    ;; Rules about read-byte-list-from-segment
    read-byte-list-from-segment-of-xw
    read-byte-list-from-segment-of-write-to-segment-diff-segments
    read-byte-list-from-segment-of-set-flag
    ;; read-byte-list-from-segment-of-set-undef
    ;; read-byte-list-from-segment-of-set-mxcsr
    ;; read-byte-list-from-segment-of-set-ms

    read-byte-from-segment-of-write-to-segment-diff-segments

    x86p-of-write-to-segment

    segment-is-32-bitsp-of-write-byte-to-segment
    segment-is-32-bitsp-of-write-to-segment

    32-bit-segment-size-of-write-byte-to-segment
    32-bit-segment-size-of-write-to-segment

    32-bit-segment-start-of-write-byte-to-segment
    32-bit-segment-start-of-write-to-segment

    segment-expand-down-bit-of-write-byte-to-segment
    segment-expand-down-bit-of-write-to-segment

    well-formed-32-bit-segmentp-of-write-byte-to-segment
    well-formed-32-bit-segmentp-of-write-to-segment

    segments-separate-of-write-byte-to-segment
    segments-separate-of-write-to-segment

    ;; Rules about code-and-stack-segments-separate (todo: do we need these and the rules about segments-separate?)
    code-and-stack-segments-separate-of-write-byte-to-segment
    code-and-stack-segments-separate-of-write-to-segment

    alignment-checking-enabled-p-of-write-byte-to-segment
    alignment-checking-enabled-p-of-write-to-segment

    64-bit-modep-of-write-bytes-to-segment

    app-view-of-write-to-segment

    code-segment-well-formedp-of-write-to-segment

    code-segment-assumptions32-for-code-of-write-to-segment

    eff-addrs-okp-of-write-to-segment

    set-flag-of-write-to-segment
    set-flag-of-write-byte-to-segment

    ;; Rules about read-byte-from-segment
    read-byte-from-segment-of-xw
    read-byte-from-segment-of-set-eip
    read-byte-from-segment-of-set-eax
    read-byte-from-segment-of-set-ebx
    read-byte-from-segment-of-set-ecx
    read-byte-from-segment-of-set-edx
    read-byte-from-segment-of-set-esp
    read-byte-from-segment-of-set-ebp
    read-byte-from-segment-of-set-rax-high
    read-byte-from-segment-of-set-rbx-high
    read-byte-from-segment-of-set-rcx-high
    read-byte-from-segment-of-set-rdx-high
    read-byte-from-segment-of-set-rsp-high
    read-byte-from-segment-of-set-rbp-high
    read-byte-from-segment-of-set-flag
    read-byte-from-segment-of-set-undef
    read-byte-from-segment-of-set-mxcsr

    ;; push memory writes inward:
    write-byte-to-segment-of-xw-rgf
    write-to-segment-of-xw-rgf

    ;; push undef stuff inward:
    set-undef-of-write-to-segment
    set-undef-of-write-byte-to-segment

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

    read-stack-dword-of-write-to-segment-diff-segments
    write-to-segment-of-write-byte-to-segment-included
    write-to-segment-of-write-to-segment-included
    ))

;; The new normal form uses:
;; EAX, etc.
;; SET-EAX, etc.
;; RAX-HIGH, etc. (these should go away)
;; what else?
;; new batch of rules for the more abstract lifter (but move some of these elsewhere):
;; todo: restrict this to memory stuff?
(defund new-normal-form-rules32 ()
  (declare (xargs :guard t))
  (append
  '(;; Introduce register writers:
    xw-becomes-set-eax
    xw-becomes-set-ebx
    xw-becomes-set-ecx
    xw-becomes-set-edx
    xw-becomes-set-esp
    xw-becomes-set-ebp
    set-rax-high-of-bvchop
    set-rbx-high-of-bvchop
    set-rcx-high-of-bvchop
    set-rdx-high-of-bvchop
    set-rsp-high-of-bvchop
    set-rbp-high-of-bvchop
    set-rax-high-does-nothing
    set-rbx-high-does-nothing
    set-rcx-high-does-nothing
    set-rdx-high-does-nothing
    set-rsp-high-does-nothing
    set-rbp-high-does-nothing

    rax-high-of-write-byte-to-segment
    rbx-high-of-write-byte-to-segment
    rcx-high-of-write-byte-to-segment
    rdx-high-of-write-byte-to-segment
    rsp-high-of-write-byte-to-segment
    rbp-high-of-write-byte-to-segment

    rax-high-of-write-to-segment
    rbx-high-of-write-to-segment
    rcx-high-of-write-to-segment
    rdx-high-of-write-to-segment
    rsp-high-of-write-to-segment
    rbp-high-of-write-to-segment

    ;; rax-high-of-write-bytes-to-segment
    ;; rbx-high-of-write-bytes-to-segment
    ;; rcx-high-of-write-bytes-to-segment
    ;; rdx-high-of-write-bytes-to-segment
    ;; rsp-high-of-write-bytes-to-segment
    ;; rbp-high-of-write-bytes-to-segment

    ;; Introduce EIP (we put in eip instead of rip since these rules are for 32-bit reasoning -- eip now returns a u32)
    xr-becomes-eip
    rip-becomes-eip
    read-*ip-becomes-eip

    ;; Introduce set-eip
    xw-becomes-set-eip
    !rip-becomes-set-eip

    ;; Introduce register readers:
    xr-becomes-eax
    xr-becomes-ebx
    xr-becomes-ecx
    xr-becomes-edx
    xr-becomes-ebp
    xr-becomes-esp

    data-segment-writeable-bit-of-set-eip
    data-segment-writeable-bit-of-set-eax
    data-segment-writeable-bit-of-set-ebx
    data-segment-writeable-bit-of-set-ecx
    data-segment-writeable-bit-of-set-edx
    data-segment-writeable-bit-of-set-esp
    data-segment-writeable-bit-of-set-ebp
    data-segment-writeable-bit-of-set-rax-high
    data-segment-writeable-bit-of-set-rbx-high
    data-segment-writeable-bit-of-set-rcx-high
    data-segment-writeable-bit-of-set-rdx-high
    data-segment-writeable-bit-of-set-rsp-high
    data-segment-writeable-bit-of-set-rbp-high

    get-flag-of-set-eip
    get-flag-of-set-eax
    get-flag-of-set-ebx
    get-flag-of-set-ecx
    get-flag-of-set-edx
    get-flag-of-set-esp
    get-flag-of-set-ebp
    get-flag-of-set-rax-high
    get-flag-of-set-rbx-high
    get-flag-of-set-rcx-high
    get-flag-of-set-rdx-high
    get-flag-of-set-rsp-high
    get-flag-of-set-rbp-high

    program-at-of-set-eip ; only needed for loop lifter?
    program-at-of-set-eax
    program-at-of-set-ebx
    program-at-of-set-ecx
    program-at-of-set-edx
    program-at-of-set-esp
    program-at-of-set-ebp
    program-at-of-set-rax-high
    program-at-of-set-rbx-high
    program-at-of-set-rcx-high
    program-at-of-set-rdx-high
    program-at-of-set-rsp-high
    program-at-of-set-rbp-high

    code-segment-readable-bit-of-set-eip
    code-segment-readable-bit-of-set-eax
    code-segment-readable-bit-of-set-ebx
    code-segment-readable-bit-of-set-ecx
    code-segment-readable-bit-of-set-edx
    code-segment-readable-bit-of-set-esp
    code-segment-readable-bit-of-set-ebp
    code-segment-readable-bit-of-set-rax-high
    code-segment-readable-bit-of-set-rbx-high
    code-segment-readable-bit-of-set-rcx-high
    code-segment-readable-bit-of-set-rdx-high
    code-segment-readable-bit-of-set-rsp-high
    code-segment-readable-bit-of-set-rbp-high

    acl2::bvchop-numeric-bound ; move
    acl2::fix-of-ifix ; move

;    not-mv-nth-0-of-ea-to-la-of-cs
    not-mv-nth-0-of-rme08
    not-mv-nth-0-of-rme16

    return-address-okp-intro

    ;; Rules about writing:
    not-mv-nth-0-of-wme-size ;gets rid of error branch

    ;; Rules about reading:
    not-mv-nth-0-of-rme-size$inline ;; gets rid of error branch
    mv-nth-2-of-rme-size$inline ;; shows that reading does not change the state
    not-mv-nth-0-of-rime-size$inline ;; gets rid of error branch
    mv-nth-2-of-rime-size$inline ;; shows that reading does not change the state


    x86isa::rme08-does-not-affect-state-in-app-view ;; targets mv-nth-2-of-rme08
    x86isa::rme16-does-not-affect-state-in-app-view ;; targets mv-nth-2-of-rme16

    ;xr-of-set-reg-high-irrel

    ;; Rules about EIP/SET-EIP:
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
    eip-of-set-rax-high
    eip-of-set-rbx-high
    eip-of-set-rcx-high
    eip-of-set-rdx-high
    eip-of-set-rsp-high
    eip-of-set-rbp-high
    eip-of-xw-irrel
;eip-of-xw-of-rip ;drop?
    not-mv-nth-0-of-add-to-*ip
;mv-nth-1-of-add-to-*ip
    mv-nth-1-of-add-to-*ip-gen

    set-eax-of-bvchop
    set-ebx-of-bvchop
    set-ecx-of-bvchop
    set-edx-of-bvchop
    set-ebp-of-bvchop
    set-esp-of-bvchop

    set-eax-when-equal-eax ; could restrict to when the val is (eax x86)
    set-ebx-when-equal-ebx
    set-ecx-when-equal-ecx
    set-edx-when-equal-edx
    set-esp-when-equal-esp
    set-ebp-when-equal-ebp
    set-undef-of-undef-same-gen ; rename?  ; in case set-reg-high is inside the set-undef

    undef-of-set-eip
    undef-of-set-eax
    undef-of-set-ebx
    undef-of-set-ecx
    undef-of-set-edx
    undef-of-set-esp
    undef-of-set-ebp
    undef-of-set-rax-high
    undef-of-set-rbx-high
    undef-of-set-rcx-high
    undef-of-set-rdx-high
    undef-of-set-rsp-high
    undef-of-set-rbp-high

    set-rax-high-of-set-eax
    set-rax-high-of-set-ebx
    set-rax-high-of-set-ecx
    set-rax-high-of-set-edx
    set-rax-high-of-set-esp
    set-rax-high-of-set-ebp

    set-rbx-high-of-set-eax
    set-rbx-high-of-set-ebx
    set-rbx-high-of-set-ecx
    set-rbx-high-of-set-edx
    set-rbx-high-of-set-esp
    set-rbx-high-of-set-ebp

    set-rcx-high-of-set-eax
    set-rcx-high-of-set-ebx
    set-rcx-high-of-set-ecx
    set-rcx-high-of-set-edx
    set-rcx-high-of-set-esp
    set-rcx-high-of-set-ebp

    set-rdx-high-of-set-eax
    set-rdx-high-of-set-ebx
    set-rdx-high-of-set-ecx
    set-rdx-high-of-set-edx
    set-rdx-high-of-set-esp
    set-rdx-high-of-set-ebp

    set-rsp-high-of-set-eax
    set-rsp-high-of-set-ebx
    set-rsp-high-of-set-ecx
    set-rsp-high-of-set-edx
    set-rsp-high-of-set-esp
    set-rsp-high-of-set-ebp

    set-rbp-high-of-set-eax
    set-rbp-high-of-set-ebx
    set-rbp-high-of-set-ecx
    set-rbp-high-of-set-edx
    set-rbp-high-of-set-esp
    set-rbp-high-of-set-ebp

    set-rax-high-of-set-eip
    set-rbx-high-of-set-eip
    set-rcx-high-of-set-eip
    set-rdx-high-of-set-eip
    set-rsp-high-of-set-eip
    set-rbp-high-of-set-eip

    set-rax-high-of-set-eax
    set-rax-high-of-set-ebx
    set-rax-high-of-set-ecx
    set-rax-high-of-set-edx
    set-rax-high-of-set-esp
    set-rax-high-of-set-ebp
    set-rbx-high-of-set-eax
    set-rbx-high-of-set-ebx
    set-rbx-high-of-set-ecx
    set-rbx-high-of-set-edx
    set-rbx-high-of-set-esp
    set-rbx-high-of-set-ebp
    set-rcx-high-of-set-eax
    set-rcx-high-of-set-ebx
    set-rcx-high-of-set-ecx
    set-rcx-high-of-set-edx
    set-rcx-high-of-set-esp
    set-rcx-high-of-set-ebp
    set-rdx-high-of-set-eax
    set-rdx-high-of-set-ebx
    set-rdx-high-of-set-ecx
    set-rdx-high-of-set-edx
    set-rdx-high-of-set-esp
    set-rdx-high-of-set-ebp
    set-rsp-high-of-set-eax
    set-rsp-high-of-set-ebx
    set-rsp-high-of-set-ecx
    set-rsp-high-of-set-edx
    set-rsp-high-of-set-esp
    set-rsp-high-of-set-ebp
    set-rbp-high-of-set-eax
    set-rbp-high-of-set-ebx
    set-rbp-high-of-set-ecx
    set-rbp-high-of-set-edx
    set-rbp-high-of-set-esp
    set-rbp-high-of-set-ebp

    set-rax-high-of-set-flag
    set-rbx-high-of-set-flag
    set-rcx-high-of-set-flag
    set-rdx-high-of-set-flag
    set-rsp-high-of-set-flag
    set-rbp-high-of-set-flag

    set-rax-high-of-!rflags
    set-rbx-high-of-!rflags
    set-rcx-high-of-!rflags
    set-rdx-high-of-!rflags
    set-rsp-high-of-!rflags
    set-rbp-high-of-!rflags

    set-rax-high-of-set-undef
    set-rbx-high-of-set-undef
    set-rcx-high-of-set-undef
    set-rdx-high-of-set-undef
    set-rsp-high-of-set-undef
    set-rbp-high-of-set-undef

    ;; set-reg-high-of-set-reg-high-same
    ;; set-reg-high-of-set-reg-high-diff

    mxcsr-of-set-eip
    mxcsr-of-set-eax
    mxcsr-of-set-ebx
    mxcsr-of-set-ecx
    mxcsr-of-set-edx
    mxcsr-of-set-esp
    mxcsr-of-set-ebp
    mxcsr-of-set-rax-high
    mxcsr-of-set-rbx-high
    mxcsr-of-set-rcx-high
    mxcsr-of-set-rdx-high
    mxcsr-of-set-rsp-high
    mxcsr-of-set-rbp-high

    ms-of-set-eip
    ms-of-set-eax
    ms-of-set-ebx
    ms-of-set-ecx
    ms-of-set-edx
    ms-of-set-esp
    ms-of-set-ebp
    ms-of-set-rax-high
    ms-of-set-rbx-high
    ms-of-set-rcx-high
    ms-of-set-rdx-high
    ms-of-set-rsp-high
    ms-of-set-rbp-high

    fault-of-set-eip
    fault-of-set-eax
    fault-of-set-ebx
    fault-of-set-ecx
    fault-of-set-edx
    fault-of-set-esp
    fault-of-set-ebp
    fault-of-set-rax-high
    fault-of-set-rbx-high
    fault-of-set-rcx-high
    fault-of-set-rdx-high
    fault-of-set-rsp-high
    fault-of-set-rbp-high

    ;; bury set-undef deep in the term:
    set-undef-of-set-eip
    set-undef-of-set-eax
    set-undef-of-set-ebx
    set-undef-of-set-ecx
    set-undef-of-set-edx
    ;; set-undef-of-set-edi
    ;; set-undef-of-set-esi
    set-undef-of-set-esp
    set-undef-of-set-ebp

    ;; bury set-mxcsr deep in the term:
    set-mxcsr-of-set-eip
    set-mxcsr-of-set-eax
    set-mxcsr-of-set-ebx
    set-mxcsr-of-set-ecx
    set-mxcsr-of-set-edx
    ;; set-mxcsr-of-set-edi
    ;; set-mxcsr-of-set-esi
    set-mxcsr-of-set-esp
    set-mxcsr-of-set-ebp

    eax-of-set-flag
    ebx-of-set-flag
    ecx-of-set-flag
    edx-of-set-flag
    ebp-of-set-flag
    esp-of-set-flag
    ;; esi-of-set-flag
    ;; edi-of-set-flag
    ;todo: more?

    rax-high-of-set-flag
    rbx-high-of-set-flag
    rcx-high-of-set-flag
    rdx-high-of-set-flag
    rbp-high-of-set-flag
    rsp-high-of-set-flag

    eax-of-set-undef
    ebx-of-set-undef
    ecx-of-set-undef
    edx-of-set-undef
    ebp-of-set-undef
    esp-of-set-undef
    ;; esi-of-set-undef
    ;; edi-of-set-undef
    ;todo: more?

    rax-high-of-set-undef
    rbx-high-of-set-undef
    rcx-high-of-set-undef
    rdx-high-of-set-undef
    rbp-high-of-set-undef
    rsp-high-of-set-undef

    eax-of-set-mxcsr
    ebx-of-set-mxcsr
    ecx-of-set-mxcsr
    edx-of-set-mxcsr
    ebp-of-set-mxcsr
    esp-of-set-mxcsr
    ;; esi-of-set-mxcsr
    ;; edi-of-set-mxcsr
    ;todo: more?

    rax-high-of-set-mxcsr
    rbx-high-of-set-mxcsr
    rcx-high-of-set-mxcsr
    rdx-high-of-set-mxcsr
    rbp-high-of-set-mxcsr
    rsp-high-of-set-mxcsr

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
    slice-63-32-of-+-of-esp-when-stack-segment-assumptions32
    bvchop-of-+-of-esp-becomes-+-of-esp ; new, lets us drop the bvchop
    ;; bvplus-32-of-esp-becomes-+-of-esp ; could uncomment if needed
    esp-bound
    natp-of-+-of-esp-lemma
    signed-byte-p-of-+-of-esp

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

    not-<-of-32-bit-segment-size
    <-of-32-bit-segment-size
    eff-addrs-lemma ; rename
    well-formed-32-bit-segmentp-when-stack-segment-assumptions32

    eff-addr-okp-when-code-segment-assumptions32-for-code
    eff-addrs-okp-when-code-segment-assumptions32-for-code
    seg-regp-constant-opener ; move?
    acl2::integer-range-p-constant-opener ; move

;    x86isa::ea-to-la-of-xw
;    ea-to-la-of-write-to-segment
;    canonical-address-p-of-mv-nth-1-of-ea-to-la-of-cs
;    canonical-address-p-of-mv-nth-1-of-ea-to-la-of-ss
    ;x86isa::mv-nth-0-rb-xw-rgf ;gen?
    ;x86isa::mv-nth-0-rb-xw-rip
    ;; x86isa::rb-xw-values
;    fix-of-mv-nth-1-of-ea-to-la
;    read-of-ea-to-la-becomes-read-byte-from-segment
;    canonical-address-p-of-+-of-mv-nth-1-of-ea-to-la-of-ss
    acl2::if-x-x-y-when-booleanp
;    mv-nth-0-of-ea-to-la ; introduces eff-addrs-okp

    eff-addr-okp-of-set-flag
    ;; eff-addr-okp-of-set-undef
    ;; eff-addr-okp-of-set-ms
    eff-addr-okp-of-write-to-segment
    stack-segment-assumptions32-of-xw-of-rgf
    esp-of-xw-of-rgf-and-rsp
    eff-addr-okp-of-+-of-esp
    ea-to-la-of-set-flag ; move?
    ;; ea-to-la-of-set-undef
    ;; ea-to-la-of-set-ms
    ;fix-of-esp
    ;bvchop-32-of-esp
    signed-byte-p-64-of-esp
    eff-addr-okp-of-esp

    ;; Rules about x86p
    x86p-of-set-eip
    x86p-of-set-eax
    x86p-of-set-ebx
    x86p-of-set-ecx
    x86p-of-set-edx
    x86p-of-set-esp
    x86p-of-set-ebp
    x86p-of-set-rax-high
    x86p-of-set-rbx-high
    x86p-of-set-rcx-high
    x86p-of-set-rdx-high
    x86p-of-set-rsp-high
    x86p-of-set-rbp-high

    ;; Rules about segment-is-32-bitsp
    segment-is-32-bitsp-of-set-eip
    segment-is-32-bitsp-of-set-eax
    segment-is-32-bitsp-of-set-ebx
    segment-is-32-bitsp-of-set-ecx
    segment-is-32-bitsp-of-set-edx
    segment-is-32-bitsp-of-set-esp
    segment-is-32-bitsp-of-set-ebp
    segment-is-32-bitsp-of-set-rax-high
    segment-is-32-bitsp-of-set-rbx-high
    segment-is-32-bitsp-of-set-rcx-high
    segment-is-32-bitsp-of-set-rdx-high
    segment-is-32-bitsp-of-set-rsp-high
    segment-is-32-bitsp-of-set-rbp-high
    segment-is-32-bitsp-of-set-flag
    segment-is-32-bitsp-of-set-undef
    segment-is-32-bitsp-of-set-mxcsr
    segment-is-32-bitsp-of-xw-irrel

    ;;Rules about 32-bit-segment-size
    32-bit-segment-size-of-set-eip
    32-bit-segment-size-of-set-eax
    32-bit-segment-size-of-set-ebx
    32-bit-segment-size-of-set-ecx
    32-bit-segment-size-of-set-edx
    32-bit-segment-size-of-set-esp
    32-bit-segment-size-of-set-ebp
    32-bit-segment-size-of-set-rax-high
    32-bit-segment-size-of-set-rbx-high
    32-bit-segment-size-of-set-rcx-high
    32-bit-segment-size-of-set-rdx-high
    32-bit-segment-size-of-set-rsp-high
    32-bit-segment-size-of-set-rbp-high
    32-bit-segment-size-of-set-flag
    32-bit-segment-size-of-set-undef
    32-bit-segment-size-of-set-mxcsr
    32-bit-segment-size-of-xw

    ;;Rules about 32-bit-segment-start
    32-bit-segment-start-of-set-eip
    32-bit-segment-start-of-set-eax
    32-bit-segment-start-of-set-ebx
    32-bit-segment-start-of-set-ecx
    32-bit-segment-start-of-set-edx
    32-bit-segment-start-of-set-esp
    32-bit-segment-start-of-set-ebp
    32-bit-segment-start-of-set-rax-high
    32-bit-segment-start-of-set-rbx-high
    32-bit-segment-start-of-set-rcx-high
    32-bit-segment-start-of-set-rdx-high
    32-bit-segment-start-of-set-rsp-high
    32-bit-segment-start-of-set-rbp-high
    32-bit-segment-start-of-set-flag
    32-bit-segment-start-of-set-undef
    32-bit-segment-start-of-set-mxcsr
    32-bit-segment-start-of-xw

    ;; Rules about segment-expand-down-bit
    segment-expand-down-bit-of-set-eip
    segment-expand-down-bit-of-set-eax
    segment-expand-down-bit-of-set-ebx
    segment-expand-down-bit-of-set-ecx
    segment-expand-down-bit-of-set-edx
    segment-expand-down-bit-of-set-esp
    segment-expand-down-bit-of-set-ebp
    segment-expand-down-bit-of-set-rax-high
    segment-expand-down-bit-of-set-rbx-high
    segment-expand-down-bit-of-set-rcx-high
    segment-expand-down-bit-of-set-rdx-high
    segment-expand-down-bit-of-set-rsp-high
    segment-expand-down-bit-of-set-rbp-high
    segment-expand-down-bit-of-set-flag
    segment-expand-down-bit-of-set-undef
    segment-expand-down-bit-of-set-mxcsr
    segment-expand-down-bit-of-xw-irrel

    ;; Rules about well-formed-32-bit-segmentp
    well-formed-32-bit-segmentp-of-set-eip
    well-formed-32-bit-segmentp-of-set-eax
    well-formed-32-bit-segmentp-of-set-ebx
    well-formed-32-bit-segmentp-of-set-ecx
    well-formed-32-bit-segmentp-of-set-edx
    well-formed-32-bit-segmentp-of-set-esp
    well-formed-32-bit-segmentp-of-set-ebp
    well-formed-32-bit-segmentp-of-set-rax-high
    well-formed-32-bit-segmentp-of-set-rbx-high
    well-formed-32-bit-segmentp-of-set-rcx-high
    well-formed-32-bit-segmentp-of-set-rdx-high
    well-formed-32-bit-segmentp-of-set-rsp-high
    well-formed-32-bit-segmentp-of-set-rbp-high
    well-formed-32-bit-segmentp-of-set-flag
    well-formed-32-bit-segmentp-of-set-undef
    well-formed-32-bit-segmentp-of-set-mxcsr
    well-formed-32-bit-segmentp-of-xw

    ;; Rules about segments-separate
    segments-separate-of-set-eip
    segments-separate-of-set-eax
    segments-separate-of-set-ebx
    segments-separate-of-set-ecx
    segments-separate-of-set-edx
    segments-separate-of-set-esp
    segments-separate-of-set-ebp
    segments-separate-of-set-rax-high
    segments-separate-of-set-rbx-high
    segments-separate-of-set-rcx-high
    segments-separate-of-set-rdx-high
    segments-separate-of-set-rsp-high
    segments-separate-of-set-rbp-high
    segments-separate-of-set-flag
    segments-separate-of-set-undef
    segments-separate-of-set-mxcsr
    segments-separate-of-xw-irrel

    ;; Rules about code-and-stack-segments-separate (todo: do we need these and the rules about segments-separate?)
    code-and-stack-segments-separate-of-set-eip
    code-and-stack-segments-separate-of-set-eax
    code-and-stack-segments-separate-of-set-ebx
    code-and-stack-segments-separate-of-set-ecx
    code-and-stack-segments-separate-of-set-edx
    code-and-stack-segments-separate-of-set-esp
    code-and-stack-segments-separate-of-set-ebp
    code-and-stack-segments-separate-of-set-rax-high
    code-and-stack-segments-separate-of-set-rbx-high
    code-and-stack-segments-separate-of-set-rcx-high
    code-and-stack-segments-separate-of-set-rdx-high
    code-and-stack-segments-separate-of-set-rsp-high
    code-and-stack-segments-separate-of-set-rbp-high
    code-and-stack-segments-separate-of-set-flag
    code-and-stack-segments-separate-of-set-undef
    code-and-stack-segments-separate-of-set-mxcsr
    code-and-stack-segments-separate-of-xw-irrel

    ;; Rules about alignment-checking-enabled-p
    alignment-checking-enabled-p-of-set-eip
    alignment-checking-enabled-p-of-set-eax
    alignment-checking-enabled-p-of-set-ebx
    alignment-checking-enabled-p-of-set-ecx
    alignment-checking-enabled-p-of-set-edx
    alignment-checking-enabled-p-of-set-esp
    alignment-checking-enabled-p-of-set-ebp
    alignment-checking-enabled-p-of-set-rax-high
    alignment-checking-enabled-p-of-set-rbx-high
    alignment-checking-enabled-p-of-set-rcx-high
    alignment-checking-enabled-p-of-set-rdx-high
    alignment-checking-enabled-p-of-set-rsp-high
    alignment-checking-enabled-p-of-set-rbp-high

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

    eax-of-set-rbx-high
    eax-of-set-rcx-high
    eax-of-set-rdx-high
    eax-of-set-rsp-high
    eax-of-set-rbp-high
    ebx-of-set-rax-high
    ebx-of-set-rcx-high
    ebx-of-set-rdx-high
    ebx-of-set-rsp-high
    ebx-of-set-rbp-high
    ecx-of-set-rax-high
    ecx-of-set-rbx-high
    ecx-of-set-rdx-high
    ecx-of-set-rsp-high
    ecx-of-set-rbp-high
    edx-of-set-rax-high
    edx-of-set-rbx-high
    edx-of-set-rcx-high
    edx-of-set-rsp-high
    edx-of-set-rbp-high
    esp-of-set-rax-high
    esp-of-set-rbx-high
    esp-of-set-rcx-high
    esp-of-set-rdx-high
    esp-of-set-rbp-high
    ebp-of-set-rax-high
    ebp-of-set-rbx-high
    ebp-of-set-rcx-high
    ebp-of-set-rdx-high
    ebp-of-set-rsp-high

    rax-high-of-set-ebx
    rax-high-of-set-ecx
    rax-high-of-set-edx
    rax-high-of-set-esp
    rax-high-of-set-ebp
    rbx-high-of-set-eax
    rbx-high-of-set-ecx
    rbx-high-of-set-edx
    rbx-high-of-set-esp
    rbx-high-of-set-ebp
    rcx-high-of-set-eax
    rcx-high-of-set-ebx
    rcx-high-of-set-edx
    rcx-high-of-set-esp
    rcx-high-of-set-ebp
    rdx-high-of-set-eax
    rdx-high-of-set-ebx
    rdx-high-of-set-ecx
    rdx-high-of-set-esp
    rdx-high-of-set-ebp
    rsp-high-of-set-eax
    rsp-high-of-set-ebx
    rsp-high-of-set-ecx
    rsp-high-of-set-edx
    rsp-high-of-set-ebp
    rbp-high-of-set-eax
    rbp-high-of-set-ebx
    rbp-high-of-set-ecx
    rbp-high-of-set-edx
    rbp-high-of-set-esp

    ;; Rules about esp
    ;; esp-of-set-reg-high
    esp-of-set-eip
    esp-of-set-flag
    esp-of-set-undef
    esp-of-set-mxcsr
    esp-of-xw-irrel
    natp-of-esp-when-stack-segment-assumptions32

    ;; Rules about 64-bit-modep

    64-bit-modep-of-set-eip
    64-bit-modep-of-set-eax
    64-bit-modep-of-set-ebx
    64-bit-modep-of-set-ecx
    64-bit-modep-of-set-edx
    64-bit-modep-of-set-esp
    64-bit-modep-of-set-ebp
    64-bit-modep-of-set-rax-high
    64-bit-modep-of-set-rbx-high
    64-bit-modep-of-set-rcx-high
    64-bit-modep-of-set-rdx-high
    64-bit-modep-of-set-rsp-high
    64-bit-modep-of-set-rbp-high

    ;; Rules about app-view

    app-view-of-set-eip
    app-view-of-set-eax
    app-view-of-set-ebx
    app-view-of-set-ecx
    app-view-of-set-edx
    app-view-of-set-esp
    app-view-of-set-ebp
    app-view-of-set-rax-high
    app-view-of-set-rbx-high
    app-view-of-set-rcx-high
    app-view-of-set-rdx-high
    app-view-of-set-rsp-high
    app-view-of-set-rbp-high

    ;; Rules about code-segment-well-formedp
    code-segment-well-formedp-of-xw ;; lets us drop most state updates
    code-segment-well-formedp-of-set-eip
    code-segment-well-formedp-of-set-eax
    code-segment-well-formedp-of-set-ebx
    code-segment-well-formedp-of-set-ecx
    code-segment-well-formedp-of-set-edx
    code-segment-well-formedp-of-set-esp
    code-segment-well-formedp-of-set-ebp
    code-segment-well-formedp-of-set-rax-high
    code-segment-well-formedp-of-set-rbx-high
    code-segment-well-formedp-of-set-rcx-high
    code-segment-well-formedp-of-set-rdx-high
    code-segment-well-formedp-of-set-rsp-high
    code-segment-well-formedp-of-set-rbp-high
    code-segment-well-formedp-of-set-flag
    code-segment-well-formedp-of-set-undef
    code-segment-well-formedp-of-set-mxcsr

    ;; Rules about code-segment-assumptions32-for-code
    code-segment-assumptions32-for-code-of-xw
    code-segment-assumptions32-for-code-of-set-eip
    code-segment-assumptions32-for-code-of-set-eax
    code-segment-assumptions32-for-code-of-set-ebx
    code-segment-assumptions32-for-code-of-set-ecx
    code-segment-assumptions32-for-code-of-set-edx
    code-segment-assumptions32-for-code-of-set-esp
    code-segment-assumptions32-for-code-of-set-ebp
    code-segment-assumptions32-for-code-of-set-rax-high
    code-segment-assumptions32-for-code-of-set-rbx-high
    code-segment-assumptions32-for-code-of-set-rcx-high
    code-segment-assumptions32-for-code-of-set-rdx-high
    code-segment-assumptions32-for-code-of-set-rsp-high
    code-segment-assumptions32-for-code-of-set-rbp-high
    code-segment-assumptions32-for-code-of-set-flag
    code-segment-assumptions32-for-code-of-set-undef
    code-segment-assumptions32-for-code-of-set-mxcsr

    unsigned-byte-p-of-+-of-esp
    eff-addr-okp-of-+-of-esp-positive-offset ; todo: bv version
    eff-addrs-okp-of-+-of-esp-positive-offset ; todo: bv version
    eff-addrs-okp-of-+-of-esp-negative-offset ; todo: bv version

    eff-addrs-okp-of-esp
    sep-eff-addr-ranges ;; we leave this enabled, at least for now

    ;; move some of these:
    unsigned-byte-p-of-+-of-esp-negative-offset-simple
    bvminus-cancel-2-2
    bvminus-cancel-2-all
    bvminus-cancel-all-2
    mv-nth-1-of-add-to-*sp-gen-special
    mv-nth-1-of-add-to-*sp-positive-offset
    segments-separate-of-code-and-stack
    write-*ip-inline-becomes-xw

    ;;segment-min-eff-addr32-of-set-undef
    ;;segment-min-eff-addr32-of-set-eip ;drop?
    ;;segment-max-eff-addr32-of-set-eip ;drop?

    ;; ea-to-la-of-set-eip

    eff-addr-okp-of-xw-irrel
    eff-addr-okp-of-set-eip
    eff-addr-okp-of-set-eax
    eff-addr-okp-of-set-ebx
    eff-addr-okp-of-set-ecx
    eff-addr-okp-of-set-edx
    eff-addr-okp-of-set-esp
    eff-addr-okp-of-set-ebp
    eff-addr-okp-of-set-rax-high
    eff-addr-okp-of-set-rbx-high
    eff-addr-okp-of-set-rcx-high
    eff-addr-okp-of-set-rdx-high
    eff-addr-okp-of-set-rsp-high
    eff-addr-okp-of-set-rbp-high

    eff-addrs-okp-of-xw-irrel
    eff-addrs-okp-of-set-flag
    eff-addrs-okp-of-set-undef
    eff-addrs-okp-of-set-mxcsr
    eff-addrs-okp-of-set-eip
    eff-addrs-okp-of-set-eax
    eff-addrs-okp-of-set-ebx
    eff-addrs-okp-of-set-ecx
    eff-addrs-okp-of-set-edx
    eff-addrs-okp-of-set-esp
    eff-addrs-okp-of-set-ebp
    eff-addrs-okp-of-set-rax-high
    eff-addrs-okp-of-set-rbx-high
    eff-addrs-okp-of-set-rcx-high
    eff-addrs-okp-of-set-rdx-high
    eff-addrs-okp-of-set-rsp-high
    eff-addrs-okp-of-set-rbp-high

    eff-addrs-okp-of-1 ;simplifies to just eff-addr-okp
    segment-is-32-bitsp-intro-code
    segment-is-32-bitsp-intro-data
    code-segment-readable-bit-intro
    data-segment-writeable-bit-intro
    data-segment-writeable-bit-when-stack-segment-assumptions32
    not-<-of-seg-hidden-limit-when-code-segment-assumptions32-for-code

    ;; normalizing nests of state updates:

    ;; push flag stuff inward:
    set-flag-of-set-eip-irrel
    set-flag-of-set-eax
    set-flag-of-set-ebx
    set-flag-of-set-ecx
    set-flag-of-set-edx
    set-flag-of-set-esp
    set-flag-of-set-ebp

    ;; read of write of same register
    eax-of-set-eax
    ebx-of-set-ebx
    ecx-of-set-ecx
    edx-of-set-edx
    esp-of-set-esp
    ebp-of-set-ebp

    ;; eax-of-set-reg-high
    eax-of-set-eip
    ;; ebx-of-set-reg-high
    ebx-of-set-eip
    ;; ecx-of-set-reg-high
    ecx-of-set-eip
    ;; edx-of-set-reg-high
    edx-of-set-eip
    ;; ebp-of-set-reg-high
    ebp-of-set-eip
    ;esp-of-set-eip

    rax-high-of-set-eip
    ;; ebx-of-set-reg-high
    rbx-high-of-set-eip
    ;; ecx-of-set-reg-high
    rcx-high-of-set-eip
    ;; edx-of-set-reg-high
    rdx-high-of-set-eip
    ;; ebp-of-set-reg-high
    rbp-high-of-set-eip
    ;esp-of-set-eip

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

    set-rbx-high-of-set-rax-high
    set-rcx-high-of-set-rax-high
    set-rdx-high-of-set-rax-high
    set-rsp-high-of-set-rax-high
    set-rbp-high-of-set-rax-high
    set-rcx-high-of-set-rbx-high
    set-rdx-high-of-set-rbx-high
    set-rsp-high-of-set-rbx-high
    set-rbp-high-of-set-rbx-high
    set-rdx-high-of-set-rcx-high
    set-rsp-high-of-set-rcx-high
    set-rbp-high-of-set-rcx-high
    set-rsp-high-of-set-rdx-high
    set-rbp-high-of-set-rdx-high
    set-rbp-high-of-set-rsp-high

    xr-of-set-eax
    xr-of-set-ebx
    xr-of-set-ecx
    xr-of-set-edx
    xr-of-set-esp
    xr-of-set-ebp
    xr-of-set-rax-high
    xr-of-set-rbx-high
    xr-of-set-rcx-high
    xr-of-set-rdx-high
    xr-of-set-rsp-high
    xr-of-set-rbp-high


;    xr-of-set-esp-same ;todo hack
    ;; xr-of-esp-and-set-eax
    ;; xr-of-esp-and-set-ebx
    ;; xr-of-esp-and-set-ecx
    ;; xr-of-esp-and-set-edx
    ;; xr-of-esp-and-set-ebp

    set-eax-of-set-eax
    set-ebx-of-set-ebx
    set-ecx-of-set-ecx
    set-edx-of-set-edx
    set-esp-of-set-esp
    set-ebp-of-set-ebp
    set-rax-high-of-set-rax-high
    set-rbx-high-of-set-rbx-high
    set-rcx-high-of-set-rcx-high
    set-rdx-high-of-set-rdx-high
    set-rsp-high-of-set-rsp-high
    set-rbp-high-of-set-rbp-high

    segment-is-32-bitsp-of-if
    esp-of-if
    xr-of-if

    eax-of-xw
    ebx-of-xw
    ecx-of-xw
    edx-of-xw
    esp-of-xw
    ebp-of-xw

    bvplus-of-constant-and-esp-when-overflow ; caused loops with turning + into bvplus
    ;;acl2::bvplus-of-constant-when-overflow ;move?  targets things like (BVPLUS 32 4294967280 (ESP X86))

    ;; Reading/writing registers (or parts of registers). These rules put in xr, which then becomes eax.  TODO: Go directly
    rgfi-size$inline ;dispatches to rr08, etc.
    rr08$inline ; exposes rgfi
    rr16$inline ; exposes rgfi
    rr32$inline ; exposes rgfi
    rr64$inline ; exposes rgfi
    rgfi rgfi$a ;exposes xr ; todo: go directly to the right reader

    !rgfi-size$inline ; dispatches to wr08, etc.
    wr08$inline ; exposes !rgfi
    wr16$inline ; exposes !rgfi
    wr32$inline ; exposes !rgfi
    wr64$inline ; exposes !rgfi
    !rgfi !rgfi$a ;exposes xw ; todo: go directly to the right writer

    mv-nth-1-of-wme-size     ;introduces write-to-segment ; rename!

    )
  (new-memory-rules32)))

(defund unroller-rules32 ()
  (declare (xargs :guard t))
  (append (lifter-rules32)
          (new-normal-form-rules-common)
          (new-normal-form-rules32)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Used by the unroller (new normal forms) and loop-lifter (old normal forms).
(defund lifter-rules64 ()
  (declare (xargs :guard t))
  (append (lifter-rules-common)
          (if-lowering-rules64)
          ;; read and write are used by the 64-bit lifter only (well, low-level 32-bit lifting also uses them):
          (linear-memory-rules) ; these introduce read and write
          (read-rules)
          (write-rules)
          (read-and-write-rules)
          (segment-base-and-bounds-rules-64)
          '(read-byte-becomes-read ; (read-byte-rules) ; read-byte can come from read-bytes
            len-of-read-bytes nth-of-read-bytes ; read-bytes can come from an output-extractor
            acl2::integerp-of-+ ; helps with nth-of-read-bytes
            )
          (get-prefixes-rules64)
          (step-opener-rules64)
          '(;; todo move these to the new-normal-form lists:
            ;; instruction pointer:
            x86isa::read-*ip-when-64-bit-modep ; goes to rip
            ;; x86isa::mv-nth-0-of-add-to-*ip-when-64-bit-modep ; subsumed by add-to-*ip-of-*64-bit-mode*
            ;; x86isa::mv-nth-1-of-add-to-*ip-when-64-bit-modep ; subsumed by add-to-*ip-of-*64-bit-mode*
            x86isa::write-*ip-when-64-bit-modep ; goes to !rip -- todo: go to set-rip
            x86isa::add-to-*ip-of-*64-bit-mode*

            ;; stack pointer:
            x86isa::read-*sp-when-64-bit-modep ; puts in rgfi -- todo: go to rsp
            x86isa::write-*sp-when-64-bit-modep ; puts in !rgfi -- todo: go to set-rsp
            ;; todo: combine these:
            x86isa::mv-nth-0-of-add-to-*sp-when-64-bit-modep
            x86isa::mv-nth-1-of-add-to-*sp-when-64-bit-modep)))

(defund new-normal-form-rules64 ()
  (declare (xargs :guard t))
  '(;; these target xr-of-rgf and introduce RAX, etc:
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

    signed-byte-p-64-of-rax
    signed-byte-p-64-of-rbx
    signed-byte-p-64-of-rcx
    signed-byte-p-64-of-rdx
    signed-byte-p-64-of-rsi
    signed-byte-p-64-of-rdi
    signed-byte-p-64-of-r8
    signed-byte-p-64-of-r9
    signed-byte-p-64-of-r10
    signed-byte-p-64-of-r11
    signed-byte-p-64-of-r12
    signed-byte-p-64-of-r13
    signed-byte-p-64-of-r14
    signed-byte-p-64-of-r15
    signed-byte-p-64-of-rsp
    signed-byte-p-64-of-rbp

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
    integerp-of-rsp-gen ; integerp-of-rsp
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

    ;; Rules about rip/set-rip:
    xr-becomes-rip ; introduces rip
    !rip-becomes-set-rip
    xw-becomes-set-rip

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
    rip-of-xw-irrel
    rip-of-write ; todo: more
    rip-of-set-flag

    ;; read of write, same register
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

    ;; undef-of-write-byte ; todo: does write-byte actually get introduced?

    ;; mxcsr-of-write-byte

    ;; ms-of-write-byte

;    fault-of-write-byte ; todo: move?

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

    ;; read-byte-of-set-rip ; now we just go to read
    ;; read-byte-of-set-rax
    ;; read-byte-of-set-rbx
    ;; read-byte-of-set-rcx
    ;; read-byte-of-set-rdx
    ;; read-byte-of-set-rsi
    ;; read-byte-of-set-rdi
    ;; read-byte-of-set-r8
    ;; read-byte-of-set-r9
    ;; read-byte-of-set-r10
    ;; read-byte-of-set-r11
    ;; read-byte-of-set-r12
    ;; read-byte-of-set-r13
    ;; read-byte-of-set-r14
    ;; read-byte-of-set-r15
    ;; read-byte-of-set-rsp
    ;; read-byte-of-set-rbp
    ;; read-byte-of-set-undef
    ;; read-byte-of-set-mxcsr

    read-chunks-of-set-rip
    read-chunks-of-set-rax
    read-chunks-of-set-rbx
    read-chunks-of-set-rcx
    read-chunks-of-set-rdx
    read-chunks-of-set-rsi
    read-chunks-of-set-rdi
    read-chunks-of-set-r8
    read-chunks-of-set-r9
    read-chunks-of-set-r10
    read-chunks-of-set-r11
    read-chunks-of-set-r12
    read-chunks-of-set-r13
    read-chunks-of-set-r14
    read-chunks-of-set-r15
    read-chunks-of-set-rsp
    read-chunks-of-set-rbp

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
    rax-of-set-mxcsr
    rax-of-set-flag

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
    rbx-of-set-mxcsr
    rbx-of-set-flag

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
    rcx-of-set-mxcsr
    rcx-of-set-flag

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
    rdx-of-set-mxcsr
    rdx-of-set-flag

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
    rsi-of-set-mxcsr
    rsi-of-set-flag

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
    rdi-of-set-mxcsr
    rdi-of-set-flag

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
    r8-of-set-mxcsr
    r8-of-set-flag

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
    r9-of-set-mxcsr
    r9-of-set-flag

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
    r10-of-set-mxcsr
    r10-of-set-flag

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
    r11-of-set-mxcsr
    r11-of-set-flag

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
    r12-of-set-mxcsr
    r12-of-set-flag

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
    r13-of-set-mxcsr
    r13-of-set-flag

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
    r14-of-set-mxcsr
    r14-of-set-flag

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
    r15-of-set-mxcsr
    r15-of-set-flag

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
    rsp-of-set-mxcsr
    rsp-of-set-flag

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
    rbp-of-set-mxcsr
    rbp-of-set-flag

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

    mxcsr-of-set-rax
    mxcsr-of-set-rbx
    mxcsr-of-set-rcx
    mxcsr-of-set-rdx
    mxcsr-of-set-rdi
    mxcsr-of-set-r8
    mxcsr-of-set-r9
    mxcsr-of-set-r10
    mxcsr-of-set-r11
    mxcsr-of-set-r12
    mxcsr-of-set-r13
    mxcsr-of-set-r14
    mxcsr-of-set-r15
    mxcsr-of-set-rsi
    mxcsr-of-set-rsp
    mxcsr-of-set-rbp

    ms-of-set-rax
    ms-of-set-rbx
    ms-of-set-rcx
    ms-of-set-rdx
    ms-of-set-rdi
    ms-of-set-r8
    ms-of-set-r9
    ms-of-set-r10
    ms-of-set-r11
    ms-of-set-r12
    ms-of-set-r13
    ms-of-set-r14
    ms-of-set-r15
    ms-of-set-rsi
    ms-of-set-rsp
    ms-of-set-rbp

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

    fault-of-set-rip
    fault-of-set-rax
    fault-of-set-rbx
    fault-of-set-rcx
    fault-of-set-rdx
    fault-of-set-rdi
    fault-of-set-r8
    fault-of-set-r9
    fault-of-set-r10
    fault-of-set-r11
    fault-of-set-r12
    fault-of-set-r13
    fault-of-set-r14
    fault-of-set-r15
    fault-of-set-rsi
    fault-of-set-rsp
    fault-of-set-rbp

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
    ;; xw-becomes-set-error

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

    ;; rip-of-myif
    ;; rax-of-myif
    ;; rbx-of-myif
    ;; rcx-of-myif
    ;; rdx-of-myif
    ;; rsi-of-myif
    ;; rdi-of-myif
    ;; r8-of-myif
    ;; r9-of-myif
    ;; r10-of-myif
    ;; r11-of-myif
    ;; r12-of-myif
    ;; r13-of-myif
    ;; r14-of-myif
    ;; r15-of-myif
    ;; rsp-of-myif
    ;; rbp-of-myif

    rip-of-if
    rax-of-if
    rbx-of-if
    rcx-of-if
    rdx-of-if
    rsi-of-if
    rdi-of-if
    rsp-of-if
    rbp-of-if
    r8-of-if
    r9-of-if
    r10-of-if
    r11-of-if
    r12-of-if
    r13-of-if
    r14-of-if
    r15-of-if

    ;; set-rip-of-myif
    ;; set-rax-of-myif
    ;; set-rbx-of-myif
    ;; set-rcx-of-myif
    ;; set-rdx-of-myif
    ;; set-rsi-of-myif
    ;; set-rdi-of-myif
    ;; set-r8-of-myif
    ;; set-r9-of-myif
    ;; set-r10-of-myif ; todo: more?
    ;; set-rsp-of-myif
    ;; set-rbp-of-myif

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

;    write-byte-of-set-rip

    ;; bury set-undef deep in the term:
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

;    set-undef-of-write-byte

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

    ;; Write of read of the same register (state terms can differ):
    set-rax-of-rax-same-gen
    set-rbx-of-rbx-same-gen
    set-rcx-of-rcx-same-gen
    set-rdx-of-rdx-same-gen
    set-rdi-of-rdi-same-gen
    set-rsi-of-rsi-same-gen
    set-r8-of-r8-same-gen
    set-r9-of-r9-same-gen
    set-r10-of-r10-same-gen
    set-r11-of-r11-same-gen
    set-r12-of-r12-same-gen
    set-r13-of-r13-same-gen
    set-r14-of-r14-same-gen
    set-r15-of-r15-same-gen
    set-rsp-of-rsp-same-gen
    set-rbp-of-rbp-same-gen

    !rflags-of-set-rip
    !rflags-of-set-rax
    !rflags-of-set-rbx
    !rflags-of-set-rcx
    !rflags-of-set-rdx
    !rflags-of-set-rdi
    !rflags-of-set-rsi
    !rflags-of-set-r8
    !rflags-of-set-r9
    !rflags-of-set-r10
    !rflags-of-set-r11
    !rflags-of-set-r12
    !rflags-of-set-r13
    !rflags-of-set-r14
    !rflags-of-set-r15
    !rflags-of-set-rsp
    !rflags-of-set-rbp

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

    ;; ;; These help make failures more clear, by dropping irrelevant
    ;; ;; state writes inside rme-size (actually, we should now be pretty good at removing rme-size):
    ;; mv-nth-0-of-rme-size-of-set-rip
    ;; mv-nth-0-of-rme-size-of-set-rax
    ;; mv-nth-0-of-rme-size-of-set-rbx
    ;; mv-nth-0-of-rme-size-of-set-rcx
    ;; mv-nth-0-of-rme-size-of-set-rdx
    ;; mv-nth-0-of-rme-size-of-set-rsi
    ;; mv-nth-0-of-rme-size-of-set-rdi
    ;; mv-nth-0-of-rme-size-of-set-r8
    ;; mv-nth-0-of-rme-size-of-set-r9
    ;; mv-nth-0-of-rme-size-of-set-r10
    ;; mv-nth-0-of-rme-size-of-set-r11
    ;; mv-nth-0-of-rme-size-of-set-r12
    ;; mv-nth-0-of-rme-size-of-set-r13
    ;; mv-nth-0-of-rme-size-of-set-r14
    ;; mv-nth-0-of-rme-size-of-set-r15
    ;; mv-nth-0-of-rme-size-of-set-rsp
    ;; mv-nth-0-of-rme-size-of-set-rbp
    ;; mv-nth-0-of-rme-size-of-set-undef ; move?
    ;; mv-nth-0-of-rme-size-of-set-mxcsr ; move?

    ;; mv-nth-1-of-rme-size-of-set-rip
    ;; mv-nth-1-of-rme-size-of-set-rax
    ;; mv-nth-1-of-rme-size-of-set-rbx
    ;; mv-nth-1-of-rme-size-of-set-rcx
    ;; mv-nth-1-of-rme-size-of-set-rdx
    ;; mv-nth-1-of-rme-size-of-set-rsi
    ;; mv-nth-1-of-rme-size-of-set-rdi
    ;; mv-nth-1-of-rme-size-of-set-r8
    ;; mv-nth-1-of-rme-size-of-set-r9
    ;; mv-nth-1-of-rme-size-of-set-r10
    ;; mv-nth-1-of-rme-size-of-set-r11
    ;; mv-nth-1-of-rme-size-of-set-r12
    ;; mv-nth-1-of-rme-size-of-set-r13
    ;; mv-nth-1-of-rme-size-of-set-r14
    ;; mv-nth-1-of-rme-size-of-set-r15
    ;; mv-nth-1-of-rme-size-of-set-rsp
    ;; mv-nth-1-of-rme-size-of-set-rbp

    if-of-set-rip-and-set-rip-same

    ;; Reading/writing registers (or parts of registers).
    rgfi-size$inline ; dispatches to rr08, etc.
    ;; These 4 go directly to the appropriate accessor, e.g., rax:
    rr08-to-normal-form64
    rr16-to-normal-form64
    rr32-to-normal-form64
    rr64-to-normal-form64
    rgfi-becomes-rax
    rgfi-becomes-rbx
    rgfi-becomes-rcx
    rgfi-becomes-rdx
    rgfi-becomes-rsi
    rgfi-becomes-rdi
    rgfi-becomes-r8
    rgfi-becomes-r9
    rgfi-becomes-r10
    rgfi-becomes-r11
    rgfi-becomes-r12
    rgfi-becomes-r13
    rgfi-becomes-r14
    rgfi-becomes-r15
    rgfi-becomes-rsp
    rgfi-becomes-rbp

    !rgfi-size$inline ; dispatches to wr08, etc.
    ;; These 4 go directly to the appropriate functions, e.g., set-rax:
    wr08-to-normal-form64
    wr16-to-normal-form64
    wr32-to-normal-form64
    wr64-to-normal-form64
    !rgfi-becomes-set-rax
    !rgfi-becomes-set-rbx
    !rgfi-becomes-set-rcx
    !rgfi-becomes-set-rdx
    !rgfi-becomes-set-rsi
    !rgfi-becomes-set-rdi
    !rgfi-becomes-set-r8
    !rgfi-becomes-set-r9
    !rgfi-becomes-set-r10
    !rgfi-becomes-set-r11
    !rgfi-becomes-set-r12
    !rgfi-becomes-set-r13
    !rgfi-becomes-set-r14
    !rgfi-becomes-set-r15
    !rgfi-becomes-set-rsp
    !rgfi-becomes-set-rbp))

(defund unroller-rules64 ()
  (declare (xargs :guard t))
  (append (lifter-rules64)
          (new-normal-form-rules-common)
          (new-normal-form-rules64)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Try this rule first
(set-axe-rule-priority read-of-write-irrel -1) ; todo: also below

;; Wait to try these rules until the read is cleaned up by removing irrelevant inner writes/sets
(set-axe-rule-priority read-when-program-at 1)
;; these are no longer used:
;; (set-axe-rule-priority read-when-program-at-1-byte-simple 1)
;; (set-axe-rule-priority read-when-program-at-1-byte 1)
;; (set-axe-rule-priority read-when-program-at-2-bytes 2) ; try these after the 1-byte one just above
;; (set-axe-rule-priority read-when-program-at-4-bytes 2)
;; (set-axe-rule-priority read-when-program-at-8-bytes 2)


;; ;; These rules expand operations on effective addresses, exposing the
;; ;; underlying operations on linear addresses.
;; (defund low-level-rules-32 ()
;;     (declare (xargs :guard t))
;;   (append (linear-memory-rules)
;;           (read-rules)
;;           (write-rules)
;;           (read-and-write-rules)
;;           (read-and-write-rules-non-bv) ; todo: allow the bv version?
;;           '(rime08$inline
;;             rime16$inline
;;             rime32$inline
;;             rime64$inline
;;             rime-size$inline

;;             wime08$inline
;;             wime16$inline
;;             wime32$inline
;;             wime64$inline
;;             wime-size$inline

;;             rme08$inline
;;             rme16$inline
;;             rme32$inline
;;             rme48$inline
;;             rme64$inline
;;             rme80$inline
;;             rme128$inline
;;             rme256$inline
;;             rme-size$inline

;;             wme08$inline
;;             wme16$inline
;;             wme32$inline
;;             wme48$inline
;;             wme64$inline
;;             wme80$inline
;;             wme128$inline
;;             wme256$inline
;;             wme-size$inline

;;             ea-to-la$inline

;;             read-*ip$inline
;;             write-*ip$inline
;;             add-to-*ip$inline
;;             read-*sp$inline
;;             write-*sp$inline
;;             add-to-*sp$inline

;;             ;; x86isa::data-segment-descriptor-attributesbits->e$inline
;;             ;; x86isa::data-segment-descriptor-attributesbits->d/b$inline
;;             ;; x86isa::data-segment-descriptor-attributesbits->w$inline
;;             ;; x86isa::code-segment-descriptor-attributesbits->d$inline
;;             ;; x86isa::code-segment-descriptor-attributesbits->r$inline
;;             ;; x86isa::data-segment-descriptor-attributesbits-fix
;;             ;; x86isa::code-segment-descriptor-attributesbits-fix

;;             ;x86isa::rflagsbits->res1$inline
;;             ;x86isa::rflagsbits->res2$inline

;;             ;; todo: there are multiple copies of this chunk:
;;             ;; Reading/writing registers (or parts of registers).  we leave
;;             ;; these enabled to expose rgfi and !rgfi, which then get rewritten
;;             ;; to xr and xw.  shilpi seems to do the same.
;;             rgfi-size$inline ;dispatches to rr08, etc.
;;             rr08$inline ; exposes rgfi
;;             rr16$inline ; exposes rgfi
;;             rr32$inline ; exposes rgfi
;;             rr64$inline ; exposes rgfi
;;             rgfi rgfi$a ;exposes xr ; todo: go directly to the right reader

;;             !rgfi-size$inline ; dispatches to wr08, etc.
;;             wr08$inline ; exposes !rgfi
;;             wr16$inline ; exposes !rgfi
;;             wr32$inline ; exposes !rgfi
;;             wr64$inline ; exposes !rgfi
;;             !rgfi !rgfi$a ;exposes xw ; todo: go directly to the right writer

;;             )))

;; some commonly monitored stuff:
;;   :monitor (acl2::get-prefixes-opener-lemma-no-prefix-byte-conjunct-1 ;todo: handle multi-conjunct rules better
;;             acl2::get-prefixes-opener-lemma-no-prefix-byte-conjunct-2
;; ;            rb-in-terms-of-nth-and-pos-eric-gen
;;             rb-returns-no-error-app-view
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
;;  ( mv-nth-1-of-add-to-*sp-positive-offset
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
;; ;;             ;;read-when-equal-of-read
;; ;;             ;;read-when-equal-of-read-alt
;; ;;             ;read-when-program-at
;; ;;             ;read-of-write-when-separate
;; ;;             ;read-of-write-irrel
;; ;; ;acl2::<-becomes-bvlt-axe-bind-free-and-bind-free
;; ;; ;            read-byte-from-segment-when-code-segment-assumptions32
;; ;;  ;           mv-nth-1-of-add-to-*sp
;; ;;   ;          not-mv-nth-0-of-add-to-*sp
;; ;;             ;x86isa::write-*sp-when-not-64-bit-modep-gen
;; ;;             read-*ip-becomes-eip-gen
;; ;;             code-segment-assumptions32-of-write-to-segment-of-ss
;;             )

(defund debug-rules-common ()
  (declare (xargs :guard t))
  '(run-until-stack-shorter-than-opener
    not-mv-nth-0-of-wme-size ;gets rid of error branch
    mv-nth-1-of-wme-size     ;introduces write-to-segment
    ;; mv-nth-1-of-rb-becomes-read
    ;; mv-nth-1-of-rb-1-becomes-read
    wb-becomes-write-when-app-view
    ))

(defund debug-rules32 ()
  (declare (xargs :guard t))
  (append (debug-rules-common)
          (step-opener-rules32)
          '(not-mv-nth-0-of-add-to-*sp-gen
            mv-nth-1-of-add-to-*sp-gen
            )))

(defund debug-rules64 ()
  (declare (xargs :guard t))
  (append (debug-rules-common)
          (step-opener-rules64)
          (get-prefixes-openers)
          ;; todo: flesh out this list:
          '(x86isa::rme-size-when-64-bit-modep-and-not-fs/gs-strong
            x86isa::wme-size-when-64-bit-modep-and-not-fs/gs-strong
            ;; could consider things like these:
            ;; READ-OF-WRITE-WHEN-SEPARATE
            )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Push many of these tester rules back into more fundamental rule sets

;; these are used both for lifting and proving
(defund extra-tester-rules ()
  (declare (xargs :guard t))
  '(acl2::integerp-of-expt
    acl2::integerp-of-*                 ; for array index calcs
    acl2::my-integerp-<-non-integerp    ; for array index calcs
    acl2::bvsx-when-bvlt
    ;; x86isa::canonical-address-p-between-special5 ; todo: move these
    ;; x86isa::canonical-address-p-between-special5-alt
    ;; x86isa::canonical-address-p-between-special6
    ;; x86isa::canonical-address-p-between-special7
    bitops::ash-is-expt-*-x
    acl2::natp-of-*
    acl2::<-of-constant-and-+-of-constant ; for address calcs
    acl2::<-of-15-and-*-of-4
    acl2::unsigned-byte-p-2-of-bvchop-when-bvlt-of-4
    acl2::not-bvlt-of-max-arg2
    acl2::<-of-*-when-constant-integers
            ;separate-when-separate-2 ; todo: drop? but that caused problems
    acl2::collect-constants-over-<-2
    acl2::commutativity-of-*-when-constant
    acl2::<-of-*-of-constant-and-constant
    acl2::rationalp-when-integerp
    acl2::+-of-+-of---same
    acl2::<-of-minus-and-constant ; ensure needed
    acl2::acl2-numberp-of--
    acl2::acl2-numberp-of-*
    bitops::ash-of-0-c ; at least for now
    ;;rflagsbits->af-of-myif
    ;;rflagsbits->af-of-if

    ;; acl2::equal-of-constant-and-bvuminus
    ;; acl2::bvor-of-myif-arg2 ; introduces bvif (myif can arise from expanding a shift into cases)
    ;; acl2::bvor-of-myif-arg3 ; introduces bvif (myif can arise from expanding a shift into cases)
    ;; acl2::bvif-of-myif-arg3 ; introduces bvif
    ;; acl2::bvif-of-myif-arg4 ; introduces bvif
    ;; help to show that divisions don't overflow or underflow:
    acl2::not-sbvlt-of-constant-and-sbvdiv-32-64
    acl2::not-sbvlt-of-sbvdiv-and-minus-constant-32-64
    acl2::not-bvlt-of-constant-and-bvdiv-64-128
    acl2::not-bvlt-of-constant-and-bvdiv-32-64
    acl2::slice-of-bvsx-high ; move back, but this introduces repeatbit
    acl2::bvcat-of-repeatbit-of-getbit-of-bvsx-same
    acl2::not-sbvlt-of-bvsx-of-constant-arg2-64-8
    acl2::not-sbvlt-of-bvsx-of-constant-arg2-64-16
    acl2::not-sbvlt-of-bvsx-of-constant-arg2-64-32
    acl2::not-sbvlt-of-bvsx-of-constant-arg2-128-64
    acl2::not-sbvlt-of-bvsx-of-constant-arg3-64-8
    acl2::not-sbvlt-of-bvsx-of-constant-arg3-64-16
    acl2::not-sbvlt-of-bvsx-of-constant-arg3-64-32
    acl2::not-sbvlt-of-bvsx-of-constant-arg3-128-64
    acl2::floor-of-1-when-integerp ; simplified something that showed up in an error case?
    unicity-of-1 ; simplified something that showed up in an error case
    acl2::bvcat-of-repeatbit-of-getbit-becomes-bvsx
    acl2::bvcat-of-repeatbit-tighten-64-32 ;gen!
    acl2::bvlt-of-bvsx-arg2
    acl2::sbvlt-of-bvsx-32-16-constant
    acl2::sbvlt-false-when-sbvlt-gen ; did nothing?
    acl2::if-of-sbvlt-and-not-sbvlt-helper
    if-of-set-flag-and-set-flag
    xr-of-!rflags-irrel ; todo: better normal form?

    acl2::logext-of-+-of-bvplus-same-size
    acl2::logext-of-+-of-+-of-mult-same-size
            ;acl2::minus-cancellation-on-right ; todo: use an arithmetic-light rule
    acl2::bvchop-of-nth-becomes-bv-array-read2 ; needed for stp to see the array op
    acl2::bv-array-read-of-*-arg3 ; introduces bvmult for the index
    acl2::bv-array-read-of-+-arg3 ; introduces bvplus for the index
    acl2::nth-becomes-bv-array-read-strong2
    acl2::bvplus-of-*-arg1 ; introduces bvmult
    acl2::bvplus-of-*-arg2 ; introduces bvmult -- todo: alt version?
    not-equal-of-+-and-+-when-separate
    not-equal-of-+-of-+-and-+-when-separate
    not-equal-of-+-of-+-and-+-when-separate-gen
    acl2::<-of-negative-constant-and-bv
    ;;read-1-of-write-1-both
    acl2::not-bvlt-of-constant-when-usb-dag ; rename
    ;; separate-of-1-and-1 ; do we ever need this?
    acl2::equal-of-bvshl-and-constant ; move to core-rules-bv?
    ;; acl2::equal-of-myif-arg1-safe
    ;; acl2::equal-of-myif-arg2-safe
    acl2::bvminus-of-bvplus-and-bvplus-same-2-2
    acl2::bvplus-of-unary-minus
    acl2::bvplus-of-unary-minus-arg2
    acl2::if-becomes-bvif-1-axe
    ;; acl2::boolif-of-t-and-nil-when-booleanp
    acl2::slice-of-bvand-of-constant
    ;; acl2::myif-becomes-boolif-axe ; since stp translation supports disjuncts that are calls to boolif but not if.
    acl2::if-becomes-boolif-axe ; since stp translation supports disjuncts that are calls to boolif but not if. ; todo: get this to work
    acl2::equal-of-bvplus-constant-and-constant
    acl2::equal-of-bvplus-constant-and-constant-alt
    acl2::bvchop-of-bvshr-same
    acl2::getbit-of-lognot ; todo: handle all cases of logops inside bvops
    acl2::bvif-of-if-constants-nil-nonnil
    acl2::bvif-of-if-constants-nonnil-nil
    acl2::equal-of-constant-and-bitand
    acl2::equal-of-bitand-and-constant
            ;acl2::boolif-of-nil-and-t
    ;; acl2::booleanp-of-myif ; or convert myif to boolif when needed
    acl2::bitxor-of-1-becomes-bitnot-arg1 ; not in core-rules-bv since we have special handling of bitxor nests for crypto code
    acl2::bitxor-of-1-becomes-bitnot-arg2 ; not in core-rules-bv since we have special handling of bitxor nests for crypto code
    ;; these next few did seem needed after lifting (todo: either add the rest like this or drop these):
    booleanp-of-jp-condition
    booleanp-of-jnp-condition
    booleanp-of-jz-condition
    booleanp-of-jnz-condition
    acl2::getbit-0-of-bool-to-bit
    acl2::equal-of-bool-to-bit-and-0 ; alt version needed, or do equals get turned around?
    acl2::equal-of-bool-to-bit-and-1 ; alt version needed, or do equals get turned around?
    acl2::equal-of-1-and-bitnot ; todo: add 0 version
    ;;acl2::bvif-of-1-and-0-becomes-bool-to-bit ; introduces bool-to-bit?  maybe bad.
    ;; todo: just include boolean-rules?:
    ;; acl2::bvmult-tighten-when-power-of-2p-axe ; todo: uncomment
    acl2::bvchop-of-bool-to-bit ;todo: drop
    acl2::logext-of-bool-to-bit
    acl2::<-of-if-arg1-safe
    ;; acl2::<-of-if-arg2-safe
    acl2::equal-of-bvif-safe2
    acl2::unsigned-byte-p-of-+-becomes-unsigned-byte-p-of-bvplus-axe ; needed?
    ))

;; beyond what def-unrolled uses
(defund extra-tester-lifting-rules ()
  (declare (xargs :guard t))
  (append ;(new-normal-form-rules64) ; todo: drop?  but that caused failures! why?  seemed to involve equality of addresses and separation hyps
          (extra-tester-rules)
          '(<-of-fp-to-rat ; do we want this?

            !rflags-of-if-arg1 ; do we want this?
            !rflags-of-if-arg2
            ;;xr-of-!rflags-irrel
            acl2::if-x-x-y-when-booleanp
            ;; acl2::if-of-t-and-nil-when-booleanp
            acl2::equal-of-if-arg1-when-quotep
            acl2::equal-of-if-arg2-when-quotep
            sse-cmp-special ; scary
            acl2::bvchop-of-if
            acl2::ifix-of-if

            ;; move all of these:
            ;acl2::integerp-of-bvplus ;todo: more
            ;acl2::integerp-of-bvchop

            ;zf-spec$inline     ; needed for unsigned_add_associates -- but does this ruin rules about jle-condition? zf-spec seems to be used in more things that just the conditional branches?

            ;x86isa::sub-zf-spec32-same ; this can mess up the condition rules...
            ;x86isa::if-of-sub-zf-spec32-arg2
            ;;stuff related to flags changes:

            ;acl2::logand-of-1-becomes-getbit-arg2 ;move
            of-spec-of-logext-32
            acl2::unsigned-byte-p-of-if
            ;acl2::unsigned-byte-p-of-bvplus ;todo: more
            ;; acl2::bvchop-of-myif
            xr-of-if ;restrict?
            ;acl2::slice-out-of-order

            ;acl2::bvcat-of-0-arg2
            acl2::bvmod-tighten-64-32
            acl2::bvdiv-tighten-64-32
            acl2::not-bvlt-of-max-when-unsiged-byte-p
            ;x86isa::sf-spec32-rewrite ; trying without...
            ;jle-condition-rewrite-1-with-bvif ; this one works on bvif
            ;jle-condition-rewrite-1-with-bvif-and-bvchop
            ;jle-condition-rewrite-1-with-bvchop
            ;; jnl-condition-of-getbit-31-and-0
            ;;jnl-condition-rewrite-16
            ;;jnl-condition-rewrite-16b
            ; acl2::bvchop-of-logext-becomes-bvsx ; needed for jnl-condition-rewrite-16
            ;acl2::bvsx-when-sizes-match
            ;acl2::bvchop-of-bvchop
            ;acl2::bvplus-of-bvchop-arg2
            ;acl2::sbvlt-of-bvchop-arg2
            ;acl2::bvuminus-of-bvuminus
            ;acl2::bvplus-of-bvuminus-same
            acl2::bvchop-numeric-bound
            ;;acl2::bvuminus-of-bvsx-low ; todo: other cases? todo: push back
            sf-spec64-of-bvchop-64
            of-spec64-of-logext-64
            acl2::sbvlt-of-bvsx-arg2

            ;; sse-cmp ;todo: limit?
            ;; feature-flag-sse-of-xw
            ;; feature-flag-sse-of-write
            ;; feature-flag-sse-of-set-flag
            ;; feature-flag-sse2-of-xw
            ;; feature-flag-sse2-of-write
            ;; feature-flag-sse2-of-set-flag
            acl2::equal-of-if-constants
            ;; acl2::bvlt-of-bvplus-1-cancel-alt ; optional
            ;x86isa::idiv-spec-32 ; trying
            acl2::bvchop-when-size-is-not-posp ; move?

            acl2::bvcat-of-if-arg2 ; these just lift the if
            acl2::bvcat-of-if-arg4
            ;;acl2::bvif-of-0-arg1
            ;acl2::bvplus-when-size-is-not-positive ; todo: more like this, make a rule-list

            acl2::bvcat-of-slice-of-bvsx-same
            acl2::not-sbvlt-64-of-sbvdiv-64-of-bvsx-64-32-and--2147483648
            acl2::not-sbvlt-64-of-2147483647-and-sbvdiv-64-of-bvsx-64-32
            acl2::bvplus-commutative-increasing-axe ; do we really want this?
            acl2::bvplus-commutative-2-increasing-axe ; do we really want this?
            ;;acl2::equal-same
            ;; bvcat-of-minus-becomes-bvshl ; except stp doesn't support the shift operators
            ;acl2::<-lemma-for-known-operators-axe
            ;acl2::bvlt-of-bvchop-arg2
            ;acl2::bvlt-of-bvchop-arg3
            ;acl2::sbvlt-of-bvchop-arg2
            ;acl2::sbvlt-of-bvchop-arg3
            ;acl2::bvand-of-bvchop-1 ;rename
            ;acl2::bvand-of-bvchop-2 ;rename
            acl2::bvchop-of-minus-becomes-bvuminus ; todo: or re-characterize the subl instruction
            acl2::bvplus-of-+-arg2 ; todo: drop once we characterize long negation?
            acl2::bvplus-of-+-arg3 ; todo: drop once we characterize long negation?
            ;acl2::integerp-when-unsigned-byte-p-free ; needed for the bvplus-of-+ rules.
            acl2::natp-of-+-of-- ; trying, or simplify (natp (binary-+ '32 (unary-- (bvchop '5 x))))
            min ; why is min arising?  or add min-same
            acl2::<-becomes-bvlt-axe-bind-free-arg1-strong
            acl2::<-becomes-bvlt-dag-gen-better2
            ;; after adding core-rules-bv:
            acl2::bvlt-tighten-bind-and-bind-dag
            ;;acl2::unsigned-byte-p-of-0-arg1 ; move to a more fundamental rule list
            ;; acl2::boolif-x-x-y-becomes-boolor ; introduces boolor
            acl2::boolor-becomes-boolif
            ;; acl2::bvlt-hack-1-gen
            acl2::bvchop-subst-constant ; move
            acl2::bvchop-subst-constant-alt ; move
            acl2::boolif-of-bvlt-strengthen-to-equal
            acl2::bvlt-reduce-when-not-equal-one-less
            ;read-1-of-write-4
            ;read-1-of-write-1-both ; can make things, like failure to resolve rip, hard to debug
            ;read-1-of-write-within-new
            not-equal-of-+-when-separate
            not-equal-of-+-when-separate-alt
            x86isa::canonical-address-p-of-sum-when-unsigned-byte-p-32
            )))

(defund tester-proof-rules ()
  (declare (xargs :guard t))
  (append '(;;myif-of-sub-zf-spec32-arg2
            ;;myif-of-sub-zf-spec32-arg3
            equal-of-sub-zf-spec32-and-1
            equal-of-1-and-sub-zf-spec32
            acl2::equal-of-if-constants
            ;; acl2::if-becomes-myif ; todo: do we want this when lifting?
            ;; acl2::myif-becomes-bvif-1-axe
            ;; acl2::bvchop-of-myif
            acl2::integerp-of---when-integerp
            acl2::equal-of-bvplus-move-bvminus-better
            acl2::equal-of-bvplus-move-bvminus-alt-better
            acl2::bvplus-commutative-increasing-axe
            ;acl2::bvchop-of-bvmod ; just use bvchop-identity-axe
            acl2::bvuminus-of-bvif-constants
            acl2::equal-of-bvif ;restrict to constant x?
            acl2::equal-of-bvif-alt ;restrict to constant x?
            ;; just include boolean-rules?
            acl2::boolif-when-quotep-arg2
            acl2::boolif-when-quotep-arg3
            acl2::bvchop-of-bvuminus-same
            acl2::signed-byte-p-of-bvif
            acl2::logext-identity
            acl2::signed-byte-p-when-unsigned-byte-p-one-less
            ;acl2::boolif-x-x-y-becomes-boolor ; introduces boolor
            acl2::boolor-becomes-boolif
            ;acl2::bvlt-hack-1-gen
            acl2::bvchop-subst-constant
            acl2::bvchop-subst-constant-alt
            acl2::boolif-of-bvlt-strengthen-to-equal
            acl2::bvlt-reduce-when-not-equal-one-less
            bool->bit$inline ; from sub-cf-spec8, etc. (todo: go to bool-to-bit)
            ;; If any of these survive to the proof stage, we should probably open them up:
            js-condition
            jns-condition
            jo-condition
            jno-condition
            jb-condition
            jnb-condition
            jbe-condition
            jnbe-condition
            jl-condition
            jnl-condition
            jle-condition
            jnle-condition
            jp-condition
            jnp-condition
            jz-condition
            jnz-condition
            ;; todo: it would be good to turn these into BVs earlier, during symbolic execution when not passed to rflags
            ;; todo: need rules like these for all the sub-xxx functions too
            add-af-spec8-becomes-bvlt
            add-af-spec16-becomes-bvlt
            add-af-spec32-becomes-bvlt
            add-af-spec64-becomes-bvlt
            adc-af-spec8-becomes-bvlt
            adc-af-spec16-becomes-bvlt
            adc-af-spec32-becomes-bvlt
            adc-af-spec64-becomes-bvlt
            sub-af-spec8-becomes-bvlt
            sub-af-spec16-becomes-bvlt
            sub-af-spec32-becomes-bvlt
            sub-af-spec64-becomes-bvlt
            sbb-af-spec8-becomes-bvlt
            sbb-af-spec16-becomes-bvlt
            sbb-af-spec32-becomes-bvlt
            sbb-af-spec64-becomes-bvlt
            cf-spec8-becomes-getbit  ; cf-spec8$inline
            cf-spec16-becomes-getbit ; cf-spec16$inline
            cf-spec32-becomes-getbit ; cf-spec32$inline
            cf-spec64-becomes-getbit ; cf-spec64$inline
            pf-spec8$inline ; these expose logcount, which logcount-opener-8 then opens
            pf-spec16$inline
            pf-spec32$inline
            pf-spec64$inline
            logcount-opener-8 ; improve?
            sf-spec8-becomes-getbit
            sf-spec16-becomes-getbit
            sf-spec32-becomes-getbit
            sf-spec64-becomes-getbit
            zf-spec$inline
            ;;sub-af-spec8$inline
            x86isa::sub-cf-spec8-opener
            sub-of-spec8
            sub-pf-spec8
            sub-sf-spec8
            sub-zf-spec8
            ;;sub-af-spec16$inline
            x86isa::sub-cf-spec16-opener
            sub-of-spec16
            sub-pf-spec16
            sub-sf-spec16
            sub-zf-spec16
            ;;sub-af-spec32$inline
            x86isa::sub-cf-spec32-opener
            sub-of-spec32
            sub-pf-spec32
            sub-sf-spec32
            sub-zf-spec32
            ;;sub-af-spec64$inline
            x86isa::sub-cf-spec64-opener
            sub-of-spec64
            sub-pf-spec64
            sub-sf-spec64
            sub-zf-spec64
            ;; todo: how to open the other flags, like pf, to bv notions?
            acl2::signed-byte-p-of-+-becomes-bv-claim ; todo: can't include during symbolic execution?
            acl2::signed-byte-p-of-+-of---becomes-bv-claim
            acl2::bvplus-convert-arg2-to-bv-axe ; would like to do this earlier, but it might cause problems
            acl2::bvplus-convert-arg3-to-bv-axe
            acl2::slice-convert-arg3-to-bv-axe
            !rflagsbits->af-opener ; todo: open before proof stage?
            !rflagsbits->cf-opener
            !rflagsbits->of-opener
            !rflagsbits->pf-opener
            !rflagsbits->sf-opener
            !rflagsbits->zf-opener
            !rflagsbits->res1-opener
            !rflagsbits->res2-opener
            !rflagsbits->res3-opener)
          ;; todo: this stuff is duplicated in the lifter-rules:
          *unsigned-choppers* ;; these are just logead, aka bvchop
          *signed-choppers* ;; these are just logext
          *unsigned-recognizers* ;; these are just unsigned-byte-p
          *signed-recognizers* ;; these are just signed-byte-p
          ;; These are just logext: ; todo: more!
          '(x86isa::n08-to-i08$inline
            x86isa::n16-to-i16$inline
            x86isa::n32-to-i32$inline
            x86isa::n64-to-i64$inline
            x86isa::n128-to-i128$inline
            x86isa::n256-to-i256$inline
            x86isa::n512-to-i512$inline)
          (logops-to-bv-rules)

          (x86-type-rules) ; since some of these functions may survive to the proof stage
          (separate-rules) ; i am seeing some read-over-write reasoning persist into the proof stage
          (float-rules) ; i need booleanp-of-isnan, at least
          (extra-tester-rules)
          (acl2::convert-to-bv-rules) ; turns things like logxor into things like bvxor
          (acl2::booleanp-rules)
          (acl2::boolean-rules-safe)
          (acl2::type-rules)
          (new-normal-form-rules64) ; overkill?
          (acl2::base-rules)
          (acl2::core-rules-bv) ; trying
          (acl2::bv-of-logext-rules)
          (acl2::unsigned-byte-p-rules)
          (acl2::array-reduction-rules)
          (acl2::trim-rules) ; these seem needed for a few examples, like getting tea-wiki-elf64 by rewriting
          ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Usually not needed except for in the loop lifter (showing that assumptions are preserved):
(defund program-at-rules ()
  (declare (xargs :guard t))
  '(program-at-of-write
    x86isa::program-at-of-if
    program-at-of-set-flag ; may not be needed, since the corresponding read ignores set-flag and the program-at claim will only be on the initial state
    program-at-of-set-undef ; do we not need something like this?
    program-at-of-set-mxcsr
    ))

(defund extra-loop-lifter-rules ()
  (declare (xargs :guard t))
  (append ;or put these in symbolic-execution-rules-loop ?:
   '(stack-height-increased-wrt
     stack-height-decreased-wrt
     get-pc
     acl2::memberp-of-cons-irrel-strong
     acl2::memberp-of-cons-same
     acl2::memberp-of-nil
;     acl2::member-equal-of-cons
     acl2::equal-of-same-cancel-4
     x86isa::logext-64-does-nothing-when-canonical-address-p
     x86isa::equal-of-if-constants
     x86isa::equal-of-if-constants-alt
     acl2::bool-fix-when-booleanp
     acl2::if-of-t-and-nil-becomes-bool-fix
     acl2::mv-nth-of-if
     x86isa::canonical-address-p-of-if
     x86isa::+-of-if-arg1
     x86isa::+-of-if-arg2
     acl2::bvchop-numeric-bound
     x86isa::xw-of-rip-and-if
     acl2::if-x-x-y-when-booleanp
     read-of-xw-irrel ; drop -- but is it elsewhere?
     read-bytes-of-xw-irrel
     read-bytes-of-set-flag ; todo: more like this, for other state changers
     read-bytes-of-!rflags
     read-bytes-of-set-rip
     read-bytes-of-set-undef
     read-bytes-of-set-mxcsr
     read-bytes-of-write-when-disjoint-regions48p
     read-bytes-of-write-when-disjoint-regions48p-alt
     mod-of-plus-reduce-constants
     ;; mv-nth-1-of-rb-becomes-read
     ;mv-nth-1-of-wb-becomes-write-when-app-view
     read-of-set-flag ; drop
     read-of-write-when-separate ; drop
     write-of-write-same ; drop
     ;; read-when-program-at-1-byte ; this is for resolving reads of the program.
     ;; read-when-program-at-4-bytes ; this is for resolving reads of the program.
     ;; read-when-program-at-2-bytes ; this is for resolving reads of the program.
     ;; read-when-program-at-8-bytes ; this is for resolving reads of the program.
     acl2::equal-of-same-cancel-4
     acl2::equal-of-same-cancel-3
     acl2::equal-of-bvplus-constant-and-constant
     acl2::equal-of-bvplus-constant-and-constant-alt
     acl2::mod-of-+-of-constant
     xr-of-if

     xw-of-xr-same-gen

     set-undef ; can be introduced by write-user-rflags-rewrite-better
     )
   (program-at-rules) ; to show that program-at assumptions still hold after the loop body
   (write-rules)
;(x86isa::lifter-rules)
   ))

;; For the loop lifter
;; todo: consider making a 32-bit variant (see above)
(defund symbolic-execution-rules-loop-lifter ()
  (declare (xargs :guard t))
  '(;;run-until-exit-segment-or-hit-loop-header-opener-1
    run-until-exit-segment-or-hit-loop-header-opener-2
    run-until-exit-segment-or-hit-loop-header-base-case-1
    run-until-exit-segment-or-hit-loop-header-base-case-2
    run-until-exit-segment-or-hit-loop-header-base-case-3
    ;; run-until-exit-segment-or-hit-loop-header-of-myif-split
    run-until-exit-segment-or-hit-loop-header-of-if-split
    run-until-exit-segment-or-hit-loop-header-of-if))

;; Eventually we may add these rules about read to extra-loop-lifter-rules.
(defund loop-lifter-invariant-preservation-rules ()
  (declare (xargs :guard t))
  (append (extra-loop-lifter-rules)
          '(;; mv-nth-1-of-rb-becomes-read
            ;; read-of-write-irrel
            read-of-write-when-disjoint-regions48p-gen
            read-of-write-when-disjoint-regions48p-gen-alt
            read-bytes-of-write-when-disjoint-regions48p-gen
            read-bytes-of-write-when-disjoint-regions48p-gen-alt
            read-of-write-same
            )))

;todo: add more?
(defund loop-lifter-state-component-extraction-rules ()
  (declare (xargs :guard t))
  '(acl2::integerp-of-+
    x86isa::x86-elem-fix
    x86isa::canonical-address-p-between-special1
    x86isa::xr-of-xw-diff
    x86isa::xr-of-xw-intra-field
    acl2::ifix-when-integerp
    x86isa::integerp-of-xr-rgf
    x86isa::logext-64-does-nothing-when-canonical-address-p
    xr-of-write-when-not-mem ; add 32-bit versions too?
    xr-of-set-flag
    xr-of-set-undef-irrel ; maybe this normal form is not used?
    xr-of-set-mxcsr-irrel ; maybe this normal form is not used?
    ))

;; These are for both 32 and 64 bit modes.
;; For the old normal form, we expose XR and XW.
(defund old-normal-form-rules ()
  (declare (xargs :guard t))
  '(fault fault$a ; exposes xr
    !fault !fault$a ; exposes xw
    ms ms$a ; exposes xr
    !ms !ms$a ; exposes xw
    mxcsr mxcsr$a ; exposes xr
    !mxcsr !mxcsr$a ; exposes xw
    undef undef$a ; exposes xr
    !undef !undef$a ; exposes xw
    ;; app-view ; not needed because we never change it?
    rip rip$a ; exposes xr
    !rip !rip$a ; exposes xw

    ;; Reading/writing registers (or parts of registers).  we leave
    ;; these enabled to expose rgfi and !rgfi, which then get rewritten
    ;; to xr and xw.
    rgfi-size$inline ;dispatches to rr08, etc.
    rr08$inline ; exposes rgfi
    rr16$inline ; exposes rgfi
    rr32$inline ; exposes rgfi
    rr64$inline ; exposes rgfi
    rgfi rgfi$a ;exposes xr

    !rgfi-size$inline ; dispatches to wr08, etc.
    wr08$inline ; exposes !rgfi
    wr16$inline ; exposes !rgfi
    wr32$inline ; exposes !rgfi
    wr64$inline ; exposes !rgfi
    !rgfi !rgfi$a ;exposes xw

    x86isa::xw-rgf-of-xr-rgf-same ; drop since we don't use this normal form?
    ))

;; Can't really use the new, nicer normal forms for readers and writers, since
;; the loop-lifter expects state terms built from XW, WRITE, and SET-FLAG.
(defund loop-lifter-rules32 ()
  (declare (xargs :guard t))
  (append (lifter-rules32)
          (old-normal-form-rules)))

;; Can't really use the new, nicer normal forms for readers and writers, since
;; the loop-lifter expects state terms built from XW, WRITE, and SET-FLAG.
(defund loop-lifter-rules64 ()
  (declare (xargs :guard t))
  (append (lifter-rules64)
          (old-normal-form-rules) ;;(new-normal-form-rules64); todo, but we'd have to change the loop-lifter significantly
          ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority set-flag-of-write -3)
(set-axe-rule-priority set-flag-of-set-flag-diff-axe -2)
(set-axe-rule-priority set-flag-of-set-rbp -1)
(set-axe-rule-priority set-flag-of-set-rip -1)
(set-axe-rule-priority set-flag-of-set-rsi -1)
(set-axe-rule-priority set-flag-of-set-rax -1)
(set-axe-rule-priority set-flag-of-set-rsp -1)

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority get-flag-of-set-flag -3)
(set-axe-rule-priority get-flag-of-write -2)
(set-axe-rule-priority get-flag-of-set-rbp -1)
(set-axe-rule-priority get-flag-of-set-rip -1)
(set-axe-rule-priority get-flag-of-set-rsi -1)
(set-axe-rule-priority get-flag-of-set-rax -1)
(set-axe-rule-priority get-flag-of-set-rsp -1)

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority 64-bit-modep-of-write -4)
(set-axe-rule-priority 64-bit-modep-of-set-flag -3)
(set-axe-rule-priority 64-bit-modep-of-set-rip -2)
(set-axe-rule-priority 64-bit-modep-of-set-rbp -1)
(set-axe-rule-priority 64-bit-modep-of-set-rsi -1)
(set-axe-rule-priority 64-bit-modep-of-set-rax -1)
(set-axe-rule-priority 64-bit-modep-of-set-rsp -1)

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority app-view-of-write -4)
(set-axe-rule-priority app-view-of-set-flag -3)
(set-axe-rule-priority app-view-of-set-rip -2)
(set-axe-rule-priority app-view-of-set-rbp -1)
(set-axe-rule-priority app-view-of-set-rsi -1)
(set-axe-rule-priority app-view-of-set-rax -1)
(set-axe-rule-priority app-view-of-set-rsp -1)

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority alignment-checking-enabled-p-of-write -4)
(set-axe-rule-priority alignment-checking-enabled-p-of-set-flag -3)
(set-axe-rule-priority alignment-checking-enabled-p-of-set-rip -2)
(set-axe-rule-priority alignment-checking-enabled-p-of-set-rbp -1)
(set-axe-rule-priority alignment-checking-enabled-p-of-set-rsi -1)
(set-axe-rule-priority alignment-checking-enabled-p-of-set-rax -1)
(set-axe-rule-priority alignment-checking-enabled-p-of-set-rsp -1)

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority x86p-of-write -4)
(set-axe-rule-priority x86p-of-set-flag -3)
(set-axe-rule-priority x86p-of-set-rip -2)
(set-axe-rule-priority x86p-of-set-rbp -1)
(set-axe-rule-priority x86p-of-set-rsi -1)
(set-axe-rule-priority x86p-of-set-rax -1)
(set-axe-rule-priority x86p-of-set-rsp -1)

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority read-of-set-rip -2)
(set-axe-rule-priority read-of-set-rbp -2)
(set-axe-rule-priority read-of-set-rsi -2)
(set-axe-rule-priority read-of-set-rax -2)
(set-axe-rule-priority read-of-set-rsp -2)
(set-axe-rule-priority read-of-write-same -1)
(set-axe-rule-priority read-of-write-irrel -1)
(set-axe-rule-priority read-of-write-irrel-bv-axe 1) ; try late, as this uses SMT, todo: add smt to name

;; Try last
(set-axe-rule-priority canonical-address-p-when-bvlt-of-bvplus-axe 1) ; todo: add smt to name

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority ms-of-write -4)
(set-axe-rule-priority ms-of-set-flag -3)
(set-axe-rule-priority ms-of-set-rip -2)
(set-axe-rule-priority ms-of-set-rbp -1)
(set-axe-rule-priority ms-of-set-rsi -1)
(set-axe-rule-priority ms-of-set-rax -1)
(set-axe-rule-priority ms-of-set-rsp -1)

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority fault-of-write -4)
(set-axe-rule-priority fault-of-set-flag -3)
(set-axe-rule-priority fault-of-set-rip -2)
(set-axe-rule-priority fault-of-set-rbp -1)
(set-axe-rule-priority fault-of-set-rsi -1)
(set-axe-rule-priority fault-of-set-rax -1)
(set-axe-rule-priority fault-of-set-rsp -1)

;; todo: add the rest
(set-axe-rule-priority rgfi-becomes-rbp -1)
(set-axe-rule-priority rgfi-becomes-rsp -1)
(set-axe-rule-priority rgfi-becomes-rax -1)
(set-axe-rule-priority rgfi-becomes-rbx -1)

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority program-at-of-write -4)
(set-axe-rule-priority program-at-of-set-flag -3)

;; Based on how commonly these rules were used in an example:
(set-axe-rule-priority xw-becomes-set-rip -4)
(set-axe-rule-priority xw-becomes-set-rax -4)

(set-axe-rule-priority !rip-becomes-set-rip -1) ; drop once this is only rule for 64-bit mode

(set-axe-rule-priority acl2::part-install-width-low-becomes-bvcat-32 1)
(set-axe-rule-priority acl2::part-install-width-low-becomes-bvcat-64 2)
(set-axe-rule-priority acl2::part-install-width-low-becomes-bvcat-128 3)
(set-axe-rule-priority acl2::part-install-width-low-becomes-bvcat-256 4)
(set-axe-rule-priority acl2::part-install-width-low-becomes-bvcat-512 5) ; try last

(set-axe-rule-priority riml08-becomes-read -1)

;; If these are present, we want them to be tried instead of opening the definition
(set-axe-rule-priority rml-size-of-1-becomes-read -1)
(set-axe-rule-priority rml-size-of-2-becomes-read -1)
(set-axe-rule-priority rml-size-of-4-becomes-read -1)
(set-axe-rule-priority rml-size-of-6-becomes-read -1)
(set-axe-rule-priority rml-size-of-8-becomes-read -1)
(set-axe-rule-priority rml-size-of-10-becomes-read -1)
(set-axe-rule-priority rml-size-of-16-becomes-read -1)
(set-axe-rule-priority rml-size-of-32-becomes-read -1)

;; If these are present, we want them to be tried instead of opening the definition
(set-axe-rule-priority riml-size-of-1-becomes-read -1)
(set-axe-rule-priority riml-size-of-2-becomes-read -1)
(set-axe-rule-priority riml-size-of-4-becomes-read -1)
(set-axe-rule-priority riml-size-of-8-becomes-read -1)

;; This may be the rule that is used the most
(set-axe-rule-priority acl2::mv-nth-of-cons-safe -1)

;; Delay under we've tried to resolve the read of write:
(set-axe-rule-priority read-of-write-becomes-read-of-write-of-clear-flags-extend-axe 1)
;; Remove the clear-flags-retract before we try to resolve the read-of-write
(set-axe-rule-priority read-of-write-of-clear-flags-retract -1)
