; A package for x86 proof work
;
; Copyright (C) 2017-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The "X" package, for doing proofs about x86 code.  We could improve the name
;; if we want, but "X86" is taken.

;(include-book "std/portcullis" :dir :system)
(include-book "projects/x86isa/portcullis/portcullis" :dir :system)
(include-book "rtl/rel11/portcullis" :dir :system)

;; A Package for x86 analysis tools and proofs

;; TODO: Add a bunch of x86 ISA stuff here
(defconst *x86isa-exports*
  '(x86isa::x86 ;the stobj name
    x86isa::memi$inline
    x86isa::memi
    x86isa::!memi
    x86isa::n48$inline
    x86isa::n48
    x86isa::app-view$inline
    x86isa::app-view
    x86isa::canonical-address-p$inline
    x86isa::canonical-address-p
    x86isa::xr
    x86isa::xw
    x86isa::rb
    x86isa::wb
    x86isa::rb-1
    x86isa::wb-1
    x86isa::x86p
    x86isa::rvm08 ;todo more like this
    x86isa::wvm08
    x86isa::flgi
    x86isa::!flgi
    x86isa::!flgi-undefined
    x86isa::separate
    x86isa::program-at
    x86isa::byte-listp ;todo: compare with unsigned-byte-p-list
    x86isa::memi*
    x86isa::gz
    x86isa::sz
    x86isa::alignment-checking-enabled-p
    x86isa::get-prefixes
    x86isa::!ms
    x86isa::!ms$inline
    x86isa::x86-fetch-decode-execute

    x86isa::64-bit-modep
    x86isa::*compatibility-mode*
    x86isa::*64-bit-mode*

    x86isa::rme-size
    x86isa::rme-size$inline

    x86isa::rml-size
    x86isa::rml-size$inline
    x86isa::rml08
    x86isa::rml16
    x86isa::rml32
    x86isa::rml48
    x86isa::rml64
    x86isa::rml80
    x86isa::rml128

    ;; registers (the order is odd but follows the numeric values):
    x86isa::*rax*
    x86isa::*rcx*
    x86isa::*rdx*
    x86isa::*rbx*
    x86isa::*rsp*
    x86isa::*rbp*
    x86isa::*rsi*
    x86isa::*rdi*
    x86isa::*r8*
    x86isa::*r9*
    x86isa::*r10*
    x86isa::*r11*
    x86isa::*r12*
    x86isa::*r13*
    x86isa::*r14*
    x86isa::*r15*

    ;; flags:
    x86isa::*flg-names*
    x86isa::*cf*
    x86isa::*pf*
    x86isa::*af*
    x86isa::*zf*
    x86isa::*sf*
    x86isa::*of*

    ;; segment registers:
    x86isa::*cs*
    x86isa::*ss*
    x86isa::*ds*

    x86isa::zf-spec
    x86isa::zf-spec$inline
    x86isa::cf-spec32
    x86isa::cf-spec32$inline
    x86isa::cf-spec64
    x86isa::cf-spec64$inline
    x86isa::pf-spec32
    x86isa::pf-spec32$inline
    x86isa::pf-spec64
    x86isa::pf-spec64$inline
    x86isa::of-spec8
    x86isa::of-spec8$inline
    x86isa::of-spec16
    x86isa::of-spec16$inline
    x86isa::of-spec32
    x86isa::of-spec32$inline
    x86isa::of-spec64
    x86isa::of-spec64$inline
    x86isa::sf-spec32
    x86isa::sf-spec32$inline
    x86isa::sf-spec64
    x86isa::sf-spec64$inline
    x86isa::add-af-spec32
    x86isa::add-af-spec32$inline
    x86isa::add-af-spec64
    x86isa::add-af-spec64$inline
    x86isa::sub-af-spec32
    x86isa::sub-af-spec32$inline
    x86isa::sub-af-spec64
    x86isa::sub-af-spec64$inline
    x86isa::sub-of-spec8
    x86isa::sub-of-spec16
    x86isa::sub-of-spec32
    x86isa::sub-of-spec64

    ;; do we want to include stuff like this?
    x86isa::x86-one-byte-opcode-modr/m-p$inline

    ;; my x86 stuff (what package should this stuff be in?)
    x86isa::lift-subroutine
    x86isa::lift-subroutine-fn
    x86isa::x86-lifter-table
    x86isa::run-until-exit-segment-or-hit-loop-header

    x86isa::text-offset ;variables put in by the lifter
    x86isa::x86_0
    x86isa::x86_1
    x86isa::x86_2
    x86isa::x86_3 ; todo: add more like this?

    ;;my stuff (move this to the X package):
    x86isa::lifter-rules

    x86isa::!app-view
    x86isa::init-x86-state-64
    x86isa::rgfi
    x86isa::!rgfi
    x86isa::rip
    x86isa::x86-run
    x86isa::x86-run-halt
    x86isa::prefixes-slice

    x86isa::disjoint-p
    x86isa::subset-p
    x86isa::member-p
    x86isa::no-duplicates-p

    x86isa::create-canonical-address-list
    x86isa::canonical-address-listp

    ;; special symbol that can appear in the MS field:
    x86isa::X86-HLT

    x86isa::increment-*ip
    x86isa::one-byte-opcode-execute
    x86isa::fault
    x86isa::fault$a
    x86isa::!fault
    x86isa::ms
    x86isa::ms$a
    x86isa::combine-bytes

    x86isa::ea-to-la
    x86isa::ea-to-la$inline
    x86isa::segment-base-and-bounds
    x86isa::*segment-register-names-len*

    ;; new stuff after change to x86 model state representation:

    x86isa::rflags
    x86isa::rflagsbits
    x86isa::!rflags
    x86isa::rflagsbits->of$inline
    x86isa::rflagsbits->sf$inline
    x86isa::rflagsbits->cf$inline
    x86isa::rflagsbits->af$inline
    x86isa::rflagsbits->zf$inline
    x86isa::rflagsbits->pf$inline
    x86isa::rflagsbits->of
    x86isa::rflagsbits->sf
    x86isa::rflagsbits->cf
    x86isa::rflagsbits->af
    x86isa::rflagsbits->zf
    x86isa::rflagsbits->pf

    x86isa::!seg-hidden-attri
    x86isa::seg-hidden-attri
    x86isa::seg-hidden-limiti
    x86isa::seg-hidden-basei
    x86isa::seg-visiblei
    x86isa::!rip

    x86isa::ctri
    ;; todo: more like this:
    x86isa::cr0bits->ts
    x86isa::cr0bits->em
    x86isa::cr4bits->osfxsr

    x86isa::msri

    x86isa::mxcsrbits-fix
    ;; todo: more like this?:
    x86isa::mxcsrbits->daz$inline
    x86isa::mxcsrbits->de$inline
    x86isa::mxcsrbits->im$inline
    x86isa::mxcsrbits->dm$inline
    x86isa::mxcsrbits->ie$inline
    x86isa::mxcsrbits->ze$inline
    x86isa::mxcsrbits->pe$inline
    x86isa::mxcsrbits->ue$inline
    x86isa::mxcsrbits->zm$inline
    x86isa::mxcsrbits->oe$inline
    x86isa::mxcsrbits->rc$inline

    x86isa::mxcsrbits->daz
    x86isa::mxcsrbits->de
    x86isa::mxcsrbits->im
    x86isa::mxcsrbits->dm
    x86isa::mxcsrbits->ie
    x86isa::mxcsrbits->ze
    x86isa::mxcsrbits->pe
    x86isa::mxcsrbits->ue
    x86isa::mxcsrbits->zm
    x86isa::mxcsrbits->oe
    x86isa::mxcsrbits->rc

    x86isa::feature-flag

    ;; floating-point stuff:
    x86isa::fp-decode
    x86isa::sse-cmp
    x86isa::sse-cmp-special
    x86isa::mxcsr
    x86isa::mxcsr$a

    ;; todo: more like the above
    x86isa::snan
    x86isa::qnan
    x86isa::indef
    x86isa::inf
    x86isa::*op-cmpeq*
    x86isa::*op-cmplt*
    x86isa::*op-cmple*
    x86isa::*op-cmpunord*
    x86isa::*op-cmpneq*
    x86isa::*op-cmpnlt*
    x86isa::*op-cmpnle*
    x86isa::*op-cmpord*
    x86isa::*op-ucomi*
    x86isa::*op-comi*

    x86isa::undef
    ))

(defconst *symbols-from-acl2-package*
  '(;loghead$inline
    bvchop
    logext
    getbit
    bvlt
    bvle
    sbvlt
    sbvle
    bvcat
    bvplus
    bvminus
    bvuminus
    bvmult
    bvshl
    bvshr
    bvashr
    bvdiv
    sbvdiv
    bvmod
    sbvrem
    logtail
    slice ;note that we don't get the slice from x86isa
    putbits
    putbit
    putbyte
    bool->bit$inline
    bool->bit
    boolif
    boolor
    booland
    bool-fix
    bool-fix$inline
    loghead
    logapp
    logmask

    bitxor
    bitnot
    bitand
    bitor
    bool-to-bit
    bvxor
    bvand
    bvor
    bvnot
    bvif
    bvsx
    repeatbit
    leftrotate
    rightrotate
    leftrotate32
    rightrotate32

    ceiling-of-lg
    lg
    log2

    farg1
    farg2
    farg3
    farg4
    check-arities

    lookup-eq-safe

    want-to-weaken ; for polarity-based reasoning
    want-to-strengthen ; for polarity-based reasoning

    ;; Stuff from ACL2 (TODO: Should these be in *acl2-exports*?):
    my-sublis-var
    *t*
    *nil*
    ffn-symb

    defp

    erp-nil
    erp-t

    def-constant-opener
    defopeners
    add-known-boolean

    defconst-computed
    defconst-computed2 ;drop?
    defconst-computed3

    ;; Axe stuff (TODO: Maybe remove these since they are just functions we call):
    simp-dag
    compose-term-and-dag
    compose-term-and-dags
    compose-dags
    make-axe-rules
    make-axe-rules!
    result-array-stobj
    dag-to-term
    dag-info
    make-term-into-dag
    ;; simplify-terms-using-each-other
    make-cons-nest
    dag-fns
    make-rule-alist
    dagify-term
    dagify-term2
    axe-syntaxp
    axe-bind-free

    ;; axe-syntaxp and axe-bind-free functions:
    bind-bv-size-axe
    heavier-dag-term

    prove-equivalence
    prove-equal-with-tactics
    symbolic-byte-assumptions
    symbolic-list
    ;rule lists:
    lookup-rules
    list-rules
    core-rules-bv
    amazing-rules-bv
    set-axe-rule-priority

    memberp

    bv-array-to-list
    bv-array-to-list-aux
    bv-array-read
    bv-array-write
    bv-arrayp

    ;; Stuff supporting b*
    b*
    when
    ///

    ;; APT transformations (sometimes used to verify listed code):
    wrap-output
    extract-output
    rename-params
    flatten-params
    drop-irrelevant-params
    tailrec
    make-tail-rec-bv-up
    make-tail-rec-bv-up2
    def ; handy APT utility

    ;; utilities:
    call-of
    fargs
    pack-in-package-of-symbol
    pack-in-package-of-first-symbol
    myif
    extend-progn
    get-vars-from-term
    doublets-to-alist
    translate-terms
    lookup-eq
    lookup
    lookup-safe
    myquotep
    variablep
    empty-alist
    empty-acc
    defforall-simple
    subset-eq
    submit-event
    must-be-redundant

    ;; x86 stuff (more to x package?):
    elf-info
    ))

;; Ideally, these would all be rewritten to BV ops
(defconst *symbols-from-bitops*
  '(bitops::part-install-width-low$inline))

;; Ideally, these would all be rewritten away
(defconst *symbols-from-rtl*
  '(rtl::bitn
    rtl::bits
    rtl::bvecp
    rtl::daz
    rtl::snanp
    rtl::qnanp
    rtl::denormp
    rtl::infp
    rtl::mxcsr-masks
    rtl::zencode
    rtl::iencode
    rtl::dencode
    rtl::nencode
    ))

;; formals that appear in theorems (or do we want to import these from acl2?):
(defconst *common-x86isa-formals*
  '(x86isa::k
    x86isa::k2
    ;; x86isa::n ; same as in acl2 package
    x86isa::n2))

;; TODO: Think about this...
(defconst *common-acl2-formals*
  '(x y z m n size i
    acl2::free
    acl2::freesize
    x86isa::ad x86isa::low x86isa::high
    x86isa::proc-mode
    x86isa::eff-addr
    x86isa::nbytes
    x86isa::seg-reg
    x86isa::flg))

(defpkg "X" (append *acl2-exports*
                    *symbols-from-acl2-package*
                    *x86isa-exports*
                    *symbols-from-bitops*
                    *symbols-from-rtl*
                    *common-acl2-formals*
                    *common-x86isa-formals*))
