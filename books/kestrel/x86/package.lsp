; A package for x86 proof work
;
; Copyright (C) 2017-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
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
    x86isa::!ms$inline
    x86isa::x86-fetch-decode-execute
    x86isa::rflags

    x86isa::64-bit-modep
    x86isa::*compatibility-mode*
    x86isa::*64-bit-mode*

    x86isa::rml08
    x86isa::rml32
    x86isa::rml64

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

    ;; formals that appear in theorems (or do we want to import these from acl2?):
    x86isa::k
    x86isa::k2
    x86isa::n
    x86isa::n2

    x86isa::!app-view
    x86isa::init-x86-state-64
    x86isa::rgfi
    x86isa::!rgfi
    x86isa::rip
    x86isa::ms
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
    x86isa::fault$inline
    x86isa::ms
    x86isa::ms$inline
    x86isa::combine-bytes

    x86isa::ea-to-la
    x86isa::ea-to-la$inline
    x86isa::segment-base-and-bounds
    x86isa::*segment-register-names-len*

    ;; new stuff after change to x86 model state representation:
    x86isa::!rflags
    x86isa::!seg-hidden-attri
    x86isa::seg-hidden-attri
    x86isa::seg-hidden-limiti
    x86isa::seg-hidden-basei
    x86isa::seg-visiblei
    x86isa::!rip
    ))

(defconst *symbols-from-acl2-package*
  '(;loghead$inline
    bvchop
    logext
    getbit
    sbvlt
    bvlt
    bvle
    sbvle
    bvcat
    bvplus
    bvminus
    bvuminus
    bvmult
    logtail
    slice ;note that we don't get the slice from x86isa
    myif
    bool->bit$inline
    bool->bit
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

    farg1
    farg2
    farg3
    farg4
    check-arities

    ;; Stuff from ACL2 (TODO: Should these be in *acl2-exports*?):
    common-lisp::ignorable
    my-sublis-var
    *t*
    *nil*
    ffn-symb

    defp

    erp-nil
    erp-t

    defconst-computed
    defconst-computed2 ;drop?
    defconst-computed3

    ;; Axe stuff:
    simp-dag
    compose-term-and-dag
    compose-term-and-dags
    compose-dags
    make-axe-rules
    make-axe-rules!
    result-array-stobj
    dag-to-term
    make-term-into-dag
    simplify-terms-using-each-other
    make-cons-nest
    dag-fns
    make-rule-alist
    dagify-term
    dagify-term2
    axe-syntaxp
    axe-bind-free
    prove-equivalence
    symbolic-byte-assumptions
    symbolic-list
    ;rule lists:
    lookup-rules
    list-rules
    core-rules-bv
    amazing-rules-bv

    memberp

    bv-array-to-list
    bv-array-to-list-aux

    ;; Stuff supporting b*
    b*
    when
    ///

    ;; APT stuff:
    def
    wrap-output
    flatten-params
    drop-irrelevant-params
    tailrec
    make-tail-rec-bv-up
    make-tail-rec-bv-up2

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
    untranslate
    subset-eq
    submit-event
    ))

;; TODO: Think about this...
(defconst *common-formals*
  '(x y m n))

(defpkg "X" (append *acl2-exports*
                    *symbols-from-acl2-package*
                    *x86isa-exports*
                    *common-formals*))
