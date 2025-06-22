; A package for x86 proof work
;
; Copyright (C) 2017-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The "X" package, for doing proofs about x86 code.  We could improve the name
;; if we want, but "X86" is taken.

;; In general, we import function names, but not theorem names, from other
;; packages into this package.

;; TODO: Combine some of these lists

;(include-book "std/portcullis" :dir :system)
(include-book "projects/x86isa/portcullis/portcullis" :dir :system)
(include-book "rtl/rel11/portcullis" :dir :system)

;; TODO: Add a bunch of x86 ISA stuff here
(defconst *symbols-from-x86isa*
  '(x86isa::x86 ;the stobj name
    x86isa::x86p
    x86isa::x86$ap

    x86isa::x86rec-get
    x86isa::x86rec-get1
    x86isa::x86rec-to-mtr
    x86isa::x86rec-p
    x86isa::x86rec-p1
    x86isa::x86-elem-p-top
    x86isa::x86-elem-p
    x86isa::x86-elem-default
    x86isa::x86-elem-default-top
    x86isa::tlbp
    x86isa::tlb-entryp
    x86isa::good-tlb-key-p
    x86isa::tlb-key-p
    x86isa::tlb-key->r-w-x$inline
    x86isa::tlb-key-fix
    x86isa::tty-bufferp
    x86isa::env-alistp
    x86isa::rip-ret-alistp

    x86isa::memi
    x86isa::!memi
    x86isa::memi$a
    x86isa::!memi$a

    x86isa::n48$inline
    x86isa::n48
    x86isa::app-view$inline
    x86isa::app-view
    x86isa::app-view$a
    x86isa::canonical-address-p$inline
    x86isa::canonical-address-p
    x86isa::xr
    x86isa::xw

    ;; Memory operations (from most to least complex):

    x86isa::rime-size
    x86isa::rime08
    x86isa::rime16
    x86isa::rime32
    x86isa::rime64
    x86isa::rime-size$inline
    x86isa::rime08$inline
    x86isa::rime16$inline
    x86isa::rime32$inline
    x86isa::rime64$inline

    x86isa::wime-size
    x86isa::wime08
    x86isa::wime16
    x86isa::wime32
    x86isa::wime64
    x86isa::wime-size$inline
    x86isa::wime08$inline
    x86isa::wime16$inline
    x86isa::wime32$inline
    x86isa::wime64$inline

    x86isa::rme-size
    x86isa::rme08
    x86isa::rme16
    x86isa::rme32
    x86isa::rme48
    x86isa::rme64
    x86isa::rme80
    x86isa::rme128
    x86isa::rme256
    x86isa::rme-size$inline
    x86isa::rme08$inline
    x86isa::rme16$inline
    x86isa::rme32$inline
    x86isa::rme48$inline
    x86isa::rme64$inline
    x86isa::rme80$inline
    x86isa::rme128$inline
    x86isa::rme256$inline

    x86isa::wme-size
    x86isa::wme08
    x86isa::wme16
    x86isa::wme32
    x86isa::wme48
    x86isa::wme64
    x86isa::wme80
    x86isa::wme128
    x86isa::wme256
    x86isa::wme-size$inline
    x86isa::wme08$inline
    x86isa::wme16$inline
    x86isa::wme32$inline
    x86isa::wme48$inline
    x86isa::wme64$inline
    x86isa::wme80$inline
    x86isa::wme128$inline
    x86isa::wme256$inline

    x86isa::riml-size
    x86isa::riml-size$inline
    x86isa::riml08
    x86isa::riml16
    x86isa::riml32
    x86isa::riml64

    x86isa::wiml-size
    x86isa::wiml-size$inline
    x86isa::wiml08
    x86isa::wiml16
    x86isa::wiml32
    x86isa::wiml64

    x86isa::rml-size
    x86isa::rml-size$inline
    x86isa::rml08
    x86isa::rml16
    x86isa::rml32
    x86isa::rml48
    x86isa::rml64
    x86isa::rml80
    x86isa::rml128
    x86isa::rml256
    x86isa::rml512

    x86isa::wml-size
    x86isa::wml-size$inline
    x86isa::wml08
    x86isa::wml16
    x86isa::wml32
    x86isa::wml48
    x86isa::wml64
    x86isa::wml80
    x86isa::wml128
    x86isa::wml256
    x86isa::wml512

    x86isa::rb
    x86isa::wb

    x86isa::rb-1
    x86isa::wb-1

    x86isa::rvm08
    x86isa::rvm16
    x86isa::rvm32
    x86isa::rvm48
    x86isa::rvm64
    x86isa::rvm80
    x86isa::rvm128
    x86isa::rvm256
    x86isa::rvm512
    x86isa::rvm08$inline
    x86isa::rvm16$inline
    x86isa::rvm32$inline
    x86isa::rvm48$inline
    x86isa::rvm64$inline
    x86isa::rvm80$inline
    x86isa::rvm128$inline
    x86isa::rvm256$inline
    x86isa::rvm512$inline

    x86isa::wvm08
    x86isa::wvm16
    x86isa::wvm32
    x86isa::wvm48
    x86isa::wvm64
    x86isa::wvm80
    x86isa::wvm128
    x86isa::wvm256
    x86isa::wvm512
    x86isa::wvm08$inline
    x86isa::wvm16$inline
    x86isa::wvm32$inline
    x86isa::wvm48$inline
    x86isa::wvm64$inline
    x86isa::wvm80$inline
    x86isa::wvm128$inline
    x86isa::wvm256$inline
    x86isa::wvm512$inline

    x86isa::flgi
    x86isa::!flgi
    x86isa::!flgi-undefined
    x86isa::separate
    x86isa::program-at
    x86isa::byte-listp ;todo: compare with unsigned-byte-p-list
    x86isa::alignment-checking-enabled-p
    x86isa::get-prefixes
    x86isa::x86-fetch-decode-execute

    x86isa::64-bit-modep
    x86isa::*compatibility-mode*
    x86isa::*64-bit-mode*
    x86isa::x86-operation-mode

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

    ;; See books/projects/x86isa/utils/basic-structs.lisp
    x86isa::2bits-fix
    x86isa::3bits-fix
    x86isa::4bits-fix
    x86isa::5bits-fix
    x86isa::6bits-fix
    x86isa::7bits-fix
    x86isa::8bits-fix
    x86isa::10bits-fix
    x86isa::11bits-fix
    x86isa::12bits-fix
    x86isa::13bits-fix
    x86isa::16bits-fix
    x86isa::17bits-fix
    x86isa::19bits-fix
    x86isa::22bits-fix
    x86isa::24bits-fix
    x86isa::31bits-fix
    x86isa::32bits-fix
    x86isa::36bits-fix
    x86isa::40bits-fix
    x86isa::45bits-fix
    x86isa::54bits-fix
    x86isa::64bits-fix

    ;; flags (todo: more):
    x86isa::*flg-names*
    x86isa::*cf*
    x86isa::*pf*
    x86isa::*af*
    x86isa::*zf*
    x86isa::*sf*
    x86isa::*of*

    ;; segment registers (see define-segment-registers):
    x86isa::*es*
    x86isa::*cs*
    x86isa::*ss*
    x86isa::*ds*
    x86isa::*fs*
    x86isa::*gs*
    x86isa::*segment-register-names-len*

    ;; flag functions:

    x86isa::zf-spec
    x86isa::zf-spec$inline

    x86isa::cf-spec8
    x86isa::cf-spec8$inline
    x86isa::cf-spec16
    x86isa::cf-spec16$inline
    x86isa::cf-spec32
    x86isa::cf-spec32$inline
    x86isa::cf-spec64
    x86isa::cf-spec64$inline

    x86isa::of-spec8
    x86isa::of-spec8$inline
    x86isa::of-spec16
    x86isa::of-spec16$inline
    x86isa::of-spec32
    x86isa::of-spec32$inline
    x86isa::of-spec64
    x86isa::of-spec64$inline

    x86isa::pf-spec8
    x86isa::pf-spec8$inline
    x86isa::pf-spec16
    x86isa::pf-spec16$inline
    x86isa::pf-spec32
    x86isa::pf-spec32$inline
    x86isa::pf-spec64
    x86isa::pf-spec64$inline

    x86isa::sf-spec8
    x86isa::sf-spec8$inline
    x86isa::sf-spec16
    x86isa::sf-spec16$inline
    x86isa::sf-spec32
    x86isa::sf-spec32$inline
    x86isa::sf-spec64
    x86isa::sf-spec64$inline

    x86isa::add-af-spec8
    x86isa::add-af-spec8$inline
    x86isa::add-af-spec16
    x86isa::add-af-spec16$inline
    x86isa::add-af-spec32
    x86isa::add-af-spec32$inline
    x86isa::add-af-spec64
    x86isa::add-af-spec64$inline

    x86isa::sub-af-spec8
    x86isa::sub-af-spec8$inline
    x86isa::sub-af-spec16
    x86isa::sub-af-spec16$inline
    x86isa::sub-af-spec32
    x86isa::sub-af-spec32$inline
    x86isa::sub-af-spec64
    x86isa::sub-af-spec64$inline

    x86isa::adc-af-spec8
    x86isa::adc-af-spec8$inline
    x86isa::adc-af-spec16
    x86isa::adc-af-spec16$inline
    x86isa::adc-af-spec32
    x86isa::adc-af-spec32$inline
    x86isa::adc-af-spec64
    x86isa::adc-af-spec64$inline

    x86isa::sbb-af-spec8
    x86isa::sbb-af-spec8$inline
    x86isa::sbb-af-spec16
    x86isa::sbb-af-spec16$inline
    x86isa::sbb-af-spec32
    x86isa::sbb-af-spec32$inline
    x86isa::sbb-af-spec64
    x86isa::sbb-af-spec64$inline

    x86isa::sub-cf-spec8
    x86isa::sub-cf-spec16
    x86isa::sub-cf-spec32
    x86isa::sub-cf-spec64

    x86isa::sub-of-spec8
    x86isa::sub-of-spec16
    x86isa::sub-of-spec32
    x86isa::sub-of-spec64

    x86isa::sub-pf-spec8
    x86isa::sub-pf-spec16
    x86isa::sub-pf-spec32
    x86isa::sub-pf-spec64

    x86isa::sub-sf-spec8
    x86isa::sub-sf-spec16
    x86isa::sub-sf-spec32
    x86isa::sub-sf-spec64

    x86isa::sub-zf-spec8
    x86isa::sub-zf-spec16
    x86isa::sub-zf-spec32
    x86isa::sub-zf-spec64

    x86isa::ror-spec
    x86isa::ror-spec$inline ; todo: more like this
    x86isa::ror-spec-8
    x86isa::ror-spec-16
    x86isa::ror-spec-32
    x86isa::ror-spec-64

    x86isa::rol-spec
    x86isa::rol-spec-8
    x86isa::rol-spec-16
    x86isa::rol-spec-32
    x86isa::rol-spec-64

    x86isa::mul-spec$inline
    x86isa::mul-spec-8
    x86isa::mul-spec-16
    x86isa::mul-spec-32
    x86isa::mul-spec-64

    x86isa::imul-spec$inline
    x86isa::imul-spec-8
    x86isa::imul-spec-16
    x86isa::imul-spec-32
    x86isa::imul-spec-64

    x86isa::div-spec-8
    x86isa::div-spec-16
    x86isa::div-spec-32
    x86isa::div-spec-64

    x86isa::idiv-spec-8
    x86isa::idiv-spec-16
    x86isa::idiv-spec-32
    x86isa::idiv-spec-64

    x86isa::one-byte-opcode-modr/m-p$inline
    x86isa::two-byte-opcode-modr/m-p$inline
    x86isa::32-bit-mode-two-byte-opcode-modr/m-p
    x86isa::32-bit-compute-mandatory-prefix-for-two-byte-opcode$inline

    ;; my x86 stuff (what package should this stuff be in?)
    x86isa::lift-subroutine
    x86isa::lift-subroutine-fn
    x86isa::x86-lifter-table
    x86isa::run-until-exit-segment-or-hit-loop-header

    x86isa::segment-selectorbits->rpl$inline

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
    x86isa::rgfi$a
    x86isa::rgfi-size
    x86isa::rgfi-size$inline
    x86isa::!rgfi
    x86isa::!rgfi$a
    x86isa::!rgfi-size
    x86isa::!rgfi-size$inline

    x86isa::rip
    x86isa::rip$a
    x86isa::!rip
    x86isa::!rip$a

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

    x86isa::increment-*ip ; remove?
    x86isa::one-byte-opcode-execute

    x86isa::fault
    x86isa::fault$a
    x86isa::!fault
    x86isa::!fault$a
    x86isa::ms
    x86isa::ms$a
    x86isa::!ms
    x86isa::!ms$a

    x86isa::combine-bytes

    x86isa::ea-to-la
    x86isa::ea-to-la$inline
    x86isa::segment-base-and-bounds

    ;; new stuff after change to x86 model state representation:

    x86isa::rflagsbits-fix
    x86isa::rflagsbits-fix$inline
    x86isa::rflags
    x86isa::rflags$a
    x86isa::rflagsbits
    x86isa::!rflags
    x86isa::!rflags$a
    x86isa::change-rflagsbits
    x86isa::write-user-rflags

    x86isa::rflagsbits->cf
    x86isa::rflagsbits->res1
    x86isa::rflagsbits->pf
    x86isa::rflagsbits->res2
    x86isa::rflagsbits->af
    x86isa::rflagsbits->res3
    x86isa::rflagsbits->zf
    x86isa::rflagsbits->sf
    x86isa::rflagsbits->tf
    x86isa::rflagsbits->intf
    x86isa::rflagsbits->df
    x86isa::rflagsbits->of
    x86isa::rflagsbits->iopl
    x86isa::rflagsbits->nt
    x86isa::rflagsbits->res4
    x86isa::rflagsbits->rf
    x86isa::rflagsbits->vm
    x86isa::rflagsbits->ac
    x86isa::rflagsbits->vif
    x86isa::rflagsbits->vip
    x86isa::rflagsbits->id
    x86isa::rflagsbits->res5
    x86isa::rflagsbits$inline

    x86isa::rflagsbits->cf$inline
    x86isa::rflagsbits->res1$inline
    x86isa::rflagsbits->pf$inline
    x86isa::rflagsbits->res2$inline
    x86isa::rflagsbits->af$inline
    x86isa::rflagsbits->res3$inline
    x86isa::rflagsbits->zf$inline
    x86isa::rflagsbits->sf$inline
    x86isa::rflagsbits->tf$inline
    x86isa::rflagsbits->intf$inline
    x86isa::rflagsbits->df$inline
    x86isa::rflagsbits->of$inline
    x86isa::rflagsbits->iopl$inline
    x86isa::rflagsbits->nt$inline
    x86isa::rflagsbits->res4$inline
    x86isa::rflagsbits->rf$inline
    x86isa::rflagsbits->vm$inline
    x86isa::rflagsbits->ac$inline
    x86isa::rflagsbits->vif$inline
    x86isa::rflagsbits->vip$inline
    x86isa::rflagsbits->id$inline
    x86isa::rflagsbits->res5$inline

    x86isa::!rflagsbits->cf
    x86isa::!rflagsbits->res1
    x86isa::!rflagsbits->pf
    x86isa::!rflagsbits->res2
    x86isa::!rflagsbits->af
    x86isa::!rflagsbits->res3
    x86isa::!rflagsbits->zf
    x86isa::!rflagsbits->sf
    x86isa::!rflagsbits->tf
    x86isa::!rflagsbits->intf
    x86isa::!rflagsbits->df
    x86isa::!rflagsbits->of
    x86isa::!rflagsbits->iopl
    x86isa::!rflagsbits->nt
    x86isa::!rflagsbits->res4
    x86isa::!rflagsbits->rf
    x86isa::!rflagsbits->vm
    x86isa::!rflagsbits->ac
    x86isa::!rflagsbits->vif
    x86isa::!rflagsbits->vip
    x86isa::!rflagsbits->id
    x86isa::!rflagsbits->res5

    x86isa::!rflagsbits->cf$inline
    x86isa::!rflagsbits->res1$inline
    x86isa::!rflagsbits->pf$inline
    x86isa::!rflagsbits->res2$inline
    x86isa::!rflagsbits->af$inline
    x86isa::!rflagsbits->res3$inline
    x86isa::!rflagsbits->zf$inline
    x86isa::!rflagsbits->sf$inline
    x86isa::!rflagsbits->tf$inline
    x86isa::!rflagsbits->intf$inline
    x86isa::!rflagsbits->df$inline
    x86isa::!rflagsbits->of$inline
    x86isa::!rflagsbits->iopl$inline
    x86isa::!rflagsbits->nt$inline
    x86isa::!rflagsbits->res4$inline
    x86isa::!rflagsbits->rf$inline
    x86isa::!rflagsbits->vm$inline
    x86isa::!rflagsbits->ac$inline
    x86isa::!rflagsbits->vif$inline
    x86isa::!rflagsbits->vip$inline
    x86isa::!rflagsbits->id$inline
    x86isa::!rflagsbits->res5$inline

    x86isa::!seg-hidden-attri
    x86isa::seg-hidden-attri
    x86isa::seg-hidden-limiti
    x86isa::seg-hidden-basei
    x86isa::seg-visiblei

    x86isa::ctri
    x86isa::ctri$a
    x86isa::!ctri
    x86isa::!ctri$a

    x86isa::cr0bits-p$inline
    x86isa::cr0bits-p
    x86isa::cr0bits->pe
    x86isa::cr0bits->mp
    x86isa::cr0bits->em
    x86isa::cr0bits->ts
    x86isa::cr0bits->et
    x86isa::cr0bits->ne
    x86isa::cr0bits->res1
    x86isa::cr0bits->wp
    x86isa::cr0bits->res2
    x86isa::cr0bits->am
    x86isa::cr0bits->res3
    x86isa::cr0bits->nw
    x86isa::cr0bits->cd
    x86isa::cr0bits->pg
    x86isa::cr0bits->pe$inline
    x86isa::cr0bits->mp$inline
    x86isa::cr0bits->em$inline
    x86isa::cr0bits->ts$inline
    x86isa::cr0bits->et$inline
    x86isa::cr0bits->ne$inline
    x86isa::cr0bits->res1$inline
    x86isa::cr0bits->wp$inline
    x86isa::cr0bits->res2$inline
    x86isa::cr0bits->am$inline
    x86isa::cr0bits->res3$inline
    x86isa::cr0bits->nw$inline
    x86isa::cr0bits->cd$inline
    x86isa::cr0bits->pg$inline

    x86isa::cr3bits-p$inline
    x86isa::cr3bits->res1
    x86isa::cr3bits->pwt
    x86isa::cr3bits->pcd
    x86isa::cr3bits->res2
    x86isa::cr3bits->pdb
    x86isa::cr3bits->res3

    x86isa::cr4bits-p$inline
    x86isa::cr4bits-p
    x86isa::cr4bits->vme
    x86isa::cr4bits->pvi
    x86isa::cr4bits->tsd
    x86isa::cr4bits->de
    x86isa::cr4bits->pse
    x86isa::cr4bits->pae
    x86isa::cr4bits->mce
    x86isa::cr4bits->pge
    x86isa::cr4bits->pce
    x86isa::cr4bits->osfxsr
    x86isa::cr4bits->osxmmexcpt
    x86isa::cr4bits->umip
    x86isa::cr4bits->la57
    x86isa::cr4bits->vmxe
    x86isa::cr4bits->smxe
    x86isa::cr4bits->res1
    x86isa::cr4bits->fsgsbase
    x86isa::cr4bits->pcide
    x86isa::cr4bits->osxsave
    x86isa::cr4bits->res2
    x86isa::cr4bits->smep
    x86isa::cr4bits->smap
    x86isa::cr4bits->vme$inline
    x86isa::cr4bits->pvi$inline
    x86isa::cr4bits->tsd$inline
    x86isa::cr4bits->de$inline
    x86isa::cr4bits->pse$inline
    x86isa::cr4bits->pae$inline
    x86isa::cr4bits->mce$inline
    x86isa::cr4bits->pge$inline
    x86isa::cr4bits->pce$inline
    x86isa::cr4bits->osfxsr$inline
    x86isa::cr4bits->osxmmexcpt$inline
    x86isa::cr4bits->umip$inline
    x86isa::cr4bits->la57$inline
    x86isa::cr4bits->vmxe$inline
    x86isa::cr4bits->smxe$inline
    x86isa::cr4bits->res1$inline
    x86isa::cr4bits->fsgsbase$inline
    x86isa::cr4bits->pcide$inline
    x86isa::cr4bits->osxsave$inline
    x86isa::cr4bits->res2$inline
    x86isa::cr4bits->smep$inline
    x86isa::cr4bits->smap$inline

    x86isa::cr8bits-p$inline
    x86isa::cr8bits->cr8-trpl

    x86isa::msri
    x86isa::msri$a
    x86isa::!msri
    x86isa::!msri$a

    x86isa::mxcsr
    x86isa::mxcsr$a
    x86isa::!mxcsr
    x86isa::!mxcsr$a
    x86isa::mxcsrbits-fix

    x86isa::mxcsrbits->ie$inline
    x86isa::mxcsrbits->de$inline
    x86isa::mxcsrbits->ze$inline
    x86isa::mxcsrbits->oe$inline
    x86isa::mxcsrbits->ue$inline
    x86isa::mxcsrbits->pe$inline
    x86isa::mxcsrbits->daz$inline
    x86isa::mxcsrbits->im$inline
    x86isa::mxcsrbits->dm$inline
    x86isa::mxcsrbits->zm$inline
    x86isa::mxcsrbits->om$inline
    x86isa::mxcsrbits->um$inline
    x86isa::mxcsrbits->pm$inline
    x86isa::mxcsrbits->rc$inline
    x86isa::mxcsrbits->ftz$inline
    x86isa::mxcsrbits->reserved$inline

    x86isa::mxcsrbits->ie
    x86isa::mxcsrbits->de
    x86isa::mxcsrbits->ze
    x86isa::mxcsrbits->oe
    x86isa::mxcsrbits->ue
    x86isa::mxcsrbits->pe
    x86isa::mxcsrbits->daz
    x86isa::mxcsrbits->im
    x86isa::mxcsrbits->dm
    x86isa::mxcsrbits->zm
    x86isa::mxcsrbits->om
    x86isa::mxcsrbits->um
    x86isa::mxcsrbits->pm
    x86isa::mxcsrbits->rc
    x86isa::mxcsrbits->ftz
    x86isa::mxcsrbits->reserved

    x86isa::!mxcsrbits->ie$inline
    x86isa::!mxcsrbits->de$inline
    x86isa::!mxcsrbits->ze$inline
    x86isa::!mxcsrbits->oe$inline
    x86isa::!mxcsrbits->ue$inline
    x86isa::!mxcsrbits->pe$inline
    x86isa::!mxcsrbits->daz$inline
    x86isa::!mxcsrbits->im$inline
    x86isa::!mxcsrbits->dm$inline
    x86isa::!mxcsrbits->zm$inline
    x86isa::!mxcsrbits->om$inline
    x86isa::!mxcsrbits->um$inline
    x86isa::!mxcsrbits->pm$inline
    x86isa::!mxcsrbits->rc$inline
    x86isa::!mxcsrbits->ftz$inline
    x86isa::!mxcsrbits->reserved$inline

    x86isa::!mxcsrbits->ie
    x86isa::!mxcsrbits->de
    x86isa::!mxcsrbits->ze
    x86isa::!mxcsrbits->oe
    x86isa::!mxcsrbits->ue
    x86isa::!mxcsrbits->pe
    x86isa::!mxcsrbits->daz
    x86isa::!mxcsrbits->im
    x86isa::!mxcsrbits->dm
    x86isa::!mxcsrbits->zm
    x86isa::!mxcsrbits->om
    x86isa::!mxcsrbits->um
    x86isa::!mxcsrbits->pm
    x86isa::!mxcsrbits->rc
    x86isa::!mxcsrbits->ftz
    x86isa::!mxcsrbits->reserved

    x86isa::feature-flag

    ;; floating-point stuff:
    x86isa::fp-decode
    x86isa::fp-to-rat
    x86isa::sse-cmp
    x86isa::sse-cmp-special
    x86isa::sp-sse-cmp
    x86isa::dp-sse-cmp
    x86isa::sse-daz
    x86isa::denormal-exception
    x86isa::*OP-UCOMI*

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
    x86isa::undef$a
    x86isa::!undef
    x86isa::!undef$a
    x86isa::create-undef

    x86isa::read-*ip
    x86isa::write-*ip
    x86isa::add-to-*ip
    x86isa::read-*ip$inline
    x86isa::write-*ip$inline
    x86isa::add-to-*ip$inline

    x86isa::read-*sp
    x86isa::write-*sp
    x86isa::add-to-*sp
    x86isa::read-*sp$inline
    x86isa::write-*sp$inline
    x86isa::add-to-*sp$inline

    x86isa::vex->vvvv$inline
    x86isa::vex->l$inline
    x86isa::vex->pp$inline
    x86isa::vex->r$inline
    x86isa::vex->w$inline
    x86isa::vex->b$inline
    x86isa::vex->x$inline

    x86isa::vex->vvvv
    x86isa::vex->l
    x86isa::vex->pp
    x86isa::vex->r
    x86isa::vex->w
    x86isa::vex->b
    x86isa::vex->x

    x86isa::x86-illegal-instruction
    x86isa::x86-step-unimplemented
    x86isa::feature-flags

    ;; this list is from (acl2::get-ruleset 'x86isa::nw-defs (w state)):
    x86isa::n01
    x86isa::n02
    x86isa::n03
    x86isa::n04
    x86isa::n05
    x86isa::n06
    x86isa::n08
    x86isa::n09
    x86isa::n11
    x86isa::n12
    x86isa::n16
    x86isa::n17
    x86isa::n18
    x86isa::n20
    x86isa::n21
    x86isa::n22
    x86isa::n24
    x86isa::n25
    x86isa::n26
    x86isa::n27
    x86isa::n28
    x86isa::n30
    x86isa::n32
    x86isa::n33
    x86isa::n35
    x86isa::n43
    x86isa::n44
    x86isa::n45
    x86isa::n47
    x86isa::n48
    x86isa::n49
    x86isa::n51
    x86isa::n52
    x86isa::n55
    x86isa::n59
    x86isa::n60
    x86isa::n64
    x86isa::n65
    x86isa::n80
    x86isa::n112
    x86isa::n120
    x86isa::n128
    x86isa::n256
    x86isa::n512

    ;; same as above list but with $inline:
    x86isa::n01$inline
    x86isa::n02$inline
    x86isa::n03$inline
    x86isa::n04$inline
    x86isa::n05$inline
    x86isa::n06$inline
    x86isa::n08$inline
    x86isa::n09$inline
    x86isa::n11$inline
    x86isa::n12$inline
    x86isa::n16$inline
    x86isa::n17$inline
    x86isa::n18$inline
    x86isa::n20$inline
    x86isa::n21$inline
    x86isa::n22$inline
    x86isa::n24$inline
    x86isa::n25$inline
    x86isa::n26$inline
    x86isa::n27$inline
    x86isa::n28$inline
    x86isa::n30$inline
    x86isa::n32$inline
    x86isa::n33$inline
    x86isa::n35$inline
    x86isa::n43$inline
    x86isa::n44$inline
    x86isa::n45$inline
    x86isa::n47$inline
    x86isa::n48$inline
    x86isa::n49$inline
    x86isa::n51$inline
    x86isa::n52$inline
    x86isa::n55$inline
    x86isa::n59$inline
    x86isa::n60$inline
    x86isa::n64$inline
    x86isa::n65$inline
    x86isa::n80$inline
    x86isa::n112$inline
    x86isa::n120$inline
    x86isa::n128$inline
    x86isa::n256$inline
    x86isa::n512$inline

    ;; this list is from (acl2::get-ruleset 'x86isa::ni-defs (w state)):
    x86isa::i01
    x86isa::i02
    x86isa::i03
    x86isa::i04
    x86isa::i05
    x86isa::i06
    x86isa::i08
    x86isa::i09
    x86isa::i11
    x86isa::i12
    x86isa::i16
    x86isa::i17
    x86isa::i18
    x86isa::i20
    x86isa::i21
    x86isa::i22
    x86isa::i24
    x86isa::i25
    x86isa::i26
    x86isa::i27
    x86isa::i28
    x86isa::i30
    x86isa::i32
    x86isa::i33
    x86isa::i35
    x86isa::i43
    x86isa::i44
    x86isa::i45
    x86isa::i47
    x86isa::i48
    x86isa::i49
    x86isa::i51
    x86isa::i52
    x86isa::i55
    x86isa::i59
    x86isa::i60
    x86isa::i64
    x86isa::i65
    x86isa::i80
    x86isa::i112
    x86isa::i120
    x86isa::i128
    x86isa::i256
    x86isa::i512

    ;; same as above list but with $inline:
    x86isa::i01$inline
    x86isa::i02$inline
    x86isa::i03$inline
    x86isa::i04$inline
    x86isa::i05$inline
    x86isa::i06$inline
    x86isa::i08$inline
    x86isa::i09$inline
    x86isa::i11$inline
    x86isa::i12$inline
    x86isa::i16$inline
    x86isa::i17$inline
    x86isa::i18$inline
    x86isa::i20$inline
    x86isa::i21$inline
    x86isa::i22$inline
    x86isa::i24$inline
    x86isa::i25$inline
    x86isa::i26$inline
    x86isa::i27$inline
    x86isa::i28$inline
    x86isa::i30$inline
    x86isa::i32$inline
    x86isa::i33$inline
    x86isa::i35$inline
    x86isa::i43$inline
    x86isa::i44$inline
    x86isa::i45$inline
    x86isa::i47$inline
    x86isa::i48$inline
    x86isa::i49$inline
    x86isa::i51$inline
    x86isa::i52$inline
    x86isa::i55$inline
    x86isa::i59$inline
    x86isa::i60$inline
    x86isa::i64$inline
    x86isa::i65$inline
    x86isa::i80$inline
    x86isa::i112$inline
    x86isa::i120$inline
    x86isa::i128$inline
    x86isa::i256$inline
    x86isa::i512$inline

    x86isa::i48p
    x86isa::i48p$inline  ;todo: more like this

    x86isa::n64-to-i64  ;todo: more like this

    x86isa::code-segment-descriptor-attributesbits->d
    x86isa::code-segment-descriptor-attributesbits->d$inline
    x86isa::code-segment-descriptor-attributesbits->p
    x86isa::code-segment-descriptor-attributesbits->p$inline
    x86isa::code-segment-descriptor-attributesbits-fix

    x86isa::data-segment-descriptor-attributesbits->
    x86isa::data-segment-descriptor-attributesbits->e$inline

    ;; error values:
    x86isa::rime-size-opt-error
    ;; there is no wime-size-opt-error
    x86isa::quotient
    x86isa::remainder
    x86isa::quotient-int
    x86isa::remainder-int

    x86isa::rr32$inline
    x86isa::reg-index$inline

    x86isa::x86-general-protection
    x86isa::x86-device-not-available
    x86isa::x86-syscall-both-views

    ;; not used much, since we use app-view:
    x86isa::ia32e-la-to-pa
    x86isa::la-to-pa
    x86isa::las-to-pas

    X86ISA::ADDRESS-ALIGNED-P

    ;; register-related functions:

    x86isa::rr08 ; there are only 4 of these
    x86isa::rr16
    x86isa::rr32
    x86isa::rr64
    x86isa::rr08$inline
    x86isa::rr16$inline
    x86isa::rr32$inline
    x86isa::rr64$inline

    x86isa::wr08 ; there are only 4 of these
    x86isa::wr16
    x86isa::wr32
    x86isa::wr64
    x86isa::wr08$inline
    x86isa::wr16$inline
    x86isa::wr32$inline
    x86isa::wr64$inline

    x86isa::rx32 ; there seem to be only 3 of these
    x86isa::rx64
    x86isa::rx128
    x86isa::rx32$inline
    x86isa::rx64$inline
    x86isa::rx128$inline

    x86isa::wx32$inline ; there seem to be only 3 of these
    x86isa::wx64$inline
    x86isa::wx128$inline
    x86isa::wx32
    x86isa::wx64
    x86isa::wx128

    x86isa::rz32 ; there seem to be only 5 of these
    x86isa::rz64
    x86isa::rz128
    x86isa::rz256
    x86isa::rz512
    x86isa::rz32$inline
    x86isa::rz64$inline
    x86isa::rz128$inline
    x86isa::rz256$inline
    x86isa::rz512$inline

    x86isa::wz32$inline ; there seem to be only 5 of these
    x86isa::wz64$inline
    x86isa::wz128$inline
    x86isa::wz256$inline
    x86isa::wz512$inline
    x86isa::wz32
    x86isa::wz64
    x86isa::wz128
    x86isa::wz256
    x86isa::wz512

    x86isa::xmmi-size
    x86isa::xmmi-size$inline
    x86isa::!xmmi-size
    x86isa::!xmmi-size$inline

    x86isa::zmmi
    x86isa::zmmi$a
    x86isa::!zmmi
    x86isa::!zmmi$a

    x86isa::zmmi-size
    x86isa::zmmi-size$inline
    x86isa::!zmmi-size
    x86isa::!zmmi-size$inline

    x86isa::64-bit-mode-two-byte-opcode-modr/m-p

    x86isa::simd-add-spec
    x86isa::simd-sub-spec

    x86isa::convert-arith-operation-to-rtl-op$inline

    ;; names introduced by defbitstruct:

    x86isa::prefixes-fix$inline
    x86isa::prefixes-fix
    x86isa::prefixes->num$inline
    x86isa::prefixes->lck$inline
    x86isa::prefixes->rep$inline
    x86isa::prefixes->seg$inline
    x86isa::prefixes->opr$inline
    x86isa::prefixes->adr$inline
    x86isa::prefixes->nxt$inline
    x86isa::prefixes->num
    x86isa::prefixes->lck
    x86isa::prefixes->rep
    x86isa::prefixes->seg
    x86isa::prefixes->opr
    x86isa::prefixes->adr
    x86isa::prefixes->nxt
    x86isa::!prefixes->num$inline
    x86isa::!prefixes->lck$inline
    x86isa::!prefixes->rep$inline
    x86isa::!prefixes->seg$inline
    x86isa::!prefixes->opr$inline
    x86isa::!prefixes->adr$inline
    x86isa::!prefixes->nxt$inline
    x86isa::!prefixes->num
    x86isa::!prefixes->lck
    x86isa::!prefixes->rep
    x86isa::!prefixes->seg
    x86isa::!prefixes->opr
    x86isa::!prefixes->adr
    x86isa::!prefixes->nxt

    x86isa::vex-prefixes-fix$inline
    x86isa::vex-prefixes-fix
    x86isa::vex-prefixes->byte0$inline
    x86isa::vex-prefixes->byte1$inline
    x86isa::vex-prefixes->byte2$inline
    x86isa::vex-prefixes->byte0
    x86isa::vex-prefixes->byte1
    x86isa::vex-prefixes->byte2
    x86isa::!vex-prefixes->byte0$inline
    x86isa::!vex-prefixes->byte1$inline
    x86isa::!vex-prefixes->byte2$inline
    x86isa::!vex-prefixes->byte0
    x86isa::!vex-prefixes->byte1
    x86isa::!vex-prefixes->byte2

    ;;todo: changers too?
    x86isa::vex2-byte1-fix$inline
    x86isa::vex2-byte1-fix
    x86isa::vex2-byte1->pp$inline
    x86isa::vex2-byte1->l$inline
    x86isa::vex2-byte1->vvvv$inline
    x86isa::vex2-byte1->r$inline
    x86isa::vex2-byte1->pp
    x86isa::vex2-byte1->l
    x86isa::vex2-byte1->vvvv
    x86isa::vex2-byte1->r

    ;;todo: changers too?
    x86isa::vex3-byte1-fix$inline
    x86isa::vex3-byte1-fix
    x86isa::vex3-byte1->m-mmmm$inline
    x86isa::vex3-byte1->b$inline
    x86isa::vex3-byte1->x$inline
    x86isa::vex3-byte1->r$inline
    x86isa::vex3-byte1->m-mmmm
    x86isa::vex3-byte1->b
    x86isa::vex3-byte1->x
    x86isa::vex3-byte1->r

    ;;todo: changers too?
    x86isa::vex3-byte2-fix$inline
    x86isa::vex3-byte2-fix
    x86isa::vex3-byte2->pp$inline
    x86isa::vex3-byte2->l$inline
    x86isa::vex3-byte2->vvvv$inline
    x86isa::vex3-byte2->w$inline
    x86isa::vex3-byte2->pp
    x86isa::vex3-byte2->l
    x86isa::vex3-byte2->vvvv
    x86isa::vex3-byte2->w

    x86isa::evex-prefixes-fix$inline
    x86isa::evex-prefixes-fix
    x86isa::evex-prefixes->byte0$inline
    x86isa::evex-prefixes->byte1$inline
    x86isa::evex-prefixes->byte2$inline
    x86isa::evex-prefixes->byte3$inline
    x86isa::evex-prefixes->byte0
    x86isa::evex-prefixes->byte1
    x86isa::evex-prefixes->byte2
    x86isa::evex-prefixes->byte3
    x86isa::!evex-prefixes->byte0$inline
    x86isa::!evex-prefixes->byte1$inline
    x86isa::!evex-prefixes->byte2$inline
    x86isa::!evex-prefixes->byte3$inline
    x86isa::!evex-prefixes->byte0
    x86isa::!evex-prefixes->byte1
    x86isa::!evex-prefixes->byte2
    x86isa::!evex-prefixes->byte3

    x86isa::evex-byte1-fix$inline
    x86isa::evex-byte1-fix
    x86isa::evex-byte1->mmm$inline
    x86isa::evex-byte1->res$inline
    x86isa::evex-byte1->r-prime$inline
    x86isa::evex-byte1->b$inline
    x86isa::evex-byte1->x$inline
    x86isa::evex-byte1->r$inline
    x86isa::evex-byte1->mmm
    x86isa::evex-byte1->res
    x86isa::evex-byte1->r-prime
    x86isa::evex-byte1->b
    x86isa::evex-byte1->x
    x86isa::evex-byte1->r

    x86isa::evex-byte2-fix$inline
    x86isa::evex-byte2-fix
    x86isa::evex-byte2->pp$inline
    x86isa::evex-byte2->res$inline
    x86isa::evex-byte2->vvvv$inline
    x86isa::evex-byte2->w$inline
    x86isa::evex-byte2->pp
    x86isa::evex-byte2->res
    x86isa::evex-byte2->vvvv
    x86isa::evex-byte2->w

    x86isa::evex-byte3-fix$inline
    x86isa::evex-byte3-fix
    x86isa::evex-byte3->aaa$inline
    x86isa::evex-byte3->v-prime$inline
    x86isa::evex-byte3->b$inline
    x86isa::evex-byte3->vl/rc$inline
    x86isa::evex-byte3->z$inline
    x86isa::evex-byte3->aaa
    x86isa::evex-byte3->v-prime
    x86isa::evex-byte3->b
    x86isa::evex-byte3->vl/rc
    x86isa::evex-byte3->z

    x86isa::modr/m-fix$inline
    x86isa::modr/m-fix
    x86isa::modr/m->r/m$inline
    x86isa::modr/m->reg$inline
    x86isa::modr/m->mod$inline
    x86isa::modr/m->r/m
    x86isa::modr/m->reg
    x86isa::modr/m->mod

    x86isa::sib-fix$inline
    x86isa::sib-fix
    x86isa::sib->base$inline
    x86isa::sib->index$inline
    x86isa::sib->scale$inline
    x86isa::sib->base
    x86isa::sib->index
    x86isa::sib->scale

    ))

(defconst *symbols-from-acl2-package*
  '(loghead
    loghead$inline
    logapp
    logmask

    expt2$inline ; from IHS

    bvchop
    logext
    getbit
    bvlt
    bvle
    bvgt
    bvge
    sbvlt
    sbvle
    sbvgt
    sbvge
    bvcat
    bvcat2
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
    trim

    bool->bit$inline
    bool->bit
    boolif
    boolor
    booland
    bool-fix
    bool-fix$inline

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

    acl2::bfix$
    acl2::bfix$inline

    binary-logand
    binary-logxor
    binary-logior

    unsigned-byte-p-forced

    ceiling-of-lg
    lg
    log2
    power-of-2p

    ;; list and bv-list stuff:
    prefixp
    ;; byte-listp ; todo: clash!
    all-integerp
    all-all-unsigned-byte-p
    all-true-listp
    items-have-len
    all-unsigned-byte-p
    bit-to-bool

    farg1
    farg2
    farg3
    farg4
    check-arities

    lookup-eq
    lookup-eq-safe
    lookup
    lookup-safe
    lookup-equal
    lookup-equal-safe

    want-to-weaken ; for polarity-based reasoning
    want-to-strengthen ; for polarity-based reasoning

    ;; Stuff from ACL2 (TODO: Should these be in *acl2-exports*?):
    my-sublis-var
    *t*
    *nil*
    ffn-symb

    define
    __function__
    defrule

    defpun
    defp

    erp-nil
    erp-t

    def-constant-opener
    defopeners
    add-known-boolean

    defconst-computed
    defconst-computed2 ;drop?
    defconst-computed3
    def-simplified-basic
    basic ; name of the basic rewriter (may be printed by "The ~x0 rewriter lacks SMT support ...")

    ;; Axe stuff (TODO: Maybe remove these since they are just functions we call):
    simp-dag
    compose-term-and-dag
    compose-term-and-dags
    compose-dags
    make-axe-rules
    make-axe-rules!
    axe-quotep
    result-array-stobj
    dag-to-term
    make-term-into-dag
    ;; simplify-terms-using-each-other
    make-cons-nest
    dag-info
    dag-fns
    dag-vars
    dag-size
    make-rule-alist
    make-rule-alist!
    dagify-term
    dagify-term2
    axe-syntaxp
    axe-bind-free
    axe-binding-hyp
    axe-smt
    work-hard ; may not be needed
    axe-rewrite-objective ; may not be needed
    dag-array ; for calls of axe-syntaxp functions
    def-simplified-x86
    dag-val-with-axe-evaluator
    defthm-axe
    defthm-axe-basic
    defthm-stp
    prove-with-stp
    defmacrodoc

    ;; These are for writing axe-syntaxp and axe-bind-free functions:
    pseudo-dag-arrayp
    dargs
    darg1
    darg2
    darg3
    darg4

    ;; axe-syntaxp and axe-bind-free functions:
    bind-bv-size-axe

    syntactic-call-of
    term-should-be-trimmed-axe
    lighter-dargp

    prove-equal-with-axe
    prove-equality
    prove-with-axe
    prove-equal-with-tactics
    symbolic-byte-assumptions
    symbolic-list
    ;rule lists:
    lookup-rules
    list-rules
    core-rules-bv
    amazing-rules-bv
    trim-rules
    set-axe-rule-priority
    unroll-spec-basic
    unroll-spec

    memberp

    list-to-bv-array
    bv-array-to-list
    bv-array-to-list-aux
    bv-array-read
    bv-array-write
    bv-array-read-chunk-little
    bv-arrayp

    ;; Stuff supporting b*
    b*
    when
    unless
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
    translate-term
    translate-terms
    myquotep
    variablep
    empty-alist
    empty-acc
    defforall-simple
    subset-eq
    submit-event
    must-be-redundant
    must-fail
    strip-cadrs

    ;; x86 stuff (move to x package?):
    elf-info
    parse-elf-file-bytes ; helpful for tracing
    parsed-elfp

    ;; Testing utilities:
    assert-equal
    deftest

    ruleset
    e/d*

    defconst-computed-simple

    _  ; for printing non-pure node patterns
    ))

;; Ideally, these would all be rewritten to BV ops
(defconst *symbols-from-bitops*
  '(bitops::part-select ; a macro
    bitops::part-select-low-high
    bitops::part-select-low-high$inline
    bitops::part-select-width-low
    bitops::part-select-width-low$inline
    bitops::part-install ; a macro
    bitops::part-install-width-low
    bitops::part-install-width-low$inline
    b-xor ; from ihs, via bitops
    b-xor$inline ; really from ihs
    logbit
    logbit$inline ; really from ihs
    ))

;; Ideally, these would all be rewritten away
(defconst *symbols-from-rtl*
  '(rtl::fl
    rtl::bitn
    rtl::bits
    rtl::binary-cat
    rtl::bvecp
    rtl::daz
    rtl::nanp
    rtl::snanp
    rtl::qnanp
    rtl::denormp
    rtl::infp
    rtl::unsupp
    rtl::formatp
    rtl::encodingp
    rtl::explicitp
    rtl::sigw
    rtl::expf
    rtl::sgnf
    rtl::manf
    rtl::sigf
    rtl::prec
    rtl::mxcsr-masks
    ;; rtl::set-flag ; conflict with our set-flag
    rtl::zencode
    rtl::iencode
    rtl::dencode
    rtl::nencode
    rtl::decode
    rtl::ddecode
    rtl::zencode
    rtl::mxcsr-rc))

;; formals that appear in theorems (or do we want to import these from acl2?):
;; also includes some vars that are let-bound in definitions
(defconst *common-x86isa-formals*
  '(x86isa::k
    x86isa::k2
    ;; x86isa::n ; same as in acl2 package
    x86isa::n1
    x86isa::n2
    x86isa::n3
    x86isa::n4
    x86isa::ad1
    x86isa::ad2
    x86isa::ad3
    x86isa::ad4
    x86isa::rwx
    x86isa::input-rflags
    x86isa::cf
    x86isa::of
    x86isa::af
    x86isa::sf
    x86isa::zf
    x86isa::pf
    x86isa::ad x86isa::low x86isa::high
    x86isa::proc-mode
    x86isa::eff-addr
    x86isa::nbytes
    x86isa::seg-reg
    x86isa::flg
    x86isa::dst
    x86isa::src
    x86isa::cnt
    x86isa::rex-byte
    x86isa::prefixes
    x86isa::start-rip
    x86isa::temp-rip
    x86isa::rex?
    x86isa::lin-addr
    x86isa::r-x
    x86isa::7+lin-addr
    x86isa::modr/m
    x86isa::fault-var
    x86isa::mandatory-prefix
    x86isa::cs-attr

    x86isa::opcode
    x86isa::sib

    x86isa::ignore-p3-64?
    x86isa::p3?
    x86isa::cs.d
    x86isa::ignore-rex?
    x86isa::imm?
    x86isa::flg0
    x86isa::dword
    x86isa::addr

    x86isa::x86$a

    x86isa::mem-ptr?
    x86isa::check-alignment?
    x86isa::base

    x86isa::*ip

    x86isa::reg
    x86isa::rex
    x86isa::qword

    x86isa::result
    x86isa::raw-result

    x86isa::low-nibble

    x86isa::cs.limit
    x86isa::*ip+delta
))

;; TODO: Think about this...
(defconst *common-acl2-formals*
  '(x y z m n size i
    x1 x2 y1 y2
    free
    freesize
    xsize
    ysize
    lowsize
    highsize
    lowval
    highval
    ;; low high ; can't include these as above we get them from the x86isa package
    size
    size1
    size2))

(defpkg "X" (append *acl2-exports*
                    *symbols-from-acl2-package*
                    *symbols-from-x86isa*
                    *symbols-from-bitops*
                    *symbols-from-rtl*
                    *common-acl2-formals*
                    *common-x86isa-formals*))
