; Rule Lists used by the Formal Unit Tester
;
; Copyright (C) 2021-2022 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "kestrel/axe/rule-lists" :dir :system)

(defun lifter-rules64-new ()
  (declare (xargs :guard t))
  '(;; Rules about RIP/SET-RIP:
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

    integerp-of-rsp
    fix-of-rsp

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
    xr-becomes-undef))

;; these are used both for lifting and proving
(defun extra-rules ()
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
            separate-when-separate
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
            separate-of-1-and-1
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
            fix-of-rsp
            acl2::myif-becomes-boolif-axe ; since STP translation supports disjuncts that are calls to boolif but not if.
            acl2::equal-of-bvplus-constant-and-constant
            acl2::equal-of-bvplus-constant-and-constant-alt
            acl2::bvchop-of-bvshr-same
            bvand-of-lognot-arg2
            bvand-of-lognot-arg3
            bvxor-of-lognot-arg2
            bvxor-of-lognot-arg3
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
          (acl2::booleanp-rules)
          (acl2::boolean-rules-safe)
          (acl2::type-rules)))

(defun extra-lifting-rules ()
  (declare (xargs :guard t))
  (append (lifter-rules64-new)
          (extra-rules)
          '(X86ISA::WX32$inline ; more?
            X86ISA::WZ32$inline ; more?
            <-of-fp-to-rat ; do we want this?
            X86ISA::!EVEX-PREFIXES->BYTE0$INLINE-CONSTANT-OPENER
            !RFLAGS-of-if-arg1
            !RFLAGS-of-if-arg2
            ;;xr-of-!rflags-irrel
            X86ISA::IF-X-X-Y
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
            X86ISA::SSE-CMP ; scary
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
            jnl-condition-rewrite-32 ; todo
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
            ;drop some of these?
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

            ;jnbe-condition-of-BOOL->BIT-of-<-of-bvchop-and-ZF-SPEC-of-bvplus-of-bvuminus
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
            acl2::integerp-of-if
            acl2::ifix-does-nothing
            of-spec-of-logext-32
            ACL2::LOGXOR-BVCHOP-BVCHOP        ; introduce bvxor
            ACL2::LOGXOR-of-BVCHOP-becomes-bvxor-arg1 ; introduce bvxor
            bvplus-of-logxor-arg1                     ; introduce bvxor
            bvxor-of-logxor-arg2                      ; introduce bvxor
            integerp-of-logxor                        ;todo: more
            acl2::unsigned-byte-p-of-if
            acl2::unsigned-byte-p-of-bvplus ;todo: more
            ACL2::BVCHOP-OF-MYIF
            XR-OF-IF ;restrict?
            ACL2::SLICE-OUT-OF-ORDER
            X86ISA::DIV-SPEC$inline ; just a dispatch on the size
            ;; todo: more like this?:
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
            BVUMINUS-OF-BVSX-16-32-16
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
            ;; ACL2::BOOLIF-X-X-Y ; introduces boolor
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
            ;; These help make failures more clear:
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
            read-of-2 ; splits into 2 reads
            )
          (acl2::core-rules-bv) ; trying
          (acl2::unsigned-byte-p-rules)
          (acl2::unsigned-byte-p-forced-rules)))

(defun proof-rules ()
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
            bvuminus-of-bvsx-16-32-16
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
            ;ACL2::BOOLIF-X-X-Y ; introduces boolor
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
          (extra-rules)
          (lifter-rules64-new) ; overkill?
          (acl2::base-rules)
          (acl2::core-rules-bv) ; trying
          (acl2::unsigned-byte-p-rules)
          (acl2::unsigned-byte-p-forced-rules)))
