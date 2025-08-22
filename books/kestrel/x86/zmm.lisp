; Setters and getters for ZMM registers
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;(include-book "projects/x86isa/machine/state" :dir :system) ;for xr
(include-book "kestrel/utilities/myif" :dir :system)
(include-book "register-readers-and-writers64")
(include-book "flags")
(include-book "read-and-write")
(include-book "read-bytes-and-write-bytes")
(include-book "readers-and-writers64") ; drop?
(include-book "readers-and-writers")
(include-book "projects/x86isa/machine/decoding-and-spec-utils" :dir :system) ; for alignment-checking-enabled-p
(local (include-book "read-over-write-rules64"))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Get the value of ZMM register N, a 512-bit unsigned value.  We do not make
;; separate setters and getters for each ZMM register, because there are just
;; too many and they have nice, systematic names.
(defund-nx zmm (n x86)
  (declare (xargs :guard (and (natp n)
                              (< n 32))
                  :stobjs x86))
  (zmmi n x86))

(defthm unsigned-byte-p-of-zmm
  (implies (<= 512 size)
           (equal (unsigned-byte-p size (zmm reg x86))
                  (natp size)))
  :hints (("Goal" :use (:instance x86isa::elem-p-of-xr-zmm
                                  (i reg)
                                  (x86$a x86))
           :in-theory (e/d (zmm) (x86isa::elem-p-of-xr-zmm)))))

(defthmd xr-becomes-zmm
  (equal (xr :zmm n x86)
         (zmm n x86))
  :hints (("Goal" :in-theory (enable zmm))))

(theory-invariant (incompatible (:rewrite xr-becomes-zmm) (:definition zmm)))

(defthmd zmmi-becomes-zmm
  (equal (zmmi n x86)
         (zmm n x86))
  :hints (("Goal" :in-theory (enable zmm))))

(theory-invariant (incompatible (:rewrite zmmi-becomes-zmm) (:definition zmm)))

;; todo: zmm-of-xw, or do we never go to xw?
;; todo: zmm-of-if ?
(defthm zmm-of-set-rip (equal (zmm n (set-rip rip x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rax (equal (zmm n (set-rax rax x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rbx (equal (zmm n (set-rbx rbx x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rcx (equal (zmm n (set-rcx rcx x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rdx (equal (zmm n (set-rdx rdx x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rsi (equal (zmm n (set-rsi rsi x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rdi (equal (zmm n (set-rdi rdi x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-r8 (equal (zmm n (set-r8 r8 x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-r9 (equal (zmm n (set-r9 r9 x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-r10 (equal (zmm n (set-r10 r10 x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-r11 (equal (zmm n (set-r11 r11 x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-r12 (equal (zmm n (set-r12 r12 x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-r13 (equal (zmm n (set-r13 r13 x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-r14 (equal (zmm n (set-r14 r14 x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-r15 (equal (zmm n (set-r15 r15 x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rsp (equal (zmm n (set-rsp rsp x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rbp (equal (zmm n (set-rbp rbp x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))));todo: more

(defthm zmm-of-set-flag (equal (zmm n (set-flag flag val x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-!rflags (equal (zmm n (!rflags flags x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-mxcsr (equal (zmm n (set-mxcsr mxcsr x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-undef (equal (zmm n (set-undef undef x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))

(defthm zmm-of-write-byte (equal (zmm n (write-byte base-addr byte x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable write-byte zmm))))
(defthm zmm-of-write (equal (zmm n (write n2 base-addr byte x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable write))))
(defthm zmm-of-write-bytes (equal (zmm n (write-bytes base-addr bytes x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund set-zmm (n val x86)
  (declare (xargs :guard (and (natp n)
                              (< n 32)
                              (unsigned-byte-p 512 val) ; todo: tighten
                              )
                  :stobjs x86))
  (!zmmi n val x86))

(defthmd xw-becomes-set-zmm
  (equal (xw :zmm n val x86)
         (set-zmm n val x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(theory-invariant (incompatible (:rewrite xw-becomes-set-zmm) (:definition set-zmm)))

(defthmd !zmmi-becomes-set-zmm
  (equal (!zmmi n val x86)
         (set-zmm n val x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(theory-invariant (incompatible (:rewrite !zmmi-becomes-set-zmm) (:definition set-zmm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zmm-of-set-zmm-same
  (equal (zmm reg (set-zmm reg val x86))
         (bvchop 512 val))
  :hints (("Goal" :in-theory (enable zmm set-zmm bvchop loghead))))

(defthm zmm-of-set-zmm-diff
  (implies (not (equal reg1 reg2))
           (equal (zmm reg1 (set-zmm reg2 val x86))
                  (zmm reg1 x86)))
  :hints (("Goal" :in-theory (enable zmm set-zmm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm 64-bit-modep-of-set-zmm
  (equal (64-bit-modep (set-zmm reg val x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm alignment-checking-enabled-p-of-set-zmm
  (equal (alignment-checking-enabled-p (set-zmm reg val x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm app-view-of-set-zmm
  (equal (app-view (set-zmm reg val x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm ctri-of-set-zmm
  (equal (ctri i (set-zmm reg val x86))
         (ctri i x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm fault-of-set-zmm
  (equal (fault (set-zmm reg val x86))
         (fault x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm get-flag-of-set-zmm
  (equal (get-flag flag (set-zmm reg val x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm ms-of-set-zmm
  (equal (ms (set-zmm reg val x86))
         (ms x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm mxcsr-of-set-zmm
  (equal (mxcsr (set-zmm reg val x86))
         (mxcsr x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm undef-of-set-zmm
  (equal (undef (set-zmm reg val x86))
         (undef x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

;; strengthen?
(defthm x86p-of-set-zmm
  (implies (x86p x86)
           (x86p (set-zmm reg val x86)))
  :hints (("Goal" :in-theory (enable set-zmm))))



;; todo: do we need xr-of-zmm?  perhaps we no never see xr?
(defthm rip-of-set-zmm (equal (rip (set-zmm reg val x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm rax-of-set-zmm (equal (rax (set-zmm reg val x86)) (rax x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm rbx-of-set-zmm (equal (rbx (set-zmm reg val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm rcx-of-set-zmm (equal (rcx (set-zmm reg val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm rdx-of-set-zmm (equal (rdx (set-zmm reg val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm rsi-of-set-zmm (equal (rsi (set-zmm reg val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm rdi-of-set-zmm (equal (rdi (set-zmm reg val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm r8-of-set-zmm (equal (r8 (set-zmm reg val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm r9-of-set-zmm (equal (r9 (set-zmm reg val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm r10-of-set-zmm (equal (r10 (set-zmm reg val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm r11-of-set-zmm (equal (r11 (set-zmm reg val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm r12-of-set-zmm (equal (r12 (set-zmm reg val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm r13-of-set-zmm (equal (r13 (set-zmm reg val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm r14-of-set-zmm (equal (r14 (set-zmm reg val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm r15-of-set-zmm (equal (r15 (set-zmm reg val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm rsp-of-set-zmm (equal (rsp (set-zmm reg val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm rbp-of-set-zmm (equal (rbp (set-zmm reg val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable set-zmm))))

(defthm read-byte-of-set-zmm
  (equal (read-byte addr (set-zmm reg val x86))
         (read-byte addr x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm read-of-set-zmm
  (equal (read n addr (set-zmm reg val x86))
         (read n addr x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm read-bytes-of-set-zmm
  (equal (read-bytes addr n (set-zmm reg val x86))
         (read-bytes addr n x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; write-of-write rules

(defthm set-zmm-of-set-zmm-same
  (equal (set-zmm reg val1 (set-zmm reg val2 x86))
         (set-zmm reg val1 x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm set-zmm-of-set-zmm-diff-constant-version
  (implies (and (syntaxp (and (quotep reg1)
                              (quotep reg2)))
                (< reg2 reg1))
           (equal (set-zmm reg1 val1 (set-zmm reg2 val2 x86))
                  (set-zmm reg2 val2 (set-zmm reg1 val1 x86))))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm set-flag-of-set-zmm
  (equal (set-flag flag fval (set-zmm reg val x86))
         (set-zmm reg val (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable set-flag set-zmm))))

(defthm !rflags-of-set-zmm
  (equal (!rflags flags (set-zmm reg val x86))
         (set-zmm reg val (!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag set-zmm))))

(defthm set-undef-of-set-zmm
  (equal (set-undef undef (set-zmm reg val x86))
         (set-zmm reg val (set-undef undef x86)))
  :hints (("Goal" :in-theory (enable set-undef set-zmm))))

(defthm set-mxcsr-of-set-zmm
  (equal (set-mxcsr mxcsr (set-zmm reg val x86))
         (set-zmm reg val (set-mxcsr mxcsr x86)))
  :hints (("Goal" :in-theory (enable set-mxcsr set-zmm))))

;; not clear which we want to pull forward, so we treat set-zmm like set-rax
(defthm write-byte-of-set-zmm
  (equal (write-byte addr val (set-zmm i val2 x86))
         (set-zmm i val2 (write-byte addr val x86)))
  :hints (("Goal" :in-theory (enable set-zmm write-byte))))

(defthm write-of-set-zmm
  (equal (write n addr val (set-zmm i val2 x86))
         (set-zmm i val2 (write n addr val x86)))
  :hints (("Goal" :in-theory (enable write))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm set-zmm-of-set-rip (equal (set-zmm reg val (set-rip rip x86)) (set-rip rip (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-rax (equal (set-zmm reg val (set-rax rax x86)) (set-rax rax (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-rbx (equal (set-zmm reg val (set-rbx rbx x86)) (set-rbx rbx (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-rcx (equal (set-zmm reg val (set-rcx rcx x86)) (set-rcx rcx (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-rdx (equal (set-zmm reg val (set-rdx rdx x86)) (set-rdx rdx (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-rsi (equal (set-zmm reg val (set-rsi rsi x86)) (set-rsi rsi (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-rdi (equal (set-zmm reg val (set-rdi rdi x86)) (set-rdi rdi (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-r8 (equal (set-zmm reg val (set-r8 r8 x86)) (set-r8 r8 (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-r9 (equal (set-zmm reg val (set-r9 r9 x86)) (set-r9 r9 (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-r10 (equal (set-zmm reg val (set-r10 r10 x86)) (set-r10 r10 (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-r11 (equal (set-zmm reg val (set-r11 r11 x86)) (set-r11 r11 (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-r12 (equal (set-zmm reg val (set-r12 r12 x86)) (set-r12 r12 (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-r13 (equal (set-zmm reg val (set-r13 r13 x86)) (set-r13 r13 (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-r14 (equal (set-zmm reg val (set-r14 r14 x86)) (set-r14 r14 (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-r15 (equal (set-zmm reg val (set-r15 r15 x86)) (set-r15 r15 (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-rbp (equal (set-zmm reg val (set-rbp rbp x86)) (set-rbp rbp (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
(defthm set-zmm-of-set-rsp (equal (set-zmm reg val (set-rsp rsp x86)) (set-rsp rsp (set-zmm reg val x86))) :hints (("Goal" :in-theory (enable set-zmm))))
