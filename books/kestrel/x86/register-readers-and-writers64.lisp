; A theory of register readers and writers (emphasis on readability of terms)
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book defines readers and writers for (64-bit) x86 registers, such as
;; RAX, RSP, etc.  It aims for maximum brevity and clarity, so to access RAX,
;; one simply calls (rax <x86>).  Instead, we could define a general function,
;; get-reg, and say something like (get-reg :rax <x86>).  This would allow us
;; to prove fewer rules about "read over write" and similar properties, at the
;; cost of making proof terms a bit bigger and a bit less readable.

(include-book "projects/x86isa/machine/state" :dir :system) ;for xr
(include-book "kestrel/utilities/myif" :dir :system)
(include-book "readers-and-writers64") ; drop?
(include-book "readers-and-writers")
(include-book "kestrel/bv/logext-def" :dir :system)
(include-book "kestrel/bv/bvcat-def" :dir :system)
(include-book "kestrel/bv/slice-def" :dir :system)
(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "kestrel/bv/signed-byte-p" :dir :system))
(local (include-book "kestrel/bv/bitops" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))

(in-theory (disable xw logext))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Register readers.
;; When we need an ordering on registers, we can use the order given here.
;; NOTE: Unlike the model's accessors, these accessors return unsigned-bytes:
(defund rax (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *rax* x86)))
(defund rbx (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *rbx* x86)))
(defund rcx (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *rcx* x86)))
(defund rdx (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *rdx* x86)))
(defund rsi (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *rsi* x86)))
(defund rdi (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *rdi* x86)))
(defund r8 (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *r8* x86)))
(defund r9 (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *r9* x86)))
(defund r10 (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *r10* x86)))
(defund r11 (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *r11* x86)))
(defund r12 (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *r12* x86)))
(defund r13 (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *r13* x86)))
(defund r14 (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *r14* x86)))
(defund r15 (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *r15* x86)))
(defund rsp (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *rsp* x86)))
(defund rbp (x86) (declare (xargs :stobjs x86)) (bvchop 64 (rgfi *rbp* x86)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm integerp-of-rax (implies (x86p x86) (integerp (rax x86))) :hints (("Goal" :in-theory (enable rax))))
(defthm integerp-of-rbx (implies (x86p x86) (integerp (rbx x86))) :hints (("Goal" :in-theory (enable rbx))))
(defthm integerp-of-rcx (implies (x86p x86) (integerp (rcx x86))) :hints (("Goal" :in-theory (enable rcx))))
(defthm integerp-of-rdx (implies (x86p x86) (integerp (rdx x86))) :hints (("Goal" :in-theory (enable rdx))))
(defthm integerp-of-rsi (implies (x86p x86) (integerp (rsi x86))) :hints (("Goal" :in-theory (enable rsi))))
(defthm integerp-of-rdi (implies (x86p x86) (integerp (rdi x86))) :hints (("Goal" :in-theory (enable rdi))))
(defthm integerp-of-r8 (implies (x86p x86) (integerp (r8 x86))) :hints (("Goal" :in-theory (enable r8))))
(defthm integerp-of-r9 (implies (x86p x86) (integerp (r9 x86))) :hints (("Goal" :in-theory (enable r9))))
(defthm integerp-of-r10 (implies (x86p x86) (integerp (r10 x86))) :hints (("Goal" :in-theory (enable r10))))
(defthm integerp-of-r11 (implies (x86p x86) (integerp (r11 x86))) :hints (("Goal" :in-theory (enable r11))))
(defthm integerp-of-r12 (implies (x86p x86) (integerp (r12 x86))) :hints (("Goal" :in-theory (enable r12))))
(defthm integerp-of-r13 (implies (x86p x86) (integerp (r13 x86))) :hints (("Goal" :in-theory (enable r13))))
(defthm integerp-of-r14 (implies (x86p x86) (integerp (r14 x86))) :hints (("Goal" :in-theory (enable r14))))
(defthm integerp-of-r15 (implies (x86p x86) (integerp (r15 x86))) :hints (("Goal" :in-theory (enable r15))))
(defthm integerp-of-rsp (implies (x86p x86) (integerp (rsp x86))) :hints (("Goal" :in-theory (enable rsp))))
(defthm integerp-of-rbp (implies (x86p x86) (integerp (rbp x86))) :hints (("Goal" :in-theory (enable rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm unsigned-byte-p-64-of-rax (unsigned-byte-p 64 (rax x86)) :hints (("Goal" :in-theory (enable rax))))
(defthm unsigned-byte-p-64-of-rbx (unsigned-byte-p 64 (rbx x86)) :hints (("Goal" :in-theory (enable rbx))))
(defthm unsigned-byte-p-64-of-rcx (unsigned-byte-p 64 (rcx x86)) :hints (("Goal" :in-theory (enable rcx))))
(defthm unsigned-byte-p-64-of-rdx (unsigned-byte-p 64 (rdx x86)) :hints (("Goal" :in-theory (enable rdx))))
(defthm unsigned-byte-p-64-of-rsi (unsigned-byte-p 64 (rsi x86)) :hints (("Goal" :in-theory (enable rsi))))
(defthm unsigned-byte-p-64-of-rdi (unsigned-byte-p 64 (rdi x86)) :hints (("Goal" :in-theory (enable rdi))))
(defthm unsigned-byte-p-64-of-r8 (unsigned-byte-p 64 (r8 x86)) :hints (("Goal" :in-theory (enable r8))))
(defthm unsigned-byte-p-64-of-r9 (unsigned-byte-p 64 (r9 x86)) :hints (("Goal" :in-theory (enable r9))))
(defthm unsigned-byte-p-64-of-r10 (unsigned-byte-p 64 (r10 x86)) :hints (("Goal" :in-theory (enable r10))))
(defthm unsigned-byte-p-64-of-r11 (unsigned-byte-p 64 (r11 x86)) :hints (("Goal" :in-theory (enable r11))))
(defthm unsigned-byte-p-64-of-r12 (unsigned-byte-p 64 (r12 x86)) :hints (("Goal" :in-theory (enable r12))))
(defthm unsigned-byte-p-64-of-r13 (unsigned-byte-p 64 (r13 x86)) :hints (("Goal" :in-theory (enable r13))))
(defthm unsigned-byte-p-64-of-r14 (unsigned-byte-p 64 (r14 x86)) :hints (("Goal" :in-theory (enable r14))))
(defthm unsigned-byte-p-64-of-r15 (unsigned-byte-p 64 (r15 x86)) :hints (("Goal" :in-theory (enable r15))))
(defthm unsigned-byte-p-64-of-rsp (unsigned-byte-p 64 (rsp x86)) :hints (("Goal" :in-theory (enable rsp))))
(defthm unsigned-byte-p-64-of-rbp (unsigned-byte-p 64 (rbp x86)) :hints (("Goal" :in-theory (enable rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm fix-of-rax (equal (fix (rax x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax))))
(defthm fix-of-rbx (equal (fix (rbx x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx))))
(defthm fix-of-rcx (equal (fix (rcx x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx))))
(defthm fix-of-rdx (equal (fix (rdx x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx))))
(defthm fix-of-rsi (equal (fix (rsi x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi))))
(defthm fix-of-rdi (equal (fix (rdi x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi))))
(defthm fix-of-r8 (equal (fix (r8 x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8))))
(defthm fix-of-r9 (equal (fix (r9 x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9))))
(defthm fix-of-r10 (equal (fix (r10 x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10))))
(defthm fix-of-r11 (equal (fix (r11 x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11))))
(defthm fix-of-r12 (equal (fix (r12 x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12))))
(defthm fix-of-r13 (equal (fix (r13 x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13))))
(defthm fix-of-r14 (equal (fix (r14 x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14))))
(defthm fix-of-r15 (equal (fix (r15 x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15))))
(defthm fix-of-rsp (equal (fix (rsp x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp))))
(defthm fix-of-rbp (equal (fix (rbp x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Register writers:
;; NOTE: Unlike the model's accessors, these take unsigned-bytes
(defund set-rax (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *rax* (logext 64 val) x86))
(defund set-rbx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *rbx* (logext 64 val) x86))
(defund set-rcx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *rcx* (logext 64 val) x86))
(defund set-rdx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *rdx* (logext 64 val) x86))
(defund set-rsi (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *rsi* (logext 64 val) x86))
(defund set-rdi (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *rdi* (logext 64 val) x86))
(defund set-r8 (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *r8* (logext 64 val) x86))
(defund set-r9 (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *r9* (logext 64 val) x86))
(defund set-r10 (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *r10* (logext 64 val) x86))
(defund set-r11 (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *r11* (logext 64 val) x86))
(defund set-r12 (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *r12* (logext 64 val) x86))
(defund set-r13 (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *r13* (logext 64 val) x86))
(defund set-r14 (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *r14* (logext 64 val) x86))
(defund set-r15 (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *r15* (logext 64 val) x86))
(defund set-rsp (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *rsp* (logext 64 val) x86))
(defund set-rbp (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 64 val))) (!rgfi *rbp* (logext 64 val) x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Introduce the register readers:
(defthmd xr-becomes-rax (equal (xr :rgf *rax* x86) (logext 64 (rax x86))) :hints (("Goal" :in-theory (enable rax))))
(defthmd xr-becomes-rbx (equal (xr :rgf *rbx* x86) (logext 64 (rbx x86))) :hints (("Goal" :in-theory (enable rbx))))
(defthmd xr-becomes-rcx (equal (xr :rgf *rcx* x86) (logext 64 (rcx x86))) :hints (("Goal" :in-theory (enable rcx))))
(defthmd xr-becomes-rdx (equal (xr :rgf *rdx* x86) (logext 64 (rdx x86))) :hints (("Goal" :in-theory (enable rdx))))
(defthmd xr-becomes-rsi (equal (xr :rgf *rsi* x86) (logext 64 (rsi x86))) :hints (("Goal" :in-theory (enable rsi))))
(defthmd xr-becomes-rdi (equal (xr :rgf *rdi* x86) (logext 64 (rdi x86))) :hints (("Goal" :in-theory (enable rdi))))
(defthmd xr-becomes-r8 (equal (xr :rgf *r8* x86) (logext 64 (r8 x86))) :hints (("Goal" :in-theory (enable r8))))
(defthmd xr-becomes-r9 (equal (xr :rgf *r9* x86) (logext 64 (r9 x86))) :hints (("Goal" :in-theory (enable r9))))
(defthmd xr-becomes-r10 (equal (xr :rgf *r10* x86) (logext 64 (r10 x86))) :hints (("Goal" :in-theory (enable r10))))
(defthmd xr-becomes-r11 (equal (xr :rgf *r11* x86) (logext 64 (r11 x86))) :hints (("Goal" :in-theory (enable r11))))
(defthmd xr-becomes-r12 (equal (xr :rgf *r12* x86) (logext 64 (r12 x86))) :hints (("Goal" :in-theory (enable r12))))
(defthmd xr-becomes-r13 (equal (xr :rgf *r13* x86) (logext 64 (r13 x86))) :hints (("Goal" :in-theory (enable r13))))
(defthmd xr-becomes-r14 (equal (xr :rgf *r14* x86) (logext 64 (r14 x86))) :hints (("Goal" :in-theory (enable r14))))
(defthmd xr-becomes-r15 (equal (xr :rgf *r15* x86) (logext 64 (r15 x86))) :hints (("Goal" :in-theory (enable r15))))
(defthmd xr-becomes-rsp (equal (xr :rgf *rsp* x86) (logext 64 (rsp x86))) :hints (("Goal" :in-theory (enable rsp))))
(defthmd xr-becomes-rbp (equal (xr :rgf *rbp* x86) (logext 64 (rbp x86))) :hints (("Goal" :in-theory (enable rbp))))

(theory-invariant (incompatible (:definition rax) (:rewrite xr-becomes-rax)))
(theory-invariant (incompatible (:definition rbx) (:rewrite xr-becomes-rbx)))
(theory-invariant (incompatible (:definition rcx) (:rewrite xr-becomes-rcx)))
(theory-invariant (incompatible (:definition rdx) (:rewrite xr-becomes-rdx)))
(theory-invariant (incompatible (:definition rsi) (:rewrite xr-becomes-rsi)))
(theory-invariant (incompatible (:definition rdi) (:rewrite xr-becomes-rdi)))
(theory-invariant (incompatible (:definition r8) (:rewrite xr-becomes-r8)))
(theory-invariant (incompatible (:definition r9) (:rewrite xr-becomes-r9)))
(theory-invariant (incompatible (:definition r10) (:rewrite xr-becomes-r10)))
(theory-invariant (incompatible (:definition r11) (:rewrite xr-becomes-r11)))
(theory-invariant (incompatible (:definition r12) (:rewrite xr-becomes-r12)))
(theory-invariant (incompatible (:definition r13) (:rewrite xr-becomes-r13)))
(theory-invariant (incompatible (:definition r14) (:rewrite xr-becomes-r14)))
(theory-invariant (incompatible (:definition r15) (:rewrite xr-becomes-r15)))
(theory-invariant (incompatible (:definition rsp) (:rewrite xr-becomes-rsp)))
(theory-invariant (incompatible (:definition rbp) (:rewrite xr-becomes-rbp)))

;; These go in one step:
(defthmd rgfi-becomes-rax (equal (rgfi *rax* x86) (logext 64 (rax x86))) :hints (("Goal" :in-theory (enable rax))))
(defthmd rgfi-becomes-rbx (equal (rgfi *rbx* x86) (logext 64 (rbx x86))) :hints (("Goal" :in-theory (enable rbx))))
(defthmd rgfi-becomes-rcx (equal (rgfi *rcx* x86) (logext 64 (rcx x86))) :hints (("Goal" :in-theory (enable rcx))))
(defthmd rgfi-becomes-rdx (equal (rgfi *rdx* x86) (logext 64 (rdx x86))) :hints (("Goal" :in-theory (enable rdx))))
(defthmd rgfi-becomes-rsi (equal (rgfi *rsi* x86) (logext 64 (rsi x86))) :hints (("Goal" :in-theory (enable rsi))))
(defthmd rgfi-becomes-rdi (equal (rgfi *rdi* x86) (logext 64 (rdi x86))) :hints (("Goal" :in-theory (enable rdi))))
(defthmd rgfi-becomes-r8 (equal (rgfi *r8* x86) (logext 64 (r8 x86))) :hints (("Goal" :in-theory (enable r8))))
(defthmd rgfi-becomes-r9 (equal (rgfi *r9* x86) (logext 64 (r9 x86))) :hints (("Goal" :in-theory (enable r9))))
(defthmd rgfi-becomes-r10 (equal (rgfi *r10* x86) (logext 64 (r10 x86))) :hints (("Goal" :in-theory (enable r10))))
(defthmd rgfi-becomes-r11 (equal (rgfi *r11* x86) (logext 64 (r11 x86))) :hints (("Goal" :in-theory (enable r11))))
(defthmd rgfi-becomes-r12 (equal (rgfi *r12* x86) (logext 64 (r12 x86))) :hints (("Goal" :in-theory (enable r12))))
(defthmd rgfi-becomes-r13 (equal (rgfi *r13* x86) (logext 64 (r13 x86))) :hints (("Goal" :in-theory (enable r13))))
(defthmd rgfi-becomes-r14 (equal (rgfi *r14* x86) (logext 64 (r14 x86))) :hints (("Goal" :in-theory (enable r14))))
(defthmd rgfi-becomes-r15 (equal (rgfi *r15* x86) (logext 64 (r15 x86))) :hints (("Goal" :in-theory (enable r15))))
(defthmd rgfi-becomes-rsp (equal (rgfi *rsp* x86) (logext 64 (rsp x86))) :hints (("Goal" :in-theory (enable rsp))))
(defthmd rgfi-becomes-rbp (equal (rgfi *rbp* x86) (logext 64 (rbp x86))) :hints (("Goal" :in-theory (enable rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Introduce the register writers:
(defthm xw-of-rgf-and-logext-64 (equal (xw :rgf reg (logext 64 val) x86)  (xw :rgf reg val x86)) :hints (("Goal" :in-theory (enable xw))))
(defthm xw-of-rgf-and-bvchop-64 (equal (xw :rgf reg (bvchop 64 val) x86)  (xw :rgf reg val x86)) :hints (("Goal" :in-theory (enable xw))))

(defthmd xw-becomes-set-rax (equal (xw :rgf *rax* val x86) (set-rax (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthmd xw-becomes-set-rbx (equal (xw :rgf *rbx* val x86) (set-rbx (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthmd xw-becomes-set-rcx (equal (xw :rgf *rcx* val x86) (set-rcx (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthmd xw-becomes-set-rdx (equal (xw :rgf *rdx* val x86) (set-rdx (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthmd xw-becomes-set-rsi (equal (xw :rgf *rsi* val x86) (set-rsi (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthmd xw-becomes-set-rdi (equal (xw :rgf *rdi* val x86) (set-rdi (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthmd xw-becomes-set-r8 (equal (xw :rgf *r8* val x86) (set-r8 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthmd xw-becomes-set-r9 (equal (xw :rgf *r9* val x86) (set-r9 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthmd xw-becomes-set-r10 (equal (xw :rgf *r10* val x86) (set-r10 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthmd xw-becomes-set-r11 (equal (xw :rgf *r11* val x86) (set-r11 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthmd xw-becomes-set-r12 (equal (xw :rgf *r12* val x86) (set-r12 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthmd xw-becomes-set-r13 (equal (xw :rgf *r13* val x86) (set-r13 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthmd xw-becomes-set-r14 (equal (xw :rgf *r14* val x86) (set-r14 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthmd xw-becomes-set-r15 (equal (xw :rgf *r15* val x86) (set-r15 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthmd xw-becomes-set-rsp (equal (xw :rgf *rsp* val x86) (set-rsp (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthmd xw-becomes-set-rbp (equal (xw :rgf *rbp* val x86) (set-rbp (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rbp))))

(theory-invariant (incompatible (:definition set-rax) (:rewrite xw-becomes-set-rax)))
(theory-invariant (incompatible (:definition set-rbx) (:rewrite xw-becomes-set-rbx)))
(theory-invariant (incompatible (:definition set-rcx) (:rewrite xw-becomes-set-rcx)))
(theory-invariant (incompatible (:definition set-rdx) (:rewrite xw-becomes-set-rdx)))
(theory-invariant (incompatible (:definition set-rsi) (:rewrite xw-becomes-set-rsi)))
(theory-invariant (incompatible (:definition set-rdi) (:rewrite xw-becomes-set-rdi)))
(theory-invariant (incompatible (:definition set-r8) (:rewrite xw-becomes-set-r8)))
(theory-invariant (incompatible (:definition set-r9) (:rewrite xw-becomes-set-r9)))
(theory-invariant (incompatible (:definition set-r10) (:rewrite xw-becomes-set-r10)))
(theory-invariant (incompatible (:definition set-r11) (:rewrite xw-becomes-set-r11)))
(theory-invariant (incompatible (:definition set-r12) (:rewrite xw-becomes-set-r12)))
(theory-invariant (incompatible (:definition set-r13) (:rewrite xw-becomes-set-r13)))
(theory-invariant (incompatible (:definition set-r14) (:rewrite xw-becomes-set-r14)))
(theory-invariant (incompatible (:definition set-r15) (:rewrite xw-becomes-set-r15)))
(theory-invariant (incompatible (:definition set-rsp) (:rewrite xw-becomes-set-rsp)))
(theory-invariant (incompatible (:definition set-rbp) (:rewrite xw-becomes-set-rbp)))

(defthmd !rgfi-becomes-set-rax (equal (!rgfi *rax* val x86) (set-rax (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthmd !rgfi-becomes-set-rbx (equal (!rgfi *rbx* val x86) (set-rbx (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthmd !rgfi-becomes-set-rcx (equal (!rgfi *rcx* val x86) (set-rcx (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthmd !rgfi-becomes-set-rdx (equal (!rgfi *rdx* val x86) (set-rdx (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthmd !rgfi-becomes-set-rsi (equal (!rgfi *rsi* val x86) (set-rsi (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthmd !rgfi-becomes-set-rdi (equal (!rgfi *rdi* val x86) (set-rdi (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthmd !rgfi-becomes-set-r8 (equal (!rgfi *r8* val x86) (set-r8 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthmd !rgfi-becomes-set-r9 (equal (!rgfi *r9* val x86) (set-r9 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthmd !rgfi-becomes-set-r10 (equal (!rgfi *r10* val x86) (set-r10 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthmd !rgfi-becomes-set-r11 (equal (!rgfi *r11* val x86) (set-r11 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthmd !rgfi-becomes-set-r12 (equal (!rgfi *r12* val x86) (set-r12 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthmd !rgfi-becomes-set-r13 (equal (!rgfi *r13* val x86) (set-r13 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthmd !rgfi-becomes-set-r14 (equal (!rgfi *r14* val x86) (set-r14 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthmd !rgfi-becomes-set-r15 (equal (!rgfi *r15* val x86) (set-r15 (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthmd !rgfi-becomes-set-rsp (equal (!rgfi *rsp* val x86) (set-rsp (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthmd !rgfi-becomes-set-rbp (equal (!rgfi *rbp* val x86) (set-rbp (bvchop 64 val) x86)) :hints (("Goal" :in-theory (enable set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Read-of-write of the same register:
(defthm rax-of-set-rax (equal (rax (set-rax val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable rax set-rax))))
(defthm rbx-of-set-rbx (equal (rbx (set-rbx val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable rbx set-rbx))))
(defthm rcx-of-set-rcx (equal (rcx (set-rcx val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable rcx set-rcx))))
(defthm rdx-of-set-rdx (equal (rdx (set-rdx val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable rdx set-rdx))))
(defthm rsi-of-set-rsi (equal (rsi (set-rsi val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable rsi set-rsi))))
(defthm rdi-of-set-rdi (equal (rdi (set-rdi val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable rdi set-rdi))))
(defthm r8-of-set-r8 (equal (r8 (set-r8 val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable r8 set-r8))))
(defthm r9-of-set-r9 (equal (r9 (set-r9 val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable r9 set-r9))))
(defthm r10-of-set-r10 (equal (r10 (set-r10 val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable r10 set-r10))))
(defthm r11-of-set-r11 (equal (r11 (set-r11 val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable r11 set-r11))))
(defthm r12-of-set-r12 (equal (r12 (set-r12 val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable r12 set-r12))))
(defthm r13-of-set-r13 (equal (r13 (set-r13 val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable r13 set-r13))))
(defthm r14-of-set-r14 (equal (r14 (set-r14 val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable r14 set-r14))))
(defthm r15-of-set-r15 (equal (r15 (set-r15 val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable r15 set-r15))))
(defthm rsp-of-set-rsp (equal (rsp (set-rsp val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable rsp set-rsp))))
(defthm rbp-of-set-rbp (equal (rbp (set-rbp val x86)) (bvchop 64 val)) :hints (("Goal" :in-theory (enable rbp set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Write-of-write of the same register:
(defthm set-rax-of-set-rax (equal (set-rax rax1 (set-rax rax2 x86)) (set-rax rax1 x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm set-rbx-of-set-rbx (equal (set-rbx rbx1 (set-rbx rbx2 x86)) (set-rbx rbx1 x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm set-rcx-of-set-rcx (equal (set-rcx rcx1 (set-rcx rcx2 x86)) (set-rcx rcx1 x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm set-rdx-of-set-rdx (equal (set-rdx rdx1 (set-rdx rdx2 x86)) (set-rdx rdx1 x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm set-rsi-of-set-rsi (equal (set-rsi rsi1 (set-rsi rsi2 x86)) (set-rsi rsi1 x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm set-rdi-of-set-rdi (equal (set-rdi rdi1 (set-rdi rdi2 x86)) (set-rdi rdi1 x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm set-r8-of-set-r8 (equal (set-r8 r81 (set-r8 r82 x86)) (set-r8 r81 x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm set-r9-of-set-r9 (equal (set-r9 r91 (set-r9 r92 x86)) (set-r9 r91 x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm set-r10-of-set-r10 (equal (set-r10 r101 (set-r10 r102 x86)) (set-r10 r101 x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm set-r11-of-set-r11 (equal (set-r11 r111 (set-r11 r112 x86)) (set-r11 r111 x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm set-r12-of-set-r12 (equal (set-r12 r121 (set-r12 r122 x86)) (set-r12 r121 x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm set-r13-of-set-r13 (equal (set-r13 r131 (set-r13 r132 x86)) (set-r13 r131 x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm set-r14-of-set-r14 (equal (set-r14 r141 (set-r14 r142 x86)) (set-r14 r141 x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm set-r15-of-set-r15 (equal (set-r15 r151 (set-r15 r152 x86)) (set-r15 r151 x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm set-rsp-of-set-rsp (equal (set-rsp rsp1 (set-rsp rsp2 x86)) (set-rsp rsp1 x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm set-rbp-of-set-rbp (equal (set-rbp rbp1 (set-rbp rbp2 x86)) (set-rbp rbp1 x86)) :hints (("Goal" :in-theory (enable set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Write-of-read of the same register (but see the -gen rules below that match better).
(defthm set-rax-of-rax-same (equal (set-rax (rax x86) x86) x86) :hints (("Goal" :in-theory (enable rax set-rax))))
(defthm set-rbx-of-rbx-same (equal (set-rbx (rbx x86) x86) x86) :hints (("Goal" :in-theory (enable rbx set-rbx))))
(defthm set-rcx-of-rcx-same (equal (set-rcx (rcx x86) x86) x86) :hints (("Goal" :in-theory (enable rcx set-rcx))))
(defthm set-rdx-of-rdx-same (equal (set-rdx (rdx x86) x86) x86) :hints (("Goal" :in-theory (enable rdx set-rdx))))
(defthm set-rdi-of-rdi-same (equal (set-rdi (rdi x86) x86) x86) :hints (("Goal" :in-theory (enable rdi set-rdi))))
(defthm set-rsi-of-rsi-same (equal (set-rsi (rsi x86) x86) x86) :hints (("Goal" :in-theory (enable rsi set-rsi))))
(defthm set-r8-of-r8-same (equal (set-r8 (r8 x86) x86) x86) :hints (("Goal" :in-theory (enable r8 set-r8))))
(defthm set-r9-of-r9-same (equal (set-r9 (r9 x86) x86) x86) :hints (("Goal" :in-theory (enable r9 set-r9))))
(defthm set-r10-of-r10-same (equal (set-r10 (r10 x86) x86) x86) :hints (("Goal" :in-theory (enable r10 set-r10))))
(defthm set-r11-of-r11-same (equal (set-r11 (r11 x86) x86) x86) :hints (("Goal" :in-theory (enable r11 set-r11))))
(defthm set-r12-of-r12-same (equal (set-r12 (r12 x86) x86) x86) :hints (("Goal" :in-theory (enable r12 set-r12))))
(defthm set-r13-of-r13-same (equal (set-r13 (r13 x86) x86) x86) :hints (("Goal" :in-theory (enable r13 set-r13))))
(defthm set-r14-of-r14-same (equal (set-r14 (r14 x86) x86) x86) :hints (("Goal" :in-theory (enable r14 set-r14))))
(defthm set-r15-of-r15-same (equal (set-r15 (r15 x86) x86) x86) :hints (("Goal" :in-theory (enable r15 set-r15))))
(defthm set-rsp-of-rsp-same (equal (set-rsp (rsp x86) x86) x86) :hints (("Goal" :in-theory (enable rsp set-rsp))))
(defthm set-rbp-of-rbp-same (equal (set-rbp (rbp x86) x86) x86) :hints (("Goal" :in-theory (enable rbp set-rbp))))

;; These match better than the rules just above, like set-rax-of-rax-same.
;; And they are probably cheaper than very generic rules about writing values that are already in the registers.
;; Here, x86 may often be the variable X86, whereas x86_2 may often be some
;; updated state (with the given register unchanged).
;; The rule for RBP here is especially useful, since RBP is commonly saved and
;; restored.  The rules for other callee-saved registers are also likely to be
;; useful (I suppose we could wait to apply these until the very end of the symbolic execution).
(defthm set-rax-of-rax-same-gen (implies (equal (rax x86) (rax x86_2)) (equal (set-rax (rax x86) x86_2) x86_2)))
(defthm set-rbx-of-rbx-same-gen (implies (equal (rbx x86) (rbx x86_2)) (equal (set-rbx (rbx x86) x86_2) x86_2)))
(defthm set-rcx-of-rcx-same-gen (implies (equal (rcx x86) (rcx x86_2)) (equal (set-rcx (rcx x86) x86_2) x86_2)))
(defthm set-rdx-of-rdx-same-gen (implies (equal (rdx x86) (rdx x86_2)) (equal (set-rdx (rdx x86) x86_2) x86_2)))
(defthm set-rdi-of-rdi-same-gen (implies (equal (rdi x86) (rdi x86_2)) (equal (set-rdi (rdi x86) x86_2) x86_2)))
(defthm set-rsi-of-rsi-same-gen (implies (equal (rsi x86) (rsi x86_2)) (equal (set-rsi (rsi x86) x86_2) x86_2)))
(defthm set-r8-of-r8-same-gen (implies (equal (r8 x86) (r8 x86_2)) (equal (set-r8 (r8 x86) x86_2) x86_2)))
(defthm set-r9-of-r9-same-gen (implies (equal (r9 x86) (r9 x86_2)) (equal (set-r9 (r9 x86) x86_2) x86_2)))
(defthm set-r10-of-r10-same-gen (implies (equal (r10 x86) (r10 x86_2)) (equal (set-r10 (r10 x86) x86_2) x86_2)))
(defthm set-r11-of-r11-same-gen (implies (equal (r11 x86) (r11 x86_2)) (equal (set-r11 (r11 x86) x86_2) x86_2)))
(defthm set-r12-of-r12-same-gen (implies (equal (r12 x86) (r12 x86_2)) (equal (set-r12 (r12 x86) x86_2) x86_2)))
(defthm set-r13-of-r13-same-gen (implies (equal (r13 x86) (r13 x86_2)) (equal (set-r13 (r13 x86) x86_2) x86_2)))
(defthm set-r14-of-r14-same-gen (implies (equal (r14 x86) (r14 x86_2)) (equal (set-r14 (r14 x86) x86_2) x86_2)))
(defthm set-r15-of-r15-same-gen (implies (equal (r15 x86) (r15 x86_2)) (equal (set-r15 (r15 x86) x86_2) x86_2)))
(defthm set-rsp-of-rsp-same-gen (implies (equal (rsp x86) (rsp x86_2)) (equal (set-rsp (rsp x86) x86_2) x86_2)))
(defthm set-rbp-of-rbp-same-gen (implies (equal (rbp x86) (rbp x86_2)) (equal (set-rbp (rbp x86) x86_2) x86_2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; <reg> of set-rip:

(defthm rax-of-set-rip (equal (rax (set-rip rip x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax))))
(defthm rbx-of-set-rip (equal (rbx (set-rip rip x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx))))
(defthm rcx-of-set-rip (equal (rcx (set-rip rip x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx))))
(defthm rdx-of-set-rip (equal (rdx (set-rip rip x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx))))
(defthm rsi-of-set-rip (equal (rsi (set-rip rip x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi))))
(defthm rdi-of-set-rip (equal (rdi (set-rip rip x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi))))
(defthm r8-of-set-rip (equal (r8 (set-rip rip x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8))))
(defthm r9-of-set-rip (equal (r9 (set-rip rip x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9))))
(defthm r10-of-set-rip (equal (r10 (set-rip rip x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10))))
(defthm r11-of-set-rip (equal (r11 (set-rip rip x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11))))
(defthm r12-of-set-rip (equal (r12 (set-rip rip x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12))))
(defthm r13-of-set-rip (equal (r13 (set-rip rip x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13))))
(defthm r14-of-set-rip (equal (r14 (set-rip rip x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14))))
(defthm r15-of-set-rip (equal (r15 (set-rip rip x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15))))
(defthm rsp-of-set-rip (equal (rsp (set-rip rip x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp))))
(defthm rbp-of-set-rip (equal (rbp (set-rip rip x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; rip of set-<reg>:

(defthm rip-of-set-rax (equal (rip (set-rax rax x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm rip-of-set-rbx (equal (rip (set-rbx rbx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm rip-of-set-rcx (equal (rip (set-rcx rcx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm rip-of-set-rdx (equal (rip (set-rdx rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm rip-of-set-rsi (equal (rip (set-rsi rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm rip-of-set-rdi (equal (rip (set-rdi rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm rip-of-set-r8 (equal (rip (set-r8 rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm rip-of-set-r9 (equal (rip (set-r9 rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm rip-of-set-r10 (equal (rip (set-r10 rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm rip-of-set-r11 (equal (rip (set-r11 rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm rip-of-set-r12 (equal (rip (set-r12 rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm rip-of-set-r13 (equal (rip (set-r13 rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm rip-of-set-r14 (equal (rip (set-r14 rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm rip-of-set-r15 (equal (rip (set-r15 rdx x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm rip-of-set-rsp (equal (rip (set-rsp rsp x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm rip-of-set-rbp (equal (rip (set-rbp rbp x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Read of a write of a different register

(defthm rax-of-set-rbx (equal (rax (set-rbx val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-rbx))))
(defthm rax-of-set-rcx (equal (rax (set-rcx val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-rcx))))
(defthm rax-of-set-rdx (equal (rax (set-rdx val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-rdx))))
(defthm rax-of-set-rsi (equal (rax (set-rsi val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-rsi))))
(defthm rax-of-set-rdi (equal (rax (set-rdi val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-rdi))))
(defthm rax-of-set-r8 (equal (rax (set-r8 val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-r8))))
(defthm rax-of-set-r9 (equal (rax (set-r9 val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-r9))))
(defthm rax-of-set-r10 (equal (rax (set-r10 val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-r10))))
(defthm rax-of-set-r11 (equal (rax (set-r11 val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-r11))))
(defthm rax-of-set-r12 (equal (rax (set-r12 val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-r12))))
(defthm rax-of-set-r13 (equal (rax (set-r13 val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-r13))))
(defthm rax-of-set-r14 (equal (rax (set-r14 val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-r14))))
(defthm rax-of-set-r15 (equal (rax (set-r15 val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-r15))))
(defthm rax-of-set-rsp (equal (rax (set-rsp val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-rsp))))
(defthm rax-of-set-rbp (equal (rax (set-rbp val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-rbp))))

(defthm rbx-of-set-rax (equal (rbx (set-rax val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-rax))))
(defthm rbx-of-set-rcx (equal (rbx (set-rcx val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-rcx))))
(defthm rbx-of-set-rdx (equal (rbx (set-rdx val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-rdx))))
(defthm rbx-of-set-rsi (equal (rbx (set-rsi val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-rsi))))
(defthm rbx-of-set-rdi (equal (rbx (set-rdi val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-rdi))))
(defthm rbx-of-set-r8 (equal (rbx (set-r8 val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-r8))))
(defthm rbx-of-set-r9 (equal (rbx (set-r9 val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-r9))))
(defthm rbx-of-set-r10 (equal (rbx (set-r10 val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-r10))))
(defthm rbx-of-set-r11 (equal (rbx (set-r11 val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-r11))))
(defthm rbx-of-set-r12 (equal (rbx (set-r12 val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-r12))))
(defthm rbx-of-set-r13 (equal (rbx (set-r13 val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-r13))))
(defthm rbx-of-set-r14 (equal (rbx (set-r14 val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-r14))))
(defthm rbx-of-set-r15 (equal (rbx (set-r15 val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-r15))))
(defthm rbx-of-set-rsp (equal (rbx (set-rsp val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-rsp))))
(defthm rbx-of-set-rbp (equal (rbx (set-rbp val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-rbp))))

(defthm rcx-of-set-rax (equal (rcx (set-rax val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-rax))))
(defthm rcx-of-set-rbx (equal (rcx (set-rbx val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-rbx))))
(defthm rcx-of-set-rdx (equal (rcx (set-rdx val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-rdx))))
(defthm rcx-of-set-rsi (equal (rcx (set-rsi val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-rsi))))
(defthm rcx-of-set-rdi (equal (rcx (set-rdi val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-rdi))))
(defthm rcx-of-set-r8 (equal (rcx (set-r8 val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-r8))))
(defthm rcx-of-set-r9 (equal (rcx (set-r9 val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-r9))))
(defthm rcx-of-set-r10 (equal (rcx (set-r10 val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-r10))))
(defthm rcx-of-set-r11 (equal (rcx (set-r11 val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-r11))))
(defthm rcx-of-set-r12 (equal (rcx (set-r12 val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-r12))))
(defthm rcx-of-set-r13 (equal (rcx (set-r13 val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-r13))))
(defthm rcx-of-set-r14 (equal (rcx (set-r14 val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-r14))))
(defthm rcx-of-set-r15 (equal (rcx (set-r15 val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-r15))))
(defthm rcx-of-set-rsp (equal (rcx (set-rsp val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-rsp))))
(defthm rcx-of-set-rbp (equal (rcx (set-rbp val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-rbp))))

(defthm rdx-of-set-rax (equal (rdx (set-rax val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-rax))))
(defthm rdx-of-set-rbx (equal (rdx (set-rbx val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-rbx))))
(defthm rdx-of-set-rcx (equal (rdx (set-rcx val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-rcx))))
(defthm rdx-of-set-rsi (equal (rdx (set-rsi val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-rsi))))
(defthm rdx-of-set-rdi (equal (rdx (set-rdi val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-rdi))))
(defthm rdx-of-set-r8 (equal (rdx (set-r8 val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-r8))))
(defthm rdx-of-set-r9 (equal (rdx (set-r9 val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-r9))))
(defthm rdx-of-set-r10 (equal (rdx (set-r10 val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-r10))))
(defthm rdx-of-set-r11 (equal (rdx (set-r11 val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-r11))))
(defthm rdx-of-set-r12 (equal (rdx (set-r12 val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-r12))))
(defthm rdx-of-set-r13 (equal (rdx (set-r13 val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-r13))))
(defthm rdx-of-set-r14 (equal (rdx (set-r14 val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-r14))))
(defthm rdx-of-set-r15 (equal (rdx (set-r15 val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-r15))))
(defthm rdx-of-set-rsp (equal (rdx (set-rsp val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-rsp))))
(defthm rdx-of-set-rbp (equal (rdx (set-rbp val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-rbp))))

(defthm rsi-of-set-rax (equal (rsi (set-rax val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-rax))))
(defthm rsi-of-set-rbx (equal (rsi (set-rbx val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-rbx))))
(defthm rsi-of-set-rcx (equal (rsi (set-rcx val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-rcx))))
(defthm rsi-of-set-rdx (equal (rsi (set-rdx val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-rdx))))
(defthm rsi-of-set-rdi (equal (rsi (set-rdi val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-rdi))))
(defthm rsi-of-set-r8 (equal (rsi (set-r8 val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-r8))))
(defthm rsi-of-set-r9 (equal (rsi (set-r9 val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-r9))))
(defthm rsi-of-set-r10 (equal (rsi (set-r10 val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-r10))))
(defthm rsi-of-set-r11 (equal (rsi (set-r11 val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-r11))))
(defthm rsi-of-set-r12 (equal (rsi (set-r12 val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-r12))))
(defthm rsi-of-set-r13 (equal (rsi (set-r13 val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-r13))))
(defthm rsi-of-set-r14 (equal (rsi (set-r14 val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-r14))))
(defthm rsi-of-set-r15 (equal (rsi (set-r15 val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-r15))))
(defthm rsi-of-set-rsp (equal (rsi (set-rsp val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-rsp))))
(defthm rsi-of-set-rbp (equal (rsi (set-rbp val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-rbp))))

(defthm rdi-of-set-rax (equal (rdi (set-rax val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-rax))))
(defthm rdi-of-set-rbx (equal (rdi (set-rbx val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-rbx))))
(defthm rdi-of-set-rcx (equal (rdi (set-rcx val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-rcx))))
(defthm rdi-of-set-rdx (equal (rdi (set-rdx val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-rdx))))
(defthm rdi-of-set-rsi (equal (rdi (set-rsi val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-rsi))))
(defthm rdi-of-set-r8 (equal (rdi (set-r8 val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-r8))))
(defthm rdi-of-set-r9 (equal (rdi (set-r9 val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-r9))))
(defthm rdi-of-set-r10 (equal (rdi (set-r10 val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-r10))))
(defthm rdi-of-set-r11 (equal (rdi (set-r11 val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-r11))))
(defthm rdi-of-set-r12 (equal (rdi (set-r12 val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-r12))))
(defthm rdi-of-set-r13 (equal (rdi (set-r13 val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-r13))))
(defthm rdi-of-set-r14 (equal (rdi (set-r14 val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-r14))))
(defthm rdi-of-set-r15 (equal (rdi (set-r15 val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-r15))))
(defthm rdi-of-set-rsp (equal (rdi (set-rsp val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-rsp))))
(defthm rdi-of-set-rbp (equal (rdi (set-rbp val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-rbp))))

(defthm r8-of-set-rax (equal (r8 (set-rax val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-rax))))
(defthm r8-of-set-rbx (equal (r8 (set-rbx val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-rbx))))
(defthm r8-of-set-rcx (equal (r8 (set-rcx val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-rcx))))
(defthm r8-of-set-rdx (equal (r8 (set-rdx val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-rdx))))
(defthm r8-of-set-rsi (equal (r8 (set-rsi val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-rsi))))
(defthm r8-of-set-rdi (equal (r8 (set-rdi val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-rdi))))
(defthm r8-of-set-r9 (equal (r8 (set-r9 val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-r9))))
(defthm r8-of-set-r10 (equal (r8 (set-r10 val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-r10))))
(defthm r8-of-set-r11 (equal (r8 (set-r11 val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-r11))))
(defthm r8-of-set-r12 (equal (r8 (set-r12 val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-r12))))
(defthm r8-of-set-r13 (equal (r8 (set-r13 val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-r13))))
(defthm r8-of-set-r14 (equal (r8 (set-r14 val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-r14))))
(defthm r8-of-set-r15 (equal (r8 (set-r15 val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-r15))))
(defthm r8-of-set-rsp (equal (r8 (set-rsp val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-rsp))))
(defthm r8-of-set-rbp (equal (r8 (set-rbp val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-rbp))))

(defthm r9-of-set-rax (equal (r9 (set-rax val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-rax))))
(defthm r9-of-set-rbx (equal (r9 (set-rbx val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-rbx))))
(defthm r9-of-set-rcx (equal (r9 (set-rcx val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-rcx))))
(defthm r9-of-set-rdx (equal (r9 (set-rdx val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-rdx))))
(defthm r9-of-set-rsi (equal (r9 (set-rsi val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-rsi))))
(defthm r9-of-set-rdi (equal (r9 (set-rdi val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-rdi))))
(defthm r9-of-set-r8 (equal (r9 (set-r8 val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-r8))))
(defthm r9-of-set-r10 (equal (r9 (set-r10 val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-r10))))
(defthm r9-of-set-r11 (equal (r9 (set-r11 val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-r11))))
(defthm r9-of-set-r12 (equal (r9 (set-r12 val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-r12))))
(defthm r9-of-set-r13 (equal (r9 (set-r13 val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-r13))))
(defthm r9-of-set-r14 (equal (r9 (set-r14 val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-r14))))
(defthm r9-of-set-r15 (equal (r9 (set-r15 val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-r15))))
(defthm r9-of-set-rsp (equal (r9 (set-rsp val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-rsp))))
(defthm r9-of-set-rbp (equal (r9 (set-rbp val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-rbp))))

(defthm r10-of-set-rax (equal (r10 (set-rax val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-rax))))
(defthm r10-of-set-rbx (equal (r10 (set-rbx val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-rbx))))
(defthm r10-of-set-rcx (equal (r10 (set-rcx val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-rcx))))
(defthm r10-of-set-rdx (equal (r10 (set-rdx val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-rdx))))
(defthm r10-of-set-rsi (equal (r10 (set-rsi val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-rsi))))
(defthm r10-of-set-rdi (equal (r10 (set-rdi val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-rdi))))
(defthm r10-of-set-r8 (equal (r10 (set-r8 val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-r8))))
(defthm r10-of-set-r9 (equal (r10 (set-r9 val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-r9))))
(defthm r10-of-set-r11 (equal (r10 (set-r11 val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-r11))))
(defthm r10-of-set-r12 (equal (r10 (set-r12 val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-r12))))
(defthm r10-of-set-r13 (equal (r10 (set-r13 val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-r13))))
(defthm r10-of-set-r14 (equal (r10 (set-r14 val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-r14))))
(defthm r10-of-set-r15 (equal (r10 (set-r15 val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-r15))))
(defthm r10-of-set-rsp (equal (r10 (set-rsp val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-rsp))))
(defthm r10-of-set-rbp (equal (r10 (set-rbp val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-rbp))))

(defthm r11-of-set-rax (equal (r11 (set-rax val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-rax))))
(defthm r11-of-set-rbx (equal (r11 (set-rbx val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-rbx))))
(defthm r11-of-set-rcx (equal (r11 (set-rcx val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-rcx))))
(defthm r11-of-set-rdx (equal (r11 (set-rdx val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-rdx))))
(defthm r11-of-set-rsi (equal (r11 (set-rsi val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-rsi))))
(defthm r11-of-set-rdi (equal (r11 (set-rdi val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-rdi))))
(defthm r11-of-set-r8 (equal (r11 (set-r8 val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-r8))))
(defthm r11-of-set-r9 (equal (r11 (set-r9 val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-r9))))
(defthm r11-of-set-r10 (equal (r11 (set-r10 val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-r10))))
(defthm r11-of-set-r12 (equal (r11 (set-r12 val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-r12))))
(defthm r11-of-set-r13 (equal (r11 (set-r13 val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-r13))))
(defthm r11-of-set-r14 (equal (r11 (set-r14 val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-r14))))
(defthm r11-of-set-r15 (equal (r11 (set-r15 val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-r15))))
(defthm r11-of-set-rsp (equal (r11 (set-rsp val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-rsp))))
(defthm r11-of-set-rbp (equal (r11 (set-rbp val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-rbp))))

(defthm r12-of-set-rax (equal (r12 (set-rax val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-rax))))
(defthm r12-of-set-rbx (equal (r12 (set-rbx val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-rbx))))
(defthm r12-of-set-rcx (equal (r12 (set-rcx val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-rcx))))
(defthm r12-of-set-rdx (equal (r12 (set-rdx val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-rdx))))
(defthm r12-of-set-rsi (equal (r12 (set-rsi val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-rsi))))
(defthm r12-of-set-rdi (equal (r12 (set-rdi val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-rdi))))
(defthm r12-of-set-r8 (equal (r12 (set-r8 val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-r8))))
(defthm r12-of-set-r9 (equal (r12 (set-r9 val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-r9))))
(defthm r12-of-set-r10 (equal (r12 (set-r10 val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-r10))))
(defthm r12-of-set-r11 (equal (r12 (set-r11 val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-r11))))
(defthm r12-of-set-r13 (equal (r12 (set-r13 val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-r13))))
(defthm r12-of-set-r14 (equal (r12 (set-r14 val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-r14))))
(defthm r12-of-set-r15 (equal (r12 (set-r15 val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-r15))))
(defthm r12-of-set-rsp (equal (r12 (set-rsp val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-rsp))))
(defthm r12-of-set-rbp (equal (r12 (set-rbp val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-rbp))))

(defthm r13-of-set-rax (equal (r13 (set-rax val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-rax))))
(defthm r13-of-set-rbx (equal (r13 (set-rbx val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-rbx))))
(defthm r13-of-set-rcx (equal (r13 (set-rcx val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-rcx))))
(defthm r13-of-set-rdx (equal (r13 (set-rdx val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-rdx))))
(defthm r13-of-set-rsi (equal (r13 (set-rsi val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-rsi))))
(defthm r13-of-set-rdi (equal (r13 (set-rdi val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-rdi))))
(defthm r13-of-set-r8 (equal (r13 (set-r8 val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-r8))))
(defthm r13-of-set-r9 (equal (r13 (set-r9 val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-r9))))
(defthm r13-of-set-r10 (equal (r13 (set-r10 val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-r10))))
(defthm r13-of-set-r11 (equal (r13 (set-r11 val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-r11))))
(defthm r13-of-set-r12 (equal (r13 (set-r12 val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-r12))))
(defthm r13-of-set-r14 (equal (r13 (set-r14 val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-r14))))
(defthm r13-of-set-r15 (equal (r13 (set-r15 val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-r15))))
(defthm r13-of-set-rsp (equal (r13 (set-rsp val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-rsp))))
(defthm r13-of-set-rbp (equal (r13 (set-rbp val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-rbp))))

(defthm r14-of-set-rax (equal (r14 (set-rax val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-rax))))
(defthm r14-of-set-rbx (equal (r14 (set-rbx val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-rbx))))
(defthm r14-of-set-rcx (equal (r14 (set-rcx val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-rcx))))
(defthm r14-of-set-rdx (equal (r14 (set-rdx val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-rdx))))
(defthm r14-of-set-rsi (equal (r14 (set-rsi val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-rsi))))
(defthm r14-of-set-rdi (equal (r14 (set-rdi val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-rdi))))
(defthm r14-of-set-r8 (equal (r14 (set-r8 val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-r8))))
(defthm r14-of-set-r9 (equal (r14 (set-r9 val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-r9))))
(defthm r14-of-set-r10 (equal (r14 (set-r10 val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-r10))))
(defthm r14-of-set-r11 (equal (r14 (set-r11 val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-r11))))
(defthm r14-of-set-r12 (equal (r14 (set-r12 val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-r12))))
(defthm r14-of-set-r13 (equal (r14 (set-r13 val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-r13))))
(defthm r14-of-set-r15 (equal (r14 (set-r15 val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-r15))))
(defthm r14-of-set-rsp (equal (r14 (set-rsp val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-rsp))))
(defthm r14-of-set-rbp (equal (r14 (set-rbp val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-rbp))))

(defthm r15-of-set-rax (equal (r15 (set-rax val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-rax))))
(defthm r15-of-set-rbx (equal (r15 (set-rbx val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-rbx))))
(defthm r15-of-set-rcx (equal (r15 (set-rcx val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-rcx))))
(defthm r15-of-set-rdx (equal (r15 (set-rdx val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-rdx))))
(defthm r15-of-set-rsi (equal (r15 (set-rsi val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-rsi))))
(defthm r15-of-set-rdi (equal (r15 (set-rdi val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-rdi))))
(defthm r15-of-set-r8 (equal (r15 (set-r8 val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-r8))))
(defthm r15-of-set-r9 (equal (r15 (set-r9 val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-r9))))
(defthm r15-of-set-r10 (equal (r15 (set-r10 val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-r10))))
(defthm r15-of-set-r11 (equal (r15 (set-r11 val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-r11))))
(defthm r15-of-set-r12 (equal (r15 (set-r12 val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-r12))))
(defthm r15-of-set-r13 (equal (r15 (set-r13 val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-r13))))
(defthm r15-of-set-r14 (equal (r15 (set-r14 val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-r14))))
(defthm r15-of-set-rsp (equal (r15 (set-rsp val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-rsp))))
(defthm r15-of-set-rbp (equal (r15 (set-rbp val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-rbp))))

(defthm rsp-of-set-rax (equal (rsp (set-rax val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-rax))))
(defthm rsp-of-set-rbx (equal (rsp (set-rbx val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-rbx))))
(defthm rsp-of-set-rcx (equal (rsp (set-rcx val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-rcx))))
(defthm rsp-of-set-rdx (equal (rsp (set-rdx val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-rdx))))
(defthm rsp-of-set-rsi (equal (rsp (set-rsi val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-rsi))))
(defthm rsp-of-set-rdi (equal (rsp (set-rdi val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-rdi))))
(defthm rsp-of-set-r8 (equal (rsp (set-r8 val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-r8))))
(defthm rsp-of-set-r9 (equal (rsp (set-r9 val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-r9))))
(defthm rsp-of-set-r10 (equal (rsp (set-r10 val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-r10))))
(defthm rsp-of-set-r11 (equal (rsp (set-r11 val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-r11))))
(defthm rsp-of-set-r12 (equal (rsp (set-r12 val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-r12))))
(defthm rsp-of-set-r13 (equal (rsp (set-r13 val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-r13))))
(defthm rsp-of-set-r14 (equal (rsp (set-r14 val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-r14))))
(defthm rsp-of-set-r15 (equal (rsp (set-r15 val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-r15))))
(defthm rsp-of-set-rbp (equal (rsp (set-rbp val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-rbp))))

(defthm rbp-of-set-rax (equal (rbp (set-rax val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-rax))))
(defthm rbp-of-set-rbx (equal (rbp (set-rbx val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-rbx))))
(defthm rbp-of-set-rcx (equal (rbp (set-rcx val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-rcx))))
(defthm rbp-of-set-rdx (equal (rbp (set-rdx val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-rdx))))
(defthm rbp-of-set-rsi (equal (rbp (set-rsi val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-rsi))))
(defthm rbp-of-set-rdi (equal (rbp (set-rdi val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-rdi))))
(defthm rbp-of-set-r8 (equal (rbp (set-r8 val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-r8))))
(defthm rbp-of-set-r9 (equal (rbp (set-r9 val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-r9))))
(defthm rbp-of-set-r10 (equal (rbp (set-r10 val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-r10))))
(defthm rbp-of-set-r11 (equal (rbp (set-r11 val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-r11))))
(defthm rbp-of-set-r12 (equal (rbp (set-r12 val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-r12))))
(defthm rbp-of-set-r13 (equal (rbp (set-r13 val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-r13))))
(defthm rbp-of-set-r14 (equal (rbp (set-r14 val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-r14))))
(defthm rbp-of-set-r15 (equal (rbp (set-r15 val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-r15))))
(defthm rbp-of-set-rsp (equal (rbp (set-rsp val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-rsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Do we need this series?  Yes, currently, for the :ms field.
(defthm xr-of-set-rax-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-rax rax x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rax))))
(defthm xr-of-set-rbx-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-rbx rbx x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm xr-of-set-rcx-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-rcx rcx x86)) (xr fld index x86))):hints (("Goal" :in-theory (enable set-rcx))))
(defthm xr-of-set-rdx-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-rdx rdx x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm xr-of-set-rsi-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-rsi rsi x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm xr-of-set-rdi-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-rdi rdi x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm xr-of-set-r8-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-r8 r8 x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-r8))))
(defthm xr-of-set-r9-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-r9 r9 x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-r9))))
(defthm xr-of-set-r10-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-r10 r10 x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-r10))))
(defthm xr-of-set-r11-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-r11 r11 x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-r11))))
(defthm xr-of-set-r12-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-r12 r12 x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-r12))))
(defthm xr-of-set-r13-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-r13 r13 x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-r13))))
(defthm xr-of-set-r14-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-r14 r14 x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-r14))))
(defthm xr-of-set-r15-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-r15 r15 x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-r15))))
(defthm xr-of-set-rsp-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-rsp rsp x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm xr-of-set-rbp-irrel (implies (not (equal fld :rgf)) (equal (xr fld index (set-rbp rbp x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rbp))))

;; These are used to prove some other rules, but can we delete these?:

(defthm set-rax-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-rax rax (xw fld index val x86))
                  (xw fld index val (set-rax rax x86))))
  :hints (("Goal" :in-theory (enable set-rax
                                     ))))

(defthm set-rbx-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-rbx rbx (xw fld index val x86))
                  (xw fld index val (set-rbx rbx x86))))
  :hints (("Goal" :in-theory (enable set-rbx
                                     ))))

(defthm set-rcx-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-rcx rcx (xw fld index val x86))
                  (xw fld index val (set-rcx rcx x86))))
  :hints (("Goal" :in-theory (enable set-rcx
                                     ))))

(defthm set-rdx-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-rdx rdx (xw fld index val x86))
                  (xw fld index val (set-rdx rdx x86))))
  :hints (("Goal" :in-theory (enable set-rdx
                                     ))))

(defthm set-rsi-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-rsi rsi (xw fld index val x86))
                  (xw fld index val (set-rsi rsi x86))))
  :hints (("Goal" :in-theory (enable set-rsi
                                     ))))

(defthm set-rdi-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-rdi rdi (xw fld index val x86))
                  (xw fld index val (set-rdi rdi x86))))
  :hints (("Goal" :in-theory (enable set-rdi
                                     ))))

(defthm set-r8-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-r8 r8 (xw fld index val x86))
                  (xw fld index val (set-r8 r8 x86))))
  :hints (("Goal" :in-theory (enable set-r8
                                     ))))

(defthm set-r9-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-r9 r9 (xw fld index val x86))
                  (xw fld index val (set-r9 r9 x86))))
  :hints (("Goal" :in-theory (enable set-r9
                                     ))))

(defthm set-r10-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-r10 r10 (xw fld index val x86))
                  (xw fld index val (set-r10 r10 x86))))
  :hints (("Goal" :in-theory (enable set-r10
                                     ))))

(defthm set-rsp-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-rsp rsp (xw fld index val x86))
                  (xw fld index val (set-rsp rsp x86))))
  :hints (("Goal" :in-theory (enable set-rsp
                                     ))))

(defthm set-rbp-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-rbp rbp (xw fld index val x86))
                  (xw fld index val (set-rbp rbp x86))))
  :hints (("Goal" :in-theory (enable set-rbp
                                     ))))

(defthm set-rbp-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-rbp rbp (xw fld index val x86))
                  (xw fld index val (set-rbp rbp x86))))
  :hints (("Goal" :in-theory (enable set-rbp
                                     ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; sort calls to register writers
;;;

;;; bring set-rax forward
(defthm set-rbx-of-set-rax (equal (set-rbx rbx (set-rax rax x86)) (set-rax rax (set-rbx rbx x86))) :hints (("Goal" :in-theory (enable set-rax set-rbx))))
(defthm set-rcx-of-set-rax (equal (set-rcx rcx (set-rax rax x86)) (set-rax rax (set-rcx rcx x86))) :hints (("Goal" :in-theory (enable set-rax set-rcx))))
(defthm set-rdx-of-set-rax (equal (set-rdx rdx (set-rax rax x86)) (set-rax rax (set-rdx rdx x86))) :hints (("Goal" :in-theory (enable set-rax set-rdx))))
(defthm set-rsi-of-set-rax (equal (set-rsi rsi (set-rax rax x86)) (set-rax rax (set-rsi rsi x86))) :hints (("Goal" :in-theory (enable set-rax set-rsi))))
(defthm set-rdi-of-set-rax (equal (set-rdi rdi (set-rax rax x86)) (set-rax rax (set-rdi rdi x86))) :hints (("Goal" :in-theory (enable set-rax set-rdi))))
(defthm set-r8-of-set-rax (equal (set-r8 r8 (set-rax rax x86)) (set-rax rax (set-r8  r8  x86))) :hints (("Goal" :in-theory (enable set-rax set-r8))))
(defthm set-r9-of-set-rax (equal (set-r9 r9 (set-rax rax x86)) (set-rax rax (set-r9  r9  x86))) :hints (("Goal" :in-theory (enable set-rax set-r9))))
(defthm set-r10-of-set-rax (equal (set-r10 r10 (set-rax rax x86)) (set-rax rax (set-r10 r10 x86))) :hints (("Goal" :in-theory (enable set-rax set-r10))))
(defthm set-r11-of-set-rax (equal (set-r11 r11 (set-rax rax x86)) (set-rax rax (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-rax set-r11))))
(defthm set-r12-of-set-rax (equal (set-r12 r12 (set-rax rax x86)) (set-rax rax (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-rax set-r12))))
(defthm set-r13-of-set-rax (equal (set-r13 r13 (set-rax rax x86)) (set-rax rax (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-rax set-r13))))
(defthm set-r14-of-set-rax (equal (set-r14 r14 (set-rax rax x86)) (set-rax rax (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-rax set-r14))))
(defthm set-r15-of-set-rax (equal (set-r15 r15 (set-rax rax x86)) (set-rax rax (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-rax set-r15))))
(defthm set-rsp-of-set-rax (equal (set-rsp rsp (set-rax rax x86)) (set-rax rax (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-rax set-rsp))))
(defthm set-rbp-of-set-rax (equal (set-rbp rbp (set-rax rax x86)) (set-rax rax (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-rax set-rbp))))

;;; bring set-rbx forward
(defthm set-rcx-of-set-rbx (equal (set-rcx rcx (set-rbx rbx x86)) (set-rbx rbx (set-rcx rcx x86))) :hints (("Goal" :in-theory (enable set-rbx set-rcx))))
(defthm set-rdx-of-set-rbx (equal (set-rdx rdx (set-rbx rbx x86)) (set-rbx rbx (set-rdx rdx x86))) :hints (("Goal" :in-theory (enable set-rbx set-rdx))))
(defthm set-rsi-of-set-rbx (equal (set-rsi rsi (set-rbx rbx x86)) (set-rbx rbx (set-rsi rsi x86))) :hints (("Goal" :in-theory (enable set-rbx set-rsi))))
(defthm set-rdi-of-set-rbx (equal (set-rdi rdi (set-rbx rbx x86)) (set-rbx rbx (set-rdi rdi x86))) :hints (("Goal" :in-theory (enable set-rbx set-rdi))))
(defthm set-r8-of-set-rbx (equal (set-r8 r8 (set-rbx rbx x86)) (set-rbx rbx (set-r8 r8 x86))) :hints (("Goal" :in-theory (enable set-rbx set-r8))))
(defthm set-r9-of-set-rbx (equal (set-r9 r9 (set-rbx rbx x86)) (set-rbx rbx (set-r9 r9 x86))) :hints (("Goal" :in-theory (enable set-rbx set-r9))))
(defthm set-r10-of-set-rbx (equal (set-r10 r10 (set-rbx rbx x86)) (set-rbx rbx (set-r10 r10 x86))) :hints (("Goal" :in-theory (enable set-rbx set-r10))))
(defthm set-r11-of-set-rbx (equal (set-r11 r11 (set-rbx rbx x86)) (set-rbx rbx (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-rbx set-r11))))
(defthm set-r12-of-set-rbx (equal (set-r12 r12 (set-rbx rbx x86)) (set-rbx rbx (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-rbx set-r12))))
(defthm set-r13-of-set-rbx (equal (set-r13 r13 (set-rbx rbx x86)) (set-rbx rbx (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-rbx set-r13))))
(defthm set-r14-of-set-rbx (equal (set-r14 r14 (set-rbx rbx x86)) (set-rbx rbx (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-rbx set-r14))))
(defthm set-r15-of-set-rbx (equal (set-r15 r15 (set-rbx rbx x86)) (set-rbx rbx (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-rbx set-r15))))
(defthm set-rsp-of-set-rbx (equal (set-rsp rsp (set-rbx rbx x86)) (set-rbx rbx (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-rbx set-rsp))))
(defthm set-rbp-of-set-rbx (equal (set-rbp rbp (set-rbx rbx x86)) (set-rbx rbx (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-rbx set-rbp))))

;;; bring set-rcx forward
(defthm set-rdx-of-set-rcx (equal (set-rdx rdx (set-rcx rcx x86)) (set-rcx rcx (set-rdx rdx x86))) :hints (("Goal" :in-theory (enable set-rcx set-rdx))))
(defthm set-rsi-of-set-rcx (equal (set-rsi rsi (set-rcx rcx x86)) (set-rcx rcx (set-rsi rsi x86))) :hints (("Goal" :in-theory (enable set-rcx set-rsi))))
(defthm set-rdi-of-set-rcx (equal (set-rdi rdi (set-rcx rcx x86)) (set-rcx rcx (set-rdi rdi x86))) :hints (("Goal" :in-theory (enable set-rcx set-rdi))))
(defthm set-r8-of-set-rcx (equal (set-r8 r8 (set-rcx rcx x86)) (set-rcx rcx (set-r8 r8 x86))) :hints (("Goal" :in-theory (enable set-rcx set-r8))))
(defthm set-r9-of-set-rcx (equal (set-r9 r9 (set-rcx rcx x86)) (set-rcx rcx (set-r9 r9 x86))) :hints (("Goal" :in-theory (enable set-rcx set-r9))))
(defthm set-r10-of-set-rcx (equal (set-r10 r10 (set-rcx rcx x86)) (set-rcx rcx (set-r10 r10 x86))) :hints (("Goal" :in-theory (enable set-rcx set-r10))))
(defthm set-r11-of-set-rcx (equal (set-r11 r11 (set-rcx rcx x86)) (set-rcx rcx (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-rcx set-r11))))
(defthm set-r12-of-set-rcx (equal (set-r12 r12 (set-rcx rcx x86)) (set-rcx rcx (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-rcx set-r12))))
(defthm set-r13-of-set-rcx (equal (set-r13 r13 (set-rcx rcx x86)) (set-rcx rcx (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-rcx set-r13))))
(defthm set-r14-of-set-rcx (equal (set-r14 r14 (set-rcx rcx x86)) (set-rcx rcx (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-rcx set-r14))))
(defthm set-r15-of-set-rcx (equal (set-r15 r15 (set-rcx rcx x86)) (set-rcx rcx (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-rcx set-r15))))
(defthm set-rsp-of-set-rcx (equal (set-rsp rsp (set-rcx rcx x86)) (set-rcx rcx (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-rcx set-rsp))))
(defthm set-rbp-of-set-rcx (equal (set-rbp rbp (set-rcx rcx x86)) (set-rcx rcx (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-rcx set-rbp))))

;;; bring set-rdx forward
(defthm set-rsi-of-set-rdx (equal (set-rsi rsi (set-rdx rdx x86)) (set-rdx rdx (set-rsi rsi x86))) :hints (("Goal" :in-theory (enable set-rdx set-rsi))))
(defthm set-rdi-of-set-rdx (equal (set-rdi rdi (set-rdx rdx x86)) (set-rdx rdx (set-rdi rdi x86))) :hints (("Goal" :in-theory (enable set-rdx set-rdi))))
(defthm set-r8-of-set-rdx (equal (set-r8 r8 (set-rdx rdx x86)) (set-rdx rdx (set-r8 r8 x86))) :hints (("Goal" :in-theory (enable set-rdx set-r8))))
(defthm set-r9-of-set-rdx (equal (set-r9 r9 (set-rdx rdx x86)) (set-rdx rdx (set-r9 r9 x86))) :hints (("Goal" :in-theory (enable set-rdx set-r9))))
(defthm set-r10-of-set-rdx (equal (set-r10 r10 (set-rdx rdx x86)) (set-rdx rdx (set-r10 r10 x86))) :hints (("Goal" :in-theory (enable set-rdx set-r10))))
(defthm set-r11-of-set-rdx (equal (set-r11 r11 (set-rdx rdx x86)) (set-rdx rdx (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-rdx set-r11))))
(defthm set-r12-of-set-rdx (equal (set-r12 r12 (set-rdx rdx x86)) (set-rdx rdx (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-rdx set-r12))))
(defthm set-r13-of-set-rdx (equal (set-r13 r13 (set-rdx rdx x86)) (set-rdx rdx (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-rdx set-r13))))
(defthm set-r14-of-set-rdx (equal (set-r14 r14 (set-rdx rdx x86)) (set-rdx rdx (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-rdx set-r14))))
(defthm set-r15-of-set-rdx (equal (set-r15 r15 (set-rdx rdx x86)) (set-rdx rdx (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-rdx set-r15))))
(defthm set-rsp-of-set-rdx (equal (set-rsp rsp (set-rdx rdx x86)) (set-rdx rdx (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-rdx set-rsp))))
(defthm set-rbp-of-set-rdx (equal (set-rbp rbp (set-rdx rdx x86)) (set-rdx rdx (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-rdx set-rbp))))

;;; bring set-rsi forward
(defthm set-rdi-of-set-rsi (equal (set-rdi rdi (set-rsi rdx x86)) (set-rsi rdx (set-rdi rdi x86))) :hints (("Goal" :in-theory (enable set-rsi set-rdi))))
(defthm set-r8-of-set-rsi (equal (set-r8 r8 (set-rsi rdx x86)) (set-rsi rdx (set-r8 r8 x86))) :hints (("Goal" :in-theory (enable set-rsi set-r8))))
(defthm set-r9-of-set-rsi (equal (set-r9 r9 (set-rsi rdx x86)) (set-rsi rdx (set-r9 r9 x86))) :hints (("Goal" :in-theory (enable set-rsi set-r9))))
(defthm set-r10-of-set-rsi (equal (set-r10 r10 (set-rsi rdx x86)) (set-rsi rdx (set-r10 r10 x86))) :hints (("Goal" :in-theory (enable set-rsi set-r10))))
(defthm set-r11-of-set-rsi (equal (set-r11 r11 (set-rsi rsi x86)) (set-rsi rsi (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-rsi set-r11))))
(defthm set-r12-of-set-rsi (equal (set-r12 r12 (set-rsi rsi x86)) (set-rsi rsi (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-rsi set-r12))))
(defthm set-r13-of-set-rsi (equal (set-r13 r13 (set-rsi rsi x86)) (set-rsi rsi (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-rsi set-r13))))
(defthm set-r14-of-set-rsi (equal (set-r14 r14 (set-rsi rsi x86)) (set-rsi rsi (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-rsi set-r14))))
(defthm set-r15-of-set-rsi (equal (set-r15 r15 (set-rsi rsi x86)) (set-rsi rsi (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-rsi set-r15))))
(defthm set-rsp-of-set-rsi (equal (set-rsp rsp (set-rsi rsi x86)) (set-rsi rsi (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-rsi set-rsp))))
(defthm set-rbp-of-set-rsi (equal (set-rbp rbp (set-rsi rsi x86)) (set-rsi rsi (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-rsi set-rbp))))

;;; bring set-rdi forward
(defthm set-r8-of-set-rdi (equal (set-r8 r8 (set-rdi rdi x86)) (set-rdi rdi (set-r8 r8 x86))) :hints (("Goal" :in-theory (enable set-rdi set-r8))))
(defthm set-r9-of-set-rdi (equal (set-r9 r9 (set-rdi rdi x86)) (set-rdi rdi (set-r9 r9 x86))) :hints (("Goal" :in-theory (enable set-rdi set-r9))))
(defthm set-r10-of-set-rdi (equal (set-r10 r10 (set-rdi rdi x86)) (set-rdi rdi (set-r10 r10 x86))) :hints (("Goal" :in-theory (enable set-rdi set-r10))))
(defthm set-r11-of-set-rdi (equal (set-r11 r11 (set-rdi rdi x86)) (set-rdi rdi (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-rdi set-r11))))
(defthm set-r12-of-set-rdi (equal (set-r12 r12 (set-rdi rdi x86)) (set-rdi rdi (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-rdi set-r12))))
(defthm set-r13-of-set-rdi (equal (set-r13 r13 (set-rdi rdi x86)) (set-rdi rdi (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-rdi set-r13))))
(defthm set-r14-of-set-rdi (equal (set-r14 r14 (set-rdi rdi x86)) (set-rdi rdi (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-rdi set-r14))))
(defthm set-r15-of-set-rdi (equal (set-r15 r15 (set-rdi rdi x86)) (set-rdi rdi (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-rdi set-r15))))
(defthm set-rsp-of-set-rdi (equal (set-rsp rsp (set-rdi rdi x86)) (set-rdi rdi (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-rdi set-rsp))))
(defthm set-rbp-of-set-rdi (equal (set-rbp rbp (set-rdi rdi x86)) (set-rdi rdi (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-rdi set-rbp))))

;;; bring set-r8 forward
(defthm set-r9-of-set-r8 (equal (set-r9 r9 (set-r8 r8 x86)) (set-r8 r8 (set-r9 r9 x86))) :hints (("Goal" :in-theory (enable set-r8 set-r9))))
(defthm set-r10-of-set-r8 (equal (set-r10 r10 (set-r8 r8 x86)) (set-r8 r8 (set-r10 r10 x86))) :hints (("Goal" :in-theory (enable set-r8 set-r10))))
(defthm set-r11-of-set-r8 (equal (set-r11 r11 (set-r8 r8 x86)) (set-r8 r8 (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-r8 set-r11))))
(defthm set-r12-of-set-r8 (equal (set-r12 r12 (set-r8 r8 x86)) (set-r8 r8 (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-r8 set-r12))))
(defthm set-r13-of-set-r8 (equal (set-r13 r13 (set-r8 r8 x86)) (set-r8 r8 (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-r8 set-r13))))
(defthm set-r14-of-set-r8 (equal (set-r14 r14 (set-r8 r8 x86)) (set-r8 r8 (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-r8 set-r14))))
(defthm set-r15-of-set-r8 (equal (set-r15 r15 (set-r8 r8 x86)) (set-r8 r8 (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-r8 set-r15))))
(defthm set-rsp-of-set-r8 (equal (set-rsp rsp (set-r8 r8 x86)) (set-r8 r8 (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-r8 set-rsp))))
(defthm set-rbp-of-set-r8 (equal (set-rbp rbp (set-r8 r8 x86)) (set-r8 r8 (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-r8 set-rbp))))

;;; bring set-r9 forward
(defthm set-r10-of-set-r9 (equal (set-r10 r10 (set-r9 r9 x86)) (set-r9 r9 (set-r10 r10 x86))) :hints (("Goal" :in-theory (enable set-r9 set-r10))))
(defthm set-r11-of-set-r9 (equal (set-r11 r11 (set-r9 r9 x86)) (set-r9 r9 (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-r9 set-r11))))
(defthm set-r12-of-set-r9 (equal (set-r12 r12 (set-r9 r9 x86)) (set-r9 r9 (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-r9 set-r12))))
(defthm set-r13-of-set-r9 (equal (set-r13 r13 (set-r9 r9 x86)) (set-r9 r9 (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-r9 set-r13))))
(defthm set-r14-of-set-r9 (equal (set-r14 r14 (set-r9 r9 x86)) (set-r9 r9 (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-r9 set-r14))))
(defthm set-r15-of-set-r9 (equal (set-r15 r15 (set-r9 r9 x86)) (set-r9 r9 (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-r9 set-r15))))
(defthm set-rsp-of-set-r9 (equal (set-rsp rsp (set-r9 r9 x86)) (set-r9 r9 (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-r9 set-rsp))))
(defthm set-rbp-of-set-r9 (equal (set-rbp rbp (set-r9 r9 x86)) (set-r9 r9 (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-r9 set-rbp))))

;;; bring set-r10 forward
(defthm set-r11-of-set-r10 (equal (set-r11 r11 (set-r10 r10 x86)) (set-r10 r10 (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-r10 set-r11))))
(defthm set-r12-of-set-r10 (equal (set-r12 r12 (set-r10 r10 x86)) (set-r10 r10 (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-r10 set-r12))))
(defthm set-r13-of-set-r10 (equal (set-r13 r13 (set-r10 r10 x86)) (set-r10 r10 (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-r10 set-r13))))
(defthm set-r14-of-set-r10 (equal (set-r14 r14 (set-r10 r10 x86)) (set-r10 r10 (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-r10 set-r14))))
(defthm set-r15-of-set-r10 (equal (set-r15 r15 (set-r10 r10 x86)) (set-r10 r10 (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-r10 set-r15))))
(defthm set-rsp-of-set-r10 (equal (set-rsp rsp (set-r10 r10 x86)) (set-r10 r10 (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-r10 set-rsp))))
(defthm set-rbp-of-set-r10 (equal (set-rbp rbp (set-r10 r10 x86)) (set-r10 r10 (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-r10 set-rbp))))

;;; bring set-r11 forward
(defthm set-r12-of-set-r11 (equal (set-r12 r12 (set-r11 r11 x86)) (set-r11 r11 (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-r11 set-r12))))
(defthm set-r13-of-set-r11 (equal (set-r13 r13 (set-r11 r11 x86)) (set-r11 r11 (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-r11 set-r13))))
(defthm set-r14-of-set-r11 (equal (set-r14 r14 (set-r11 r11 x86)) (set-r11 r11 (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-r11 set-r14))))
(defthm set-r15-of-set-r11 (equal (set-r15 r15 (set-r11 r11 x86)) (set-r11 r11 (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-r11 set-r15))))
(defthm set-rsp-of-set-r11 (equal (set-rsp rsp (set-r11 r11 x86)) (set-r11 r11 (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-r11 set-rsp))))
(defthm set-rbp-of-set-r11 (equal (set-rbp rbp (set-r11 r11 x86)) (set-r11 r11 (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-r11 set-rbp))))

;;; bring set-r12 forward
(defthm set-r13-of-set-r12 (equal (set-r13 r13 (set-r12 r12 x86)) (set-r12 r12 (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-r12 set-r13))))
(defthm set-r14-of-set-r12 (equal (set-r14 r14 (set-r12 r12 x86)) (set-r12 r12 (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-r12 set-r14))))
(defthm set-r15-of-set-r12 (equal (set-r15 r15 (set-r12 r12 x86)) (set-r12 r12 (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-r12 set-r15))))
(defthm set-rsp-of-set-r12 (equal (set-rsp rsp (set-r12 r12 x86)) (set-r12 r12 (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-r12 set-rsp))))
(defthm set-rbp-of-set-r12 (equal (set-rbp rbp (set-r12 r12 x86)) (set-r12 r12 (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-r12 set-rbp))))

;;; bring set-r13 forward
(defthm set-r14-of-set-r13 (equal (set-r14 r14 (set-r13 r13 x86)) (set-r13 r13 (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-r13 set-r14))))
(defthm set-r15-of-set-r13 (equal (set-r15 r15 (set-r13 r13 x86)) (set-r13 r13 (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-r13 set-r15))))
(defthm set-rsp-of-set-r13 (equal (set-rsp rsp (set-r13 r13 x86)) (set-r13 r13 (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-r13 set-rsp))))
(defthm set-rbp-of-set-r13 (equal (set-rbp rbp (set-r13 r13 x86)) (set-r13 r13 (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-r13 set-rbp))))

;;; bring set-r14 forward
(defthm set-r15-of-set-r14 (equal (set-r15 r15 (set-r14 r14 x86)) (set-r14 r14 (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-r14 set-r15))))
(defthm set-rsp-of-set-r14 (equal (set-rsp rsp (set-r14 r14 x86)) (set-r14 r14 (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-r14 set-rsp))))
(defthm set-rbp-of-set-r14 (equal (set-rbp rbp (set-r14 r14 x86)) (set-r14 r14 (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-r14 set-rbp))))

;;; bring set-r15 forward
(defthm set-rsp-of-set-r15 (equal (set-rsp rsp (set-r15 r15 x86)) (set-r15 r15 (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-r15 set-rsp))))
(defthm set-rbp-of-set-r15 (equal (set-rbp rbp (set-r15 r15 x86)) (set-r15 r15 (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-r15 set-rbp))))

;;; bring set-rsp forward
(defthm set-rbp-of-set-rsp (equal (set-rbp rbp (set-rsp rsp x86)) (set-rsp rsp (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-rsp set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; todo: can we get rid of these?

;; (defthm xr-of-set-rsp-same
;;   (equal (xr ':rgf '4 (set-rsp rsp x86))
;;          (logext 64 rsp))
;;   :hints (("Goal" :in-theory (enable set-rsp))))

(defthm xr-of-rsp-and-set-rax
  (equal (xr ':rgf '4 (set-rax rsp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-rax))))

(defthm xr-of-rsp-and-set-rbx
  (equal (xr ':rgf '4 (set-rbx rsp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-rbx))))

(defthm xr-of-rsp-and-set-rcx
  (equal (xr ':rgf '4 (set-rcx rsp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-rcx))))

(defthm xr-of-rsp-and-set-rdx
  (equal (xr ':rgf '4 (set-rdx rsp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-rdx))))

(defthm xr-of-rsp-and-set-rsi
  (equal (xr ':rgf '4 (set-rsi rsp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-rsi))))

(defthm xr-of-rsp-and-set-rdi
  (equal (xr ':rgf '4 (set-rdi rsp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-rdi))))

(defthm xr-of-rsp-and-set-r8
  (equal (xr ':rgf '4 (set-r8 rsp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-r8))))

(defthm xr-of-rsp-and-set-r9
  (equal (xr ':rgf '4 (set-r9 rsp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-r9))))

(defthm xr-of-rsp-and-set-r10
  (equal (xr ':rgf '4 (set-r10 rsp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-r10))))

(defthm xr-of-rsp-and-set-rbp
  (equal (xr ':rgf '4 (set-rbp rbp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-rbp))))

;;;

; todo: do we want these or the myif ones?
(defthm rip-of-if (equal (rip (if test x y)) (if test (rip x) (rip y))))
(defthm rax-of-if (equal (rax (if test x y)) (if test (rax x) (rax y))))
(defthm rbx-of-if (equal (rbx (if test x y)) (if test (rbx x) (rbx y))))
(defthm rcx-of-if (equal (rcx (if test x y)) (if test (rcx x) (rcx y))))
(defthm rdx-of-if (equal (rdx (if test x y)) (if test (rdx x) (rdx y))))
(defthm rsi-of-if (equal (rsi (if test x y)) (if test (rsi x) (rsi y))))
(defthm rdi-of-if (equal (rdi (if test x y)) (if test (rdi x) (rdi y))))
(defthm r8-of-if (equal (r8 (if test x y)) (if test (r8 x) (r8 y))))
(defthm r9-of-if (equal (r9 (if test x y)) (if test (r9 x) (r9 y))))
(defthm r10-of-if (equal (r10 (if test x y)) (if test (r10 x) (r10 y))))
(defthm r11-of-if (equal (r11 (if test x y)) (if test (r11 x) (r11 y))))
(defthm r12-of-if (equal (r12 (if test x y)) (if test (r12 x) (r12 y))))
(defthm r13-of-if (equal (r13 (if test x y)) (if test (r13 x) (r13 y))))
(defthm r14-of-if (equal (r14 (if test x y)) (if test (r14 x) (r14 y))))
(defthm r15-of-if (equal (r15 (if test x y)) (if test (r15 x) (r15 y))))
(defthm rsp-of-if (equal (rsp (if test x y)) (if test (rsp x) (rsp y))))
(defthm rbp-of-if (equal (rbp (if test x y)) (if test (rbp x) (rbp y))))

(defthm rip-of-myif (equal (rip (myif test x y)) (myif test (rip x) (rip y))) :hints (("Goal" :in-theory (enable myif))))
(defthm rax-of-myif (equal (rax (myif test x y)) (myif test (rax x) (rax y))) :hints (("Goal" :in-theory (enable myif))))
(defthm rbx-of-myif (equal (rbx (myif test x y)) (myif test (rbx x) (rbx y))) :hints (("Goal" :in-theory (enable myif))))
(defthm rcx-of-myif (equal (rcx (myif test x y)) (myif test (rcx x) (rcx y))) :hints (("Goal" :in-theory (enable myif))))
(defthm rdx-of-myif (equal (rdx (myif test x y)) (myif test (rdx x) (rdx y))) :hints (("Goal" :in-theory (enable myif))))
(defthm rsi-of-myif (equal (rsi (myif test x y)) (myif test (rsi x) (rsi y))) :hints (("Goal" :in-theory (enable myif))))
(defthm rdi-of-myif (equal (rdi (myif test x y)) (myif test (rdi x) (rdi y))) :hints (("Goal" :in-theory (enable myif))))
(defthm r8-of-myif (equal (r8 (myif test x y)) (myif test (r8 x) (r8 y))) :hints (("Goal" :in-theory (enable myif))))
(defthm r9-of-myif (equal (r9 (myif test x y)) (myif test (r9 x) (r9 y))) :hints (("Goal" :in-theory (enable myif))))
(defthm r10-of-myif (equal (r10 (myif test x y)) (myif test (r10 x) (r10 y))) :hints (("Goal" :in-theory (enable myif))))
(defthm r11-of-myif (equal (r11 (myif test x y)) (myif test (r11 x) (r11 y))) :hints (("Goal" :in-theory (enable myif))))
(defthm r12-of-myif (equal (r12 (myif test x y)) (myif test (r12 x) (r12 y))) :hints (("Goal" :in-theory (enable myif))))
(defthm r13-of-myif (equal (r13 (myif test x y)) (myif test (r13 x) (r13 y))) :hints (("Goal" :in-theory (enable myif))))
(defthm r14-of-myif (equal (r14 (myif test x y)) (myif test (r14 x) (r14 y))) :hints (("Goal" :in-theory (enable myif))))
(defthm r15-of-myif (equal (r15 (myif test x y)) (myif test (r15 x) (r15 y))) :hints (("Goal" :in-theory (enable myif))))
(defthm rsp-of-myif (equal (rsp (myif test x y)) (myif test (rsp x) (rsp y))) :hints (("Goal" :in-theory (enable myif))))
(defthm rbp-of-myif (equal (rbp (myif test x y)) (myif test (rbp x) (rbp y))) :hints (("Goal" :in-theory (enable myif))))

;; These are used to prove some of the read-over-write rules:
(defthm rax-of-xw (implies (not (equal fld :rgf)) (equal (rax (xw fld index value x86)) (rax x86))) :hints (("Goal" :in-theory (enable rax))))
(defthm rbx-of-xw (implies (not (equal fld :rgf)) (equal (rbx (xw fld index value x86)) (rbx x86))) :hints (("Goal" :in-theory (enable rbx))))
(defthm rcx-of-xw (implies (not (equal fld :rgf)) (equal (rcx (xw fld index value x86)) (rcx x86))) :hints (("Goal" :in-theory (enable rcx))))
(defthm rdx-of-xw (implies (not (equal fld :rgf)) (equal (rdx (xw fld index value x86)) (rdx x86))) :hints (("Goal" :in-theory (enable rdx))))
(defthm rsi-of-xw (implies (not (equal fld :rgf)) (equal (rsi (xw fld index value x86)) (rsi x86))) :hints (("Goal" :in-theory (enable rsi))))
(defthm rdi-of-xw (implies (not (equal fld :rgf)) (equal (rdi (xw fld index value x86)) (rdi x86))) :hints (("Goal" :in-theory (enable rdi))))
(defthm r8-of-xw (implies (not (equal fld :rgf)) (equal (r8 (xw fld index value x86)) (r8 x86))) :hints (("Goal" :in-theory (enable r8))))
(defthm r9-of-xw (implies (not (equal fld :rgf)) (equal (r9 (xw fld index value x86)) (r9 x86))) :hints (("Goal" :in-theory (enable r9))))
(defthm r10-of-xw (implies (not (equal fld :rgf)) (equal (r10 (xw fld index value x86)) (r10 x86))) :hints (("Goal" :in-theory (enable r10))))
(defthm r11-of-xw (implies (not (equal fld :rgf)) (equal (r11 (xw fld index value x86)) (r11 x86))) :hints (("Goal" :in-theory (enable r11))))
(defthm r12-of-xw (implies (not (equal fld :rgf)) (equal (r12 (xw fld index value x86)) (r12 x86))) :hints (("Goal" :in-theory (enable r12))))
(defthm r13-of-xw (implies (not (equal fld :rgf)) (equal (r13 (xw fld index value x86)) (r13 x86))) :hints (("Goal" :in-theory (enable r13))))
(defthm r14-of-xw (implies (not (equal fld :rgf)) (equal (r14 (xw fld index value x86)) (r14 x86))) :hints (("Goal" :in-theory (enable r14))))
(defthm r15-of-xw (implies (not (equal fld :rgf)) (equal (r15 (xw fld index value x86)) (r15 x86))) :hints (("Goal" :in-theory (enable r15))))
(defthm rsp-of-xw (implies (not (equal fld :rgf)) (equal (rsp (xw fld index value x86)) (rsp x86))) :hints (("Goal" :in-theory (enable rsp))))
(defthm rbp-of-xw (implies (not (equal fld :rgf)) (equal (rbp (xw fld index value x86)) (rbp x86))) :hints (("Goal" :in-theory (enable rbp))))

(defthm set-rip-of-myif (equal (set-rip val (myif test x y)) (myif test (set-rip val x) (set-rip val y))) :hints (("Goal" :in-theory (enable myif))))
(defthm set-rax-of-myif (equal (set-rax val (myif test x y)) (myif test (set-rax val x) (set-rax val y))) :hints (("Goal" :in-theory (enable myif))))
(defthm set-rbx-of-myif (equal (set-rbx val (myif test x y)) (myif test (set-rbx val x) (set-rbx val y))) :hints (("Goal" :in-theory (enable myif))))
(defthm set-rcx-of-myif (equal (set-rcx val (myif test x y)) (myif test (set-rcx val x) (set-rcx val y))) :hints (("Goal" :in-theory (enable myif))))
(defthm set-rdx-of-myif (equal (set-rdx val (myif test x y)) (myif test (set-rdx val x) (set-rdx val y))) :hints (("Goal" :in-theory (enable myif))))
(defthm set-rsi-of-myif (equal (set-rsi val (myif test x y)) (myif test (set-rsi val x) (set-rsi val y))) :hints (("Goal" :in-theory (enable myif))))
(defthm set-rdi-of-myif (equal (set-rdi val (myif test x y)) (myif test (set-rdi val x) (set-rdi val y))) :hints (("Goal" :in-theory (enable myif))))
(defthm set-r8-of-myif (equal (set-r8 val (myif test x y)) (myif test (set-r8 val x) (set-r8 val y))) :hints (("Goal" :in-theory (enable myif))))
(defthm set-r9-of-myif (equal (set-r9 val (myif test x y)) (myif test (set-r9 val x) (set-r9 val y))) :hints (("Goal" :in-theory (enable myif))))
(defthm set-r10-of-myif (equal (set-r10 val (myif test x y)) (myif test (set-r10 val x) (set-r10 val y))) :hints (("Goal" :in-theory (enable myif))))
; todo: add more here?
(defthm set-rsp-of-myif (equal (set-rsp val (myif test x y)) (myif test (set-rsp val x) (set-rsp val y))) :hints (("Goal" :in-theory (enable myif))))
(defthm set-rbp-of-myif (equal (set-rbp val (myif test x y)) (myif test (set-rbp val x) (set-rbp val y))) :hints (("Goal" :in-theory (enable myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: more!
(defthm set-rax-of-if-arg2 (equal (set-rax val (if test x86_1 x86_2)) (if test (set-rax val x86_1) (set-rax val x86_2))))
(defthm set-rbx-of-if-arg2 (equal (set-rbx val (if test x86_1 x86_2)) (if test (set-rbx val x86_1) (set-rbx val x86_2))))
(defthm set-rcx-of-if-arg2 (equal (set-rcx val (if test x86_1 x86_2)) (if test (set-rcx val x86_1) (set-rcx val x86_2))))
(defthm set-rdx-of-if-arg2 (equal (set-rdx val (if test x86_1 x86_2)) (if test (set-rdx val x86_1) (set-rdx val x86_2))))
(defthm set-rdi-of-if-arg2 (equal (set-rdi val (if test x86_1 x86_2)) (if test (set-rdi val x86_1) (set-rdi val x86_2))))
(defthm set-rsi-of-if-arg2 (equal (set-rsi val (if test x86_1 x86_2)) (if test (set-rsi val x86_1) (set-rsi val x86_2))))
(defthm set-rbp-of-if-arg2 (equal (set-rbp val (if test x86_1 x86_2)) (if test (set-rbp val x86_1) (set-rbp val x86_2))))
(defthm set-rsp-of-if-arg2 (equal (set-rsp val (if test x86_1 x86_2)) (if test (set-rsp val x86_1) (set-rsp val x86_2))))

(defthm set-rip-of-if
  (equal (set-rip val (if test x y))
         (if test (set-rip val x)
           (set-rip val y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "projects/x86isa/machine/register-readers-and-writers" :dir :system)

;; todo: could enable all these but then we should enable the other rules that introduce the normal form

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (defthm loghead-becomes-bvchop (equal (loghead size x) (bvchop size x)) :hints (("Goal" :in-theory (enable bvchop loghead)))))

;; Note that RR08 is more complicated that RR16 ,etc.
;; Goes directly to RAX, etc. and directly to BVCHOP OR SLICE.
(defthmd rr08-to-normal-form64
  (implies (and (syntaxp (and (quotep reg)
                              (quotep rex)))
                (unsigned-byte-p 4 reg) ; gets computed
                )
           (equal (rr08 reg rex x86)
                  (let* ((normalp (or (not (eql rex 0)) ;should all get computed
                                      (< reg 4)))
                         (reg (if normalp reg (- reg 4))) ; should get computed
                         (val (case reg
                                ;; The case should be resolved since REG is a constant
                                (#.*rax* (rax x86))
                                (#.*rcx* (rcx x86))
                                (#.*rdx* (rdx x86))
                                (#.*rbx* (rbx x86))
                                (#.*rsp* (rsp x86))
                                (#.*rbp* (rbp x86))
                                (#.*rsi* (rsi x86))
                                (#.*rdi* (rdi x86))
                                (#.*r8* (r8 x86))
                                (#.*r9* (r9 x86))
                                (#.*r10* (r10 x86))
                                (#.*r11* (r11 x86))
                                (#.*r12* (r12 x86))
                                (#.*r13* (r13 x86))
                                (#.*r14* (r14 x86))
                                (otherwise ;#.*r15*
                                  (r15 x86)))))
                    (if normalp
                        (bvchop 8 val)
                      (slice 15 8 val)))))
  :hints (("Goal" :in-theory (enable rr08 rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 unsigned-byte-p))))

;; Goes directly to RAX, etc. and directly to BVCHOP.
(defthmd rr16-to-normal-form64
  (implies (and (syntaxp (quotep reg))
                (unsigned-byte-p 4 reg) ; gets computed
                )
           (equal (rr16 reg x86)
                  (bvchop 16 (case reg
                               ;; The case should be resolved since REG is a constant
                               (#.*rax* (rax x86))
                               (#.*rcx* (rcx x86))
                               (#.*rdx* (rdx x86))
                               (#.*rbx* (rbx x86))
                               (#.*rsp* (rsp x86))
                               (#.*rbp* (rbp x86))
                               (#.*rsi* (rsi x86))
                               (#.*rdi* (rdi x86))
                               (#.*r8* (r8 x86))
                               (#.*r9* (r9 x86))
                               (#.*r10* (r10 x86))
                               (#.*r11* (r11 x86))
                               (#.*r12* (r12 x86))
                               (#.*r13* (r13 x86))
                               (#.*r14* (r14 x86))
                               (otherwise ;#.*r15*
                                 (r15 x86))))))
  :hints (("Goal" :in-theory (enable rr16 rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15))))

;; Goes directly to RAX, etc. and directly to BVCHOP.
(defthmd rr32-to-normal-form64
  (implies (and (syntaxp (quotep reg))
                (unsigned-byte-p 4 reg) ; gets computed
                )
           (equal (rr32 reg x86)
                  (bvchop 32 (case reg
                               ;; The case should be resolved since REG is a constant
                               (#.*rax* (rax x86))
                               (#.*rcx* (rcx x86))
                               (#.*rdx* (rdx x86))
                               (#.*rbx* (rbx x86))
                               (#.*rsp* (rsp x86))
                               (#.*rbp* (rbp x86))
                               (#.*rsi* (rsi x86))
                               (#.*rdi* (rdi x86))
                               (#.*r8* (r8 x86))
                               (#.*r9* (r9 x86))
                               (#.*r10* (r10 x86))
                               (#.*r11* (r11 x86))
                               (#.*r12* (r12 x86))
                               (#.*r13* (r13 x86))
                               (#.*r14* (r14 x86))
                               (otherwise ;#.*r15*
                                 (r15 x86))))))
  :hints (("Goal" :in-theory (enable rr32 rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15))))

(defthmd rr64-to-normal-form64
  (implies (and (syntaxp (quotep reg))
                (unsigned-byte-p 4 reg) ; gets computed
                )
           (equal (rr64 reg x86)
                  (bvchop 64 (case reg
                               ;; The case should be resolved since REG is a constant
                               (#.*rax* (rax x86))
                               (#.*rcx* (rcx x86))
                               (#.*rdx* (rdx x86))
                               (#.*rbx* (rbx x86))
                               (#.*rsp* (rsp x86))
                               (#.*rbp* (rbp x86))
                               (#.*rsi* (rsi x86))
                               (#.*rdi* (rdi x86))
                               (#.*r8* (r8 x86))
                               (#.*r9* (r9 x86))
                               (#.*r10* (r10 x86))
                               (#.*r11* (r11 x86))
                               (#.*r12* (r12 x86))
                               (#.*r13* (r13 x86))
                               (#.*r14* (r14 x86))
                               (otherwise ;#.*r15*
                                 (r15 x86))))))
  :hints (("Goal" :in-theory (enable rr64 rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd wr08-to-normal-form64
  (implies (and (syntaxp (quotep reg))
                (unsigned-byte-p 4 reg) ; gets computed
                )
           (equal (wr08 reg rex val x86)
                  (let* ((normalp (or (not (eql rex 0)) ;normalp should get computed
                                      (< reg 4)))
                         (reg (if normalp reg (- reg 4))) ; reg should get computed
                         (old-val (case reg
                                    ;; The case should be resolved since REG is a constant
                                    (#.*rax* (rax x86))
                                    (#.*rcx* (rcx x86))
                                    (#.*rdx* (rdx x86))
                                    (#.*rbx* (rbx x86))
                                    (#.*rsp* (rsp x86))
                                    (#.*rbp* (rbp x86))
                                    (#.*rsi* (rsi x86))
                                    (#.*rdi* (rdi x86))
                                    (#.*r8* (r8 x86))
                                    (#.*r9* (r9 x86))
                                    (#.*r10* (r10 x86))
                                    (#.*r11* (r11 x86))
                                    (#.*r12* (r12 x86))
                                    (#.*r13* (r13 x86))
                                    (#.*r14* (r14 x86))
                                    (otherwise ; #.*r15*
                                      (r15 x86))))
                         (new-val (if normalp
                                      ;(logext 64
                                      (bvcat 56 (slice 63 8 old-val) 8 val)
                                    ;)
                                    ;(logext 64
                                    (bvcat 48 (slice 63 16 old-val) 16 (bvcat 8 val 8 (bvchop 8 old-val)))
                                    ;)
                                    )))
                    (case reg
                      ;; The case should be resolved since REG is a constant
                      (#.*rax* (set-rax new-val x86))
                      (#.*rcx* (set-rcx new-val x86))
                      (#.*rdx* (set-rdx new-val x86))
                      (#.*rbx* (set-rbx new-val x86))
                      (#.*rsp* (set-rsp new-val x86))
                      (#.*rbp* (set-rbp new-val x86))
                      (#.*rsi* (set-rsi new-val x86))
                      (#.*rdi* (set-rdi new-val x86))
                      (#.*r8* (set-r8 new-val x86))
                      (#.*r9* (set-r9 new-val x86))
                      (#.*r10* (set-r10 new-val x86))
                      (#.*r11* (set-r11 new-val x86))
                      (#.*r12* (set-r12 new-val x86))
                      (#.*r13* (set-r13 new-val x86))
                      (#.*r14* (set-r14 new-val x86))
                      (otherwise ; #.*r15*
                        (set-r15 new-val x86))))))
  :hints (("Goal" :in-theory (e/d (wr08
                                   set-rax set-rcx set-rdx set-rbx set-rsp set-rbp set-rsi set-rdi set-r8 set-r9 set-r10 set-r11 set-r12 set-r13 set-r14 set-r15
                                   rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15
                                   unsigned-byte-p)
                                  (acl2::part-install-width-low-becomes-bvcat-512 ; todo
                                   acl2::part-install-width-low-becomes-bvcat-256
                                   acl2::part-install-width-low-becomes-bvcat-128
                                   )))))

;; Goes directly to SET-RAX, etc. and directly to BVCHOP.
(defthmd wr16-to-normal-form64
  (implies (and (syntaxp (quotep reg))
                (unsigned-byte-p 4 reg) ; gets computed
                )
           (equal (wr16 reg val x86)
                  (let* ((old-val (case reg
                                    ;; The case should be resolved since REG is a constant
                                    (#.*rax* (rax x86))
                                    (#.*rcx* (rcx x86))
                                    (#.*rdx* (rdx x86))
                                    (#.*rbx* (rbx x86))
                                    (#.*rsp* (rsp x86))
                                    (#.*rbp* (rbp x86))
                                    (#.*rsi* (rsi x86))
                                    (#.*rdi* (rdi x86))
                                    (#.*r8* (r8 x86))
                                    (#.*r9* (r9 x86))
                                    (#.*r10* (r10 x86))
                                    (#.*r11* (r11 x86))
                                    (#.*r12* (r12 x86))
                                    (#.*r13* (r13 x86))
                                    (#.*r14* (r14 x86))
                                    (otherwise ; #.*r15*
                                      (r15 x86))))
                         (new-val ;(logext 64
                           (bvcat 48 (slice 63 16 old-val) 16 val)
                           ;)
                           ))
                    (case reg
                      ;; The case should be resolved since REG is a constant
                      (#.*rax* (set-rax new-val x86))
                      (#.*rcx* (set-rcx new-val x86))
                      (#.*rdx* (set-rdx new-val x86))
                      (#.*rbx* (set-rbx new-val x86))
                      (#.*rsp* (set-rsp new-val x86))
                      (#.*rbp* (set-rbp new-val x86))
                      (#.*rsi* (set-rsi new-val x86))
                      (#.*rdi* (set-rdi new-val x86))
                      (#.*r8* (set-r8 new-val x86))
                      (#.*r9* (set-r9 new-val x86))
                      (#.*r10* (set-r10 new-val x86))
                      (#.*r11* (set-r11 new-val x86))
                      (#.*r12* (set-r12 new-val x86))
                      (#.*r13* (set-r13 new-val x86))
                      (#.*r14* (set-r14 new-val x86))
                      (otherwise ; #.*r15*
                        (set-r15 new-val x86))))))
  :hints (("Goal" :in-theory (e/d (wr16
                                   set-rax set-rcx set-rdx set-rbx set-rsp set-rbp set-rsi set-rdi set-r8 set-r9 set-r10 set-r11 set-r12 set-r13 set-r14 set-r15
                                    rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15)
                                  (acl2::part-install-width-low-becomes-bvcat-512 ; todo
                                   acl2::part-install-width-low-becomes-bvcat-256
                                   acl2::part-install-width-low-becomes-bvcat-128
                                   )))))

;; Goes directly to SET-RAX, etc. and directly to BVCHOP.
(defthmd wr32-to-normal-form64
  (implies (and (syntaxp (quotep reg))
                (unsigned-byte-p 4 reg) ; gets computed
                )
           (equal (wr32 reg val x86)
                  (let ((val (bvchop 32 val)))
                    (case reg
                      ;; The case should be resolved since REG is a constant
                      (#.*rax* (set-rax val x86))
                      (#.*rcx* (set-rcx val x86))
                      (#.*rdx* (set-rdx val x86))
                      (#.*rbx* (set-rbx val x86))
                      (#.*rsp* (set-rsp val x86))
                      (#.*rbp* (set-rbp val x86))
                      (#.*rsi* (set-rsi val x86))
                      (#.*rdi* (set-rdi val x86))
                      (#.*r8* (set-r8 val x86))
                      (#.*r9* (set-r9 val x86))
                      (#.*r10* (set-r10 val x86))
                      (#.*r11* (set-r11 val x86))
                      (#.*r12* (set-r12 val x86))
                      (#.*r13* (set-r13 val x86))
                      (#.*r14* (set-r14 val x86))
                      (otherwise ; #.*r15*
                        (set-r15 val x86))))))
  :hints (("Goal" :in-theory (enable wr32
                                     set-rax set-rcx set-rdx set-rbx set-rsp set-rbp set-rsi set-rdi set-r8 set-r9 set-r10 set-r11 set-r12 set-r13 set-r14 set-r15
                                     rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 bvchop loghead))))

(defthmd wr64-to-normal-form64
  (implies (and (syntaxp (quotep reg))
                (unsigned-byte-p 4 reg) ; gets computed
                )
           (equal (wr64 reg val x86)
                  (let (;(val (logext 64 val))
                        )
                    (case reg
                      ;; The case should be resolved since REG is a constant
                      (#.*rax* (set-rax val x86))
                      (#.*rcx* (set-rcx val x86))
                      (#.*rdx* (set-rdx val x86))
                      (#.*rbx* (set-rbx val x86))
                      (#.*rsp* (set-rsp val x86))
                      (#.*rbp* (set-rbp val x86))
                      (#.*rsi* (set-rsi val x86))
                      (#.*rdi* (set-rdi val x86))
                      (#.*r8* (set-r8 val x86))
                      (#.*r9* (set-r9 val x86))
                      (#.*r10* (set-r10 val x86))
                      (#.*r11* (set-r11 val x86))
                      (#.*r12* (set-r12 val x86))
                      (#.*r13* (set-r13 val x86))
                      (#.*r14* (set-r14 val x86))
                      (otherwise ; #.*r15*
                        (set-r15 val x86))))))
  :hints (("Goal" :in-theory (enable wr64
                                     set-rax set-rcx set-rdx set-rbx set-rsp set-rbp set-rsi set-rdi set-r8 set-r9 set-r10 set-r11 set-r12 set-r13 set-r14 set-r15
                                     rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 bvchop loghead))))
