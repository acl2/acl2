; A theory of x86 state readers and writers (emphasis on readability of terms)
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book defines readers and writers for (64-bit) x86 state components.  It
;; aims for maximum brevity and clarity, so to set the UNDEF field, one simply
;; calls (set-undef <val> <x86>).

(include-book "projects/x86isa/machine/state" :dir :system) ;for xr
(include-book "kestrel/bv/bvchop-def" :dir :system)
(include-book "canonical-unsigned") ; todo: split out the def
(local (include-book "kestrel/bv/logext" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note that X86ISA::RIP is built into the x86 model and is a 48-bit signed-byte. See x86isa::i48p-xr-rip.

;; This is different from x86isa:: rip!
;; This one returns an unsigned-byte-64 that is known to satisfy unsigned-canonical-address-p.
(defund rip (x86)
  (declare (xargs :stobjs x86))
  (bvchop 64 (x86isa::rip x86)))

(defthm unsigned-byte-p-64-of-rip
  (unsigned-byte-p 64 (rip x86))
  :hints (("Goal" :in-theory (enable rip))))

(defthm integerp-of-rip
  (integerp (rip x86))
  :hints (("Goal" :in-theory (enable rip))))

(defthm unsigned-canonical-address-p-of-rip
  (unsigned-canonical-address-p (rip x86))
  :hints (("Goal" :in-theory (enable rip))))

(defthm signed-byte-p-48-of-logext-64-of-rip
  (signed-byte-p 48 (logext 64 (rip x86)))
  :hints (("Goal" :in-theory (enable rip))))

(defthm canonical-address-p-of-logext-64-of-rip
  (canonical-address-p (logext 64 (rip x86)))
  :hints (("Goal" :in-theory (enable canonical-address-p$inline))))

;; enabled to support acl2-based symbolic execution
(defthm x86isarip-becomes-rip
  (equal (x86isa::rip x)
         (logext 64 (rip x)))
  :hints (("Goal" :in-theory (enable rip))))
(theory-invariant (incompatible (:rewrite x86isarip-becomes-rip)
                                (:definition rip)))

(defthm xw-rip-of-logext
  (implies (and (<= 48 size)
                (integerp size))
           (equal (xw :rip nil (logext size rip) x86)
                  (xw :rip nil rip x86)))
  :hints (("Goal" :in-theory (enable xw))))

(defthm xw-rip-of-bvchop
  (implies (and (<= 48 size)
                (integerp size))
           (equal (xw :rip nil (bvchop size rip) x86)
                  (xw :rip nil rip x86)))
  :hints (("Goal" :in-theory (enable xw))))

;; Introduces rip.
;; enabled to support acl2-based symbolic execution
(defthm xr-becomes-rip
  (equal (xr :rip nil x86)
         (logext 64 (rip x86)))
  :hints (("Goal" :in-theory (e/d (rip) (x86isarip-becomes-rip)))))
(theory-invariant (incompatible (:rewrite xr-becomes-rip) (:definition rip)))

;; Takes the rip as an unsigned value
(defund set-rip (rip x86)
  (declare (xargs :guard (and (unsigned-byte-p 64 rip)
                              (unsigned-canonical-address-p rip))
                  :stobjs x86))
  (x86isa::!rip (logext 48 rip) x86))

;; Introduces set-rip.
;; enabled to support acl2-based symbolic execution
;; rip usually is a signed-byte-48 here.  we convert it to an unsigned-canonical address
(defthm xw-becomes-set-rip
  (equal (xw :rip nil rip x86)
         (set-rip (bvchop 64 rip) x86))
  :hints (("Goal" :in-theory (enable set-rip))))
(theory-invariant (incompatible (:rewrite xw-becomes-set-rip)
                                (:definition set-rip)))

;; rip usually is a signed-byte-48 here.  we convert it to an unsigned-canonical address
(defthmd !rip-becomes-set-rip
  (equal (!rip rip x86)
         (set-rip (bvchop 64 rip) x86))
  :hints (("Goal" :in-theory (e/d (set-rip) (xw-becomes-set-rip)))))
(theory-invariant (incompatible (:rewrite !rip-becomes-set-rip)
                                (:definition set-rip)))

(defthm set-rip-of-logext
  (implies (and (<= 48 size)
                (integerp size))
           (equal (set-rip (logext size rip) x86)
                  (set-rip rip x86)))
  :hints (("Goal" :in-theory (e/d (set-rip xw) (xw-becomes-set-rip)))))

(defthm set-rip-of-bvchop
  (implies (and (<= 48 size)
                (integerp size))
           (equal (set-rip (bvchop size rip) x86)
                  (set-rip rip x86)))
  :hints (("Goal" :in-theory (e/d (set-rip xw) (xw-becomes-set-rip)))))

(defthm set-rip-of-+-of-logext
  (implies (and (<= 48 size)
                (integerp size)
                (integerp x)
                (integerp y))
           (equal (set-rip (+ x (logext size y)) x86)
                  (set-rip (+ x y) x86)))
  :hints (("Goal" :use ((:instance set-rip-of-logext (rip (+ x (logext size y))))
                        (:instance set-rip-of-logext (rip (+ x y))))
           :in-theory (disable set-rip-of-logext))))

;; A read-of-write rule
(defthm rip-of-set-rip
  (equal (rip (set-rip rip x86))
         (bvsx 64 48 rip))
  :hints (("Goal" :in-theory (e/d (rip set-rip) (x86isarip-becomes-rip xr-becomes-rip xw-becomes-set-rip)))))

;needed?
(defthm xr-of-set-rip-irrel
  (implies (not (equal fld :rip))
           (equal (xr fld index (set-rip rip x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (e/d (set-rip) (xw-becomes-set-rip)))))

;needed?
(defthm xw-of-set-rip-irrel
  (implies (not (equal fld :rip))
           (equal (xw fld index val (set-rip rip x86))
                  (set-rip rip (xw fld index val x86))))
  :hints (("Goal" :in-theory (e/d (set-rip) (xw-becomes-set-rip)))))

;; A write-of-write rule
(defthm set-rip-of-set-rip
  (equal (set-rip rip1 (set-rip rip2 x86))
         (set-rip rip1 x86))
  :hints (("Goal" :in-theory (e/d (set-rip) (xw-becomes-set-rip)))))

;needed?
;slow?
(defthm rip-of-xw-irrel
  (implies (not (equal fld :rip))
           (equal (rip (xw fld index value x86))
                  (rip x86)))
  :hints (("Goal" :in-theory (e/d (rip) (xr-becomes-rip x86isarip-becomes-rip)))))

;todo: more like this, also try such rules first?
(defthmd if-of-set-rip-and-set-rip-same
  (implies (and (not (ms x86a)) ; only do it if neither state is faulted
                (not (fault x86a))
                (not (ms x86b))
                (not (fault x86b)))
           (equal (if test (set-rip rip x86a) (set-rip rip x86b)) ; same rip on both branches
                  (set-rip rip (if test x86a x86b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
