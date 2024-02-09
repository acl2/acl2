; A theory of x86 state readers and writers (emphasis on readability of terms)
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
; Copyright (C) 2023 Kestrel Institute
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
;(include-book "projects/x86isa/machine/state-field-thms" :dir :system)
(local (include-book "kestrel/bv/logext" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note that RIP is built into the x86 model.

;; Introduces rip.
(defthmd xr-becomes-rip
  (equal (xr :rip nil x86)
         (rip x86)))

(defund set-rip (rip x86)
  (declare (xargs :stobjs x86
                  :guard (signed-byte-p 48 rip))) ;todo: tighten?
  (x86isa::!rip rip x86))

;; Introduces set-rip.
(defthmd xw-becomes-set-rip
  (equal (xw :rip nil rip x86)
         (set-rip rip x86))
  :hints (("Goal" :in-theory (enable set-rip))))

;; A read-of-write rule
(defthm rip-of-set-rip
  (equal (rip (set-rip rip x86))
         (logext 48 rip))
  :hints (("Goal" :in-theory (enable set-rip))))

;needed?
(defthm xr-of-set-rip-irrel
  (implies (not (equal fld :rip))
           (equal (xr fld index (set-rip rip x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-rip))))

;needed?
(defthm xw-of-set-rip-irrel
  (implies (not (equal fld :rip))
           (equal (xw fld index val (set-rip rip x86))
                  (set-rip rip (xw fld index val x86))))
  :hints (("Goal" :in-theory (enable set-rip))))

;; A write-of-write rule
(defthm set-rip-of-set-rip
  (equal (set-rip rip1 (set-rip rip2 x86))
         (set-rip rip1 x86))
  :hints (("Goal" :in-theory (enable set-rip))))

;needed?
;slow?
(defthm rip-of-xw-irrel
  (implies (not (equal fld :rip))
           (equal (rip (xw fld index value x86))
                  (rip x86)))
  :hints (("Goal" :in-theory (enable rip))))

;todo: more like this, also try such rules first?
(defthmd if-of-set-rip-and-set-rip-same
  (equal (if test (set-rip rip x86_1) (set-rip rip x86_2)) ; same rip on both branches
         (set-rip rip (if test x86_1 x86_2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
