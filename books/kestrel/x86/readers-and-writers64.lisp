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

;; Reads the undef state component.
;; TODO Just import x86isa::undef into the X package
(defund undef (x86)
  (declare (xargs :stobjs x86))
  (x86isa::undef x86))

;; Introduces undef
(defthmd xr-becomes-undef
  (equal (xr :undef nil x86)
         (undef x86))
  :hints (("Goal" :in-theory (enable undef))))

;; Writes the undef state component.
(defund set-undef (undef x86)
  (declare (xargs :stobjs x86))
  (x86isa::!undef undef x86))

;; Introduces set-undef
(defthmd xw-becomes-set-undef
  (equal (xw :undef nil undef x86)
         (set-undef undef x86))
  :hints (("Goal" :in-theory (enable set-undef))))

;needed?
(defthm xr-of-set-undef-irrel
  (implies (or (not (equal fld :undef))
               ;;(not (equal index *rax*))
               )
           (equal (xr fld index (set-undef undef x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-undef))))

;; read-of-write rule
(defthm undef-of-set-undef
  (equal (undef (set-undef val x86))
         val)
  :hints (("Goal" :in-theory (enable undef set-undef))))

;; write-of-write rule
(defthm set-undef-of-set-undef
  (equal (set-undef undef1 (set-undef undef2 x86))
         (set-undef undef1 x86))
  :hints (("Goal" :in-theory (enable set-undef))))

;; write-of-read rule
(defthm set-undef-of-undef-same
  (equal (set-undef (undef x86) x86)
         x86)
  :hints (("Goal" :in-theory (enable undef set-undef))))

;; These lower the IF:
(defthmd if-of-set-undef-arg2 (equal (if test (set-undef undef x86_1) x86_2) (set-undef (if test undef (undef x86_2)) (if test x86_1 x86_2))))
(defthmd if-of-set-undef-arg3 (equal (if test x86_1 (set-undef undef x86_2)) (set-undef (if test (undef x86_1) undef) (if test x86_1 x86_2))) )

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
(defthm if-of-set-rip-and-set-rip-same
  (equal (if test (set-rip rip x86_1) (set-rip rip x86_2)) ; same rip on both branches
         (set-rip rip (if test x86_1 x86_2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund set-error (error x86)
  (declare (xargs :stobjs x86))
  (x86isa::!ms error x86))

(defthmd xw-becomes-set-error
  (equal (xw :ms nil error x86)
         (set-error error x86))
  :hints (("Goal" :in-theory (enable set-error))))

;; What is the getter for this state component, or do we not need one?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
