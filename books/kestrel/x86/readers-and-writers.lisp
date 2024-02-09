; A theory of x86 state readers and writers (emphasis on readability of terms)
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book focues on things that are not specific to 32-bit or 64-bit mode.

(include-book "projects/x86isa/machine/state" :dir :system) ;for xr
(include-book "kestrel/utilities/myif" :dir :system)

(in-theory (disable undef))

;; Introduces undef
(defthmd xr-becomes-undef
  (equal (xr :undef nil x86)
         (undef x86))
  :hints (("Goal" :in-theory (enable undef))))

(defthm undef-of-xw (implies (not (equal fld :undef)) (equal (undef (xw fld index value x86)) (undef x86))) :hints (("Goal" :in-theory (enable undef))))

(defthm undef-of-if (equal (undef (if test x y)) (if test (undef x) (undef y))))

(defthm undef-of-myif (equal (undef (myif test x y)) (myif test (undef x) (undef y))) :hints (("Goal" :in-theory (enable myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes the undef state component.
(defund set-undef (undef x86)
  (declare (xargs :stobjs x86))
  (x86isa::!undef undef x86))

(defthmd x86isa::!undef-becomes-set-undef
  (equal (x86isa::!undef undef x86)
         (set-undef undef x86))
  :hints (("Goal" :in-theory (enable set-undef))))

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

(defthm set-undef-of-myif (equal (set-undef val (myif test x y)) (myif test (set-undef val x) (set-undef val y))) :hints (("Goal" :in-theory (enable myif))))

(defthm set-undef-of-if (equal (set-undef val (if test x y)) (if test (set-undef val x) (set-undef val y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd xr-becomes-ms
  (equal (xr :ms nil x86)
         (ms x86)))

;; todo: do we want to call it MS or ERROR?

(defund set-error (error x86)
  (declare (xargs :stobjs x86))
  (x86isa::!ms error x86))

(defthmd xw-becomes-set-error
  (equal (xw :ms nil error x86)
         (set-error error x86))
  :hints (("Goal" :in-theory (enable set-error))))

;; What is the getter for this state component, or do we not need one?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
