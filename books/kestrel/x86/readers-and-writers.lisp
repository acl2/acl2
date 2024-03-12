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
;(include-book "projects/x86isa/machine/instructions/fp/mxcsr" :dir :system) ; would support integerp-of-mxcsr, but it has a ttag
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

;; Introduces set-undef
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

(defthm set-undef-of-myif (equal (set-undef val (myif test x y)) (myif test (set-undef val x) (set-undef val y))) :hints (("Goal" :in-theory (enable myif))))

(defthm set-undef-of-if (equal (set-undef val (if test x y)) (if test (set-undef val x) (set-undef val y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: do we want to call it MS or ERROR?

(defthmd xr-becomes-ms
  (equal (xr :ms nil x86)
         (ms x86)))

(defthm ms-of-xw (implies (not (equal fld :ms)) (equal (ms (xw fld index value x86)) (ms x86))) :hints (("Goal" :in-theory (enable ms))))

(defthm ms-of-if (equal (ms (if test x y)) (if test (ms x) (ms y))))

(defthm ms-of-myif (equal (ms (myif test x y)) (myif test (ms x) (ms y))) :hints (("Goal" :in-theory (enable myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes the ms state component.
(defund set-ms (ms x86)
  (declare (xargs :stobjs x86))
  (x86isa::!ms ms x86))

;; Introduces set-ms.
(defthmd xw-becomes-set-ms
  (equal (xw :ms nil ms x86)
         (set-ms ms x86))
  :hints (("Goal" :in-theory (enable set-ms))))

;; Introduces set-ms.
(defthmd !ms-becomes-set-ms
  (equal (!ms ms x86)
         (set-ms ms x86))
  :hints (("Goal" :in-theory (enable set-ms))))

(defthm xr-of-set-ms-irrel
  (implies (or (not (equal fld :ms))
               ;;(not (equal index *rax*))
               )
           (equal (xr fld index (set-ms ms x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-ms))))

;; read-of-write rule
(defthm ms-of-set-ms
  (equal (ms (set-ms val x86))
         val)
  :hints (("Goal" :in-theory (enable ms set-ms))))

;; Not sure whether we need more rules about set-ms, as it generally causes the execution to stop.


;; (defund set-error (error x86)
;;   (declare (xargs :stobjs x86))
;;   (x86isa::!ms error x86))

;; (defthmd xw-becomes-set-error
;;   (equal (xw :ms nil error x86)
;;          (set-error error x86))
;;   :hints (("Goal" :in-theory (enable set-error))))

;; (defund set-error (ms x86)
;;   (declare (xargs :stobjs x86))
;;   (x86isa::!ms ms x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable fault))

;; Introduces fault
(defthmd xr-becomes-fault
  (equal (xr :fault nil x86)
         (fault x86))
  :hints (("Goal" :in-theory (enable fault))))

(defthm fault-of-xw (implies (not (equal fld :fault)) (equal (fault (xw fld index value x86)) (fault x86))) :hints (("Goal" :in-theory (enable fault))))

(defthm fault-of-if (equal (fault (if test x y)) (if test (fault x) (fault y))))

(defthm fault-of-myif (equal (fault (myif test x y)) (myif test (fault x) (fault y))) :hints (("Goal" :in-theory (enable myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes the fault state component.
(defund set-fault (fault x86)
  (declare (xargs :stobjs x86))
  (x86isa::!fault fault x86))

;; Introduces set-fault.
(defthmd xw-becomes-set-fault
  (equal (xw :fault nil fault x86)
         (set-fault fault x86))
  :hints (("Goal" :in-theory (enable set-fault))))

;; Introduces set-fault.
(defthmd !fault-becomes-set-fault
  (equal (!fault fault x86)
         (set-fault fault x86))
  :hints (("Goal" :in-theory (enable set-fault))))

(defthm xr-of-set-fault-irrel
  (implies (or (not (equal fld :fault))
               ;;(not (equal index *rax*))
               )
           (equal (xr fld index (set-fault fault x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-fault))))

;; read-of-write rule
(defthm fault-of-set-fault
  (equal (fault (set-fault val x86))
         val)
  :hints (("Goal" :in-theory (enable fault set-fault))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Introduces mxcsr
(defthmd xr-becomes-mxcsr
  (equal (xr :mxcsr nil x86)
         (mxcsr x86))
  :hints (("Goal" :in-theory (enable mxcsr))))

(defthm mxcsr-of-xw (implies (not (equal fld :mxcsr)) (equal (mxcsr (xw fld index value x86)) (mxcsr x86))) :hints (("Goal" :in-theory (enable mxcsr))))

(defthm mxcsr-of-if (equal (mxcsr (if test x y)) (if test (mxcsr x) (mxcsr y))))

(defthm integerp-of-mxcsr
  (integerp (mxcsr x86))
  :hints (("Goal" :use (:instance x86isa::elem-p-of-xr-mxcsr (i nil) (x86isa::x86$a x86))
           :in-theory (disable x86isa::elem-p-of-xr-mxcsr))))

;(defthm mxcsr-of-myif (equal (mxcsr (myif test x y)) (myif test (mxcsr x) (mxcsr y))) :hints (("Goal" :in-theory (enable myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes the mxcsr state component.
(defund set-mxcsr (mxcsr x86)
  (declare (xargs :guard (unsigned-byte-p 32 mxcsr)
                  :stobjs x86))
  (x86isa::!mxcsr mxcsr x86))

;; Introduces set-mxcsr
(defthmd x86isa::!mxcsr-becomes-set-mxcsr
  (equal (x86isa::!mxcsr mxcsr x86)
         (set-mxcsr mxcsr x86))
  :hints (("Goal" :in-theory (enable set-mxcsr))))

;; Introduces set-mxcsr
(defthmd xw-becomes-set-mxcsr
  (equal (xw :mxcsr nil mxcsr x86)
         (set-mxcsr mxcsr x86))
  :hints (("Goal" :in-theory (enable set-mxcsr))))

;needed?
(defthm xr-of-set-mxcsr-irrel
  (implies (or (not (equal fld :mxcsr))
               ;;(not (equal index *rax*))
               )
           (equal (xr fld index (set-mxcsr mxcsr x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-mxcsr))))

;; read-of-write rule
(defthm mxcsr-of-set-mxcsr
  (equal (mxcsr (set-mxcsr val x86))
         (loghead 32 val))
  :hints (("Goal" :in-theory (enable mxcsr set-mxcsr))))

;; write-of-write rule
(defthm set-mxcsr-of-set-mxcsr
  (equal (set-mxcsr mxcsr1 (set-mxcsr mxcsr2 x86))
         (set-mxcsr mxcsr1 x86))
  :hints (("Goal" :in-theory (enable set-mxcsr))))

;; write-of-read rule
(defthm set-mxcsr-of-mxcsr-same
  (equal (set-mxcsr (mxcsr x86) x86)
         x86)
  :hints (("Goal" :in-theory (enable mxcsr set-mxcsr))))

;(defthm set-mxcsr-of-myif (equal (set-mxcsr val (myif test x y)) (myif test (set-mxcsr val x) (set-mxcsr val y))) :hints (("Goal" :in-theory (enable myif))))

(defthm set-mxcsr-of-if (equal (set-mxcsr val (if test x y)) (if test (set-mxcsr val x) (set-mxcsr val y))))
