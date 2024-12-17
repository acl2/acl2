; "Write over write" rules for our x86-64 state writers
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book focuses on things that are not specific to 32-bit or 64-bit mode.

(include-book "readers-and-writers")
(include-book "flags")

(defthm set-undef-of-set-flag (equal (set-undef undef (set-flag flag fval x86)) (set-flag flag fval (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-flag set-undef))))
(defthm set-undef-of-!rflags (equal (set-undef undef (!rflags flags x86)) (!rflags flags (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef))))

(defthm set-mxcsr-of-set-flag (equal (set-mxcsr mxcsr (set-flag flag fval x86)) (set-flag flag fval (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-flag set-mxcsr))))
(defthm set-mxcsr-of-!rflags (equal (set-mxcsr mxcsr (!rflags flags x86)) (!rflags flags (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr))))
