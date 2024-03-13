; Assumptions for x86 proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "projects/x86isa/machine/state" :dir :system)
(include-book "projects/x86isa/machine/cpuid" :dir :system) ; for feature-flag

;; Assumptions that are common to 32-bit and 64-bit mode.
(defun standard-state-assumption (x86)
  (declare (xargs :stobjs x86))
  (and ;; The x86 state is well-formed:
   (x86p x86)

   ;; The model is operating in the application view (ignore paging):
   (equal (app-view x86) t) ;todo: get rid of the (equal ... t) wrapper (may need to improve the rewriter)

   ;; The initial state is error-free:
   (equal (ms x86) nil)
   (equal (fault x86) nil)

   ;; Certain CPU features are enabled (we can extend this list fairly freely as needed):
   ;; Note that we leave the function feature-flag disabled and do not prove a constant opener for it.
   ;; So far, all of these have been needed by actual examples:
   (equal (feature-flag :avx) 1)
   (equal (feature-flag :bmi2) 1)
   (equal (feature-flag :sse) 1)
   ))

;; A lifter target is either a numeric offset, the name of a subroutine (a string), or the symbol :entry-point.
(defun lifter-targetp (target)
  (declare (xargs :guard t))
  (or (natp target)
      (stringp target)
      (eq :entry-point target)))
