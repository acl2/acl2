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
(include-book "projects/x86isa/utils/fp-structures" :dir :system) ; for mxcsrbits

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
   (equal (feature-flag :sse2) 1)

   ;; Instead of the assumptions below about the MXCSR, we could just assume
   ;; that it is initially the constant #x1F80.

   ;; Assume denormals are not treated as 0 (this is 0 upon power up or reset
   ;; and is incompatible with IEEE 754)::
   (equal (mxcsrbits->daz (mxcsr x86)) 0)

   ;; Assume exceptions are being masked (these are 1 at power up or reset):
   (equal (mxcsrbits->im (mxcsr x86)) 1)
   (equal (mxcsrbits->dm (mxcsr x86)) 1)
   (equal (mxcsrbits->zm (mxcsr x86)) 1)
   (equal (mxcsrbits->om (mxcsr x86)) 1)
   (equal (mxcsrbits->um (mxcsr x86)) 1)
   (equal (mxcsrbits->pm (mxcsr x86)) 1)

   ;; These help with things like SSE/AVX/etc
   (x86isa::cr0bits-p (x86isa::ctri 0 x86)) ; so we can extract the bits
   (equal (x86isa::cr0bits->ts (x86isa::ctri 0 x86)) 0)
   (equal (x86isa::cr0bits->em (x86isa::ctri 0 x86)) 0)
   (x86isa::cr4bits-p (x86isa::ctri 4 x86)) ; so we can call x86isa::cr4bits->osfxsr
   (equal (x86isa::cr4bits->osfxsr (x86isa::ctri 4 x86)) 1)

   ;; Assume the rounding mode is round-to-nearest-ties-to-even (the default
   ;; rounding mode):
   (equal (mxcsrbits->rc (mxcsr x86)) 0)

   ;; Assume that we are are not flushing to 0 (this is 0 upon power up or reset and
   ;; is incompatible with IEEE 754):
   (equal (mxcsrbits->fz (mxcsr x86)) 0)))

;; A lifter target is either a numeric offset, the name of a subroutine (a string), or the symbol :entry-point.
(defun lifter-targetp (target)
  (declare (xargs :guard t))
  (or (natp target)
      (stringp target)
      (eq :entry-point target)))
