; Assumptions for x86 proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "projects/x86isa/machine/state" :dir :system)
(include-book "projects/x86isa/machine/cpuid" :dir :system) ; for feature-flag
(include-book "projects/x86isa/utils/fp-structures" :dir :system) ; for mxcsrbits

;; Not sure where this should go:
(in-theory (disable bitops::signed-byte-p-induct))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of (untranslated) terms over STATE-VAR.
(defund make-standard-state-assumptions-fn (state-var)
  (declare (xargs :guard (symbolp state-var)))
  `(;; The x86 state is well-formed:
    (x86p ,state-var)

    ;; The model is operating in the application view (ignore paging):
    (app-view ,state-var)

    ;; The initial state is error-free:
    (equal (ms ,state-var) nil)
    (equal (fault ,state-var) nil)

    ;; Certain CPU features are enabled (we can extend this list fairly freely as needed):
    ;; Note that we leave the function feature-flag disabled and do not prove a constant opener for it.
    ;; So far, all of these have been needed by actual examples:
    ;; Note that these don't take state-var!
    (equal (feature-flag :avx) 1)
    (equal (feature-flag :avx2) 1)
    (equal (feature-flag :bmi2) 1)
    (equal (feature-flag :sse) 1)
    (equal (feature-flag :sse2) 1)
    (equal (feature-flag :lahf-sahf) 1)

    ;; Instead of the assumptions below about the MXCSR, we could just assume
    ;; that it is initially the constant #x1F80.

    ;; Assume denormals are not treated as 0 (this is 0 upon power up or reset
    ;; and is incompatible with IEEE 754):
    (equal (mxcsrbits->daz (mxcsr ,state-var)) 0)

    ;; Assume exceptions are being masked (these are 1 at power up or reset):
    (equal (mxcsrbits->im (mxcsr ,state-var)) 1)
    (equal (mxcsrbits->dm (mxcsr ,state-var)) 1)
    (equal (mxcsrbits->zm (mxcsr ,state-var)) 1)
    (equal (mxcsrbits->om (mxcsr ,state-var)) 1)
    (equal (mxcsrbits->um (mxcsr ,state-var)) 1)
    (equal (mxcsrbits->pm (mxcsr ,state-var)) 1)

    ;; Assume that we are are not flushing to 0 (this is 0 upon power up or reset and
    ;; is incompatible with IEEE 754):
    (equal (mxcsrbits->ftz (mxcsr ,state-var)) 0)

    ;; Assume the rounding mode is round-to-nearest-ties-to-even (the default
    ;; rounding mode):
    (equal (mxcsrbits->rc (mxcsr ,state-var)) 0)

    ;; These help with things like SSE/AVX/etc
    (cr0bits-p (ctri 0 ,state-var)) ; so we can extract the bits (todo: avoid actually using this assumption?)
    (equal (cr0bits->ts (ctri 0 ,state-var)) 0)
    (equal (cr0bits->em (ctri 0 ,state-var)) 0)
    (cr4bits-p (ctri 4 ,state-var)) ; so we can call cr4bits->osfxsr (todo: avoid actually using this assumption?)
    (equal (cr4bits->osfxsr (ctri 4 ,state-var)) 1)))

(defmacro make-standard-state-assumptions (state-var)
  `(and ,@(make-standard-state-assumptions-fn state-var)))

;; Assumptions that are common to 32-bit and 64-bit mode.
(defun standard-state-assumption (x86)
  (declare (xargs :stobjs x86))
  (make-standard-state-assumptions x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
