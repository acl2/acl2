; Assumptions for x86 proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "projects/x86isa/machine/state" :dir :system)
(include-book "projects/x86isa/machine/cpuid" :dir :system) ; for feature-flag
(include-book "projects/x86isa/utils/fp-structures" :dir :system) ; for mxcsrbits
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; Not sure where this should go:
(in-theory (disable bitops::signed-byte-p-induct))

(local (in-theory (disable acl2::reverse-removal acl2::revappend-removal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We can extend this list fairly freely as needed (but we may want to consider
;; whether any actual CPU supports all the features).  We should also consider
;; whether any flags may contradict other flags.  So far, all of these have
;; been needed by actual examples:
(defconst *default-feature-flags*
  '(:avx
    :avx2
    :bmi2
    :sse
    :sse2
    :sse3
    :lahf-sahf))

(defun feature-flagsp (flags)
  (declare (xargs :guard t))
  (keyword-listp flags) ; todo: strengthen to check for allowed values
  )

;; Note that we leave the function feature-flag disabled and do not prove a constant opener for it.
;; Also note that feature-flag does not take x86 as an argument!
(defund make-feature-flag-assumptions (flags acc)
  (declare (xargs :guard (and (feature-flagsp flags)
                              (pseudo-term-listp acc))))
  (if (endp flags)
      (reverse acc)
    (make-feature-flag-assumptions (rest flags)
                                   (cons `(equal (feature-flag ',(first flags)) '1)
                                         acc))))

(local
 (defthm true-listp-of-make-feature-flag-assumptions
   (implies (true-listp acc)
            (true-listp (make-feature-flag-assumptions flags acc)))
   :hints (("Goal" :in-theory (enable make-feature-flag-assumptions)))))

(local
 (defthm pseudo-term-listp-of-make-feature-flag-assumptions
   (implies (and ;; (feature-flagsp flags)
                 (pseudo-term-listp acc))
            (pseudo-term-listp (make-feature-flag-assumptions flags acc)))
   :hints (("Goal" :in-theory (enable make-feature-flag-assumptions)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 ;; Returns a list of (untranslated) terms over STATE-VAR.
(defund make-standard-state-assumptions-fn-aux (state-var feature-flags)
  (declare (xargs :guard (and (symbolp state-var)
                              (feature-flagsp feature-flags))))
  `(;; The x86 state is well-formed:
    (x86p ,state-var)

    ;; The model is operating in the application view (ignore paging):
    (app-view ,state-var)

    ;; The initial state is error-free:
    (equal (ms ,state-var) 'nil)
    (equal (fault ,state-var) 'nil)

    ;; Certain CPU features are enabled:
    ,@(make-feature-flag-assumptions feature-flags nil)

    ;; Instead of the assumptions below about the MXCSR, we could just assume
    ;; that it is initially the constant #x1F80.

    ;; Assume denormals are not treated as 0 (this is 0 upon power up or reset
    ;; and is incompatible with IEEE 754):
    (equal (mxcsrbits->daz$inline (mxcsr ,state-var)) '0)

    ;; Assume exceptions are being masked (these are 1 at power up or reset):
    (equal (mxcsrbits->im$inline (mxcsr ,state-var)) '1)
    (equal (mxcsrbits->dm$inline (mxcsr ,state-var)) '1)
    (equal (mxcsrbits->zm$inline (mxcsr ,state-var)) '1)
    (equal (mxcsrbits->om$inline (mxcsr ,state-var)) '1)
    (equal (mxcsrbits->um$inline (mxcsr ,state-var)) '1)
    (equal (mxcsrbits->pm$inline (mxcsr ,state-var)) '1)

    ;; Assume that we are are not flushing to 0 (this is 0 upon power up or reset and
    ;; is incompatible with IEEE 754):
    (equal (mxcsrbits->ftz$inline (mxcsr ,state-var)) '0)

    ;; Assume the rounding mode is round-to-nearest-ties-to-even (the default
    ;; rounding mode):
    (equal (mxcsrbits->rc$inline (mxcsr ,state-var)) '0)

    ;; These help with things like SSE/AVX/etc
    (unsigned-byte-p '32 ; cr0bits-p
     (ctri '0 ,state-var)) ; so we can extract the bits (todo: avoid actually using this assumption?)
    (equal (cr0bits->ts$inline (ctri '0 ,state-var)) '0)
    (equal (cr0bits->em$inline (ctri '0 ,state-var)) '0)
    (unsigned-byte-p '26 ;cr4bits-p
                     (ctri '4 ,state-var)) ; so we can call cr4bits->osfxsr (todo: avoid actually using this assumption?)
    (equal (cr4bits->osfxsr$inline (ctri '4 ,state-var)) '1)))

(defthm pseudo-term-listp-of-make-standard-state-assumptions-fn-aux
  (implies (symbolp state-var)
           (pseudo-term-listp (make-standard-state-assumptions-fn-aux state-var feature-flags)))
  :hints (("Goal" :in-theory (enable make-standard-state-assumptions-fn-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund make-standard-state-assumptions-fn (state-var feature-flags)
  (declare (xargs :guard (and (symbolp state-var)
                              (feature-flagsp feature-flags))))
  `(and ,@(make-standard-state-assumptions-fn-aux state-var feature-flags)))

(defthm pseudo-termp-of-make-standard-state-assumptions-fn
  (implies (symbolp state-var)
           (pseudo-termp (make-standard-state-assumptions-fn state-var feature-flags)))
  :hints (("Goal" :in-theory (enable make-standard-state-assumptions-fn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defmacro make-standard-state-assumptions (state-var
                                             &key
                                               (feature-flags ',*default-feature-flags*))
    (make-standard-state-assumptions-fn state-var feature-flags)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Assumptions that are common to 32-bit and 64-bit mode.
(defun standard-state-assumption (x86)
  (declare (xargs :stobjs x86))
  (make-standard-state-assumptions x86))
