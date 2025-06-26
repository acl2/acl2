; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "field-samples")

(include-book "projects/aleo/vm/circuits/sampling/prime-field-macros" :dir :system)

(include-book "projects/aleo/vm/circuits/r1cs/field-neq" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Note, the field-equal sample gets the same constraints as field-neq
; because the negation of the resulting field just changes the linear
; combination "on the fly".
; This issue must be resolved when we deploy tgc, if not before.

(assert-event
 (equal (aleovm::field-neq-gadget  ; r = (x /= y)
         (wvar 0) ; x
         (wvar 1) ; y
         (wvar 3) ; w
         (wvar 2) ; r
         (xvar 0) ; b
         (eprime)
         )
        (field-equal--constraints)))
