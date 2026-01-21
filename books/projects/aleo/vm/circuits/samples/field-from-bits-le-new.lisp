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

(include-book "projects/aleo/vm/circuits/r1cs/boolean-check" :dir :system)
(include-book "projects/aleo/vm/circuits/r1cs/field-from-bits" :dir :system)
(include-book "projects/aleo/vm/circuits/r1cs/bits-lte-const" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check sample (field-from_bits_le--constraints)
; against an instantiation of field-from-bits-gadget,
; but with the following caveat:
; snarkVM does not actually create a variable for x
; (because it is just a linear combination that is created on the fly),
; so we just add one to pass to the gadget,
; but we remove the final pow2sum constraint from the comparison.

(assert-event
 (equal
  (let ((constrs
        ;; Note, field-from-bits-gadget doesn't include the bit constraints
        ;; because we want to also be able to use it in places where the bits have
        ;; already been constrained.  So we add the bit constraints here to show
        ;; equivalence with the R1CS sample that has the bit constraints.
        (append
         (aleovm::boolean-check-gadget-list
          (loop$ for i from 0 to 255 collect (wvar i))
          (eprime))
         (aleovm::field-from-bits-gadget
          (loop$ for i from 0 to 255 collect (wvar i))
          (wvar 510)
          (loop$ for i from 256 to 507 collect (wvar i))
          (xvar 0)
          (eprime)))))
    ;; since snarkVM does not create a variable for x,
    ;; but rather creates the weighted sum linear constraint on the fly,
    ;; we remove the last constraint from the gadget:
    (butlast constrs 1))
  (field-from_bits_le--constraints)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check sample (field-from_bits_le_diff_const--constraints)
; against an instantiation of bits-lte-const-gadget,
; but with the following caveat:
; the gadget bits-lte-const-gadget is intended to be used both in a testing
; context (where we want to end with a boolean variable that states whether
; the bits were lte the const or not)
; and in an assertion context (where we want to assert that the previous
; boolean variable is 0).
; The way we get the sample from snarkVM is in the assertion context,
; so there is an additional constraint
;   (-w15 + x0) * (1) = (1)
; where x0 is a special variable equal to 1,
; therefore the last constraint is asserting that w15 is 0.
; To check the gadget against this sample, we must remove that last constraint
; from the sample.

#|
ALEO !>(p1cs (field-from_bits_le_diff_const--constraints))
Total of 17 constraints.
These variables have bit constraints: w0..w9
Non-bit constraints:
(-w4 + 1) * (-w3 + 1) = (-w10 + 1)
(-w5 + 1) * (-w10 + 1) = (-w11 + 1)
(w6) * (w11) = (w12)
(w7) * (w12) = (w13)
(-w8 + 1) * (-w13 + 1) = (-w14 + 1)
(w9) * (w14) = (w15)
(-w15 + x0) * (1) = (1)
|#

(assert-event
 (equal
  (append
   (aleovm::boolean-check-gadget-list
    (loop$ for i from 0 to 9 collect (wvar i))
    (eprime))
   (aleovm::bits-lte-const-gadget
    (loop$ for i from 0 to 9 collect (wvar i))
    '(1 1 1 0 0 0 1 1 0 1)
    (loop$ for i from 10 to 15 collect (wvar i))
    (eprime)))
  ;; Remove last constraint from sample:
  (butlast (field-from_bits_le_diff_const--constraints) 1)))
