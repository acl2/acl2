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

(include-book "projects/aleo/vm/circuits/sampling/prime-field-macros" :dir :system)

(include-book "psd_rate2_1-json-auto")
(include-book "psd_rate2_3-json-auto")
(include-book "psd_rate4_1-json-auto")
(include-book "psd_rate4_5-json-auto")

(include-book "psd_rate2_1_wef-json-auto")
(include-book "psd_rate2_3_wef-json-auto")
(include-book "psd_rate4_1_wef-json-auto")
(include-book "psd_rate4_5_wef-json-auto")

(include-book "projects/aleo/vm/circuits/sampling/gadget-json-message-to-r1cs-defagg" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*poseidon::hash::tests2::psd_rate2_1*|)))
   `(define psd-rate2-1--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*poseidon::hash::tests2::psd_rate2_3*|)))
   `(define psd-rate2-3--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*poseidon::hash::tests4::psd_rate4_1*|)))
   `(define psd-rate4-1--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*poseidon::hash::tests4::psd_rate4_5*|)))
   `(define psd-rate4-5--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; New versions of the above four samples that have an added input variable
;; that is expected to be 1 that is multiplied by the result, to cause
;; FormalCircuit::clear() to output one more constraint capturing the
;; correct output in a single variable.

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*poseidon::hash::tests2::psd_rate2_1_with_dummy_mul*|)))
   `(define psd-rate2-1-wef--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))
; w0 is the input to hash2, w266 is the dummy variable which must be set equal to 1, and w267 is the output.

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*poseidon::hash::tests2::psd_rate2_3_with_dummy_mul*|)))
   `(define psd-rate2-3-wef--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*poseidon::hash::tests4::psd_rate4_1_with_dummy_mul*|)))
   `(define psd-rate4-1-wef--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*poseidon::hash::tests4::psd_rate4_5_with_dummy_mul*|)))
   `(define psd-rate4-5-wef--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))
