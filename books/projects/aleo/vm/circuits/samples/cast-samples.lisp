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

(include-book "field-cast-message-json-auto")
; these next two have been included in the previous
;(include-book "field-op-then-cast-message-json-auto")
;(include-book "public-field-op-then-cast-message-json-auto")

(include-book "field-cast-lossy-message-json-auto")

; Experimental:
(include-book "field-cast-lossy-pre-pr2113-message-json-auto")
(include-book "field-cast-lossy-post-pr2113-message-json-auto")

(include-book "projects/aleo/vm/circuits/sampling/gadget-json-message-to-r1cs-defagg" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; field cast to group

;; The digit means the number that was used for a witness while generating the circuit.

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast::field::tests::formal_sample_field_0_cast_to_group*|)))
   `(define cast-field-0-group--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast::field::tests::formal_sample_field_1_cast_to_group*|)))
   `(define cast-field-1-group--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast::field::tests::formal_sample_field_2_cast_to_group*|)))
   `(define cast-field-2-group--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast::field::tests::formal_sample_field_3_cast_to_group*|)))
   `(define cast-field-3-group--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;; try an op on the field first, in this case it is x^2 + 1
(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast::field::tests::formal_sample_field_op_then_cast_to_group*|)))
   `(define cast-field-op-to-group--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;; The same as previous except field is public instead of private
(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast::field::tests::formal_sample_field_public_op_then_cast_to_group*|)))
   `(define cast-public-field-op-to-group--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; field cast_lossy to group

;; The digit means the number that was used for a witness while generating the circuit.

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast_lossy::field::tests::formal_sample_field_0_cast_lossy_to_group*|)))
   `(define cast-lossy-field-0-group--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast_lossy::field::tests::formal_sample_field_1_cast_lossy_to_group*|)))
   `(define cast-lossy-field-1-group--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast_lossy::field::tests::formal_sample_field_2_cast_lossy_to_group*|)))
   `(define cast-lossy-field-2-group--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast_lossy::field::tests::formal_sample_field_3_cast_lossy_to_group*|)))
   `(define cast-lossy-field-3-group--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Experimental:
;; field cast_lossy to group
;; before and after snarkVM PR#2113

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast_lossy::field::tests::formal_sample_field_0_cast_lossy_to_group_pre*|)))
   `(define cast-lossy-field-group-pre--constraints ()
     ; Took out "-0" from the name since that has never made a difference (see
     ; snarkVM test cases).  Probably should clean that up in snarkVM.
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*data::literal::cast_lossy::field::tests::formal_sample_field_0_cast_lossy_to_group_post*|)))
   `(define cast-lossy-field-group-post--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))
