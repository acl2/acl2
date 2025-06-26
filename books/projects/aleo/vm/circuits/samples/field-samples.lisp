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

(include-book "field-message-json-auto")

;; This next book will naturally be part of field-message-json-auto the next
;; time that is regenerated.
(include-book "field-square-roots-message-json-auto")

(include-book "projects/aleo/vm/circuits/sampling/gadget-json-message-to-r1cs-defagg" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::add*|)))
   `(define field-add--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::compare*|)))
   `(define field-compare--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::div*|)))
   `(define field-div--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::div_unchecked*|)))
   `(define field-div_unchecked--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::double*|)))
   `(define field-double--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::equal*|)))
   `(define field-equal--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::even_square_root*|)))
   `(define field-even-square-root--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::from_bits_le*|)))
   `(define field-from_bits_le--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::from_bits_le_diff_const*|)))
   `(define field-from_bits_le_diff_const--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::inverse*|)))
   `(define field-inverse--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::mul*|)))
   `(define field-mul--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::neg*|)))
   `(define field-neg--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::pow10*|)))
   `(define field-pow10--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::pow_half_p*|)))
   `(define field-pow-half-p--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::c7237005577332262213973186563042994240829374041602535252466099000494570602495pow*|)))
   `(define field-cNpow--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::c15pow*|)))
   `(define field-c15pow--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::c11pow*|)))
   `(define field-c11pow--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::c6pow*|)))
   `(define field-c6pow--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::c1pow*|)))
   `(define field-c1pow--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::c0pow*|)))
   `(define field-c0pow--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::pow*|)))
   `(define field-pow--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::square*|)))
   `(define field-square--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::square_root*|)))
   `(define field-square_root--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::square_roots_flagged_nondeterministic*|)))
   `(define field-square_roots-flagged-nondeterministic--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::sub*|)))
   `(define field-sub--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::ternary*|)))
   `(define field-ternary--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*field::to_bits_le*|)))
   `(define field-to_bits_le--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))
