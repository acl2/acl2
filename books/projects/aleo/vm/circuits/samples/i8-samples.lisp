; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

; This file contains nullary function definitions for the i8 samples.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

#||
This file was WIP

;;; TODO: generate this file from the raw file
;(include-book "i8-message-json-auto")

;(include-book "../gadget-json-message-to-r1cs-defagg")
;(include-book "../prime-field-macros")

;(include-book "../r1cs/signed-small-mul-checked")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; mul_and_check
; A component of mul_checked.  (Replaced mul_with_carry late 2023.)

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::mul_and_check_var_var*|)))
   `(define i8-mul_and_check_var_var--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; mul checked

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::mul_checked_0_var*|)))
   `(define i8-mul_checked_0_var--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::mul_checked_1_var*|)))
   `(define i8-mul_checked_1_var--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::mul_checked_N_var*|)))
   `(define i8-mul_checked_N_var--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::mul_checked_var_1*|)))
   `(define i8-mul_checked_var_1--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::mul_checked_var_var*|)))
   `(define i8-mul_checked_var_var--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;; TODO:
      ///
      (defruled i8-mul_checked_var_var--constraints-check
        (equal
         ;; The first 24 constraints are bit constraints
         (nthcdr 24 (i8-mul_checked_var_var--constraints))
         (signed-small-mul-checked-gadget-new .... TODO
                                         
          (loop$ for i from 0 to 7 collect (wvar i)) ; xs
          (loop$ for i from 8 to 15 collect (wvar i)) ; ys
          (loop$ for i from 81 to 88 collect (wvar i)) ; zs
          (loop$ for i from 16 to 23 collect (wvar i)) ; minus-xs
          (loop$ for i from 25 to 32 collect (wvar i)) ; abs-xs
          (wvar 24) ; abs-xs-carry
          (loop$ for i from 33 to 40 collect (wvar i)) ; minus-ys
          (loop$ for i from 42 to 49 collect (wvar i)) ; abs-ys
          (wvar 41) ; abs-ys-carry
          (wvar 50) ; axs*ays-val
          (loop$ for i from 51 to 58 collect (wvar i)) ; axs*ays
          (loop$ for i from 59 to 66 collect (wvar i)) ; axs*ays-carry
          (wvar 67) ; diff-sign
          (wvar 68) ; pos-prod-overflow
          (wvar 74) ; low-prod-bits-nonzero
          (rev (loop$ for i from 69 to 73 collect (wvar i))) ; naryor-bits
          (wvar 75) ; prod-min
          (wvar 76) ; prod-neg-or-min
          (wvar 77) ; neg-prod-underflow
          (loop$ for i from 78 to 85 collect (wvar i)) ; minus-prod
          (wvar 86) ; minus-prod-carry
          (xvar 0) ; one
          (eprime)))))))

||#

