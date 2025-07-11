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

(include-book "u8-shift-pre-message-json-auto")
(include-book "i8-shift-pre-message-json-auto")
(include-book "u8-shift-post-message-json-auto")
(include-book "i8-shift-post-message-json-auto")

(include-book "projects/aleo/vm/circuits/sampling/gadget-json-message-to-r1cs-defagg" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We reorder the above so that each before/after pair is together.

;; ----------------
;; u8 shl checked

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*u8::shl_checked_var_var_pre*|)))
   `(define u8-shl-checked-pre--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*u8::shl_checked_var_var*|)))
   `(define u8-shl-checked-post--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;; ----------------
;; u8 shl wrapped

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*u8::shl_wrapped_var_var_pre*|)))
   `(define u8-shl-wrapped-pre--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*u8::shr_wrapped_var_var*|)))
   `(define u8-shl-wrapped-post--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;; ----------------
;; u8 shr checked

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*u8::shr_checked_var_var_pre*|)))
   `(define u8-shr-checked-pre--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*u8::shr_checked_var_var*|)))
   `(define u8-shr-checked-post--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;; ----------------
;; u8 shr wrapped

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*u8::shr_wrapped_var_var_pre*|)))
   `(define u8-shr-wrapped-pre--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*u8::shr_wrapped_var_var*|)))
   `(define u8-shr-wrapped-post--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;; ----------------
;; i8 shl checked

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::shl_checked_var_var_pre*|)))
   `(define i8-shl-checked-pre--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::shl_checked_var_var*|)))
   `(define i8-shl-checked-post--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;; ----------------
;; i8 shl wrapped

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::shl_wrapped_var_var_pre*|)))
   `(define i8-shl-wrapped-pre--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::shr_wrapped_var_var*|)))
   `(define i8-shl-wrapped-post--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;; ----------------
;; i8 shr checked

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::shr_checked_var_var_pre*|)))
   `(define i8-shr-checked-pre--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::shr_checked_var_var*|)))
   `(define i8-shr-checked-post--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

;; ----------------
;; i8 shr wrapped

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::shr_wrapped_var_var_pre*|)))
   `(define i8-shr-wrapped-pre--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))

(make-event
 (b* (((mv & constraints)
       (json-message-group-string-to-constraints |*i8::shr_wrapped_var_var*|)))
   `(define i8-shr-wrapped-post--constraints ()
      :returns (constraints r1cs::r1cs-constraint-listp)
      ',constraints)))
