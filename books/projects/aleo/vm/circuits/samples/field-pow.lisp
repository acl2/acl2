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

(include-book "projects/aleo/vm/circuits/r1cs/field-pow" :dir :system)
(include-book "projects/aleo/vm/circuits/r1cs/field-const-pow" :dir :system)
(include-book "projects/aleo/vm/circuits/r1cs/field-pow-const" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; field var ** field var

; prev v2 gadget, which didn't have the check on p after bitifying,
; was called field-pow-field-gadget-v2 and was defined in r1cs/field-pow.lisp
; and the previous sample check was defined in field-gadget-tests.lisp

(assert-event
 (equal (aleovm::field-pow-gadget
         (wvar 0)
         (wvar 1) ; exponent
         (loop$ for i from 2 to 254 collect (wvar i)) ; exponent's bit vars
         (loop$ for i from 255 to 506 collect (wvar i)) ; make sure bit decomp is < p
         ; Note, the next three are in reverse order from
         ; their order in field-pow-field-gadget-v2.
         (rev (loop$ for i from 508 to 1261 by 3 collect (wvar i))) ; ss
         (rev (loop$ for i from 509 to 1262 by 3 collect (wvar i))) ; ps
         (rev (loop$ for i from 507 to 1263 by 3 collect (wvar i))) ; rs
         'r1cs::|x0|
         (eprime))
        (field-pow--constraints)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; field constant ** field var

; For check of previous snarkvm version sample, see
; field-gadget-tests.lisp

; Note, the variables used in field-const-pow-gadget
; do not depend on the input constant
; (although some of the coefficients do)
; so we define a macro that expands to the parameters.
(defmacro field-const-pow-gadget-macro (const)
  `(aleovm::field-const-pow-gadget
         ,const
         (xvar 0)
         (wvar 0)
         (loop$ for i from 1 to 253 collect (wvar i)) ; exponent's bit vars
         (loop$ for i from 254 to 505 collect (wvar i)) ; make sure bit decomp is < p
         ;; ss
         (rev (loop$ for i from 506 to 1008 by 2 collect (wvar i)))
         ;; rs
         (rev (loop$ for i from 507 to 1009 by 2 collect (wvar i)))
         (eprime)))

; (2**252 - 1) ** field var)
(assert-event
 (equal (field-const-pow-gadget-macro (- (expt 2 252) 1))
        (field-cNpow--constraints)))

; (15 ** field var)
(assert-event
 (equal (field-const-pow-gadget-macro 15)
        (field-c15pow--constraints)))

; (11 ** field var)
(assert-event
 (equal (field-const-pow-gadget-macro 11)
        (field-c11pow--constraints)))

; (6 ** field var)
(assert-event
 (equal (field-const-pow-gadget-macro 6)
        (field-c6pow--constraints)))

; (1 ** field var)
(assert-event
 (equal (field-const-pow-gadget-macro 1)
        (field-c1pow--constraints)))

; (0 ** field var)
(assert-event
 (equal (field-const-pow-gadget-macro 0)
        (field-c0pow--constraints)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; field var ** field constant


; prev gadget was field-pow-constant-gadget from r1cs/field-pow.lisp
; But now we use field-pow-const-gadget from r1cs/field-pow-const.lisp

; Note, field-pow-const-gadget does not support an exponent of 0 or 1.

; (field var ** 10)
(assert-event
 (equal (aleovm::field-pow-const-gadget
         (wvar 0)
         10 ; be: 1010; le: 0101
         ;; The ss vars are those that are the intermediate results of squares
         ;; that are then multiplied by w0.  I.e., they are the variables
         ;; are not themselves squared. (In reverse order.)
         (list (wvar 2)) ; ss
         ;; The rs vars are results of previous steps,
         ;; either just from squaring the prev var
         ;; or from an element of ss times w0.
         (list (wvar 4) (wvar 3) (wvar 1) ) ; rs
         (eprime))
        (field-pow10--constraints)))

; A separate test, not a sample, but we should have some more
; samples of (field var ** field constant)
; test (field ** 7)
(assert-event
 (let ((constraints (aleovm::field-pow-const-gadget
                     (wvar 0)
                     7 ; be/le: 111
                     ;; The ss vars are those that are the intermediate results of squares
                     ;; that are then multiplied by w0.  I.e., they are the variables
                     ;; are not themselves squared. (In reverse order.)
                     (list (wvar 3) (wvar 1)) ; ss   2 of these
                     ;; The rs vars are results of previous steps,
                     ;; either just from squaring the prev var
                     ;; or from an element of ss times w0.
                     (list (wvar 4) (wvar 2)) ; rs  2 of these, also
                     (eprime))))
   (r1cs::r1cs-constraints-holdp constraints
                                 `((,(wvar 0) . 2)
                                   (,(wvar 1) . 4)
                                   (,(wvar 2) . 8)
                                   (,(wvar 3) . 64)
                                   (,(wvar 4) . 128))
                                 (eprime))))
