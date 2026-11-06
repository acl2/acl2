; Tests of printing an R1CS in a more human-readable format.
;
; Copyright (C) 2026 Kestrel Institute (https://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (bendyarm on GitHub)

(in-package "R1CS")

(include-book "p1cs")
(include-book "gadgets/boolean")
(include-book "gadgets/boolean-alt")
(include-book "gadgets/xor")
(include-book "gadgets/selection")
(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Recognizing bit constraints

;; A bit-xor circuit built with the gadget generators, which write -1 as -1.
(defconst *xor-circuit*
  (list (make-boolean-constraint 'b0)     ; b0 * (b0 - 1) = 0
        (make-boolean-constraint 'b1)
        (make-boolean-constraint-alt 'b2) ; b2 * (1 - b2) = 0
        (make-bitxor-constraint 'b0 'b1 'b2)))

(acl2::assert-equal
 (vars-constrained-to-be-bits (fp1) *xor-circuit*)
 '(b0 b1 b2))

;; The same bit constraints with -1 written as fp-1.
(acl2::assert-equal
 (vars-constrained-to-be-bits
  (fp1)
  (list (r1cs-constraint '((1 b0)) (list '(1 b0) (list (- (fp1) 1) 1)) nil)
        (r1cs-constraint '((1 b2)) (list '(1 1) (list (- (fp1) 1) 'b2)) nil)))
 '(b0 b2))

;; The zero on the right-hand side can be written as no terms,
;; or as one term with coefficient 0.
(acl2::assert-equal
 (vars-constrained-to-be-bits
  (fp1)
  (list (r1cs-constraint '((1 b3)) '((1 b3) (-1 1)) nil)
        (r1cs-constraint '((1 b4)) '((1 b4) (-1 1)) '((0 1)))
        (r1cs-constraint '((1 b5)) '((1 b5) (-1 1)) '((0 x)))))
 '(b3 b4 b5))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Listing bit variables

;; Consecutively numbered variables are shown as a range;
;; other variables, including ones whose names do not end in digits,
;; are shown by name.
(acl2::assert-equal
 (bit-vars-message '(b0 b1 b2 b7 x))
 "These variables have bit constraints: B0..B2, B7, X")

(acl2::assert-equal
 (bit-vars-message '(x y z))
 "These variables have bit constraints: X, Y, Z")

;; Names whose digits have leading zeros are shown as they are,
;; not as part of a range.
(acl2::assert-equal
 (bit-vars-message '(b01 b02 b03))
 "These variables have bit constraints: B01, B02, B03")

(acl2::assert-equal
 (bit-vars-message '(b007))
 "These variables have bit constraints: B007")

(acl2::assert-equal
 (bit-vars-message '(b08 b09 b10 b11))
 "These variables have bit constraints: B08, B09, B10..B11")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Printing constraints

;; An empty linear combination is printed as 0.
;; Terms with coefficient 0 are printed as they are written.
(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint nil '((1 y)) '((1 z))))
 "0 * (Y) = (Z)")

(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint '((1 x)) nil '((1 z))))
 "(X) * 0 = (Z)")

(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint '((1 x)) '((1 y)) nil))
 "(X) * (Y) = 0")

(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint '((0 1)) '((1 y)) '((0 1))))
 "(0) * (Y) = (0)")

(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint '((0 x)) '((1 y)) '((0 x))))
 "(0.X) * (Y) = (0.X)")

(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint '((1 x) (0 w) (3 1)) '((1 y)) '((2 z) (0 1) (1 v))))
 "(X + 0.W + 3) * (Y) = (2.Z + 0 + V)")

;; Printing does not depend on how a coefficient is written.
(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint (list (list (- (expt 2 40)) 'x)) '((1 y)) '((1 z))))
 "(-(2^40).X) * (Y) = (Z)")

(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint (list (list (- (fp1) (expt 2 40)) 'x)) '((1 y)) '((1 z))))
 "(-(2^40).X) * (Y) = (Z)")

;; A gadget constraint.
(acl2::assert-equal
 (p1cs1 (fp1) (make-selection-constraint 'b 'x 'y 'z))
 "(B) * (Y - X) = (Y - Z)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Coefficients printed by name

;; Each field element has at most one name.
(assert-event (no-duplicatesp (strip-cars (nums-to-strings (fp1)))))
(assert-event (no-duplicatesp (strip-cars (nums-to-strings (fp2)))))

(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint (list (list (expt 2 200) 'x)) '((1 y)) '((1 z))))
 "(2^200.X) * (Y) = (Z)")

;; (1/2)^200, using 1/2 = (fp+1)/2
(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint (list (list (mod (expt (/ (+ (fp1) 1) 2) 200) (fp1)) 'x))
                               '((1 y))
                               '((1 z))))
 "(1/2^200.X) * (Y) = (Z)")

;; (-2)^199
(acl2::assert-equal
 (p1cs1 (fp1) (r1cs-constraint (list (list (mod (- (fp1) (mod (expt 2 199) (fp1))) (fp1)) 'x))
                               '((1 y))
                               '((1 z))))
 "(-(2^199).X) * (Y) = (Z)")
