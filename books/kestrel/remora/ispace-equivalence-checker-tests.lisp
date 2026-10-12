; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-equivalence-checker")
(include-book "abstract-syntax-constructors")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of NORMALIZE-DIM.
; The dimensions are written with the constructor macros
; DIM+, DIM*, and DIM-, where $i denotes a dimension variable.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Variables and constants are unchanged.

(assert-equal (normalize-dim (dim-var "i"))
              (dim-var "i"))

(assert-equal (normalize-dim (dim-const 3))
              (dim-const 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Additions.

; Nested additions are flattened,
; the constants are added up and put first,
; and the variables are sorted.

(assert-equal (normalize-dim (dim+ "$k" (dim+ 1 "$i") 2 "$j"))
              (dim+ 3 "$i" "$j" "$k"))

; An addition of no dimensions is 0,
; an addition of one dimension is that dimension,
; and a zero constant sum is dropped.

(assert-equal (normalize-dim (dim+))
              (dim-const 0))

(assert-equal (normalize-dim (dim+ "$i"))
              (dim-var "i"))

(assert-equal (normalize-dim (dim+ 0 "$i"))
              (dim-var "i"))

(assert-equal (normalize-dim (dim+ 0 0))
              (dim-const 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Multiplications and subtractions.

; The normalization goes through polynomials
; (see DIMENSION-POLYNOMIALS and its tests);
; here we test a few representative cases.

; A multiplication of variables and a subtraction of a variable and a constant
; are unchanged, while a multiplication of constants is calculated.

(assert-equal (normalize-dim (dim* "$m" "$n"))
              (dim* "$m" "$n"))

(assert-equal (normalize-dim (dim* 2 3))
              (dim-const 6))

(assert-equal (normalize-dim (dim- "$m" 1))
              (dim- "$m" 1))

; A multiplication is distributed over the additions in its operands,
; and the additions in the operands of a subtraction are normalized.

(assert-equal (normalize-dim (dim* "$m" (dim+ 2 (dim+ 1 "$n"))))
              (dim+ (dim* 3 "$m") (dim* "$m" "$n")))

(assert-equal (normalize-dim (dim- (dim+ "$n" "$m") (dim+ 1 1)))
              (dim- (dim+ "$m" "$n") 2))

; A multiplication of constants that is an addend
; is added to the other constants,
; a singleton addition is its addend,
; and a zero addend is dropped.

(assert-equal (normalize-dim (dim+ "$i" 1 (dim* 2 3)))
              (dim+ 7 "$i"))

(assert-equal (normalize-dim (dim+ (dim* "$m" "$n")))
              (dim* "$m" "$n"))

(assert-equal (normalize-dim (dim+ 0 (dim- "$m" 1)))
              (dim- "$m" 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of DIM-ADDENDS.
; Each test compares the two results (constant and addends)
; with the expected ones.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An addition yields the sum of its constants and its other addends, in order.

(assert-equal (mv-list 2 (dim-addends (dim+ 3 "$i" (dim* "$m" "$n"))))
              (list 3 (list (dim-var "i") (dim* "$m" "$n"))))

(assert-equal (mv-list 2 (dim-addends (dim+ 1 "$j" 2 "$i")))
              (list 3 (list (dim-var "j") (dim-var "i"))))

(assert-equal (mv-list 2 (dim-addends (dim+)))
              (list 0 nil))

; A constant yields itself and no addends.

(assert-equal (mv-list 2 (dim-addends (dim-const 3)))
              (list 3 nil))

; A variable, multiplication, or subtraction yields 0 and itself.

(assert-equal (mv-list 2 (dim-addends (dim-var "i")))
              (list 0 (list (dim-var "i"))))

(assert-equal (mv-list 2 (dim-addends (dim* "$m" "$n")))
              (list 0 (list (dim* "$m" "$n"))))

(assert-equal (mv-list 2 (dim-addends (dim- "$m" 1)))
              (list 0 (list (dim- "$m" 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of NORMALIZE-SHAPE and NORMALIZE-ISPACE.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A normalized shape is a concatenation of
; shape variables and single-dimension shapes,
; with the dimensions normalized.

(assert-equal (normalize-shape (shp 2 (dim+ "$n" 1)))
              (shp++ (shp 2) (shp (dim+ 1 "$n"))))

(assert-equal (normalize-shape (shp++ "@s" (shp++) (shp)))
              (shp++ "@s"))

; A splice is turned into a concatenation.
; A multiplication of variables is unchanged.

(assert-equal (normalize-shape (shp[] (dim* "$m" "$n") "@s"))
              (shp++ (shp (dim* "$m" "$n")) "@s"))

; A dimension ispace is turned into a shape ispace.

(assert-equal (normalize-ispace (ispace-dim (dim+ "$n" 1)))
              (ispace-shape (shp++ (shp (dim+ 1 "$n")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of DIM-EQUIVP, SHAPE-EQUIVP, and ISPACE-EQUIVP.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Dimensions, shapes, and ispaces are equivalent
; iff they normalize to the same dimension, shape, or ispace.

(assert-equal (dim-equivp (dim+ "$n" 1)
                          (dim+ 1 "$n"))
              t)

(assert-equal (dim-equivp (dim+ 1 (dim+ 2 "$n"))
                          (dim+ 3 "$n"))
              t)

(assert-equal (dim-equivp (dim+ "$n" 1)
                          (dim+ "$n" 2))
              nil)

(assert-equal (shape-equivp (shp 2 1)
                            (shp++ (shp 2) (shp 1)))
              t)

(assert-equal (shape-equivp (shp (dim+ "$n" 1))
                            (shp (dim+ 1 "$n")))
              t)

(assert-equal (shape-equivp (shp 2 1)
                            (shp 1 2))
              nil)

(assert-equal (ispace-equivp (ispace-dim (dim-const 3))
                             (ispace-shape (shp 3)))
              t)

; Multiplication and subtraction are interpreted as well:
; a multiplication of constants is equivalent to their product,
; a multiplication is equivalent to its distribution over additions,
; and a subtraction cancels an addition;
; but a variable is not equivalent to its predecessor.

(assert-equal (dim-equivp (dim* "$m" (dim+ 1 2))
                          (dim* "$m" 3))
              t)

(assert-equal (dim-equivp (dim* 2 3)
                          (dim-const 6))
              t)

(assert-equal (dim-equivp (dim* (dim+ 1 "$m") (dim+ 1 "$n"))
                          (dim+ 1 "$m" "$n" (dim* "$m" "$n")))
              t)

(assert-equal (dim-equivp (dim+ (dim- "$n" 1) 1)
                          (dim-var "n"))
              t)

(assert-equal (dim-equivp (dim- "$n" 1)
                          (dim-var "n"))
              nil)

(assert-equal (shape-equivp (shp (dim* "$m" "$n"))
                            (shp (dim* "$m" "$n")))
              t)

(assert-equal (shape-equivp (shp (dim* "$m" (dim+ 1 2)))
                            (shp (dim* "$m" 3)))
              t)

(assert-equal (shape-equivp (shp (dim* 2 3))
                            (shp 6))
              t)
