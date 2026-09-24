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

; A multiplication or subtraction is left as it is,
; even when it could be simplified:
; no law of multiplication or subtraction is applied.

(assert-equal (normalize-dim (dim* "$m" "$n"))
              (dim* "$m" "$n"))

(assert-equal (normalize-dim (dim* 2 3))
              (dim* 2 3))

(assert-equal (normalize-dim (dim- "$m" 1))
              (dim- "$m" 1))

; The additions in the operands of a multiplication or subtraction
; are normalized, but they are not spliced into it.

(assert-equal (normalize-dim (dim* "$m" (dim+ 2 (dim+ 1 "$n"))))
              (dim* "$m" (dim+ 3 "$n")))

(assert-equal (normalize-dim (dim- (dim+ "$n" "$m") (dim+ 1 1)))
              (dim- (dim+ "$m" "$n") 2))

; A multiplication or subtraction that is an addend
; is treated like a variable:
; it is not added to the constants, and it is sorted with the variables
; (before them, according to ACL2's total order).

(assert-equal (normalize-dim (dim+ "$i" 1 (dim* 2 3)))
              (dim+ 1 (dim* 2 3) "$i"))

(assert-equal (normalize-dim (dim+ (dim* "$m" "$n")))
              (dim* "$m" "$n"))

(assert-equal (normalize-dim (dim+ 0 (dim- "$m" 1)))
              (dim- "$m" 1))

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
; A multiplication is left as it is.

(assert-equal (normalize-shape (shp[] (dim* "$m" "$n") "@s"))
              (shp++ (shp (dim* "$m" "$n")) "@s"))

; A dimension ispace is turned into a shape ispace.

(assert-equal (normalize-ispace (ispace-dim (dim+ "$n" 1)))
              (ispace-shape (shp++ (shp (dim+ 1 "$n")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of SHAPE-EQUIVP and ISPACE-EQUIVP.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Shapes and ispaces that only use addition are equivalent
; iff they normalize to the same shape or ispace.

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

; Multiplications and subtractions are uninterpreted:
; a shape with a multiplication is equivalent to itself,
; and to the same shape with the operands of the multiplication normalized,
; but a multiplication of constants is not equivalent to their product.

(assert-equal (shape-equivp (shp (dim* "$m" "$n"))
                            (shp (dim* "$m" "$n")))
              t)

(assert-equal (shape-equivp (shp (dim* "$m" (dim+ 1 2)))
                            (shp (dim* "$m" 3)))
              t)

(assert-equal (shape-equivp (shp (dim* 2 3))
                            (shp 6))
              nil)
