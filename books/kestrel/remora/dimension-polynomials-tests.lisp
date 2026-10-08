; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "dimension-polynomials")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of the operations on polynomials.
; Since the representation of polynomials is canonical
; (see DIMENSION-POLYNOMIALS),
; equal polynomials are compared as equal ACL2 values.
; A polynomial is written as an omap, i.e. an alist ordered by keys,
; from monomials (ordered lists of dimensions) to coefficients.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Monomials: the empty one is the first key,
; and a variable precedes the monomials that extend it
; and the monomials with later variables.

(assert-equal (<< nil
                  (list (dim-var "i")))
              t)

(assert-equal (<< (list (dim-var "i"))
                  (list (dim-var "i") (dim-var "j")))
              t)

(assert-equal (<< (list (dim-var "i") (dim-var "j"))
                  (list (dim-var "j")))
              t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Constant polynomials: a constant has the empty monomial;
; 0 is the empty polynomial.

(assert-equal (dim-poly-const 3)
              (list (cons nil 3)))

(assert-equal (dim-poly-const -2)
              (list (cons nil -2)))

(assert-equal (dim-poly-const 0)
              nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; One-factor polynomials: a variable, and the nullary subtraction.

(assert-equal (dim-poly-factor (dim-var "i"))
              (list (cons (list (dim-var "i")) 1)))

(assert-equal (dim-poly-factor (dim-sub nil))
              (list (cons (list (dim-sub nil)) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Coefficients: of a present monomial, and of an absent one.

(assert-equal (dim-poly-coeff nil (dim-poly-const 3))
              3)

(assert-equal (dim-poly-coeff (list (dim-var "i")) (dim-poly-const 3))
              0)

(assert-equal (dim-poly-coeff (list (dim-var "i"))
                              (dim-poly-factor (dim-var "i")))
              1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Adding terms:
; a new monomial is inserted in key order,
; an existing one has its coefficient updated,
; and a zero sum removes the entry.

(assert-equal (dim-poly-add-term (list (dim-var "i"))
                                 2
                                 (dim-poly-const 3))
              (list (cons nil 3)
                    (cons (list (dim-var "i")) 2)))

(assert-equal (dim-poly-add-term nil
                                 2
                                 (dim-poly-const 3))
              (list (cons nil 5)))

(assert-equal (dim-poly-add-term nil
                                 -3
                                 (dim-poly-const 3))
              nil)

(assert-equal (dim-poly-add-term (list (dim-var "i"))
                                 0
                                 (dim-poly-const 3))
              (list (cons nil 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Addition:
; it is commutative,
; like terms are merged,
; and opposite terms cancel.

(assert-equal (dim-poly-add (dim-poly-const 1)
                            (dim-poly-factor (dim-var "i")))
              (list (cons nil 1)
                    (cons (list (dim-var "i")) 1)))

(assert-equal (dim-poly-add (dim-poly-factor (dim-var "i"))
                            (dim-poly-const 1))
              (list (cons nil 1)
                    (cons (list (dim-var "i")) 1)))

(assert-equal (dim-poly-add (dim-poly-factor (dim-var "i"))
                            (dim-poly-factor (dim-var "i")))
              (list (cons (list (dim-var "i")) 2)))

(assert-equal (dim-poly-add (dim-poly-add (dim-poly-const 1)
                                          (dim-poly-factor (dim-var "i")))
                            (dim-poly-const -1))
              (dim-poly-factor (dim-var "i")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Negation and subtraction: a polynomial minus itself is 0.

(assert-equal (dim-poly-neg (dim-poly-add (dim-poly-const 1)
                                          (dim-poly-factor (dim-var "i"))))
              (list (cons nil -1)
                    (cons (list (dim-var "i")) -1)))

(assert-equal (dim-poly-neg nil)
              nil)

(assert-equal (dim-poly-sub (dim-poly-add (dim-poly-const 1)
                                          (dim-poly-factor (dim-var "i")))
                            (dim-poly-add (dim-poly-const 1)
                                          (dim-poly-factor (dim-var "i"))))
              nil)

(assert-equal (dim-poly-sub (dim-poly-factor (dim-var "i"))
                            (dim-poly-const 1))
              (list (cons nil -1)
                    (cons (list (dim-var "i")) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Monomial multiplication:
; the factors are merged in order,
; with repetitions for powers.

(assert-equal (dim-mono-mul (list (dim-var "j")) (list (dim-var "i")))
              (list (dim-var "i") (dim-var "j")))

(assert-equal (dim-mono-mul (list (dim-var "i")) (list (dim-var "i")))
              (list (dim-var "i") (dim-var "i")))

(assert-equal (dim-mono-mul nil (list (dim-var "i")))
              (list (dim-var "i")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Multiplication:
; constants are multiplied,
; a product by 0 is 0,
; a product by 1 is the identity,
; multiplication is commutative
; and distributes over addition,
; e.g. (i + j) * (i + j) = i^2 + 2 i j + j^2.

(assert-equal (dim-poly-mul (dim-poly-const 2)
                            (dim-poly-const 3))
              (dim-poly-const 6))

(assert-equal (dim-poly-mul (dim-poly-const 0)
                            (dim-poly-factor (dim-var "i")))
              nil)

(assert-equal (dim-poly-mul (dim-poly-const 1)
                            (dim-poly-factor (dim-var "i")))
              (dim-poly-factor (dim-var "i")))

(assert-equal (dim-poly-mul (dim-poly-factor (dim-var "i"))
                            (dim-poly-factor (dim-var "j")))
              (list (cons (list (dim-var "i") (dim-var "j")) 1)))

(assert-equal (dim-poly-mul (dim-poly-factor (dim-var "j"))
                            (dim-poly-factor (dim-var "i")))
              (list (cons (list (dim-var "i") (dim-var "j")) 1)))

(assert-equal (dim-poly-mul (dim-poly-add (dim-poly-factor (dim-var "i"))
                                          (dim-poly-factor (dim-var "j")))
                            (dim-poly-add (dim-poly-factor (dim-var "i"))
                                          (dim-poly-factor (dim-var "j"))))
              (list (cons (list (dim-var "i") (dim-var "i")) 1)
                    (cons (list (dim-var "i") (dim-var "j")) 2)
                    (cons (list (dim-var "j") (dim-var "j")) 1)))

(assert-equal (dim-poly-mul (dim-poly-add (dim-poly-const 1)
                                          (dim-poly-factor (dim-var "i")))
                            (dim-poly-sub (dim-poly-factor (dim-var "i"))
                                          (dim-poly-const 1)))
              (list (cons nil -1)
                    (cons (list (dim-var "i") (dim-var "i")) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Sums and products of lists of polynomials, including empty lists.

(assert-equal (dim-poly-list-sum nil)
              nil)

(assert-equal (dim-poly-list-sum (list (dim-poly-const 1)
                                       (dim-poly-factor (dim-var "i"))
                                       (dim-poly-const 2)))
              (list (cons nil 3)
                    (cons (list (dim-var "i")) 1)))

(assert-equal (dim-poly-list-product nil)
              (dim-poly-const 1))

(assert-equal (dim-poly-list-product (list (dim-poly-const 2)
                                           (dim-poly-factor (dim-var "i"))
                                           (dim-poly-const 3)))
              (list (cons (list (dim-var "i")) 6)))
