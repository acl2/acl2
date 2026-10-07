; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-matcher")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of REMOVE1-EQUIV-DIM and REMOVE1-EQUIV-DIMS.
; Each test compares the two results (flag and list of dimensions)
; with the expected ones.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The first dimension equivalent to the given one is removed;
; the other ones are kept, including later equivalent ones.

(assert-equal
 (mv-list 2 (remove1-equiv-dim (dim-var "k")
                               (list (dim-var "l")
                                     (dim-var "k")
                                     (dim-var "k"))))
 (list t (list (dim-var "l") (dim-var "k"))))

; The equivalence is modulo normalization.

(assert-equal
 (mv-list 2 (remove1-equiv-dim (dim-add (list (dim-var "k") (dim-const 1)))
                               (list (dim-add (list (dim-const 1)
                                                    (dim-var "k"))))))
 (list t nil))

; If no dimension is equivalent, the flag is nil and the list is unchanged.

(assert-equal
 (mv-list 2 (remove1-equiv-dim (dim-var "k")
                               (list (dim-var "l") (dim-const 3))))
 (list nil (list (dim-var "l") (dim-const 3))))

(assert-equal
 (mv-list 2 (remove1-equiv-dim (dim-var "k") nil))
 (list nil nil))

; One dimension is removed for each dimension of the first list,
; counting repetitions.

(assert-equal
 (mv-list 2 (remove1-equiv-dims (list (dim-var "k") (dim-const 3))
                                (list (dim-const 3)
                                      (dim-var "l")
                                      (dim-var "k"))))
 (list t (list (dim-var "l"))))

(assert-equal
 (mv-list 2 (remove1-equiv-dims (list (dim-var "k") (dim-var "k"))
                                (list (dim-var "k")
                                      (dim-var "k")
                                      (dim-var "l"))))
 (list t (list (dim-var "l"))))

(assert-equal
 (mv-list 2 (remove1-equiv-dims (list (dim-var "k") (dim-var "k"))
                                (list (dim-var "k") (dim-var "l"))))
 (list nil nil))

; An empty first list removes nothing.

(assert-equal
 (mv-list 2 (remove1-equiv-dims nil (list (dim-var "k"))))
 (list t (list (dim-var "k"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of DIM-VARS-BOUND-P.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal
 (dim-vars-bound-p (dim-mul (list (dim-const 2) (dim-var "i")))
                   (omap::update "i" (dim-var "k") nil))
 t)

(assert-equal
 (dim-vars-bound-p (dim-mul (list (dim-var "j") (dim-var "i")))
                   (omap::update "i" (dim-var "k") nil))
 nil)

(assert-equal
 (dim-vars-bound-p (dim-const 3) nil)
 t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of DIM-ADD-MATCH.
; Each test compares the two results (success flag and substitution)
; with the expected ones.
; The second argument consists of the addends of the pattern addition.
; The pattern variables are i and j;
; the dimensions being matched use the variables k and l.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A single unbound pattern variable is bound to
; the remainder of the dimension after accounting for the other addends,
; which may be a constant, a variable, an addition, or 0.

(assert-equal
 (mv-list 2 (dim-add-match (dim-const 5)
                           (list (dim-const 1) (dim-var "i"))
                           nil))
 (list t (omap::update "i" (dim-const 4) nil)))

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-const 1) (dim-var "k")))
                           (list (dim-const 1) (dim-var "i"))
                           nil))
 (list t (omap::update "i" (dim-var "k") nil)))

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-const 2) (dim-var "k")))
                           (list (dim-const 1) (dim-var "i"))
                           nil))
 (list t (omap::update "i" (dim-add (list (dim-const 1) (dim-var "k"))) nil)))

(assert-equal
 (mv-list 2 (dim-add-match (dim-const 1)
                           (list (dim-const 1) (dim-var "i"))
                           nil))
 (list t (omap::update "i" (dim-const 0) nil)))

; A dimension that is not an addition is viewed as one.

(assert-equal
 (mv-list 2 (dim-add-match (dim-var "k")
                           (list (dim-var "i"))
                           nil))
 (list t (omap::update "i" (dim-var "k") nil)))

; A bound pattern variable contributes its binding,
; including a variable bound to itself.

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-const 3) (dim-var "k")))
                           (list (dim-var "i") (dim-var "j"))
                           (omap::update "i" (dim-const 3) nil)))
 (list t (omap::update "i" (dim-const 3)
                       (omap::update "j" (dim-var "k") nil))))

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-const 1) (dim-var "k")))
                           (list (dim-var "i") (dim-var "k"))
                           (omap::update "k" (dim-var "k") nil)))
 (list t (omap::update "i" (dim-const 1)
                       (omap::update "k" (dim-var "k") nil))))

; Without unbound pattern variables,
; the addends must account for the whole dimension.

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-const 3) (dim-var "k")))
                           (list (dim-var "i") (dim-var "j"))
                           (omap::update "i" (dim-const 3)
                                         (omap::update "j" (dim-var "k") nil))))
 (list t (omap::update "i" (dim-const 3)
                       (omap::update "j" (dim-var "k") nil))))

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-const 3) (dim-var "k")))
                           (list (dim-var "i") (dim-var "j"))
                           (omap::update "i" (dim-const 3)
                                         (omap::update "j" (dim-var "l") nil))))
 (list nil nil))

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-const 3) (dim-var "k")))
                           (list (dim-var "i"))
                           (omap::update "i" (dim-const 3) nil)))
 (list nil nil))

; The constants of the pattern must not exceed the one of the dimension.

(assert-equal
 (mv-list 2 (dim-add-match (dim-const 3)
                           (list (dim-const 4) (dim-var "i"))
                           nil))
 (list nil nil))

; Two unbound pattern variables, or one occurring twice,
; make the solution non-unique: the match fails.

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-const 3) (dim-var "k")))
                           (list (dim-var "i") (dim-var "j"))
                           nil))
 (list nil nil))

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-var "k") (dim-var "k")))
                           (list (dim-var "i") (dim-var "i"))
                           nil))
 (list nil nil))

; A multiplication addend with all its variables bound
; is instantiated and accounted for;
; with an unbound variable, the match fails.

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-const 1)
                                          (dim-mul (list (dim-const 2)
                                                         (dim-var "k")))))
                           (list (dim-var "i")
                                 (dim-mul (list (dim-const 2) (dim-var "j"))))
                           (omap::update "j" (dim-var "k") nil)))
 (list t (omap::update "i" (dim-const 1)
                       (omap::update "j" (dim-var "k") nil))))

(assert-equal
 (mv-list 2 (dim-add-match (dim-add (list (dim-const 1)
                                          (dim-mul (list (dim-const 2)
                                                         (dim-var "k")))))
                           (list (dim-const 1)
                                 (dim-mul (list (dim-const 2) (dim-var "j"))))
                           nil))
 (list nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of DIM-MATCH and DIM-LIST-MATCH.
; Each test compares the two results (success flag and substitution)
; with the expected ones.
; The pattern variables are i and j;
; the dimensions being matched use the variables k and l.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern variables.

; An unbound pattern variable matches any dimension, and is bound to it.

(assert-equal
 (mv-list 2 (dim-match (dim-var "k") (dim-var "i") nil))
 (list t (omap::update "i" (dim-var "k") nil)))

(assert-equal
 (mv-list 2 (dim-match (dim-const 3) (dim-var "i") nil))
 (list t (omap::update "i" (dim-const 3) nil)))

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 3) (dim-var "k")))
                       (dim-var "i")
                       nil))
 (list t (omap::update "i" (dim-add (list (dim-const 3) (dim-var "k"))) nil)))

; A bound pattern variable matches only
; a dimension equivalent to the one bound to it.

(assert-equal
 (mv-list 2 (dim-match (dim-var "k")
                       (dim-var "i")
                       (omap::update "i" (dim-var "k") nil)))
 (list t (omap::update "i" (dim-var "k") nil)))

(assert-equal
 (mv-list 2 (dim-match (dim-var "l")
                       (dim-var "i")
                       (omap::update "i" (dim-var "k") nil)))
 (list nil nil))

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-var "k") (dim-const 1)))
                       (dim-var "i")
                       (omap::update "i"
                                     (dim-add (list (dim-const 1) (dim-var "k")))
                                     nil)))
 (list t (omap::update "i" (dim-add (list (dim-const 1) (dim-var "k"))) nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern constants.

; A pattern constant matches only an equivalent dimension,
; i.e. one that normalizes to the same constant;
; the substitution is unchanged.

(assert-equal
 (mv-list 2 (dim-match (dim-const 3) (dim-const 3) nil))
 (list t nil))

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 1) (dim-const 2)))
                       (dim-const 3)
                       nil))
 (list t nil))

(assert-equal
 (mv-list 2 (dim-match (dim-const 3)
                       (dim-const 3)
                       (omap::update "i" (dim-var "k") nil)))
 (list t (omap::update "i" (dim-var "k") nil)))

(assert-equal
 (mv-list 2 (dim-match (dim-const 4) (dim-const 3) nil))
 (list nil nil))

; Variables in the dimension being matched are not pattern variables:
; a variable dimension does not match a constant pattern.

(assert-equal
 (mv-list 2 (dim-match (dim-var "k") (dim-const 3) nil))
 (list nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern additions.

; A pattern addition is matched modulo additive equivalence
; (see the tests of DIM-ADD-MATCH for more details):
; the dimension need not be an addition,
; and the addends need not correspond in number or order.

(assert-equal
 (mv-list 2 (dim-match (dim-const 5)
                       (dim-add (list (dim-const 1) (dim-var "i")))
                       nil))
 (list t (omap::update "i" (dim-const 4) nil)))

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 2) (dim-var "k")))
                       (dim-add (list (dim-const 1) (dim-var "i")))
                       nil))
 (list t (omap::update "i" (dim-add (list (dim-const 1) (dim-var "k"))) nil)))

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 3) (dim-var "k")))
                       (dim-add (list (dim-var "i") (dim-const 3)))
                       nil))
 (list t (omap::update "i" (dim-var "k") nil)))

; The initial substitution constrains the match,
; and may make its solution unique.

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 3) (dim-var "k")))
                       (dim-add (list (dim-var "i") (dim-var "j")))
                       (omap::update "i" (dim-const 3) nil)))
 (list t (omap::update "i" (dim-const 3)
                       (omap::update "j" (dim-var "k") nil))))

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 3) (dim-var "k")))
                       (dim-add (list (dim-var "i") (dim-var "j")))
                       (omap::update "i" (dim-const 4) nil)))
 (list nil nil))

; Two unbound pattern variables, or one occurring twice,
; make the solution non-unique, and the match fails.

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 3) (dim-var "k")))
                       (dim-add (list (dim-var "i") (dim-var "j")))
                       nil))
 (list nil nil))

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-var "k") (dim-var "k")))
                       (dim-add (list (dim-var "i") (dim-var "i")))
                       nil))
 (list nil nil))

; The known part of the pattern must not exceed the dimension.

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 3) (dim-var "k")))
                       (dim-add (list (dim-const 4) (dim-var "i")))
                       nil))
 (list nil nil))

(assert-equal
 (mv-list 2 (dim-match (dim-var "k")
                       (dim-add (list (dim-var "l") (dim-var "i")))
                       (omap::update "l" (dim-var "l") nil)))
 (list nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lists of dimensions.

; Empty lists match, and a non-empty list does not match an empty one.

(assert-equal
 (mv-list 2 (dim-list-match nil nil nil))
 (list t nil))

(assert-equal
 (mv-list 2 (dim-list-match (list (dim-var "k")) nil nil))
 (list nil nil))

(assert-equal
 (mv-list 2 (dim-list-match nil (list (dim-var "i")) nil))
 (list nil nil))

; The substitution is threaded through the elements:
; the binding of i from the first element is checked against the second.

(assert-equal
 (mv-list 2 (dim-list-match (list (dim-var "k") (dim-var "k"))
                            (list (dim-var "i") (dim-var "i"))
                            nil))
 (list t (omap::update "i" (dim-var "k") nil)))

(assert-equal
 (mv-list 2 (dim-list-match (list (dim-var "k") (dim-const 3))
                            (list (dim-var "i") (dim-var "i"))
                            nil))
 (list nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of SHAPE-PATTERN-ELEMENTS-LENGTH.
; Each test compares the two results (flag and number of elements)
; with the expected ones.
; The pattern variables are i for dimensions and s and u for shapes;
; the shapes being matched use the variables k and l for dimensions
; and t for shapes.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An element with a single dimension needs one element.

(assert-equal
 (mv-list 2 (shape-pattern-elements-length nil nil))
 (list t 0))

(assert-equal
 (mv-list 2 (shape-pattern-elements-length (list (shape-dims (list (dim-var "i"))))
                                           nil))
 (list t 1))

(assert-equal
 (mv-list 2 (shape-pattern-elements-length (list (shape-dims (list (dim-var "i")))
                                                 (shape-dims (list (dim-const 3))))
                                           nil))
 (list t 2))

; A bound shape variable needs as many elements as its normalized binding.

(assert-equal
 (mv-list 2 (shape-pattern-elements-length
             (list (shape-var "s"))
             (omap::update "s"
                           (shape-dims (list (dim-const 2) (dim-const 3)))
                           nil)))
 (list t 2))

(assert-equal
 (mv-list 2 (shape-pattern-elements-length
             (list (shape-var "s") (shape-dims (list (dim-var "i"))))
             (omap::update "s" (shape-append nil) nil)))
 (list t 1))

(assert-equal
 (mv-list 2 (shape-pattern-elements-length
             (list (shape-var "s"))
             (omap::update "s" (shape-var "t") nil)))
 (list t 1))

; An unbound shape variable makes the number undetermined.

(assert-equal
 (mv-list 2 (shape-pattern-elements-length (list (shape-var "s")) nil))
 (list nil 0))

(assert-equal
 (mv-list 2 (shape-pattern-elements-length
             (list (shape-dims (list (dim-var "i")))
                   (shape-var "s")
                   (shape-dims (list (dim-const 3))))
             nil))
 (list nil 0))

(assert-equal
 (mv-list 2 (shape-pattern-elements-length
             (list (shape-var "s") (shape-var "u"))
             (omap::update "s" (shape-var "t") nil)))
 (list nil 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of SHAPE-ELEMENTS-MATCH.
; Each test compares the three results
; (success flag, dimension substitution, and shape substitution)
; with the expected ones.
; The two lists consist of the elements of normalized concatenations.
; The pattern variables are i and j for dimensions and s and u for shapes;
; the shapes being matched use the variables k and l for dimensions
; and t for shapes.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (dims 2 1) matched to (++ @s (dims 1)): @s is (++ (dims 2)).

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 2)))
                                        (shape-dims (list (dim-const 1))))
                                  (list (shape-var "s")
                                        (shape-dims (list (dim-const 1))))
                                  nil
                                  nil))
 (list t
       nil
       (omap::update "s"
                     (shape-append (list (shape-dims (list (dim-const 2)))))
                     nil)))

; (dims 3) matched to [$i @s]: $i is 3 and @s is (++).

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 3))))
                                  (list (shape-dims (list (dim-var "i")))
                                        (shape-var "s"))
                                  nil
                                  nil))
 (list t
       (omap::update "i" (dim-const 3) nil)
       (omap::update "s" (shape-append nil) nil)))

; (dims 3) matched to [(+ 1 $i) @s]: $i is 2 and @s is (++).

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 3))))
                                  (list (shape-dims
                                         (list (dim-add (list (dim-const 1)
                                                              (dim-var "i")))))
                                        (shape-var "s"))
                                  nil
                                  nil))
 (list t
       (omap::update "i" (dim-const 2) nil)
       (omap::update "s" (shape-append nil) nil)))

; An unbound shape variable may be anywhere in the pattern,
; and it may absorb shape variables and any number of elements.

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-var "t")
                                        (shape-dims (list (dim-const 3))))
                                  (list (shape-var "s")
                                        (shape-dims (list (dim-var "i"))))
                                  nil
                                  nil))
 (list t
       (omap::update "i" (dim-const 3) nil)
       (omap::update "s" (shape-append (list (shape-var "t"))) nil)))

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 2)))
                                        (shape-dims (list (dim-const 3)))
                                        (shape-dims (list (dim-const 4))))
                                  (list (shape-dims (list (dim-var "i")))
                                        (shape-var "s")
                                        (shape-dims (list (dim-var "j"))))
                                  nil
                                  nil))
 (list t
       (omap::update "i" (dim-const 2)
                     (omap::update "j" (dim-const 4) nil))
       (omap::update "s"
                     (shape-append (list (shape-dims (list (dim-const 3)))))
                     nil)))

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 2)))
                                        (shape-var "t"))
                                  (list (shape-var "s"))
                                  nil
                                  nil))
 (list t
       nil
       (omap::update "s"
                     (shape-append (list (shape-dims (list (dim-const 2)))
                                         (shape-var "t")))
                     nil)))

; A bound shape variable consumes the elements of its binding,
; which must be equivalent to them; the binding need not be normalized.

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 2)))
                                        (shape-dims (list (dim-const 1))))
                                  (list (shape-var "s")
                                        (shape-dims (list (dim-const 1))))
                                  nil
                                  (omap::update "s"
                                                (shape-dims (list (dim-const 2)))
                                                nil)))
 (list t
       nil
       (omap::update "s" (shape-dims (list (dim-const 2))) nil)))

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 2)))
                                        (shape-dims (list (dim-const 1))))
                                  (list (shape-var "s")
                                        (shape-dims (list (dim-const 1))))
                                  nil
                                  (omap::update "s"
                                                (shape-dims (list (dim-const 5)))
                                                nil)))
 (list nil nil nil))

; A rigid shape variable, bound to itself, consumes itself.

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-var "t")
                                        (shape-dims (list (dim-const 3))))
                                  (list (shape-var "t")
                                        (shape-dims (list (dim-var "i"))))
                                  nil
                                  (omap::update "t" (shape-var "t") nil)))
 (list t
       (omap::update "i" (dim-const 3) nil)
       (omap::update "t" (shape-var "t") nil)))

; Two unbound shape variables, or one occurring twice,
; make the solution non-unique: the match fails.

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 2)))
                                        (shape-dims (list (dim-const 3))))
                                  (list (shape-var "s") (shape-var "u"))
                                  nil
                                  nil))
 (list nil nil nil))

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-var "t") (shape-var "t"))
                                  (list (shape-var "s") (shape-var "s"))
                                  nil
                                  nil))
 (list nil nil nil))

; An element with a dimension does not match a shape variable element,
; the dimensions must match, and all the elements must be consumed.

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-var "t"))
                                  (list (shape-dims (list (dim-var "i"))))
                                  nil
                                  nil))
 (list nil nil nil))

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 2))))
                                  (list (shape-dims (list (dim-const 3))))
                                  nil
                                  nil))
 (list nil nil nil))

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 2)))
                                        (shape-dims (list (dim-const 3))))
                                  (list (shape-dims (list (dim-var "i"))))
                                  nil
                                  nil))
 (list nil nil nil))

(assert-equal
 (mv-list 3 (shape-elements-match (list (shape-dims (list (dim-const 2))))
                                  (list (shape-var "s")
                                        (shape-dims (list (dim-var "i"))))
                                  nil
                                  (omap::update "s"
                                                (shape-dims (list (dim-const 2)))
                                                nil)))
 (list nil nil nil))

; Empty lists match.

(assert-equal
 (mv-list 3 (shape-elements-match nil nil nil nil))
 (list t nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of SHAPE-MATCH and ISPACE-MATCH.
; Each test compares the three results
; (success flag, dimension substitution, and shape substitution)
; with the expected ones.
; The pattern variables are i and j for dimensions and s for shapes;
; the shapes and ispaces being matched use
; the variables k and l for dimensions and t for shapes.
; The shapes and ispaces need not be normalized,
; and the pattern shape variables are bound to normalized concatenations.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern shape variables.

; An unbound pattern variable matches any shape,
; and is bound to the normalized concatenation of the shape;
; the dimension substitution is unchanged.

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 2) (dim-const 1)))
                         (shape-var "s")
                         nil
                         nil))
 (list t
       nil
       (omap::update "s"
                     (shape-append (list (shape-dims (list (dim-const 2)))
                                         (shape-dims (list (dim-const 1)))))
                     nil)))

(assert-equal
 (mv-list 3 (shape-match (shape-var "t")
                         (shape-var "s")
                         (omap::update "i" (dim-var "k") nil)
                         nil))
 (list t
       (omap::update "i" (dim-var "k") nil)
       (omap::update "s" (shape-append (list (shape-var "t"))) nil)))

; A bound pattern variable matches only shapes equivalent to its binding,
; which is left unchanged.

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 2)))
                         (shape-var "s")
                         nil
                         (omap::update "s"
                                       (shape-dims (list (dim-const 2)))
                                       nil)))
 (list t
       nil
       (omap::update "s" (shape-dims (list (dim-const 2))) nil)))

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-dims (list (dim-const 2)))))
                         (shape-var "s")
                         nil
                         (omap::update "s"
                                       (shape-dims (list (dim-const 2)))
                                       nil)))
 (list t
       nil
       (omap::update "s" (shape-dims (list (dim-const 2))) nil)))

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 3)))
                         (shape-var "s")
                         nil
                         (omap::update "s"
                                       (shape-dims (list (dim-const 2)))
                                       nil)))
 (list nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern shapes with dimensions.

; The dimensions are matched as by DIM-MATCH,
; extending the dimension substitution;
; the shape substitution is unchanged.

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 2) (dim-const 1)))
                         (shape-dims (list (dim-var "i") (dim-const 1)))
                         nil
                         (omap::update "s" (shape-var "t") nil)))
 (list t
       (omap::update "i" (dim-const 2) nil)
       (omap::update "s" (shape-var "t") nil)))

; The initial dimension substitution constrains the match.

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 2)))
                         (shape-dims (list (dim-var "i")))
                         (omap::update "i" (dim-const 3) nil)
                         nil))
 (list nil nil nil))

; The dimensions are matched modulo additive equivalence.

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 5)))
                         (shape-dims (list (dim-add (list (dim-const 1)
                                                          (dim-var "i")))))
                         nil
                         nil))
 (list t
       (omap::update "i" (dim-const 4) nil)
       nil))

; The numbers of dimensions must agree.

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 2) (dim-const 1)))
                         (shape-dims (list (dim-var "i")))
                         nil
                         nil))
 (list nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matching modulo shape equivalence.

; (dims 2 1) is matched by the pattern (++ @s (dims 1)),
; with @s bound to (++ (dims 2)),
; and (++ (dims 2) (dims 1)) is matched by the pattern (dims 2 1).

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 2) (dim-const 1)))
                         (shape-append (list (shape-var "s")
                                             (shape-dims (list (dim-const 1)))))
                         nil
                         nil))
 (list t
       nil
       (omap::update "s"
                     (shape-append (list (shape-dims (list (dim-const 2)))))
                     nil)))

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-dims (list (dim-const 2)))
                                             (shape-dims (list (dim-const 1)))))
                         (shape-dims (list (dim-const 2) (dim-const 1)))
                         nil
                         nil))
 (list t nil nil))

; (dims 3) is matched by the pattern [$i @s],
; with $i bound to 3 and @s bound to the empty concatenation.

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 3)))
                         (shape-splice (list (ispace-dim (dim-var "i"))
                                             (ispace-shape (shape-var "s"))))
                         nil
                         nil))
 (list t
       (omap::update "i" (dim-const 3) nil)
       (omap::update "s" (shape-append nil) nil)))

; The nesting of concatenations and splices is irrelevant.

(assert-equal
 (mv-list 3 (shape-match
             (shape-append (list (shape-dims (list (dim-const 2) (dim-const 3)))
                                 (shape-var "t")))
             (shape-splice (list (ispace-dim (dim-var "i"))
                                 (ispace-shape
                                  (shape-append
                                   (list (shape-dims (list (dim-var "j")))
                                         (shape-var "s"))))))
             nil
             nil))
 (list t
       (omap::update "i" (dim-const 2) (omap::update "j" (dim-const 3) nil))
       (omap::update "s" (shape-append (list (shape-var "t"))) nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Repeated pattern variables.

; A repeated pattern dimension variable must match equivalent dimensions.

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-dims (list (dim-var "k")))
                                             (shape-dims (list (dim-var "k")))))
                         (shape-append (list (shape-dims (list (dim-var "i")))
                                             (shape-dims (list (dim-var "i")))))
                         nil
                         nil))
 (list t
       (omap::update "i" (dim-var "k") nil)
       nil))

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-dims (list (dim-var "k")))
                                             (shape-dims (list (dim-var "l")))))
                         (shape-append (list (shape-dims (list (dim-var "i")))
                                             (shape-dims (list (dim-var "i")))))
                         nil
                         nil))
 (list nil nil nil))

; A repeated unbound pattern shape variable makes the match fail,
; because the length of its segment is not determined in general,
; even though here @s could be bound to (++ @t).

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-var "t") (shape-var "t")))
                         (shape-append (list (shape-var "s") (shape-var "s")))
                         nil
                         nil))
 (list nil nil nil))

; The shape must have enough elements for the pattern.

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 2)))
                         (shape-append (list (shape-var "s")
                                             (shape-dims (list (dim-const 1)))
                                             (shape-dims (list (dim-const 2)))))
                         nil
                         nil))
 (list nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern splices.

; The ispaces of a splice are matched as the elements of a concatenation.

(assert-equal
 (mv-list 3 (shape-match (shape-splice (list (ispace-dim (dim-const 3))
                                             (ispace-shape (shape-var "t"))))
                         (shape-splice (list (ispace-dim (dim-var "i"))
                                             (ispace-shape (shape-var "s"))))
                         nil
                         nil))
 (list t
       (omap::update "i" (dim-const 3) nil)
       (omap::update "s" (shape-append (list (shape-var "t"))) nil)))

; A pattern splice also matches an equivalent concatenation.

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-dims (list (dim-const 3)))
                                             (shape-var "t")))
                         (shape-splice (list (ispace-dim (dim-var "i"))
                                             (ispace-shape (shape-var "s"))))
                         nil
                         nil))
 (list t
       (omap::update "i" (dim-const 3) nil)
       (omap::update "s" (shape-append (list (shape-var "t"))) nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ispaces.

; A pattern dimension ispace matches a dimension ispace as by DIM-MATCH.

(assert-equal
 (mv-list 3 (ispace-match (ispace-dim (dim-add (list (dim-const 3)
                                                     (dim-var "k"))))
                          (ispace-dim (dim-add (list (dim-const 1)
                                                     (dim-var "i"))))
                          nil
                          nil))
 (list t
       (omap::update "i" (dim-add (list (dim-const 2) (dim-var "k"))) nil)
       nil))

; A pattern shape ispace matches a shape ispace as by SHAPE-MATCH.

(assert-equal
 (mv-list 3 (ispace-match (ispace-shape (shape-dims (list (dim-const 3))))
                          (ispace-shape (shape-var "s"))
                          nil
                          nil))
 (list t
       nil
       (omap::update "s"
                     (shape-append (list (shape-dims (list (dim-const 3)))))
                     nil)))

; A dimension ispace is equivalent to a shape ispace with that single dimension,
; so the kinds of the ispace and of the pattern ispace need not agree.

(assert-equal
 (mv-list 3 (ispace-match (ispace-dim (dim-const 3))
                          (ispace-shape (shape-var "s"))
                          nil
                          nil))
 (list t
       nil
       (omap::update "s"
                     (shape-append (list (shape-dims (list (dim-const 3)))))
                     nil)))

(assert-equal
 (mv-list 3 (ispace-match (ispace-shape (shape-dims (list (dim-const 3))))
                          (ispace-dim (dim-var "i"))
                          nil
                          nil))
 (list t
       (omap::update "i" (dim-const 3) nil)
       nil))

; But a shape ispace with two dimensions
; does not match a pattern dimension ispace.

(assert-equal
 (mv-list 3 (ispace-match (ispace-shape (shape-dims (list (dim-const 3)
                                                          (dim-const 4))))
                          (ispace-dim (dim-var "i"))
                          nil
                          nil))
 (list nil nil nil))