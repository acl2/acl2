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

; A bound pattern variable matches only the dimension bound to it.

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern constants.

; A pattern constant matches only the same constant;
; the substitution is unchanged.

(assert-equal
 (mv-list 2 (dim-match (dim-const 3) (dim-const 3) nil))
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

; The dimensions of the addition are matched element-wise, in order.

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 3) (dim-var "k")))
                       (dim-add (list (dim-var "i") (dim-var "j")))
                       nil))
 (list t (omap::update "i" (dim-const 3)
                       (omap::update "j" (dim-var "k") nil))))

; A repeated pattern variable must match equal dimensions.

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-var "k") (dim-var "k")))
                       (dim-add (list (dim-var "i") (dim-var "i")))
                       nil))
 (list t (omap::update "i" (dim-var "k") nil)))

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-var "k") (dim-var "l")))
                       (dim-add (list (dim-var "i") (dim-var "i")))
                       nil))
 (list nil nil))

; The initial substitution constrains the match.

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

; The addition and the pattern addition must have the same number of dimensions.

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 3)
                                      (dim-var "k")
                                      (dim-var "l")))
                       (dim-add (list (dim-var "i") (dim-var "j")))
                       nil))
 (list nil nil))

(assert-equal
 (mv-list 2 (dim-match (dim-add (list (dim-const 3) (dim-var "k")))
                       (dim-add (list (dim-var "i")
                                      (dim-var "j")
                                      (dim-var "j")))
                       nil))
 (list nil nil))

; A pattern addition matches only an addition.

(assert-equal
 (mv-list 2 (dim-match (dim-var "k")
                       (dim-add (list (dim-var "i") (dim-var "j")))
                       nil))
 (list nil nil))

(assert-equal
 (mv-list 2 (dim-match (dim-const 3)
                       (dim-add (list (dim-var "i") (dim-var "j")))
                       nil))
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

; Tests of SHAPE-MATCH, SHAPE-LIST-MATCH, ISPACE-MATCH, and ISPACE-LIST-MATCH.
; Each test compares the three results
; (success flag, dimension substitution, and shape substitution)
; with the expected ones.
; The pattern variables are i and j for dimensions and s for shapes;
; the shapes and ispaces being matched use
; the variables k and l for dimensions and t for shapes.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern shape variables.

; An unbound pattern variable matches any shape, and is bound to it;
; the dimension substitution is unchanged.

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 2) (dim-const 1)))
                         (shape-var "s")
                         nil
                         nil))
 (list t
       nil
       (omap::update "s"
                     (shape-dims (list (dim-const 2) (dim-const 1)))
                     nil)))

(assert-equal
 (mv-list 3 (shape-match (shape-var "t")
                         (shape-var "s")
                         (omap::update "i" (dim-var "k") nil)
                         nil))
 (list t
       (omap::update "i" (dim-var "k") nil)
       (omap::update "s" (shape-var "t") nil)))

; A bound pattern variable matches only the shape bound to it.

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
 (mv-list 3 (shape-match (shape-dims (list (dim-const 3)))
                         (shape-var "s")
                         nil
                         (omap::update "s"
                                       (shape-dims (list (dim-const 2)))
                                       nil)))
 (list nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern shapes with dimensions.

; The dimensions are matched as by DIM-LIST-MATCH,
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

; A pattern shape with dimensions matches only a shape with dimensions,
; and a pattern concatenation matches only a concatenation:
; the matching is syntactical,
; so (dims 2 1) is not matched by the pattern (++ s (dims 1)),
; even though s could be (dims 2),
; and (++ (dims 2) (dims 1)) is not matched by the pattern (dims 2 1).

(assert-equal
 (mv-list 3 (shape-match (shape-dims (list (dim-const 2) (dim-const 1)))
                         (shape-append (list (shape-var "s")
                                             (shape-dims (list (dim-const 1)))))
                         nil
                         nil))
 (list nil nil nil))

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-dims (list (dim-const 2)))
                                             (shape-dims (list (dim-const 1)))))
                         (shape-dims (list (dim-const 2) (dim-const 1)))
                         nil
                         nil))
 (list nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern concatenations.

; The shapes are matched element-wise, in order,
; threading both substitutions.

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-dims (list (dim-const 2)))
                                             (shape-dims (list (dim-var "k")))))
                         (shape-append (list (shape-var "s")
                                             (shape-dims (list (dim-var "i")))))
                         nil
                         nil))
 (list t
       (omap::update "i" (dim-var "k") nil)
       (omap::update "s" (shape-dims (list (dim-const 2))) nil)))

; A repeated pattern variable must match equal shapes or dimensions.

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-var "t") (shape-var "t")))
                         (shape-append (list (shape-var "s") (shape-var "s")))
                         nil
                         nil))
 (list t
       nil
       (omap::update "s" (shape-var "t") nil)))

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-dims (list (dim-var "k")))
                                             (shape-dims (list (dim-var "l")))))
                         (shape-append (list (shape-dims (list (dim-var "i")))
                                             (shape-dims (list (dim-var "i")))))
                         nil
                         nil))
 (list nil nil nil))

; The concatenation and the pattern concatenation
; must have the same number of shapes.

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-var "t")))
                         (shape-append (list (shape-var "s") (shape-var "s")))
                         nil
                         nil))
 (list nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern splices.

; The ispaces are matched element-wise, in order,
; threading both substitutions.

(assert-equal
 (mv-list 3 (shape-match (shape-splice (list (ispace-dim (dim-const 3))
                                             (ispace-shape (shape-var "t"))))
                         (shape-splice (list (ispace-dim (dim-var "i"))
                                             (ispace-shape (shape-var "s"))))
                         nil
                         nil))
 (list t
       (omap::update "i" (dim-const 3) nil)
       (omap::update "s" (shape-var "t") nil)))

; A pattern splice matches only a splice.

(assert-equal
 (mv-list 3 (shape-match (shape-append (list (shape-dims (list (dim-const 3)))
                                             (shape-var "t")))
                         (shape-splice (list (ispace-dim (dim-var "i"))
                                             (ispace-shape (shape-var "s"))))
                         nil
                         nil))
 (list nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ispaces.

; A pattern dimension ispace matches a dimension ispace as by DIM-MATCH.

(assert-equal
 (mv-list 3 (ispace-match (ispace-dim (dim-add (list (dim-const 3)
                                                     (dim-var "k"))))
                          (ispace-dim (dim-add (list (dim-var "i")
                                                     (dim-var "j"))))
                          nil
                          nil))
 (list t
       (omap::update "i" (dim-const 3)
                     (omap::update "j" (dim-var "k") nil))
       nil))

; A pattern shape ispace matches a shape ispace as by SHAPE-MATCH.

(assert-equal
 (mv-list 3 (ispace-match (ispace-shape (shape-dims (list (dim-const 3))))
                          (ispace-shape (shape-var "s"))
                          nil
                          nil))
 (list t
       nil
       (omap::update "s" (shape-dims (list (dim-const 3))) nil)))

; The kinds of the ispace and of the pattern ispace must agree.

(assert-equal
 (mv-list 3 (ispace-match (ispace-dim (dim-const 3))
                          (ispace-shape (shape-var "s"))
                          nil
                          nil))
 (list nil nil nil))

(assert-equal
 (mv-list 3 (ispace-match (ispace-shape (shape-dims (list (dim-const 3))))
                          (ispace-dim (dim-var "i"))
                          nil
                          nil))
 (list nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lists of shapes and ispaces.

; Empty lists match, and the lists must have the same length.

(assert-equal
 (mv-list 3 (shape-list-match nil nil nil nil))
 (list t nil nil))

(assert-equal
 (mv-list 3 (shape-list-match nil (list (shape-var "s")) nil nil))
 (list nil nil nil))

(assert-equal
 (mv-list 3 (ispace-list-match nil nil nil nil))
 (list t nil nil))

(assert-equal
 (mv-list 3 (ispace-list-match (list (ispace-dim (dim-const 3))) nil nil nil))
 (list nil nil nil))

; The substitutions are threaded through the elements.

(assert-equal
 (mv-list 3 (ispace-list-match (list (ispace-dim (dim-var "k"))
                                     (ispace-shape (shape-var "t"))
                                     (ispace-dim (dim-var "k")))
                               (list (ispace-dim (dim-var "i"))
                                     (ispace-shape (shape-var "s"))
                                     (ispace-dim (dim-var "i")))
                               nil
                               nil))
 (list t
       (omap::update "i" (dim-var "k") nil)
       (omap::update "s" (shape-var "t") nil)))

(assert-equal
 (mv-list 3 (ispace-list-match (list (ispace-dim (dim-var "k"))
                                     (ispace-dim (dim-var "l")))
                               (list (ispace-dim (dim-var "i"))
                                     (ispace-dim (dim-var "i")))
                               nil
                               nil))
 (list nil nil nil))
