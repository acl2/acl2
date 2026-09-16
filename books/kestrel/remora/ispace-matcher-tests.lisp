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
