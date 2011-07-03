(in-package "BAG")

;note that this book (top) doesn't include the two-level stuff (see those books if you want it).

(include-book "bind-free-rules") ;this causes meta and basic to be included.
(include-book "cons")
(include-book "neq")

(include-book "eric-meta")

(in-theory (disable memberp-of-cons)) ;can introduce an if
(in-theory (disable remove-1-of-cons-both))
(in-theory (disable remove-1-of-non-consp))
(in-theory (disable subbagp-of-remove-1-implies-subbagp))

(in-theory (disable (:forward-chaining subbagp-disjoint))) ;trying...

(in-theory (disable unique-if-perm-of-something-unique
                    subbagp-false-from-witness
                    non-unique-not-subbagp-of-unique))

(in-theory (disable disjoint-of-append-one
                    disjoint-of-append-two)) ;trying
(in-theory (disable subbagp-remove-bag-append)) ;trying
(in-theory (disable subbagp-remove-bag-subbagp-append)) ;trying
(in-theory (disable non-uniqueness-implications))
(in-theory (disable subbagp-disjoint
                    subbagp-disjoint-commute))
(in-theory (disable subbagp-not-disjoint))
(in-theory (disable subbagp-append-2))
(in-theory (disable subbagp-implies-subbagp-append-rec))
(in-theory (disable unique-of-cons))
(in-theory (disable disjoint-of-cons-one
                    disjoint-of-cons-two
                    unique-of-append
                    subbagp-implies-subbagp-append-car
                    unique-despite-remove-bag
                    subbagp-uniqueness
                    subbagp-memberp-remove-1
                    subbagp-cdr-remove-1-rewrite
                    subbagp-remove-bag
                    subbagp-remove
                    subbagp-remove-1 ;leave enabled?
                    subbagp-of-non-consp-one ;??
                    subbagp-of-non-consp-two
                    subbagp-chaining
                    subbagp-cons ;improve this?
;                    unique-remove-1
                    unique-memberp-remove
                    subbagp-cons-car-memberp
                    not-memberp-implies-not-memberp-remove-1
                    memberp-false-from-disjointness
                    subbagp-implies-membership
                    remove-bag-adds-no-terms
                    memberp-of-append
                    memberp-subbagp
                    memberp-x-remove-x-implies-memberp-x-remove-1-y
                    memberp-of-remove-bag-means-memberp
                    memberp-of-remove-1
                    remove-bag-of-non-consp
                    memberp-car-when-disjoint
                    remove-bag-does-nothing
                    append-commutative-inside-perm
                    disjoint-cdr-from-disjoint
                    ))

;(in-theory (disable append-associative)) ;try
