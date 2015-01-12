; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "BAG")

;note that this book (top) doesn't include the two-level stuff (see those books if you want it).

(include-book "bind-free-rules") ;this causes meta and basic to be included.
(include-book "cons")
(include-book "neq")

(include-book "eric-meta")

(in-theory (disable LIST::memberp-of-cons)) ;can introduce an if
(in-theory (disable remove-1-of-cons-both))
(in-theory (disable remove-1-of-non-consp))
(in-theory (disable subbagp-of-remove-1-implies-subbagp))

(in-theory (disable (:forward-chaining subbagp-disjoint))) ;trying...

(in-theory (disable ;; jcd - removed unique-if-perm-of-something-unique
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
;                    subbagp-uniqueness
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
                    LIST::memberp-of-append
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