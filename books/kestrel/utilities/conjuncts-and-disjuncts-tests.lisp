; Tests of functions in conjuncts-and-disjuncts.lisp
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "conjuncts-and-disjuncts")
(include-book "std/testing/assert-equal" :dir :system)

(assert-equal (get-conjuncts-of-term 'x) '(x))
(assert-equal (get-conjuncts-of-term '(if x y 'nil)) '(x y)) ; an and
(assert-equal (get-conjuncts-of-term '(if x 't y)) '((if x 't y))) ; an or
(assert-equal (get-conjuncts-of-term '(not (if x x y))) '((not x) (not y))) ; a negated or
(assert-equal (get-conjuncts-of-term '(not (if x 't y))) '((not x) (not y))) ; a negated or

;; test of a negated IF, which is a conjunction.  Should this just return a
;; singleton list containing its argument?
(assert-equal (get-conjuncts-of-term '(not (if x y 'nil))) '((if x (not y) 't)))
