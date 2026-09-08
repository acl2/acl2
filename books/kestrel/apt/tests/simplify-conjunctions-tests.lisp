; Tests for simplify-conjunctions
;
; Copyright (C) 2022-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../simplify-conjunctions")
(include-book "../def")
(include-book "std/testing/must-be-redundant" :dir :system)

(acl2::add-known-boolean natp) ; todo: automate

(defund conj1 (x) (and (natp x) (natp x)))
(def conj1.new (simplify-conjunctions conj1))
(must-be-redundant
 (defund conj1.new (x) (declare (xargs :verify-guards nil)) (natp x)) ; one occurence of natp got removed
 (defthm conj1-becomes-conj1.new (equal (conj1 x) (conj1.new x))))

(defund conj2 (x y) (and (natp x) (equal x 3) (< x y)))
(def conj2.new (simplify-conjunctions conj2))
(must-be-redundant
 (defund conj2.new (x y) (declare (xargs :verify-guards nil)) (and (equal x 3) (< 3 y))) ; x got replaced by 3 and (natp 3) got evaluated
 (defthm conj2-becomes-conj2.new (equal (conj2 x y) (conj2.new x y))))
