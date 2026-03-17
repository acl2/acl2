; Tests for simplify-conjunctions
;
; Copyright (C) 2022-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "simplify-conjunctions")
(include-book "def")
(include-book "std/testing/must-be-redundant" :dir :system)

(acl2::add-known-boolean natp) ; todo: automate

(defund foo1 (x) (and (natp x) (natp x)))
(def foo1.new (simplify-conjunctions foo1))
(must-be-redundant
 (defund foo1.new (x) (declare (xargs :verify-guards nil)) (natp x)) ; one occurence of natp got removed
 (defthm foo1-becomes-foo1.new (equal (foo1 x) (foo1.new x))))

(defund foo2 (x y) (and (natp x) (equal x 3) (< x y)))
(def foo2.new (simplify-conjunctions foo2))
(must-be-redundant
 (defund foo2.new (x y) (declare (xargs :verify-guards nil)) (and (equal x 3) (< 3 y))) ; x got replaced by 3 and (natp 3) got evaluated
 (defthm foo2-becomes-foo2.new (equal (foo2 x y) (foo2.new x y))))
