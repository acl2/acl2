; Tests of defthm-stp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (uses-stp)

(include-book "defthm-stp")
(include-book "std/testing/must-fail" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (defthm-stp test1 (equal (bvplus 32 x y) (bvplus 32 y x))))

;; test of :rule-classes nil
(deftest
  (defthm-stp test2 (equal (bvplus 32 x y) (bvplus 32 x y)) :rule-classes nil))

;; this one is not true:
(must-fail (defthm-stp test3 (equal (bvplus 32 x y) (bvplus 32 x z))))

;; test :counterexample
(must-fail (defthm-stp test3 (equal (bvplus 32 x y) (bvplus 32 x z)) :counterexample t))

; "Dropping a disjunct that is a (possibly negated) variable: X."
; "Note: No disjuncts. Not calling STP."
(must-fail (defthm-stp test3 x :counterexample t))

;; Test whether the arg to BVSX gets chopped right:
(deftest
  (defthm-stp foo (implies (unsigned-byte-p 64 x) (equal (bvsx 32 16 x) (bvsx 32 16 x))) :rule-classes nil))
(must-fail (defthm-stp foo (implies (unsigned-byte-p 64 x) (equal (bvsx 32 16 x) (bvsx 32 16 y))) :rule-classes nil))
