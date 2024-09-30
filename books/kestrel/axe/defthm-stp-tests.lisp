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

;; A simple test that uses STP to prove that bvplus is commutative (on 32-bit values).
(deftest
  (defthm-stp test1 (equal (bvplus 32 x y) (bvplus 32 y x))))

;; A simple test that is not true:
(must-fail (defthm-stp test3 (equal (bvplus 32 x y) (bvplus 32 x z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; test of :rule-classes nil
(deftest
  (defthm-stp test2 (equal (bvplus 32 x y) (bvplus 32 x y)) :rule-classes nil))

;; test :counterexample
(must-fail (defthm-stp test3 (equal (bvplus 32 x y) (bvplus 32 x z)) :counterexample t))

; "Dropping a disjunct that is a (possibly negated) variable: X."
; "Note: No disjuncts. Not calling STP."
(must-fail (defthm-stp test3 x :counterexample t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Some tests with BVSX:
(deftest
  (defthm-stp bvsx-32-16-def
    (implies (unsigned-byte-p 64 x)
             (equal (bvsx 32 16 x)
                    (bvif 32 (equal 1 (getbit 15 x))
                          (bvcat 16 65535 16 (bvsx 32 16 x))
                          (bvsx 32 16 x))))
    :rule-classes nil))

(must-fail
  (defthm-stp bvsx-32-16-def-bad
    (implies (unsigned-byte-p 64 x)
             (equal (bvsx 32 16 x)
                    (bvif 32 (equal 1 (getbit 15 x))
                          (bvcat 16 65534 ; note this: should be 65535
                                 16 (bvsx 32 16 x))
                          (bvsx 32 16 x))))
    :rule-classes nil))

(must-fail (defthm-stp bvsx-bad
             (implies (unsigned-byte-p 64 x)
                      (equal (bvsx 32 16 x) (bvsx 32 16 y)))
             :rule-classes nil))
