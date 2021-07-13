; Tests of defthm-stp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
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

(must-fail (defthm-stp test3 x :counterexample t))
