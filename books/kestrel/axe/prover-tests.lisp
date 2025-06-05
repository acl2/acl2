; Tests of the prover
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (uses-stp)

(include-book "defthm-axe")

;;(defthm-axe test1 (equal x x)  :rule-classes nil)

(defthm-axe test2 (equal (bvxor 32 x y) (bvxor 32 y x)) :rule-classes nil)

;; todo: the implies does not get handed:
;(defthm-axe test3 (implies (unsigned-byte-p 32 x) (equal (bvxor 32 x y) (bvxor 32 y x)))  :rule-classes nil)
(defthm-axe test3 (implies (unsigned-byte-p 32 x) (equal (bvxor 32 x y) (bvxor 32 y x))) :rules '(implies) :rule-classes nil)

;(defthm-axe type-mismatch-1 (equal (bvxor 32 x y) (boolif x y z))  :rule-classes nil)

;(defthm-axe type-mismatch-1 (implies (unsigned-byte-p 32 x) (equal (bvxor 32 x y) (boolif x y z)))  :rule-classes nil)
