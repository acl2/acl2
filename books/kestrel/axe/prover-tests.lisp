; Tests of the prover
;
; Copyright (C) 2024-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (uses-stp)

;; TODO: Move the defthm-axe tests to a separate file?

(include-book "defthm-axe")
(include-book "kestrel/utilities/deftest" :dir :system)

;;(defthm-axe test1 (equal x x)  :rule-classes nil)

(defthm-axe test2 (equal (bvxor 32 x y) (bvxor 32 y x)) :rule-classes nil)

;; todo: the implies does not get handled:
;(defthm-axe test3 (implies (unsigned-byte-p 32 x) (equal (bvxor 32 x y) (bvxor 32 y x)))  :rule-classes nil)
(defthm-axe test3 (implies (unsigned-byte-p 32 x) (equal (bvxor 32 x y) (bvxor 32 y x))) :rules '(implies) :rule-classes nil)

;(defthm-axe type-mismatch-1 (equal (bvxor 32 x y) (boolif x y z))  :rule-classes nil)

;(defthm-axe type-mismatch-1 (implies (unsigned-byte-p 32 x) (equal (bvxor 32 x y) (boolif x y z)))  :rule-classes nil)

;; TODO: Works but calls STP (because replacements are not made in a way that uses the known-booleans?)
(deftest
  (defthm-axe new-test0
    (implies (and (unsigned-byte-p 3 x)
                  (unsigned-byte-p 4 y))
             (equal (unsigned-byte-p 3 x)
                    (unsigned-byte-p 4 y)))
    ;; trying to get it to rewrite:
    :rule-lists '((car-cons))
    ;;    :count-hits t ; todo
    ))

;; TODO: This works, but it calls STP (issues with known-booleans?)
(deftest
  (defthm-axe new-test1
    (implies (and (unsigned-byte-p 3 x)
                  (unsigned-byte-p 4 y))
             (equal (unsigned-byte-p 3 x)
                    (unsigned-byte-p 4 y)))))
