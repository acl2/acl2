; General lemmas used in the generalization proofs
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These lemmas could be moved to the libraries.

(include-book "kestrel/lists-light/union-equal" :dir :system)
(include-book "kestrel/lists-light/intersectp-equal" :dir :system)
(include-book "kestrel/lists-light/subsetp-equal" :dir :system)
(include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system)

(defthm intersectp-equal-of-union-equal-arg2
  (equal (intersectp-equal x (union-equal y z))
         (or (intersectp-equal x y)
             (intersectp-equal x z)))
  :hints (("Goal" :in-theory (enable intersectp-equal))))

(defthm intersectp-equal-of-true-list-fix-arg2
  (equal (intersectp-equal x (true-list-fix y))
         (intersectp-equal x y))
  :hints (("Goal" :in-theory (enable intersectp-equal true-list-fix))))
