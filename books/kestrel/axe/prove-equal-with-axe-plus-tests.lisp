; Tests of prove-equal-with-axe+
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "equivalence-checker")

(prove-equal-with-axe+ 'x 'x :types '((x . 8)))

(must-fail
  (prove-equal-with-axe+ 'x 'y :types '((x . 8) (y . 8))))
