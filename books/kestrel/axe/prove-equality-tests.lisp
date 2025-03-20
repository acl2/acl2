; Tests of prove-equality
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

;; todo: rename to test-case-type-alist:
(prove-equality 'x 'x :input-type-alist '((x . 8)))

(must-fail
  (prove-equality 'x 'y :input-type-alist '((x . 8) (y . 8))))
