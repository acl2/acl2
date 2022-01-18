; Tests of simple-subsumption-clause-processor

; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "simple-subsumption")
(include-book "std/testing/assert-equal" :dir :system)

(assert-equal (simple-subsumption-clause-processor '(x x))
              ;; returns a list containing 1 new clause:
              '((x)))

;;resolves the IF (can assume X false since if X is true the whole clause is true):
(assert-equal (simple-subsumption-clause-processor '(x (if x y1 y2)))
              '((x y2)))

;; still resolves the IF (digs out the fact that x is false from assuming that
;; (or x z) = (if x x z) is false):
(assert-equal (simple-subsumption-clause-processor '((if x x z) (if x y1 y2)))
              '(((if x x z) y2)))
