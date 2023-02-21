; Tests of sublis-var-simple
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "sublis-var-simple")
(include-book "std/testing/assert-equal" :dir :system)

;; Perhaps surprising.  Adds another binding to the let.
;; We might prefer the result to be (the translation of) (let ((z 3)) (+ y z))
;; but then we have to think about capture
(assert-equal
 (sublis-var-simple (acons 'x 'y nil)
                    ;; :trans (let ((z 3)) (+ x z))
                    '((lambda (z x) (binary-+ x z)) '3 x)
                    )
 ;; :trans (let ((z 3) (x y)) (+ x z))
 '((lambda (z x) (binary-+ x z)) '3 y))
