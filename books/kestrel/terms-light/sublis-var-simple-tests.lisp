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
 ;; the regular sublis-var gives the same thing on this
 (sublis-var-simple (acons 'x 'y nil)
                    ;; :trans (let ((z 3)) (+ x z))
                    '((lambda (z x) (binary-+ x z)) '3 x)
                    )
 ;; :trans (let ((z 3) (x y)) (+ x z))
 '((lambda (z x) (binary-+ x z)) '3 y))

;; Here, it's less clear that there is a nicer alternate result, due to
;; capture:
;; Replaces x with (cons z z) in (let ((z 3)) (+ x z)).
(assert-equal
 (sublis-var-simple (acons 'x '(cons z z) nil)
                    ;; :trans (let ((z 3)) (+ x z))
                    '((lambda (z x) (binary-+ x z)) '3 x)
                    )
 ;; :trans (let ((z 3) (x (cons z z))) (+ x z))
 '((lambda (z x) (binary-+ x z)) '3 (cons z z)))

;; Could produce (let ((x (cons z z))) (let ((z 3)) (+ x z)))
