; Tests of replace-term-with-term
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "replace-term-with-term")
(include-book "std/testing/assert-equal" :dir :system)

(assert-equal
 ;; :trans (let ((z (car x))) (cons z x))
 (replace-term-with-term 'x 'y '((lambda (z x) (cons z x)) (car x) x))
 ;; Note that the (trivial) lambda formal X got renamed to Y:
 '((lambda (z y) (cons z y)) (car y) y))
