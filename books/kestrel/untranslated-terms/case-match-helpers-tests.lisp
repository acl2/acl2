; Tests of case-match-helpers.lisp
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "case-match-helpers")
(include-book "std/testing/assert-equal" :dir :system)

(assert-equal (vars-bound-in-case-match-pattern 'x) '(x))
(assert-equal (vars-bound-in-case-match-pattern '(x (x y))) '(y x))
(assert-equal (vars-bound-in-case-match-pattern '(x (quote y))) '(x))
(assert-equal (vars-bound-in-case-match-pattern '(x (quote~ y))) '(x))
(assert-equal (vars-bound-in-case-match-pattern '(x 'y)) '(x))
(assert-equal (vars-bound-in-case-match-pattern '(x &)) '(x))
(assert-equal (vars-bound-in-case-match-pattern '(x !y)) '(x))
(defconst *foo* 7)
(assert-equal (vars-bound-in-case-match-pattern '(x t nil :keyword *foo*)) '(x))
