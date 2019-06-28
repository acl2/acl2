; Top-level book for the arithmetic-light library.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note: We recommend including just the individual books that you need, rather
;; than including this top.lisp book, which is likely to include material you
;; don't need and which we expect to grow over time.

(include-book "expt")
(include-book "expt2")
(include-book "minus")
(include-book "denominator")
(include-book "times")
(include-book "plus")
(include-book "plus-and-minus")
(include-book "numerator")
(include-book "integerp")
(include-book "ceiling")
(include-book "nonnegative-integer-quotient")
(include-book "mod-expt-fast")
(include-book "mod-and-expt")
(include-book "mod")
(include-book "floor")
(include-book "divides")
(include-book "times-and-divides")
(include-book "complex")
(include-book "less-than")
(include-book "realpart")
(include-book "imagpart")
