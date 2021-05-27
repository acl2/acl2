; Prime fields library
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; This book defines operations on the finite field consisting of the integers
;; modulo some prime p.

;; The rules in the book generally each deal with a single function. For
;; reasoning about these operations, consider including the book
;; prime-fields-rules.

;; In this version of the formalization, the prime is passed explicitly to all
;; of the operations.  See also prime-fields-alt.lisp, which uses a constrained
;; function for the prime.

;(include-book "../../projects/quadratic-reciprocity/euclid") ;brings in rtl::primep
(include-book "../utilities/pos-fix")
(include-book "fep")
(include-book "minus1")
(include-book "neg")
(include-book "add")
(include-book "sub")
(include-book "mul")
(include-book "pow")
(include-book "inv")
(include-book "div")
(local (include-book "support"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/mod"))

(in-theory (disable (:e rtl::primep)))

(defmacro primep (x) `(rtl::primep ,x))
