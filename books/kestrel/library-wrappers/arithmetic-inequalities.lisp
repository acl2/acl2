; A book to fix problems with arithmetic/inequalities.
;
; Copyright (C) 2016-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../../arithmetic/inequalities")

;; Since arithmetic/inequalities includes arithmetic/equalities, we might as
;; well include the wrapper for arithmetic-equalities.
(include-book "arithmetic-equalities")

;; TODO: Consider fixing the original rules.

; These seem like bad rules because of how they can match terms containing
; constants.  For example, they can turn (< y 1/4) into (< (* 4 Y) 1).  Here we
; just disable them and make better versions.
(in-theory (disable <-unary-/-positive-right
                    <-unary-/-positive-left
                    <-unary-/-negative-left
                    <-unary-/-negative-right))

(defthm <-unary-/-positive-right-better
  (implies (and (syntaxp (not (quotep x))) ; prevent this rule from firing when x is a constant like 1/4
                (< 0 x)
                (real/rationalp x)
                (real/rationalp y))
           (equal (< y (/ x))
                  (< (* x y) 1)))
  :hints (("Goal" :by <-unary-/-positive-right)))

(defthm <-unary-/-positive-left-better
  (implies (and (syntaxp (not (quotep x))) ; prevent this rule from firing when x is a constant like 1/4
                (< 0 x)
                (real/rationalp x)
                (real/rationalp y))
           (equal (< (/ x) y)
                  (< 1 (* x y))))
  :hints (("Goal" :by <-unary-/-positive-left)))

(defthm <-unary-/-negative-left-better
  (implies (and (syntaxp (not (quotep x))) ; prevent this rule from firing when x is a constant like -1/2
                (< x 0)
                (real/rationalp x)
                (real/rationalp y))
           (equal (< (/ x) y)
                  (< (* x y) 1)))
  :hints (("Goal" :by <-unary-/-negative-left)))

(defthm <-unary-/-negative-right-better
  (implies (and (syntaxp (not (quotep x))) ; prevent this rule from firing when x is a constant like -1/2
                (< x 0)
                (real/rationalp x)
                (real/rationalp y))
           (equal (< y (/ x))
                  (< 1 (* x y))))
  :hints (("Goal" :by <-unary-/-negative-right)))
