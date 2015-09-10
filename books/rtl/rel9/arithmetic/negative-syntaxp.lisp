; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

#|

Briefly, negative-syntaxp recognizes terms which are "syntactically negative."  These are terms which could
be simplified by multiplying them by -1.  For example, the term
  (+ -1/2 (* -1 x))
could be simplified by multiplying it by -1, yielding (with distributivity enabled) the term
  (+ 1/2 x)
. Often, a statement about a negative term can be simplified by rewriting it into a statement about the term's
positive analogue.  For example, (integerp (* -1 x)) can be simplified to (integerp x), if x is an
acl2-numberp.  However, a rule rewriting (integerp (* -1 x)) to (integerp x) is not general enough to catch all
"negative" terms.  For example, the rule would not fire on (integerp (- x)).  negative-syntaxp provides a
general and extensible facility for making such rules.

Note that the notion of "syntactically negative" pays no attention to *values*. E.g., (- x) is "syntactically
negative" regardless of the sign of the value of x.

|#



;This function operates on translated terms!
;This function should be extended to recognize more terms.
;do I need to test that binary-+ and binary-* have the right number of arguments?
;Worry: What happens on (+ -2 b)
(defun negative-syntaxp (term)
  (if (not (consp term))
      nil
    (case (car term)
      (quote (and (rationalp (cadr term))
                  (< (cadr term) 0)))
      (unary-- (not (negative-syntaxp (cadr term))))  ;perhaps we should use "positive-syntaxp" here...
      (binary-+ (and ;(equal (length term) 3) ;ok since binary-+ should always have 2 args
                 (negative-syntaxp (cadr term))
                 (negative-syntaxp (caddr term))))
      (binary-* (and ;(equal (length term) 3)
                 (or (and (negative-syntaxp (cadr term))
                          (not (negative-syntaxp (caddr term))))
                     (and (not (negative-syntaxp (cadr term)))
                          (negative-syntaxp (caddr term))))))
      (otherwise nil))))


#|

The following terms are "negative":
 negative constants
 (- x)
 (* -1 x)
 (* -5/7 x)
 (/ (- a)) - how do we simp this? - not currently handled...
 (+ -1/2 (* -1/2 x))
 the sum of two (or more) negative terms


neg
 negative numeric constants
 (- <non-neg>)
 a product with an odd number of negative factors
 a sum of two or more negative terms

pos
 positive numeric constants
 variables
 function calls other than +,*
 a product with an even number of negative factors
 a sum of two or more positive terms?

It might be nice to someday decide how to handle a mixed sum.  For example, we might prefer
  (integerp (+ 2 (* -1 x) y))
to
  (integerp (+ -1 x (* -1 y))
since the former has one fewer negated addend.  And, when exactly half the terms are negated, we might prefer
  (integerp (+ x (* -1 y)))
to
  (integerp (+ (* -1 x) y))
since the latter has the negation around the "smaller" term.  Or something like that.


so that the rules don't loop, we must ensure that a negative term * -1 is not negative


|#



