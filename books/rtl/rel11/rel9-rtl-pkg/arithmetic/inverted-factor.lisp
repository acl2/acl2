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

(in-package "RTL")

;(local (include-book "../../../../meta/meta-times-equal"))
;(local (INCLUDE-BOOK "predicate"))
;(local (INCLUDE-BOOK "fp2"))

#|
treat constants separately.  careful.  do we prefer (equal x 1/2) or (equal (* 2 x) 1) ?
Now I think we definitely prefer (equal x 1/2) because this allows us to substitue for x.

when this
 (+ 1 x (* 2 x) (* x y (/ z)))
 appears in an equality, we want to multiply through by z
either returns nil or a term to multiply through

this assumes the term is already normalized.  this will be the case if we call this function on, say (equal
lhs rhs) because by the time the equal term is processed, lhs and rhs are each individually normalized
not necessarily!


warning; multiplying through by these factors can cause problems with linear arithmetic (expand on this...)

watch out.  how do we handle (< x 1/2) ?  do we multiply through by 2?

binds the variable k

(This used to be called find-frac-coeff.)

|#

(defun find-inverted-factor (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;term was a symbol
      nil
    (case (car term)
      (quote (if (integerp (cadr term))
                 nil ;no denominator
               (if (rationalp (cadr term))
                   `((k . ',(denominator (cadr term))))
                 nil)))  ;we found one!
      (binary-+ (or (find-inverted-factor (cadr term))
                    (find-inverted-factor (caddr term))))
      (binary-* (or (find-inverted-factor (cadr term))
                    (find-inverted-factor (caddr term))))
      (unary-/ (list (cons 'k (cadr term)))) ;we found one!
      (otherwise nil)
      )))

;todo: generalize this
;TERM is a product containing FACTOR as (at least) one factor
(defun is-a-factor (factor term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;term was a symbol
      (equal factor term)
    (case (car term)
      (binary-* (if (equal factor (cadr term))
                    t
                  (is-a-factor factor (caddr term))))
      (otherwise (equal factor term)) ;anything else is not a prduct [what about a sum, each of whose addends is a multiple of FACTOR?]
      )))


;;
;; Detect that distributity and assoc rules have fired
;; (doesn't check that comm and comm-2 have fired)
;;


;Checks whether TERM is a factor, which we define as either a variable, or a call to a function other than *
;or +
;Some example factors: x  '3  (mod x y)  (/ x)  (/ (bits (* 2 x) i j))
;our normal form requires that the arg to (/ ... ) not be a product!
;it is basic to our normal form that (/ (* x y)) be rewritten to (* (/ x) (/ y))
;we can now have the routine check whether the term is a quoted constant..
(defun factor-syntaxp (term can-be-a-constant)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;term was a symbol
      t
    (case (car term)
      (binary-* nil) ;associativity of * must not have fired (or we are in the (* x y) of a (/ (* x y))
      (binary-+ nil) ;distributivity must not have fired...
      (unary-/ (and (consp (cdr term))
                    (factor-syntaxp (cadr term) nil)))
      (quote can-be-a-constant)
      (otherwise t))))


;Checks whether TERM is a product of (1 or more) "factors".
;Also checks that only the first factor (if any) is a constant...  (If the constants aren't collected, the
;term isn't yet normalized, and rules can loop). BOZO document why the cancelling rule is okay even though
;constants are a little weird..
(defun product-syntaxp (term first-factor-can-be-a-constant)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;term was a symbol
      t
    (case (car term)
      (binary-* (and (factor-syntaxp (cadr term) first-factor-can-be-a-constant)
                     (product-syntaxp (caddr term) nil)))
;check that term is a single factor..
      (otherwise (factor-syntaxp term first-factor-can-be-a-constant)))))

;Checks whether TERM is a sum of one or more products..
;rejects TERM if distributivity or associativity haven't fired yet.
;i suppose we could check that the terms have been commutted into the right order, but we don't do that
;either.
;But we do check that only the first factor (if any) of each product is a constant...
(defun sum-of-products-syntaxp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;term was a symbol
      t
    (case (car term)
      (binary-+ (and (product-syntaxp (cadr term) t)
                     (sum-of-products-syntaxp (caddr term))))
      (otherwise (product-syntaxp term t)))))




