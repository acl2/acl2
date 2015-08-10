#|

This is in an ACL2 "book" with definitions and theorems about polynomial
evaluation.  Polynomials are stored in powerlists, a data structure similar to
lists, but more amenable to parallel recursion, because its
constructors/destructors are designed to deal with sub-powerlists, not with a
sub-powerlsit and an element (as with linear lists).

The basic definitions come from Misra's 1994 paper on powerlists.  This book is
nothing more than a transliteration of the basic definitions in [Mis94] into
ACL2.

To certify this book, first define the POWERLISTS package, then execute an
appropriate certify-book command.  Something like the following will work:

|#

#|;

    (defpkg "POWERLISTS"
      (union-eq *common-lisp-symbols-from-main-lisp-package*
		*acl2-exports*))

    (certify-book "eval-poly" 1)

|#

(in-package "POWERLISTS")

(include-book "arithmetic/top" :dir :system)
(include-book "powerlists/algebra" :dir :system)

;; We begin with the basic definitions about polynomial evaluation.

;;

(defun eval-poly-at-point (p x)
  "Eval-poly-at-point evaluates a polynomial p at a point x.  The polynomial
  p is stored in a powerlist data structure.  In particular, the polynomial
  p = c_0 + c_1 x + ... + c_n x^n is stored as the powerlist
  < c_0, c_1, ..., c_n >."
  (if (powerlist-p p)
      (+ (eval-poly-at-point (p-unzip-l p) (* x x))
	 (* x (eval-poly-at-point (p-unzip-r p)
				  (* x x))))
    (fix p)))
(in-theory (disable (eval-poly-at-point)))

(defun eval-poly (p x)
  "Eval-poly evaluates polynomial p at a vector (possibly scalar) x.
  The polynomial p is stored in a powerlist, in the same format as in
  eval-poly-at-point."
  (if (powerlist-p x)
      (p-tie (eval-poly p (p-untie-l x))
	     (eval-poly p (p-untie-r x)))
    (eval-poly-at-point p x)))
(in-theory (disable (eval-poly)))

;; Now, we define arithmetic operators on vectors.  We define only addition,
;; subtraction, pointwise multiplication, and unary minus.

(defun p-unary-- (x)
  "P-unary-- returns a powerlist with all the elements of x negated."
  (if (powerlist-p x)
      (p-tie (p-unary-- (p-untie-l x))
	     (p-unary-- (p-untie-r x)))
    (- x)))
(in-theory (disable (p-unary--)))

(defun p-* (x y)
  "(p-* x y) returns a powerlist with the product of the pointwise elements
  of x and y."
  (if (powerlist-p x)
      (p-tie (p-* (p-untie-l x) (p-untie-l y))
	     (p-* (p-untie-r x) (p-untie-r y)))
    (* x y)))
(in-theory (disable (p-*)))

(defun p-+ (x y)
  "(p-+ x y) returns a powerlist with the sum of the pointwise elements
  of x and y."
  (if (powerlist-p x)
      (p-tie (p-+ (p-untie-l x) (p-untie-l y))
	     (p-+ (p-untie-r x) (p-untie-r y)))
    (+ x y)))
(in-theory (disable (p-+)))

(defun p-- (x y)
  "(p-+ x y) returns a powerlist with the different of the pointwise
  elements of x and y."
  (if (powerlist-p x)
      (p-tie (p-- (p-untie-l x) (p-untie-l y))
	     (p-- (p-untie-r x) (p-untie-r y)))
    (- x y)))
(in-theory (disable (p--)))

;; Now, we prove some basic theorems about polynomial arithmetic.

;; The first theorem is extremely useful.  It allows to reason about polynomial
;; evaluation of a vector in terms of vector arithmetic.  The previous
;; definition evaluated the polynomial pointwise at each point.  This theorem
;; uses the vector arithmetic operators, in a manner mimicking the polynomial
;; evaluation at a point.

(defthm eval-poly-lemma
  (implies (powerlist-p p)
	   (equal (eval-poly p x)
		  (p-+ (eval-poly (p-unzip-l p)
				  (p-* x x))
		       (p-* x (eval-poly (p-unzip-r p)
					 (p-* x x)))))))

;; The remaining lemmas show how we can mix the vector arithmetic operators
;; defined earlier.  In particular, they detail the behavior of the unary
;; minus operator.  Note that the arithmetic operators below are all vector
;; arithmetic operators.  The equivalent theorems are trivial about numbers.

;; First of all, we show what happens when you consider -x * y, which we show
;; is the same as -(x*y).

(defthm p-*-p-unary--
  (equal (p-* (p-unary-- x) y)
	 (p-unary-- (p-* x y))))

;; A more useful result is that -x * -y is equal to x*y.

(defthm p-*-p-unary--x-p-unary--y
  (implies (force (p-similar-p x y))
	   (equal (p-* (p-unary-- x) (p-unary-- y))
		  (p-* x y)))
  :hints (("Goal" :induct (p-* x y))))

;; As a special case of the above, -x * -x is equal to x*x.  This is a useful
;; theorem to prove, because the hypothesis that x is similar to x is trivially
;; true, so it's not needed (unlike the general case above).  So, by removing
;; the trivial hypothesis, this theorem is used more often as a rewrite rule.

(defthm p-*-p-unary--x-p-unary--x
  (equal (p-* (p-unary-- x) (p-unary-- x))
	 (p-* x x)))

;; Finally, we prove the obvious fact that x + -y is equal to x - y.

(defthm p-+-p-unary--
  (implies (force (p-similar-p x y))
	   (equal (p-+ x (p-unary-- y))
		  (p-- x y))))

