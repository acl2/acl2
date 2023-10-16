(in-package "DM")

(include-book "euclid")
(local (include-book "support/binomial"))

;; This is Ruben Gamboa's formalization of the binomial theorem (books/arithmetic/binomial.lisp),
;; imported into the DM package.

(defund choose (n k)
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (/ (fact n)
	 (* (fact k) (fact (- n k))))
    0))

(defun binomial-expansion (x y k n)
  (declare (xargs :measure (nfix (1+ (- n k)))))
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (cons (* (choose n k) (expt x k) (expt y (- n k)))
	    (binomial-expansion x y (1+ k) n))
    ()))

(defun sum-list (l)
  (if (consp l)
      (+ (car l) (sum-list (cdr l)))
    0))

(defthm binomial-theorem
  (implies (and (integerp n) (<= 0 n))
	   (equal (expt (+ x y) n)
		  (sum-list (binomial-expansion x y 0 n)))))


