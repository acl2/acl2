(in-package "DM")

(include-book "euclid")
(local (include-book "arithmetic/binomial" :dir :system))

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

(local-defthm factorial-rewrite
  (equal (acl2::factorial n) (fact n))
  :hints (("Goal" :in-theory (enable acl2::factorial fact))))

(local-defthm choose-rewrite
  (equal (acl2::choose k n) (choose n k))
  :hints (("Goal" :in-theory (enable choose))))

(local-defthm binomial-expansion-rewrite
  (equal (acl2::binomial-expansion x y k n)
	 (binomial-expansion x y k n)))

(local-defthm sumlist-rewrite
  (equal (acl2::sumlist l) (sum-list l)))

(defthm binomial-theorem
  (implies (and (integerp n) (<= 0 n))
	   (equal (expt (+ x y) n)
		  (sum-list (binomial-expansion x y 0 n))))
  :hints (("Goal" :use (acl2::binomial-theorem))))


