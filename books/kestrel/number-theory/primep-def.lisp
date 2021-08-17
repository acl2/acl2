(in-package "RTL")

;; This book just cherry-picks the definition of primep (and two supporting
;; functions) from books/projects/quadratic-reciprocity/support/euclid.lisp.
;; See the copyright in that book.

(local (include-book "projects/quadratic-reciprocity/support/euclid" :dir :system))

(defn divides (x y)
  (and (acl2-numberp x)
       (not (= x 0))
       (acl2-numberp y)
       (integerp (/ y x))))

(defn least-divisor (k n)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (integerp n)
	   (integerp k)
	   (< 1 k)
	   (<= k n))
      (if (divides k n)
	  k
	(least-divisor (1+ k) n))
    ()))

(defnd primep (n)
  (and (integerp n)
       (>= n 2)
       (equal (least-divisor 2 n) n)))
