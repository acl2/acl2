(in-package "DM")

(include-book "rtl/rel11/lib/basic" :dir :system)
(include-book "euclid")
(local (include-book "arithmetic-5/top" :dir :system))

;; The list of decimal digits of a positive integer n in reverse order:

(defun digits (n)
  (if (posp n)
      (cons (mod n 10)
	    (digits (fl (/ n 10))))
    ()))

;; The sum of a list of numbers:

(defun sum-list (l)
  (if (consp l)
      (+ (car l) (sum-list (cdr l)))
    0))

(defthm posp-digits
  (implies (natp n) (natp (sum-list (digits n))))
  :rule-classes (:type-prescription :rewrite))

;; The sum of the decimal digits of n is congruent to n mod 3:

(defthm mod-sum-list-digits
  (implies (natp n)
	   (equal (mod (sum-list (digits n)) 3)
		  (mod n 3)))
  :hints (("Subgoal *1/1" :use ((:instance rtl::mod-def (rtl::x n) (rtl::y 10))
                                (:instance rtl::mod-sum (rtl::n 3) (rtl::a (mod n 10)) (rtl::b (* 10 (fl (/ n 10)))))
			        (:instance rtl::mod-mod-times (n 3) (rtl::a 10) (rtl::b (fl (/ n 10))))
				(:instance rtl::mod-sum (rtl::n 3) (rtl::a (mod n 10)) (rtl::b (sum-list (digits (fl (/ n 10))))))))))

;; Therefore, the sum is divisible by 3 iff n is divisible by 3:

(defthm divides-3-sum-list-digits
  (implies (natp n)
	   (iff (divides 3 (sum-list (digits n)))
		(divides 3 n)))
  :hints (("Goal" :in-theory (enable divides)
                  :use ((:instance rtl::mod-equal-int (rtl::n 3) (rtl::a n) (rtl::b (sum-list (digits n))))))))
