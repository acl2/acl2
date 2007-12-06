;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(local (include-book "../../../arithmetic/top"))

(local (defun kmin (x k)
  (if (integerp k)
      (if (> k 0)
	  (if (evenp (* (expt 2 k) x))
	      (kmin x (1- k))
	    k)
	1)
    1)))

(local (defthm kmin-pos
    (implies (and (integerp k)
		  (> k 0))
	     (and (integerp (kmin x k))
		  (> (kmin x k) 0)))
  :rule-classes ()))

(local (defthm kmin-integerp
    (implies (and (rationalp x)
		  (not (integerp x))
		  (integerp k)
		  (> k 0)
		  (integerp (* (expt 2 k) x)))
	     (integerp (* (expt 2 (kmin x k)) x)))
  :rule-classes ()))

(local (defthm kmin-oddp
    (implies (and (rationalp x)
		  (not (integerp x))
		  (integerp k)
		  (> k 0)
		  (integerp (* (expt 2 k) x)))
	     (not (evenp (* (expt 2 (kmin x k)) x))))
  :rule-classes ()))

(local (in-theory (disable kmin)))

(local (defun revenp (n)
  (if (and (integerp n) (>= n 0))
      (if (= n 0)
	  t
	(if (= n 1)
	    ()
	  (revenp (- n 2))))
    ())))

(local (defthm half-lemma
    (implies (and (integerp n)
		  (>= n 0))
	     (iff (revenp n) (evenp n)))
  :rule-classes ()))

(local (defthm int-*-closed
    (implies (and (integerp x) (integerp y))
	     (integerp (* x y)))))

(local (defthm evenp-evenp
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp y)
		  (>= y 0)
		  (evenp x))
	     (evenp (* x y)))
  :hints (("Goal" :use ((:instance int-*-closed (x (/ x 2))))))))

(local (defthm evenp-oddp
    (implies (and (integerp n)
		  (>= n 0))
	     (iff (revenp n)
		  (not (revenp (1+ n)))))
  :rule-classes ()))

(local (defthm evenp-oddp-2
    (implies (and (integerp n)
		  (>= n 0))
	     (iff (evenp n)
		  (not (evenp (1+ n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance evenp-oddp)
			(:instance half-lemma)
			(:instance half-lemma (n (1+ n))))))))

(local (defthm evenp-oddp-3
    (implies (and (integerp n)
		  (>= n 0)
	          (not (evenp n)))
	     (and (>= (1- n) 0)
		  (evenp (1- n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance evenp-oddp-2 (n (1- n))))))))

(local (defthm evenp-plus
    (implies (and (integerp n)
		  (integerp m)
		  (>= n 0)
		  (>= m 0)
		  (evenp n)
		  (evenp m))
	     (evenp (+ n m)))
  :rule-classes ()))

(local (defthm evenp-x2+2x
    (implies (and (integerp x)
		  (>= x 0)
		  (evenp x))
	     (evenp (+ (* x x) (* 2 x))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance evenp-plus (n (* x x)) (m (* 2 x)))
			(:instance evenp-evenp (y x)))))))

(local (defthm hack1
    (implies (integerp x)
	     (= (+ 1 (* 2 X) (* X X))
		(+ 1 x x (* X X))))
  :rule-classes ()))

(local (defthm oddp-oddp
    (implies (and (integerp x)
		  (>= x 0)
		  (evenp x))
	     (not (evenp (* (1+ x) (1+ x)))))
  :hints (("Goal" :in-theory (disable evenp)
		  :use ((:instance evenp-x2+2x)
			(:instance hack1)
			(:instance evenp-oddp-2 (n (+ (* x x) (* 2 x)))))))))

(local (defthm oddp-oddp-2
    (implies (and (integerp x)
		  (>= x 0)
		  (not (evenp x)))
	     (not (evenp (* x x))))
  :hints (("Goal" :in-theory (disable evenp)
		  :use ((:instance oddp-oddp (x (1- x)))
			(:instance evenp-oddp-3 (n x)))))))

(local (defthm kmin-oddp-square
    (implies (and (rationalp x)
		  (not (integerp x))
		  (>= x 0)
		  (integerp k)
		  (> k 0)
		  (integerp (* (expt 2 k) x)))
	     (not (evenp (* (* (expt 2 (kmin x k)) x) (* (expt 2 (kmin x k)) x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable evenp)
		  :use ((:instance oddp-oddp-2 (x (* (expt 2 (kmin x k)) x)))
			(:instance kmin-oddp)
			(:instance kmin-pos)
			(:instance kmin-integerp))))))

(local (defthm hack2
    (implies (and (rationalp x)
		  (integerp m))
	     (= (* (* (expt 2 m) x) (* (expt 2 m) x))
		(* (* 2 x x) (expt 2 (1- (* 2 m))))))
  :rule-classes ()))

(local (defthm kmin-oddp-corollary
    (implies (and (rationalp x)
		  (not (integerp x))
		  (>= x 0)
		  (integerp k)
		  (> k 0)
		  (integerp (* (expt 2 k) x)))
	     (not (evenp (* (* 2 x x) (expt 2 (1- (* 2 (kmin x k))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt evenp)
		  :use ((:instance kmin-oddp-square)
			(:instance hack2 (m (kmin x k)))
			(:instance kmin-pos))))))

(local (defthm evenp-expt
    (implies (and (integerp n)
		  (> n 0))
	     (evenp (expt 2 n)))))

(local (defthm evenp-expt-2
    (implies (and (integerp n)
		  (> n 0))
	     (and (integerp (expt 2 n))
		  (> (expt 2 n) 0)
		  (evenp (expt 2 n))))
  :rule-classes ()))

(local (defthm evenp-expt-3
    (implies (and (integerp n)
		  (> n 0))
	     (and (integerp (expt 2 (1- (* 2 n))))
		  (> (expt 2 (1- (* 2 n))) 0)
		  (evenp (expt 2 (1- (* 2 n))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt evenp)
		  :use ((:instance evenp-expt-2 (n (1- (* 2 n)))))))))

(local (defthm evenp-2-kmin
    (implies (and (rationalp x)
		  (not (integerp x))
		  (>= x 0)
		  (integerp k)
		  (> k 0)
		  (integerp (* (expt 2 k) x)))
	     (and (integerp (expt 2 (1- (* 2 (kmin x k)))))
		  (> (expt 2 (1- (* 2 (kmin x k)))) 0)
		  (evenp (expt 2 (1- (* 2 (kmin x k)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt evenp)
		  :use ((:instance evenp-expt-3 (n (kmin x k)))
			(:instance kmin-pos)
			(:instance kmin-integerp))))))

(local (defthm 2xx-lemma-1
    (implies (and (rationalp x)
		  (not (integerp x))
		  (>= x 0)
		  (integerp k)
		  (> k 0)
		  (integerp (* (expt 2 k) x))
		  (integerp (* 2 x x)))
	     (evenp (* (* 2 x x) (expt 2 (1- (* 2 (kmin x k)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt evenp)
		  :use ((:instance evenp-2-kmin)
			(:instance evenp-evenp (x (expt 2 (1- (* 2 (kmin x k))))) (y (* 2 x x))))))))

(local (defthm x-2xx-1
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp k)
		  (> k 0)
		  (integerp (* (expt 2 k) x))
		  (integerp (* 2 x x)))
	     (integerp x))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt evenp)
		  :use ((:instance 2xx-lemma-1)
			(:instance kmin-oddp-corollary))))))

(local (defthm x-2xx-2
    (implies (and (rationalp x)
		  (<= x 0)
		  (integerp k)
		  (> k 0)
		  (integerp (* (expt 2 k) x))
		  (integerp (* 2 x x)))
	     (integerp x))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt evenp)
		  :use ((:instance x-2xx-1 (x (- x))))))))

(local (defthm x-2xx-3
    (implies (and (rationalp x)
		  (integerp k)
		  (> k 0)
		  (integerp (* (expt 2 k) x))
		  (integerp (* 2 x x)))
	     (integerp x))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt)
		  :use ((:instance x-2xx-2)
			(:instance x-2xx-1))))))

; Added for Version_2.6.
(local (in-theory (enable exponents-add-unrestricted)))

(local (defthm x-2xx-4
    (implies (and (rationalp x)
		  (integerp k)
		  (<= k 0)
		  (integerp (* (expt 2 k) x)))
	     (integerp x))
  :rule-classes ()))

;Matt says this lemma is probably true even without the expt hyp or any mention of k.

(defthm x-2xx
    (implies (and (rationalp x)
		  (integerp k)
		  (integerp (* (expt 2 k) x))
		  (integerp (* 2 x x)))
	     (integerp x))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt)
		  :use ((:instance x-2xx-3)
			(:instance x-2xx-4)))))
