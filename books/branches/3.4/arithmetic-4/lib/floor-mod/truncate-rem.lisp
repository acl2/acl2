
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; truncate-rem.lisp
;;;
;;; We rewrite expressions involving truncate and rem to floor and mod
;;; respectively.  We also handle ceiling and round.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(IN-PACKAGE "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../basic-ops/top"))

(local
 (include-book "floor-mod"))

(local
 (include-book "floor-mod-basic"))

(defthm rewrite-truncate-to-floor
  (equal (truncate x y)
	 (cond ((not (rationalp (/ x y)))
		0)
	       ((<= 0 (/ x y))
		(floor x y))
	       ((integerp (/ x y))
		(floor x y))
	       (t
		(+ 1 (floor x y)))))
  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient)))))

(defthm rewrite-rem-to-mod
  (equal (rem x y)
	 (cond ((not (rationalp (/ x y)))
		(if (acl2-numberp x)
		    x
		  0))
	       ((<= 0 (/ x y))
		(mod x y))
	       ((integerp (/ x y))
		(mod x y))
	       (t
		(- (mod x y) y))))
  :hints (("Goal" :in-theory (e/d (mod) (truncate)))))

(defthm rewrite-ceiling-to-floor
  (equal (ceiling x y)
	 (cond ((not (rationalp (/ x y)))
		0)
	       ((integerp (/ x y))
		(floor x y))
	       (t
		(+ 1 (floor x y)))))
  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient)))))

;;; This is messy, can we do any better?

(defthm rewrite-round-to-floor
  (equal (round x y)
	 (cond ((not (rationalp (/ x y)))
		(cond ((< 1/2 (/ x y))
		       1)
		      ((< (/ x y) -1/2)
		       -1)
		      (t
		       0)))
	       ((< (mod (/ x y) 1) 1/2)
		(floor x y))
	       ((< 1/2 (mod (/ x y) 1))
		(+ 1 (floor x y)))
	       (t
		(if (evenp (floor x y))
		    (floor x y)
		  (+ 1 (floor x y))))))
  :hints (("Goal" :in-theory (e/d (floor mod) (nonnegative-integer-quotient)))))

(defthm ash-to-floor
  (equal (ash i n)
	 (cond ((and (integerp i)
		     (integerp n))
		(floor i (expt 2 (- n))))
	       ((integerp i)
		(floor i 1))
	       (t
		0)))
  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient)))))

(in-theory (disable truncate rem ceiling round ash))
