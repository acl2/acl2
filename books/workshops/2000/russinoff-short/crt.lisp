;;;***************************************************************
;;;An ACL2 Proof of the Chinese Remainder Theorem

;;;David M. Russinoff
;;;April, 1999
;;;***************************************************************

(in-package "ACL2")

; Rager 11/2014: The following rel9 books may be close to enough to certify
; this book:

;; (include-book "rtl/rel9/lib/basic" :dir :system)
;; (include-book "rtl/rel9/arithmetic/fp" :dir :system)

(include-book "../../../rtl/rel1/lib1/basic")

(include-book "../../../rtl/rel1/support/fp")

(in-theory (disable rem))

(defun g-c-d (x y)
  (declare (xargs :measure (nfix (+ x y))))
  (if (zp x)
      y
    (if (zp y)
	x
      (if (<= x y)
	  (g-c-d x (- y x))
	(g-c-d (- x y) y)))))

(defun rel-prime (x y)
  (= (g-c-d x y) 1))

(defun rel-prime-all (x l)
  (if (endp l)
      t
    (and (rel-prime x (car l))
	 (rel-prime-all x (cdr l)))))

(defun rel-prime-moduli (l)
  (if (endp l)
      t
    (and (integerp (car l))
	 (>= (car l) 2)
	 (rel-prime-all (car l) (cdr l))
	 (rel-prime-moduli (cdr l)))))

(defun congruent (x y m)
  (= (rem x m) (rem y m)))

(defun congruent-all (x a m)
  (declare (xargs :measure (acl2-count m)))
  (if (endp m)
      t
    (and (congruent x (car a) (car m))
	 (congruent-all x (cdr a) (cdr m)))))

(defun natp-all (l)
  (if (endp l)
      t
    (and (natp (car l))
	 (natp-all (cdr l)))))

#|
(defthm chinese-remainder-theorem
    (implies (and (natp-all a)
		  (rel-prime-moduli m)
		  (= (len a) (len m)))
	     (and (natp (crt a m))
		  (congruent-all (crt a m) a m))))
|#

(mutual-recursion

 (defun r (x y)
   (declare (xargs :measure (nfix (+ x y))))
  (if (zp x)
      0
    (if (zp y)
	1
      (if (<= x y)
	  (- (r x (- y x)) (s x (- y x)))
	(r (- x y) y)))))

(defun s (x y)
   (declare (xargs :measure (nfix (+ x y))))
  (if (zp x)
      1
    (if (zp y)
	0
      (if (<= x y)
	  (s x (- y x))
	(- (s (- x y) y) (r (- x y) y))))))

)

(defun c (x l)
  (if (endp l)
      0
    (- (+ (r x (car l))
	  (c x (cdr l)))
       (* (r x (car l))
	  (c x (cdr l))
	  x))))

(defun d (x l)
  (if (endp l)
      1
    (* (s x (car l))
       (d x (cdr l)))))

(defun prod (l)
  (if (endp l)
      1
    (* (car l) (prod (cdr l)))))

(defun one-mod (x l) (* (d x l) (prod l) (d x l) (prod l)))

(defun crt1 (a m l)
  (if (endp a)
      0
    (+ (* (car a) (one-mod (car m) (remove (car m) l)))
       (crt1 (cdr a) (cdr m) l))))

(defun crt (a m) (crt1 a m m))

(defthm g-c-d-type
    (implies (and (integerp x) (integerp y))
	     (integerp (g-c-d x y)))
  :rule-classes (:type-prescription))

(defthm R-S-LEMMA
    (implies (and (natp x)
		  (natp y))
	     (= (+ (* (r x y) x)
		   (* (s x y) y))
		(g-c-d x y)))
  :rule-classes ())

(defthm hack-1
    (implies (and (rationalp a)
		  (rationalp b)
		  (= x a)
		  (= y b))
	     (= (* a b) (* x y)))
  :rule-classes ())

(defthm hack-2
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp x)
		  (rationalp y)
		  (rationalp c)
		  (rationalp d)
		  (rationalp l)
		  (= 1 (+ (* a x) (* b y)))
		  (= 1 (+ (* c x) (* d l))))
	     (= 1
		(+ (* a x)
		   (* c x)
		   (* b d y l)
		   (- (* x x a c)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-1
				   (x (* b y))
				   (y (* d l))
				   (a (- 1 (* a x)))
				   (b (- 1 (* c x))))))))

(defthm c-type
    (implies (and (integerp x)
		  (natp-all l))
	     (rationalp (c x l)))
  :rule-classes (:type-prescription))

(defthm prod-type
    (implies (natp-all l)
	     (rationalp (prod l)))
  :rule-classes (:type-prescription))

(defthm C-D-LEMMA
    (implies (and (natp x)
		  (natp-all l)
		  (rel-prime-all x l))
	     (= (+ (* (c x l) x)
		   (* (d x l) (prod l)))
		1))
  :rule-classes ()
  :hints (("Subgoal *1/4" :use ((:instance r-s-lemma (y (car l)))
				(:instance hack-2
					   (a (r x (car l)))
					   (b (s x (car l)))
					   (y (car l))
					   (l (prod (cdr l)))
					   (c (c x (cdr l)))
					   (d (d x (cdr l))))))))

(defthm c-int
    (implies (and (integerp x)
		  (natp-all l))
	     (integerp (c x l)))
  :rule-classes ())

(in-theory (disable rel-prime rel-prime-all rel-prime-moduli one-mod crt1 crt r s c d prod))

(defthm hack-3
    (implies (= x y)
	     (= (* x x) (* y y)))
  :rule-classes ())

(defthm hack-4
    (implies (and (rationalp c)
		  (rationalp d)
		  (rationalp m)
		  (rationalp p)
		  (= (+ (* c m) (* d p)) 1))
	     (= (* d p d p)
		(* (1+ (* m c (- (* c m) 2))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-3 (x (* d p)) (y (- 1 (* c m))))))))

(defthm one-mod-alt
    (implies (and (natp m)
		  (> m 1)
		  (natp-all l)
		  (rel-prime-all m l))
	     (= (one-mod m l)
		(1+ (* m (c m l) (- (* (c m l) m) 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable one-mod)
		  :use ((:instance c-int (x m))
			(:instance c-d-lemma (x m))
			(:instance hack-4
				   (c (c m l))
				   (d (d m l))
				   (p (prod l)))))))

(defthm hack-5
    (implies (and (integerp m)
		  (integerp c)
		  (integerp cm)
		  (>= m 2)
		  (>= c 1)
		  (>= cm 0))
	     (natp (* m c cm)))
  :rule-classes ())

(defthm hack-6
    (implies (and (integerp c)
		  (>= c 1)
		  (integerp m)
		  (> m 1))
	     (natp (1+ (* m c (- (* c m) 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-5 (cm (- (* c m) 2)))))))

(defthm hack-7
    (implies (and (integerp m)
		  (integerp c)
		  (integerp cm)
		  (>= m 2)
		  (< c 0)
		  (< cm 0))
	     (natp (* m c cm)))
  :rule-classes ())

(defthm hack-8
    (implies (and (integerp c)
		  (< c 1)
		  (integerp m)
		  (> m 1))
	     (natp (1+ (* m c (- (* c m) 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-7 (cm (- (* c m) 2)))))))

(defthm hack-9
    (implies (and (integerp c)
		  (integerp m)
		  (> m 1))
	     (natp (1+ (* m c (- (* c m) 2)))))
  :rule-classes ()
  :hints (("Goal" :use (hack-6 hack-8))))

(defthm ONE-MOD-NAT
    (implies (and (natp x)
		  (> x 1)
		  (natp-all l)
		  (rel-prime-all x l))
	     (natp (one-mod x l)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance one-mod-alt (m x))
			(:instance c-int)
			(:instance hack-9 (m x) (c (c x l)))))))

(defthm hack-10
    (implies (and (integerp m)
		  (> m 1)
		  (integerp p)
		  (>= (1+ (* m p)) 0))
	     (>= p 0))
  :rule-classes ())

(defthm hack-11
    (implies (and (integerp m)
		  (> m 1)
		  (integerp c)
		  (>= (1+ (* m c (- (* c m) 2))) 0))
	     (>= (* c (- (* c m) 2)) 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-10 (p (* c (- (* c m) 2))))))))

(defthm rem-one-mod-m-1
    (implies (and (natp m)
		  (> m 1)
		  (natp-all l)
		  (rel-prime-all m l))
	     (>= (* (c m l) (- (* (c m l) m) 2))
		 0))
  :rule-classes ()
  :hints (("Goal" :use (one-mod-alt
			(:instance one-mod-nat (x m))
			(:instance c-int (x m))
			(:instance hack-11 (c (c m l)))))))

(defthm REM-ONE-MOD-1
    (implies (and (natp x)
		  (> x 1)
		  (natp-all l)
		  (rel-prime-all x l))
	     (= (rem (one-mod x l) x) 1))
  :rule-classes ()
  :hints (("Goal" :use (one-mod-nat
			(:instance one-mod-alt (m x))
			(:instance rem-one-mod-m-1 (m x))
			(:instance c-int)
			(:instance rem< (m 1) (n x))
			(:instance rem+
				   (m 1)
				   (n x)
				   (a (* (c x l)
					 (- (* (c x l) x)
					    2))))))))

; Matt K.: Removed definition of remove1 (defined in ACL2 starting with
; v2-9-4).

(defthm prod-factor
    (implies (and (natp-all l)
		  (member x l))
	     (= (prod l)
		(* x (prod (remove1 x l)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable prod))))

(defthm one-mod-factor
    (implies (and (integerp m)
		  (natp-all l)
		  (member x l))
	     (= (one-mod m l)
		(* x (d m l) (prod (remove1 x l)) (d m l) (prod l))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable one-mod)
		  :use (prod-factor))))

(defthm prod-int
    (implies (natp-all l)
	     (integerp (prod l)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable prod))))

(defthm natp-remove1
    (implies (natp-all l)
	     (natp-all (remove1 x l))))

(defthm hack-12
    (implies (and (integerp a)
		  (integerp b)
		  (integerp c)
		  (integerp d))
	     (integerp (* a b c d)))
  :rule-classes ())

(defthm rem-one-mod-x-1
    (implies (and (natp m)
		  (> m 1)
		  (natp-all l))
	     (INTEGERP (* (PROD L)
			  (D M L)
			  (D M L)
			  (PROD (REMOVE1 X L)))))
  :hints (("Goal" :in-theory (disable prod-int)
		  :use (prod-int
			(:instance prod-int (l (remove1 x l)))
			(:instance hack-12
				   (a (prod l))
				   (b (d m l))
				   (c (d m l))
				   (d (prod (remove1 x l))))))))

(defthm rem-one-mod-x-2
    (implies (and (natp m)
		  (> m 1)
		  (natp-all l)
		  (rel-prime-all m l)
		  (member x l)
		  (integerp x)
		  (> x 0))
	     (= (rem (one-mod m l) x) 0))
  :rule-classes ()
  :hints (("Goal" :use (one-mod-factor
			(:instance one-mod-nat (x m))
			(:instance divides-rem-0
				   (n x)
				   (a (* (d m l) (prod (remove1 x l)) (d m l) (prod l))))))))

(defthm modulus-pos
    (implies (and (rel-prime-moduli l)
		  (member x l))
	     (and (integerp x)
		  (> x 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-moduli))))

(defthm moduli-natp-all
    (implies (rel-prime-moduli l)
	     (natp-all l))
  :hints (("Goal" :in-theory (enable rel-prime-moduli))))

(defthm REM-ONE-MOD-0
    (implies (and (natp x)
		  (> x 1)
		  (rel-prime-moduli l)
		  (rel-prime-all x l)
		  (member y l))
	     (= (rem (one-mod x l) y) 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-one-mod-x-2 (m x) (x y))
			(:instance modulus-pos (x y))))))

(defthm rem0+0
    (implies (and (natp a)
		  (natp b)
		  (natp c)
		  (natp n)
		  (> n 0)
		  (= (rem a n) 0)
		  (= (rem c n) 0))
	     (= (rem (+ (* a b) c) n) 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem+rem (a (* a b)) (b c))
			(:instance n<=fl (n 0) (x (/ a n)))
			(:instance divides-rem-0 (a (* (fl (/ a n)) b)))
			(:instance fl-rem-0 (m a))))))

(defthm rel-prime-all-remove
    (implies (rel-prime-all m l)
	     (rel-prime-all m (remove x l)))
  :hints (("Goal" :in-theory (enable rel-prime-all))))

(defthm rel-prime-remove
    (implies (rel-prime-moduli l)
	     (rel-prime-moduli (remove x l)))
  :hints (("Goal" :in-theory (enable rel-prime-moduli))))

(defthm member-remove
    (implies (and (member x l)
		  (not (eql x y)))
	     (member x (remove y l))))

(defun sublistp (m l)
  (if (endp m)
      t
    (and (member (car m) l)
	 (sublistp (cdr m) l))))

(defthm member-sublistp
    (implies (and (sublistp m l)
		  (member x m))
	     (member x l)))

(defthm g-c-d-commutative
    (implies (and (natp x) (natp y))
	     (= (g-c-d x y) (g-c-d y x)))
  :rule-classes ())

(defthm rel-prime-all-rel-prime
    (implies (and (rel-prime-all x l)
		  (member y l))
	     (rel-prime x y))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-all))))

(defthm rel-prime-all-moduli-remove
    (implies (and (rel-prime-moduli l)
		  (member x l))
	     (rel-prime-all x (remove x l)))
  :hints (("Goal" :in-theory (enable rel-prime-all rel-prime-moduli))
	  ("Subgoal *1/7''" :use ((:instance rel-prime-all-rel-prime
					     (x (car l))
					     (l (cdr l))
					     (y x))
				  (:instance g-c-d-commutative (y (car l))))
			    :in-theory (enable rel-prime))
	  ("Subgoal *1.1/5" :use ((:instance g-c-d-commutative (y l1))))))

(defthm rel-prime-modulus-nat
    (implies (and (member x l)
		  (rel-prime-moduli l))
	     (and (natp x) (> x 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-moduli))))

(defthm REM-CRT1
    (implies (and (natp-all a)
		  (rel-prime-moduli m)
		  (= (len a) (len m))
		  (rel-prime-moduli l)
		  (sublistp m l)
		  (member x l)
		  (not (member x m)))
	     (and (natp (crt1 a m l))
		  (= (rem (crt1 a m l) x) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-moduli crt1))
	  ("Subgoal *1/1" :use (modulus-pos
				(:instance rem< (m 0) (n x))))
	  ("Subgoal *1/3" :use ((:instance rem0+0
					   (n x)
					   (a (one-mod (car m) (remove (car m) l)))
					   (b (car a))
					   (c (crt1 (cdr a) (cdr m) l)))
				(:instance rel-prime-modulus-nat)
				(:instance rem-one-mod-0
					   (x (car m))
					   (y x)
					   (l (remove (car m) l)))
				(:instance one-mod-nat
					   (x (car m))
					   (l (remove (car m) l)))))))

(defthm rem0+1-1
    (implies (and (natp a)
		  (natp b)
		  (natp c)
		  (natp n)
		  (> n 0))
	     (= (rem (* a (1+ (* (fl (/ b n)) n))) n)
		(rem a n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance n<=fl (n 0) (x (/ b n)))
			(:instance rem+ (a (* a (fl (/ b n)))) (m a))))))

(defthm rem0+1-2
    (implies (and (natp a)
		  (natp b)
		  (natp c)
		  (natp n)
		  (= (rem b n) 1)
		  (> n 0))
	     (= (rem (* a (+ (rem b n) (* (fl (/ b n)) n))) n)
		(rem a n)))
  :rule-classes ()
  :hints (("Goal" :use (rem0+1-1))))

(defthm rem0+1-3
    (implies (and (natp a)
		  (natp b)
		  (natp c)
		  (natp n)
		  (= (rem b n) 1)
		  (> n 0))
	     (= (rem (* a b) n)
		(rem (* a (+ (rem b n) (* (fl (/ b n)) n))) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m b))))))

(defthm rem0+1-4
    (implies (and (natp a)
		  (natp b)
		  (natp c)
		  (natp n)
		  (= (rem b n) 1)
		  (> n 0))
	     (= (rem (* a b) n)
		(rem a n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a9 unicity-of-1)
		  :use (rem0+1-2
			rem0+1-3))))

(defthm rem0+1
    (implies (and (natp a)
		  (natp b)
		  (natp c)
		  (natp n)
		  (> n 0)
		  (= (rem b n) 1)
		  (= (rem c n) 0))
	     (= (rem (+ (* a b) c) n) (rem a n)))
  :rule-classes ()
  :hints (("Goal" :use (rem0+1-4
			(:instance rem+rem (a (* a b)) (b c))))))

(defthm rel-prime-not-eql
    (implies (and (natp x)
		  (natp y)
		  (> x 1)
		  (rel-prime x y))
	     (not (= x y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime g-c-d))))

(defthm not-member-rel-prime-all
    (implies (and (natp x)
		  (> x 1)
		  (rel-prime-all x m))
	     (not (member x m)))
  :hints (("Goal" :in-theory (enable rel-prime-all))
	  ("Subgoal *1/2'4'" :use ((:instance rel-prime-not-eql (x m1) (y m1))))))

(defun cong0-all (x l)
  (if (endp l)
      t
    (and (= (rem x (car l)) 0)
	 (cong0-all x (cdr l)))))

(defthm cong0-1
    (implies (and (natp a)
		  (natp m)
		  (> m 1)
		  (sublistp l1 l)
		  (rel-prime-all m l1)
		  (rel-prime-moduli l1)
		  (rel-prime-all m l)
		  (rel-prime-moduli l))
	     (cong0-all (* a (one-mod m l)) l1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-all rel-prime-moduli))
	  ("Subgoal *1/6" :use ((:instance rem-one-mod-0 (x m) (y (car l1)))
				(:instance one-mod-nat (x m))
				(:instance rem< (m 0) (n (car l1)))
				(:instance rem0+0 (c 0) (a (one-mod m l)) (b a) (n (car l1)))))))

(defun sublistp-induct (n l)
  (declare (xargs :measure (nfix (- (len l) n))))
  (if (and (natp n) (< n (len l)))
      (sublistp-induct (1+ n) l)
    t))

(defthm sublistp-last
    (sublistp (nthcdr (len l) l) m))

(defthm nthcdr+1
    (implies (natp n)
	     (equal (NTHCDR (+ 1 N) L)
		    (cdr (nthcdr n l)))))

(defthm member-car-nthcdr
    (IMPLIES (AND (INTEGERP N)
		  (<= 0 N)
		  (< N (LEN L)))
	     (MEMBER (CAR (NTHCDR N L)) L)))

(defthm sublistp-nthcdr
    (implies (and (natp n)
		  (<= n (len l)))
	     (sublistp (nthcdr n l) l))
  :rule-classes ()
  :hints (("Goal" :induct (sublistp-induct n l))))

(defthm sublistp-l-l
    (sublistp l l)
  :hints (("Goal" :use ((:instance sublistp-nthcdr (n 0))))))

(defthm sublistp-remove
    (implies (and (sublistp m l)
		  (not (member x m)))
	     (sublistp m (remove x l))))

(defun distinctp (l)
  (if (endp l)
      t
    (and (not (member (car l) (cdr l)))
	 (distinctp (cdr l)))))

(defthm sublistp-cdr-remove
    (implies (and (sublistp m l)
		  (distinctp m)
		  (consp m))
	     (sublistp (cdr m) (remove (car m) l))))

(defthm rel-prime-sublist
    (implies (and (rel-prime-all x l)
		  (sublistp m l))
	     (rel-prime-all x m))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-all))))

(defthm rel-prime-moduli-sublist
    (implies (and (rel-prime-moduli l)
		  (distinctp m)
		  (sublistp m l))
	     (rel-prime-moduli m))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-moduli rel-prime-all))
	  ("Subgoal *1/7" :use ((:instance rel-prime-modulus-nat (x (car m)))))
	  ("Subgoal *1/6" :use ((:instance rel-prime-modulus-nat (x (car m)))))
	  ("Subgoal *1/5" :use ((:instance rel-prime-sublist (x (car m)) (m (cdr m)) (l (remove (car m) l)))))))

(defthm cong0-2
    (implies (and (natp a)
		  (sublistp m l)
		  (distinctp m)
		  (rel-prime-moduli l))
	     (cong0-all (* a (one-mod (car m) (remove (car m) l))) (cdr m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-moduli rel-prime-all)
		  :use ((:instance cong0-1 (m (car m)) (l (remove (car m) l)) (l1 (cdr m)))
			(:instance rel-prime-all-moduli-remove (x (car m)))
			(:instance rel-prime-moduli-sublist)
			(:instance rel-prime-modulus-nat (x (car m)))))))

(defthm cong0-3
    (implies (and (rel-prime-moduli m)
		  (natp x)
		  (natp y)
		  (natp-all a)
		  (cong0-all x m)
		  (= (len a) (len m))
		  (congruent-all y a m))
	     (congruent-all (+ x y) a m))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-moduli))
	  ("Subgoal *1/8" :use ((:instance rem< (m 1) (n (car m)))
				(:instance rem0+1
					   (a y)
					   (b 1)
					   (c x)
					   (n (car m)))))))

(defthm natp-crt1
    (implies (and (natp-all a)
		  (rel-prime-moduli m)
		  (= (len a) (len m))
		  (rel-prime-moduli l)
		  (distinctp m)
		  (sublistp m l))
	     (natp (crt1 a m l)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-moduli crt1))
	  ("Subgoal *1/2" :use ((:instance one-mod-nat
					   (x (car m))
					   (l (remove (car m) l)))))))

(defthm crt1-lemma
    (implies (and (natp-all a)
		  (rel-prime-moduli m)
		  (distinctp m)
		  (= (len a) (len m))
		  (rel-prime-moduli l)
		  (sublistp m l))
	     (congruent-all (crt1 a m l) a m))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable congruent-all rel-prime-moduli crt1))
	  ("Subgoal *1/8" :use ((:instance rem0+1
					   (a (car a))
					   (n (car m))
					   (b (ONE-MOD (CAR M) (REMOVE (CAR M) L)))
					   (c (CRT1 (CDR A) (CDR M) L)))
				(:instance rem-one-mod-1
					   (x (car m))
					   (l (remove (car m) l)))
				(:instance one-mod-nat
					   (x (car m))
					   (l (remove (car m) l)))
				(:instance rem-crt1
					   (a (cdr a))
					   (m (cdr m))
					   (x (car m)))))
	  ("Subgoal *1/7" :use ((:instance natp-crt1 (a (cdr a)) (m (cdr m)))
				(:instance cong0-2 (a (car a)))
				(:instance one-mod-nat
					   (x (car m))
					   (l (remove (car m) l)))
				(:instance cong0-3
					   (y (CRT1 (CDR A) (CDR M) L))
					   (a (cdr a))
					   (m (cdr m))
					   (x (* (CAR A) (ONE-MOD (CAR M) (REMOVE (CAR M) L)))))))))

(defthm distinctp-rel-prime-moduli
    (implies (rel-prime-moduli m)
	     (distinctp m))
  :hints (("Goal" :in-theory (enable rel-prime-moduli rel-prime-all))))

(in-theory (disable distinctp))

(defthm CRT1-THM
    (implies (and (natp-all a)
		  (rel-prime-moduli m)
		  (= (len a) (len m))
		  (rel-prime-moduli l)
		  (sublistp m l))
	     (congruent-all (crt1 a m l) a m))
  :rule-classes ()
  :hints (("Goal" :use (crt1-lemma))))

(defthm CHINESE-REMAINDER-THEOREM
    (implies (and (natp-all a)
		  (rel-prime-moduli m)
		  (= (len a) (len m)))
	     (and (natp (crt a m))
		  (congruent-all (crt a m) a m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable crt)
		  :use ((:instance natp-crt1 (l m))
			(:instance crt1-thm (l m))))))
