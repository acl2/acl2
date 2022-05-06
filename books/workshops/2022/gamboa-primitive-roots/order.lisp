(in-package "PFIELD")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(defund all-powers-aux (x i p)
  (declare (xargs :guard (and (posp x)
			      (posp i)
			      (integerp p)
			      (< 1 p)
			      (< x p))
		  :guard-hints (("Goal" :in-theory (enable fep)))
		  :measure (nfix (- p i))))
  (if (mbt (and (posp i) (posp p)))
      (if (>= i p)
	  nil
	(let ((xi (pow x i p)))
	  (if (equal xi 1)
	      (list xi)
	    (cons xi
		  (all-powers-aux x (1+ i) p)))))
    nil))

(defund all-powers (x p)
  (declare (xargs :guard (and (posp x)
			      (integerp p)
			      (< 1 p)
			      (< x p))))
  (all-powers-aux x 1 p))

(defund order (x p)
  (declare (xargs :guard (and (posp x)
			      (integerp p)
			      (< 1 p)
			      (< x p))))
  (len (all-powers x p)))

(defthmd max-len-all-powers-aux
  (implies (and (posp i)
		(posp p)
		(< 1 p)
		(< i p))
	   (<= (len (all-powers-aux x i p)) (- p i)))
  :hints (("Goal"
	   :in-theory (enable all-powers-aux))))



(local
 (defun nth-all-powers-aux-induction (n i p)
  (declare (xargs :measure (nfix (- p i))))
   (if (or (not (natp i))
	   (not (natp p))
	   (>= i p))
       (list n i p)
     (nth-all-powers-aux-induction (1- n) (1+ i) p))))


(defthmd nth-all-powers-aux
  (implies (and (posp i)
		(posp p)
		(natp n)
		(< n (len (all-powers-aux x i p)))
		(< 1 p)
		(< i p))
	   (equal (nth n (all-powers-aux x i p))
		  (pow x (+ n i) p)))
  :hints (("Goal"
	   :induct (nth-all-powers-aux-induction n i p)
	   :in-theory (enable all-powers-aux))))

(defthmd 1-has-to-be-last-in-all-powers-aux
  (implies (and (posp i)
		(posp p)
		(natp n)
		(< 1 p)
		(< i p)
		(equal (nth n (all-powers-aux x i p)) 1))
	   (equal (len (all-powers-aux x i p)) (+ n 1)))
  :hints (("Goal"
	   :induct (nth-all-powers-aux-induction n i p)
	   :in-theory (enable all-powers-aux))))

(local
 (defun natural-induction (n)
   (if (zp n)
       0
     (1+ (natural-induction (1- n))))))

(defthmd pow-of-inv
  (implies (and (rtl::primep p)
		(fep x p)
		(not (equal x 0))
		)
	   (equal (mul (pow x n p) (pow (inv x p) n p) p) 1))
  :hints (("Goal"
	   :induct (natural-induction n))
	  ("Subgoal *1/1"
	   :in-theory (enable pow))
	  ("Subgoal *1/2"
	   :use ((:instance mul-of-inv-arg2)
		 (:instance pow-opener
			    (x x)
			    (n n)
			    (p p))
		 (:instance pow-opener
			    (x (inv x p))
			    (n n)
			    (p p))
		 )
	   :in-theory (e/d nil (mul-of-inv-arg2
				)))
	  )
  )

(defthmd equal-powers-means-some-power-is-1-part-1
  (implies (and (posp i)
		(posp j)
		(posp p)
		(posp x)
		(< x p)
		(< 1 p)
		(< i j)
		(< j p)
		(rtl::primep p)
		(equal (pow x i p) (pow x j p))
		)
	   (equal (mul (pow x j p) (pow (inv x p) i p) p) 1))
  :hints (("Goal"
	   :use ((:instance pow-of-inv
			    (x x)
			    (n i)
			    (p p))
		 )
	   :in-theory (enable fep)
	   )
	  )
  )

(defthm mul-cancel-left
  (implies (and (rtl::primep p)
		(fep x p)
		(< 0 x)
		(fep y p)
		(equal (mul x y p) x))
	   (equal y 1))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance mul-associative
			    (x (inv x p))
			    (y x)
			    (z y)
			    (p p))
                 (:instance mul-commutative
                            (x x)
                            (y (inv x p)))
		 (:instance mul-of-inv-arg2)
		 )
	   :in-theory (e/d nil (mul-associative mul-commutative mul-of-inv-arg2)))))

(defthmd equal-powers-means-some-power-is-1
  (implies (and (posp i)
		(posp j)
		(posp p)
		(posp x)
		(< x p)
		(< 1 p)
		(< i j)
		(< j p)
		(rtl::primep p)
		(equal (pow x i p) (pow x j p))
		)
	   (equal (pow x (- j i) p) 1))
  :hints (("Goal"
	   :use ((:instance equal-powers-means-some-power-is-1-part-1)
		 (:instance pow-of-+
			    (a x)
			    (b (- j i))
			    (c i)
			    (p p))
		 (:instance pow-of-inv
			    (x x)
			    (n i)
			    (p p))
		 (:instance mul-cancel-left
			    (x (pow x i p))
			    (y (pow x (- j i) p))
			    (p p))
		 )
	   :in-theory (e/d (fep)
			   (pow-of-+))
	   )
	  )
  )

(defthmd no-dups-all-powers-part-1
  (implies (and (natp i)
		(natp j)
		(posp p)
		(posp x)
		(< x p)
		(< 1 p)
		(< i j)
		(< j (order x p))
		(rtl::primep p))
	   (not (equal (nth i (all-powers x p))
		       (nth j (all-powers x p)))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance nth-all-powers-aux
			    (i 1)
			    (p p)
			    (n i)
			    (x x))
		 (:instance nth-all-powers-aux
			    (i 1)
			    (p p)
			    (n j)
			    (x x))
		 (:instance nth-all-powers-aux
			    (i 1)
			    (p p)
			    (n (1- (- j i)))
			    (x x))
		 (:instance equal-powers-means-some-power-is-1
			    (i (1+ i))
			    (j (1+ j))
			    (p p)
			    (x x))
		 (:instance 1-has-to-be-last-in-all-powers-aux
			    (i 1)
			    (x x)
			    (n (1- (- j i)))
			    (p p))
		 (:instance max-len-all-powers-aux
			    (i 1)
			    (p p)
			    (x x)
			    ))
	   :in-theory (enable all-powers order))))

(defthm nth-into-last
  (implies (consp l)
	   (equal (nth (+ -1 (len l)) l)
		  (first (last l)))))

(defthm consp-all-powers-aux
  (implies (and (rtl::primep p))
	   (consp (all-powers-aux x 1 p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal"
	   :in-theory (enable rtl::primep
			      all-powers-aux)))
  )

(defthmd car-last-all-powers-aux-part-1
  (implies (and (posp i)
		(posp p)
		(< i p)
		(not (equal (len (all-powers-aux x i p)) (- p i))))
	   (equal (car (last (all-powers-aux x i p))) 1))
  :hints (("Goal"
	   :in-theory (enable all-powers-aux))))

(defthmd car-last-all-powers-aux-part-2
  (implies (and (posp p)
		(< i p)
		(posp x)
		(< x p)
		(rtl::primep p)
		(equal (len (all-powers-aux x 1 p)) (- p 1)))
	   (equal (car (last (all-powers-aux x 1 p))) 1))
  :hints (("Goal"
	   :use ((:instance nth-all-powers-aux
			    (i 1)
			    (p p)
			    (n (1- (len (all-powers-aux x 1 p))))
			    (x x))
		 (:instance nth-into-last
			    (l (all-powers-aux x 1 p)))
		 (:instance my-fermat-little
			    (a x)
			    (p p)))
	   :in-theory (e/d (fep minus1 all-powers-aux) (my-fermat-little nth-into-last)))))

(defthm pow-order
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p))
	   (equal (pow x (order x p) p) 1))
  :hints (("Goal" :cases ((equal (order x p) (- p 1)))
	   :in-theory (enable order all-powers))
	  ("Subgoal 2"
	   :use ((:instance nth-all-powers-aux
			    (i 1)
			    (p p)
			    (n (1- (len (all-powers-aux x 1 p))))
			    (x x))
		 (:instance car-last-all-powers-aux-part-1
			    (i 1)
			    (x x)
			    (p p))
		 )
	   )
	  ("Subgoal 1"
	   :use ((:instance my-fermat-little
			    (a x)
			    (p p)))
	   :in-theory (e/d (minus1) (my-fermat-little))
	   )
	  )
  )


(defthm pow-<-order
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p)
		(posp n)
		(< n (order x p)))
	   (not (equal (pow x n p) 1)))
  :hints (("Goal"
	   :use ((:instance pow-order)
		 (:instance no-dups-all-powers-part-1
			    (i (1- n))
			    (j (1- (order x p))))
		 (:instance nth-all-powers-aux
			    (i 1)
			    (p p)
			    (n (1- n)))
		 (:instance nth-all-powers-aux
			    (i 1)
			    (p p)
			    (n (1- (order x p))))
		 )
	   :in-theory (e/d (order all-powers) (pow-order)))))


(defun-sk exists-smaller-power-eq-1 (x p n)
  (exists (m)
	  (and (posp m)
	       (< m n)
	       (equal (pow x m p) 1))))

(defthmd cons-len-not-0
  (implies (consp l)
	   (not (equal (len l) 0)))
  )

(defthm posp-order
  (implies (rtl::primep p)
	   (< 0 (order x p)))
  :hints (("Goal"
	   :use ((:instance consp-all-powers-aux)
		 (:instance cons-len-not-0
			    (l (all-powers-aux x 1 p))))
	   :in-theory (e/d (order all-powers) (consp-all-powers-aux))))
  :rule-classes (:rewrite :type-prescription))

(defthmd smallest-pow-eq-1-is-order
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p)
		(posp n)
		(equal (pow x n p) 1)
		(not (exists-smaller-power-eq-1 x p n)))
	   (equal (order x p) n))
  :hints (("Goal"
	   :cases ((< (order x p) n) (= (order x p) n) (> (order x p) n)))
	  ("Subgoal 2"
	   :use ((:instance exists-smaller-power-eq-1-suff
			    (m (order x p))
			    (n n)
			    (x x))
		 )
	   :in-theory (e/d nil (exists-smaller-power-eq-1-suff
				exists-smaller-power-eq-1
				)))
	  ))


(defthmd pow-of-*-arg2
  (implies (and (posp p)
		(< 1 p)
		(fep x p)
		(natp m)
		(natp n))
	   (equal (pow x (* m n) p)
		  (pow (pow x m p) n p)))
  :hints (("Goal"
	   :in-theory (enable pow-rewrite))
	  )
  )

(defthm pow-of-1-arg1
  (implies (and (< 1 p)
                (integerp p))
           (equal (pow 1 n p)
                  1))
  :hints (("Goal" :in-theory (enable pow))))


(defthmd pow-multiples-of-order
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p)
		(natp k))
	   (equal (pow x (* k (order x p)) p) 1))
  :hints (("Goal"
	   :use ((:instance pow-of-*-arg2
			    (x x)
			    (p p)
			    (m (order x p))
			    (n k))))))


(defthmd pow-mod-order
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p)
		(natp n))
	   (equal (pow x (mod n (order x p)) p)
		  (pow x n p)))
  :hints (("Goal"
	   :use ((:instance acl2::floor-mod-elim
			    (acl2::x n)
			    (acl2::y (order x p)))
		 (:instance pow-of-+
			    (a x)
			    (b (* (floor n (order x p)) (order x p)))
			    (c (mod n (order x p)))
			    (p p))
		 (:instance pow-multiples-of-order
			    (x x)
			    (k (floor n (order x p)))
			    (p p))
		 )
	   ))
  )

(defthmd pow-is-1->-exponent-mod-order-zero
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p)
		(natp n)
		(equal (pow x n p) 1))
	   (equal (mod n (order x p))
		  0))
  :hints (("Goal"
	   :use ((:instance pow-mod-order)
		 (:instance pow-<-order
			    (x x)
			    (p p)
			    (n (mod n (order x p)))))
	   :in-theory (disable pow-<-order))))

(defthmd pow-is-1->-order-divides-exponent
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p)
		(natp n)
		(equal (pow x n p) 1))
	   (rtl::divides (order x p) n))
  :hints (("Goal"
	   :use ((:instance pow-is-1->-exponent-mod-order-zero)
		 (:instance rtl::divides-mod-0
			    (a n)
			    (n (order x p)))))))

(defthmd order-divides-p-minus1
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p))
	   (rtl::divides (order x p) (1- p)))
  :hints (("Goal"
	   :use ((:instance pow-is-1->-order-divides-exponent
			    (x x)
			    (n (1- p))
			    (p p))
		 (:instance my-fermat-little
			    (a x)
			    (p p)))
	   :in-theory (e/d (minus1) (my-fermat-little)))))

(defthm inv-not-0
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p))
	   (not (equal (inv x p) 0)))
  :hints (("Goal"
	   :use ((:instance mul-of-inv-arg2))
	   :in-theory (disable mul-of-inv-arg2))))

(defthmd order-inv-part1
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p))
	   (equal (pow (inv x p) (order x p) p) 1))
  :hints (("Goal"
	   :use ((:instance pow-of-inv
			    (x x)
			    (n (order x p))
			    (p p))))))

(defthmd order-inv-part2
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p))
	   (<= (order (inv x p) p) (order x p)))
  :hints (("Goal"
	   :use ((:instance order-inv-part1)
		 (:instance pow-<-order
			    (x (inv x p))
			    (n (order x p))
			    (p p))))))

(defthmd order-inv-part3
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p))
	   (<= (order (inv (inv x p) p) p) (order (inv x p) p)))
  :hints (("Goal"
	   :use ((:instance order-inv-part2
                            (x (inv x p)))))))

(defthmd mul-inv-x-x-y
  (implies (and (fep x p) (fep y p)
                (not (equal 0 x))
                (rtl::primep p))
           (equal (mul (inv x p) (mul x y p) p)
                  y))
  :hints (("Goal"
	   :use ((:instance mul-associative
			    (x (inv x p))
			    (y x)
			    (z y)
			    (p p))
                 (:instance mul-commutative
                            (x x)
                            (y (inv x p)))
		 (:instance mul-of-inv-arg2))
           :in-theory (disable mul-associative mul-commutative mul-of-inv-arg2)
           )))

(defthm inv-unique
  (implies (and (fep x p)
                (fep y p)
                (equal (mul x y p) 1)
                (rtl::primep p))
           (equal (inv x p) y))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  (:theorem (implies (and (fep x p) (fep y1 p)
                                          (equal y1 y2)
                                          (rtl::primep p))
                                     (equal (mul x y1 p) (mul x y2 p))))
                  (y1 (mul x y p))
                  (y2 1)
                  (x (inv x p))
                  (p p))
                 (:instance mul-inv-x-x-y)
                 )
           )
          ))

(defthm inv-inv
  (implies (and (fep x p)
                (not (equal 0 x))
                (rtl::primep p))
           (equal (inv (inv x p) p) x))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance inv-unique
                            (x (inv x p))
                            (y x)
                            (p p))
                 (:instance mul-commutative
                            (x x)
                            (y (inv x p)))
		 (:instance mul-of-inv-arg2))
           :in-theory (disable mul-commutative mul-of-inv-arg2)
           )))

(defthmd order-inv-part4
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p))
	   (<= (order x p) (order (inv x p) p)))
  :hints (("Goal"
	   :use ((:instance order-inv-part3)
                 (:instance inv-inv)))))

(defthmd order-inv
  (implies (and (fep x p)
		(not (equal 0 x))
		(rtl::primep p))
	   (equal (order (inv x p) p) (order x p)))
  :hints (("Goal"
	   :use ((:instance order-inv-part2)
                 (:instance order-inv-part4)))))
