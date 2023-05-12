(in-package "PFIELD")

(include-book "order")
(include-book "pfield-polynomial")
(include-book "projects/numbers/euclid" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

(defund relatively-primep (a b)
  (declare (xargs :guard (and (natp a)
			      (natp b))))
  (equal (dm::gcd a b) 1))

(defthm relatively-primes-have-no-common-factors
  (implies (and (natp a)
		(natp b)
		(relatively-primep a b)
		(natp k)
		(dm::divides k a)
		(dm::divides k b))
	   (equal k 1))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance dm::divides-gcd
			    (acl2::x a)
			    (acl2::y b)
			    (acl2::d k)))
	   :in-theory (e/d (relatively-primep dm::divides)
			   (dm::divides-gcd)))))



(defthmd pow-mul-order
  (implies (and (dm::primep p)
		(fep a p)
		(fep b p)
		(not (equal 0 a))
		(not (equal 0 b)))
	   (equal (pow (mul a b p)
		       (* (order a p) (order b p))
		       p)
		  1))
  :hints (("Goal"
	   :use ((:instance pow-of-mul-arg1
			    (x a)
			    (y b)
			    (n (* (order a p) (order b p)))
			    (p p))
		 (:instance pow-multiples-of-order
			    (x a)
			    (k (order b p))
			    (p p))
		 (:instance pow-multiples-of-order
			    (x b)
			    (k (order a p))
			    (p p)))))
  )




(defthmd construct-product-order-part1
  (implies (and (dm::primep p)
		(fep a p)
		(fep b p)
		(not (equal 0 a))
		(not (equal 0 b))
		)
	   (dm::divides (order (mul a b p) p)
			 (* (order a p) (order b p))))
  :hints (("Goal"
	   :use ((:instance pow-mul-order)
		 (:instance pow-is-1->-order-divides-exponent
			    (x (mul a b p))
			    (n (* (order a p) (order b p)))
			    (p p))
		 )
	   )
	  )
  )

(defthm construct-product-order-part2a
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                ;; (not (equal 0 a))
                ;; (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1))
           (equal (inv (pow b k p) p)
                  (pow a k p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance inv-unique
                            (x (pow b k p))
                            (y (pow a k p))
                            (p p))
                 (:instance pow-of-mul-arg1
			    (x a)
			    (y b)
			    (n k)
			    (p p))
                 ))))

(defthm inv-pow
  (implies (and (dm::primep p)
                (fep a p)
                (not (equal 0 a))
                (natp k))
           (equal (inv (pow a k p) p)
                  (pow (inv a p) k p)))
  :hints (("Goal"
           :use ((:instance inv-unique
                            (x (pow a k p))
                            (y (pow (inv a p) k p))
                            (p p))
                 (:instance pow-of-mul-arg1
                            (x a)
                            (y (inv a p))
                            (n k)
                            (p p))
                 )
           )))

(defthm construct-product-order-part2b
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1))
           (equal (pow (inv b p) k p)
                  (pow a k p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2a)
                 ))))

(defthm construct-product-order-part2c
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1))
           (equal (pow (inv b p) (* k (order b p)) p)
                  (pow a (* k (order b p)) p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2b)
                 (:instance pow-of-*-arg2
                            (x (inv b p))
                            (m k)
                            (n (order b p))
                            (p p))
                 (:instance pow-of-*-arg2
                            (x a)
                            (m k)
                            (n (order b p))
                            (p p))
                 ))))

(defthm construct-product-order-part2d
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1))
           (equal (pow a (* k (order b p)) p)
                  1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2c)
                 (:instance pow-of-*-arg2
                            (x (inv b p))
                            (m (order b p))
                            (n k)
                            (p p))
                 (:instance pow-order
                            (x (inv b p))
                            (p p))
                 )
           :in-theory (e/d (order-inv)
                           (pow-order)))))

(defthm construct-product-order-part2e
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1))
           (equal (pow (pow a k p) (order b p) p)
                  1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2d)
                 (:instance pow-of-*-arg2
                            (x a)
                            (m k)
                            (n (order b p))
                            (p p))
                 ))))

(defthm construct-product-order-part2f
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1))
           (equal (pow (pow a k p) (order a p) p)
                  1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pow-of-*-arg2
                            (x a)
                            (m (order a p))
                            (n k)
                            (p p))
                 (:instance pow-of-*-arg2
                            (x a)
                            (m k)
                            (n (order a p))
                            (p p))
                 ))))

(defthm fep-euclidean
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b)))
           (not (equal (mul a b p) 0)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance dm::euclid
                            (acl2::p p)
                            (acl2::a a)
                            (acl2::b b))
                 (:instance dm::divides-mod-0
                            (acl2::n p)
                            (acl2::a a))
                 (:instance dm::divides-mod-0
                            (acl2::n p)
                            (acl2::a b))
                 (:instance dm::divides-mod-0
                            (acl2::n p)
                            (acl2::a (* a b)))
                 )
           :in-theory (enable mul))))

(defthm pow-not-zero-for-non-zero-base
  (implies (and (dm::primep p)
                (fep a p)
                (not (equal 0 a))
                (natp n))
           (not (equal (pow a n p) 0)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable pow)
           :induct (pow a n p))
          ("Subgoal *1/2"
           :use ((:instance fep-euclidean
                            (p p)
                            (a a)
                            (b (pow a (1- n) p)))))
          ))

(defthm construct-product-order-part2g
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1))
           (and (dm::divides (order (pow a k p) p) (order a p))
                (dm::divides (order (pow a k p) p) (order b p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2e)
                 (:instance construct-product-order-part2f)
                 (:instance pow-is-1->-order-divides-exponent
                            (x (pow a k p))
                            (n (order a p))
                            (p p))
                 (:instance pow-is-1->-order-divides-exponent
                            (x (pow a k p))
                            (n (order b p))
                            (p p))
                 (:instance pow-not-zero-for-non-zero-base
                            (a a)
                            (n k)
                            (p p))
                 ))))

(defthm construct-product-order-part2h
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1)
                (relatively-primep (order a p) (order b p)))
           (dm::divides (order (pow a k p) p) 1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2g)
                 (:instance dm::divides-gcd
                            (acl2::x (order a p))
                            (acl2::y (order b p))
                            (acl2::d (order (pow a k p) p)))
                 )
           :in-theory (enable relatively-primep))))

(defthm must-be-1-if-divides-1
  (implies (and (posp x)
                (dm::divides x 1))
           (equal x 1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance dm::divides-leq
                            (acl2::x x)
                            (acl2::y 1))))))

(defthm construct-product-order-part2i
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1)
                (relatively-primep (order a p) (order b p)))
           (equal (order (pow a k p) p) 1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2h)
                 (:instance must-be-1-if-divides-1
                            (x (order (pow a k p) p)))))))

(defthm car-all-powers-aux
  (implies (and (dm::primep p)
                (fep a p))
           (equal (car (all-powers-aux a 1 p))
                  a))
  :hints (("Goal"
           :expand (all-powers-aux a 1 p))))

(defthm car-last-len-1
  (implies (equal (len l) 1)
           (equal (car (last l)) (car l))))

(defthm only-1-has-order-1
  (implies (and (dm::primep p)
                (fep a p)
                (not (equal a 0))
                (equal (order a p) 1))
           (equal a 1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance car-last-all-powers-aux-part-1
                            (i 1)
                            (x a)
                            (p p))
                 (:instance car-last-all-powers-aux-part-2
                            (i 1)
                            (x a)
                            (p p)))
           :in-theory (enable order
                              all-powers
                              all-powers-aux
                              ))))

(defthm construct-product-order-part2j
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1)
                (relatively-primep (order a p) (order b p)))
           (and (equal (pow a k p) 1)
                (equal (pow (inv b p) k p) 1)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2b)
                 (:instance construct-product-order-part2i)
                 (:instance pow-not-zero-for-non-zero-base
                            (a a)
                            (n k)
                            (p p))
                 (:instance only-1-has-order-1
                            (a (pow a k p)))))))

(defthm construct-product-order-part2k
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1)
                (relatively-primep (order a p) (order b p)))
           (and (dm::divides (order a p) k)
                (dm::divides (order b p) k)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2j)
                 (:instance pow-is-1->-order-divides-exponent
                            (x a)
                            (n k)
                            (p p))
                 (:instance pow-is-1->-order-divides-exponent
                            (x (inv b p))
                            (n k)
                            (p p))
                 (:instance order-inv
                            (x b)
                            (p p)))
           :in-theory (enable relatively-primep))))

;;; -----------------------------
;;;
;;; Proof that if x|z and y|z with x, y relatively prime, then
;;; x*y|z
;;; -----------------------------


(defthm mod-*
  (implies (and (integerp x)
                (integerp y)
                (posp n))
           (equal (mod (* x y) n)
                  (mod (* (mod x n) (mod y n)) n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance acl2::mod-theorem-one-a
                            (acl2::a x)
                            (acl2::b (mod y n))
                            (acl2::n n)))
           :in-theory (disable acl2::mod-theorem-one-a
                               acl2::mod-theorem-one-b))))

(local
 (defun gcd-nat-x-1-induction-hint (x)
   (if (or (zp x) (= x 1))
       0
     (1+ (gcd-nat-x-1-induction-hint (1- x))))))

(defthm gcd-nat-x-1
  (implies (natp x)
           (= (dm::gcd-nat x 1) 1))
  :hints (("Goal"
           :induct (gcd-nat-x-1-induction-hint x)
           :in-theory (enable dm::gcd-nat)))
  )

(defthm gcd-x-1
  (implies (integerp x)
           (= (dm::gcd x 1) 1))
  :hints (("Goal"
           :in-theory (enable dm::gcd)))
  )


(defthm relatively-primep-x-1
  (implies (integerp x)
           (relatively-primep x 1))
  :hints (("Goal"
           :in-theory (enable relatively-primep))))



(encapsulate
  nil

  (local
   (defthm lemma-1
     (implies (and (natp x)
                   (posp z)
                   (relatively-primep x z))
              (= (+ (* (dm::r x z) x)
                    (* (dm::s x z) z))
                 1))
     :rule-classes nil
     :hints (("Goal"
              :use ((:instance dm::gcd-linear-combination
                               (acl2::x x)
                               (acl2::y z)))
              :in-theory (enable relatively-primep)))))

  (local
   (defthm lemma-2
     (implies (and (natp x)
                   (integerp z)
                   (< 1 z)
                   (relatively-primep x z))
              (= (mod (* (dm::r x z) x) z)
                 1))
     :rule-classes nil
     :hints (("Goal"
              :use ((:instance lemma-1)
                    (:instance acl2::mod-mult
                               (acl2::m (* (dm::r x z) x))
                               (acl2::n z)
                               (acl2::a (dm::s x z)))
                    )
              ))))

  (local
   (defthm lemma-3
     (implies (and (natp x)
                   (natp y)
                   (integerp z)
                   (< 1 z)
                   (= (mod (* x y) z) 0)
                   (relatively-primep x z))
              (= (mod (* (dm::r x z) x y) z)
                 0))
     :rule-classes nil
     :hints (("Goal"
              :use ((:instance mod-*
                               (x (dm::r x z))
                               (y (* x y))
                               (n z))
                    )
              ))))


  (local
   (defthm lemma-4
     (implies (and (natp x)
                   (natp y)
                   (integerp z)
                   (< 1 z)
                   (= (mod (* x y) z) 0)
                   (relatively-primep x z))
              (= (mod y z)
                 0))
     :rule-classes nil
     :hints (("Goal"
              :use ((:instance lemma-2)
                    (:instance lemma-3)
                    (:instance mod-*
                               (x (* (dm::r x z) x))
                               (y y)
                               (n z))
                    )
              ))))


  (defthm divides-one-of-the-terms-in-product
    (implies (and (natp x)
                  (natp y)
                  (posp z)
                  (dm::divides z (* x y))
                  (relatively-primep x z))
             (dm::divides z y))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance lemma-4)
                   (:instance dm::divides-mod-0
                              (acl2::n z)
                              (acl2::a y))
                   (:instance dm::divides-mod-0
                              (acl2::n z)
                              (acl2::a (* x y)))
                   ))))
  )

(defthm divides-floor-quotient
  (implies (and (posp x)
                (natp z))
           (iff (dm::divides x z)
                (= (* (floor z x) x) z)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance dm::divides-mod-0
                            (acl2::n x)
                            (acl2::a z))
                 )
           :in-theory (enable mod))))

(defthm divides-product
  (implies (and (integerp x)
                (integerp y)
                (not (= 0 x))
                (not (= 0 y))
                (integerp z)
                (dm::divides y z))
           (dm::divides (* x y) (* x z)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable dm::divides)))
  )

(defthmd divides-product-when-gcd-1
  (implies (and (posp x)
                (posp y)
                (natp z)
                (dm::divides x z)
                (dm::divides y z)
                (relatively-primep x y))
           (dm::divides (* x y) z))
  :hints (("Goal"
           :use ((:instance divides-floor-quotient)
                 (:instance divides-floor-quotient
                            (x y)
                            (z (floor z x)))
                 (:instance divides-one-of-the-terms-in-product
                            (z y)
                            (y (floor z x))
                            (x x))
                 (:instance divides-product
                            (x x)
                            (y y)
                            (z (* (/ x) z)))
                 ))))



(defthm construct-product-order-part2l
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (posp k)
                (equal (pow (mul a b p) k p) 1)
                (relatively-primep (order a p) (order b p)))
           (dm::divides (* (order a p) (order b p)) k))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2k)
                 (:instance divides-product-when-gcd-1
                            (x (order a p))
                            (y (order b p))
                            (z k))))))

;; (defthm mul-by-same
;;   (implies (and (dm::primep p)
;;                 (fep a p)
;;                 (fep b p)
;;                 (fep c p)
;;                 (equal b c))
;;            (equal (mul a b p) (mul a c p)))
;;   :rule-classes nil)

(defthm mul-cancel-arg1
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (= 0 a)))
           (= (mul (inv a p) (mul a b p) p) b))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance mul-associative
                            (x (inv a p))
                            (y a)
                            (z b)
                            (p p))
                 (:instance mul-of-inv-arg2
                            (x a)
                            (p p))
                 (:instance mul-commutative
                            (x (inv a p))
                            (y a)
                            (p p))
                 )
           :in-theory (disable mul-of-inv-arg2
                               mul-associative
                               mul-commutative))))

(defthm construct-product-order-part2
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (relatively-primep (order a p) (order b p)))
           (dm::divides (* (order a p) (order b p))
                         (order (mul a b p) p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part2l
                            (a a)
                            (b b)
                            (k (order (mul a b p) p))
                            (p p))
                 (:instance pow-order
                            (x (mul a b p))
                            (p p))
                 (:instance fep-euclidean)
                 )
           :in-theory (disable pow-order)
           )))


(defthm construct-product-order
  (implies (and (dm::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b))
                (relatively-primep (order a p) (order b p)))
           (equal (order (mul a b p) p)
                  (* (order a p) (order b p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance construct-product-order-part1)
                 (:instance construct-product-order-part2)
                 (:instance dm::divides-leq
                            (x (order (mul a b p) p))
                            (y (* (order a p) (order b p))))
                 (:instance dm::divides-leq
                            (x (* (order a p) (order b p)))
                            (y (order (mul a b p) p)))))))

;;----------------------------------------------------------------------

(defthm gcd-of-prime-either-1-or-p
  (implies (and (dm::primep p)
                (posp x)
                )
           (or (= (dm::gcd p x) 1)
               (= (dm::gcd p x) p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance dm::gcd-divides
                            (x p)
                            (y x))
                 (:instance dm::primep-no-divisor
                            (p p)
                            (d (dm::gcd p x)))
                 (:instance dm::gcd-pos
                            (x p)
                            (y x))
                 ))))

(local
 (defun natural-induction (n)
   (if (zp n)
       0
     (1+ (natural-induction (1- n))))))

(defun number-of-powers (x p)
  (declare (xargs :hints (("Goal"
                           :in-theory (enable dm::divides)))))
  (if (and (integerp p)
           (<= 2 p))
      (if (or (zp x) (= 1 x))
          0
        (if (dm::divides p x)
            (1+ (number-of-powers (/ x p) p))
          0))
    0))

(defthm factors-of-prime-powers-part1
  (implies (and (dm::primep p)
                (posp x)
                (natp n)
                (dm::divides x (expt p n))
                (= (dm::gcd p x) 1))
           (equal x (expt p (number-of-powers x p))))
  :rule-classes nil
  :hints (("Goal"
           :induct (natural-induction n))
          ("Subgoal *1/2"
           :use ((:instance divides-one-of-the-terms-in-product
                            (x p)
                            (y (expt p (1- n)))
                            (z x)))
           :in-theory (enable relatively-primep))
          ("Subgoal *1/1"
           :use ((:instance must-be-1-if-divides-1))
           )
          ))


(defun factors-of-prime-powers-part2-induction-hint (x p n)
  (declare (xargs :hints (("Goal"
                           :in-theory (enable dm::divides)))))
  (if (and (integerp p)
           (<= 2 p))
      (if (or (zp x) (< x p))
          n
        (if (dm::divides p x)
            (1+ (factors-of-prime-powers-part2-induction-hint (/ x p)
                                                              p
                                                              (1- n)))
          0))
    0))


(defthm divides-cancel
  (implies (and (natp x)
                (natp y)
                (posp z)
                (dm::divides (* x y) (* x z)))
           (dm::divides y z))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable dm::divides))))

(defthm factors-of-prime-powers-part2
  (implies (and (dm::primep p)
                (posp x)
                (natp n)
                (dm::divides x (expt p n))
                (= (dm::gcd p x) p))
           (equal x (expt p (number-of-powers x p))))
  :rule-classes nil
  :hints (("Goal"
           :induct (factors-of-prime-powers-part2-induction-hint x p n))
          ("Subgoal *1/3"
           :use ((:instance dm::gcd-divides
                            (x p)
                            (y x)))
           ;:in-theory (enable dm::divides)
           )
          ("Subgoal *1/2"
           :use ((:instance divides-cancel
                            (x p)
                            (y (/ x p))
                            (z (expt p (1- n))))
                 (:instance dm::gcd-divides
                            (x p)
                            (y x))
                 (:instance must-be-1-if-divides-1)
                 (:instance gcd-of-prime-either-1-or-p
                            (x (* (/ p) x))
                            (p p))
                 (:instance factors-of-prime-powers-part1
                            (x (* (/ p) x))
                            (n (1- n))
                            (p p))
                 )
           :in-theory (enable dm::divides)
           )
          ("Subgoal *1/1"
           :use ((:instance must-be-1-if-divides-1)
                 (:instance dm::gcd-divides
                            (x p)
                            (y x))
                 (:instance dm::divides-leq
                            (x (dm::gcd p x))
                            (y x))
                 )
           )
          ))

(defthm factors-of-prime-powers
  (implies (and (dm::primep p)
                (posp x)
                (natp n)
                (dm::divides x (expt p n)))
           (equal x (expt p (number-of-powers x p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance factors-of-prime-powers-part1)
                 (:instance factors-of-prime-powers-part2)
                 (:instance gcd-of-prime-either-1-or-p)))))

(defthm number-of-powers-when-x-divides-expt-p-n
  (implies (and (dm::primep p)
                (posp x)
                (natp n)
                (dm::divides x (expt p n)))
           (<= (number-of-powers x p) n))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance factors-of-prime-powers)
                 (:instance dm::divides-leq
                            (x x)
                            (y (expt p n)))))))


(defthm order-is-prime-power-when-prime-power-is-candidate
  (implies (and (dm::primep p)
                (dm::primep q)
                (<= q p)
                (fep a p)
                (not (= 0 a))
                (natp n)
                (= (pow a (expt q n) p) 1)
                )
           (equal (order a p)
                  (expt q (number-of-powers (order a p) q))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance factors-of-prime-powers
                            (x (order a p))
                            (p q)
                            (n n))
                 (:instance pow-is-1->-order-divides-exponent
                            (x a)
                            (n (expt q n))
                            (p p))))))

(defthm smaller-exponent-prime-power-is-1-then-largest-power-also-1
  (implies (and (dm::primep p)
                (dm::primep q)
                (<= q p)
                (fep a p)
                (not (= 0 a))
                (natp n)
                (= (pow a (expt q n) p) 1)
                (natp m)
                (<= n m)
                )
           (equal (pow a (expt q m) p) 1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pow-of-*-arg2
                            (x a)
                            (p p)
                            (m (expt q n))
                            (n (expt q (- m n))))
                 ))))

(defthm smaller-exponent-prime-power-is-1-then-largest-power-also-1
  (implies (and (dm::primep p)
                (dm::primep q)
                (<= q p)
                (fep a p)
                (not (= 0 a))
                (natp n)
                (= (pow a (expt q n) p) 1)
                (natp m)
                (<= n m)
                )
           (equal (pow a (expt q m) p) 1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pow-of-*-arg2
                            (x a)
                            (p p)
                            (m (expt q n))
                            (n (expt q (- m n))))
                 ))))

(defthm order-is-smaller-power-then-largest-power-also-1
  (implies (and (dm::primep p)
                (dm::primep q)
                (<= q p)
                (fep a p)
                (not (= 0 a))
                (natp n)
                (= (pow a (expt q n) p) 1)
                (not (equal (order a p) (expt q n)))
                )
           (equal (pow a (expt q (- n 1)) p) 1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance factors-of-prime-powers
                            (x (order a p))
                            (p q)
                            (n n)) ; (expt q n)))
                 (:instance number-of-powers-when-x-divides-expt-p-n
                            (x (order a p))
                            (p q)
                            (n n))
                 (:instance pow-is-1->-order-divides-exponent
                            (x a)
                            (n (expt q n))
                            (p p))
                 (:instance
                  smaller-exponent-prime-power-is-1-then-largest-power-also-1
                  (p p)
                  (q q)
                  (a a)
                  (n (number-of-powers (order a p) q))
                  (m (1- n)))
                 ))))

(defthm order-is-prime-power-lemma
  (implies (and (dm::primep p)
                (dm::primep q)
                (<= q p)
                (fep a p)
                (not (= 0 a))
                (natp n)
                (= (pow a (expt q n) p) 1)
                (not (= (pow a (expt q (- n 1)) p) 1))
                )
           (equal (order a p) (expt q n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  order-is-smaller-power-then-largest-power-also-1))))
  )

(defthm roots-of-0-poly
  (equal (pfield-polynomial-root-p '(0) a p)
         (fep a p))
  :hints (("Goal"
           :in-theory (enable pfield-polynomial-root-p
                              eval-pfield-polynomial
                              ))))

(defthm pow-root-equivalency
  (implies (and (dm::primep p)
                (fep a p)
                (natp n))
           (iff (= (pow a n p) 1)
                (pfield-polynomial-root-p (fermat-poly n) a p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance eval-pfield-polynomial-x^k-1
                            (poly (fermat-poly n))
                            (x a)
                            (p p))
                 (:instance len-fermat-poly))
           :in-theory (e/d (pfield-polynomial-root-p
                            add)
                           (len-fermat-poly
                            ;fermat-poly
                            ))
           )))

(defthm order-is-prime-power-lemma-2
  (implies (and (dm::primep p)
                (dm::primep q)
                (<= q p)
                (fep a p)
                (not (= 0 a))
                (natp n)
                (pfield-polynomial-root-p (fermat-poly (expt q n)) a p)
                (not (pfield-polynomial-root-p (fermat-poly (expt q (1- n))) a p))
                )
           (equal (order a p) (expt q n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance order-is-prime-power-lemma)
                 (:instance pow-root-equivalency
                            (a a)
                            (n (expt q n))
                            (p p))
                 (:instance pow-root-equivalency
                            (a a)
                            (n (expt q (- n 1)))
                            (p p))
                 ))))

(defun find-root-of-poly1-but-not-poly2 (poly1 poly2 x p)
  (if (zp x)
      nil
    (if (and (pfield-polynomial-root-p poly1 x p)
             (not (pfield-polynomial-root-p poly2 x p)))
        x
      (find-root-of-poly1-but-not-poly2 poly1 poly2 (1- x) p))))

(defthmd natp-find-root-of-poly1-but-not-poly2
  (implies (natp (find-root-of-poly1-but-not-poly2 poly1 poly2 x p))
           (and (pfield-polynomial-root-p poly1
                                          (find-root-of-poly1-but-not-poly2
                                           poly1
                                           poly2
                                           x
                                           p)
                                          p)
                (not (pfield-polynomial-root-p
                      poly2
                      (find-root-of-poly1-but-not-poly2 poly1 poly2 x p)
                      p)))))

(defthm exists-natp-find-root-of-poly1-but-not-poly2
  (implies (> (pfield-polynomial-num-roots-aux poly1 x p)
              (pfield-polynomial-num-roots-aux poly2 x p))
           (natp (find-root-of-poly1-but-not-poly2 poly1 poly2 x p)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable PFIELD-POLYNOMIAL-NUM-ROOTS-AUX)))
  )

(defun witness-with-order-q^n (q n p)
  (if (and (natp p)
           (<= 2 p)
           (natp q))
      (if (and (<= q p)
               (not (zp n)))
          (find-root-of-poly1-but-not-poly2 (fermat-poly (expt q n))
                                            (fermat-poly (expt q (1- n)))
                                            (1- p)
                                            p)
        1)
    nil))

(defthm bound-for-find-root-of-poly1-but-not-poly2
  (Implies (not (null (find-root-of-poly1-but-not-poly2 poly1 poly2 x p)))
           (and (integerp (find-root-of-poly1-but-not-poly2 poly1 poly2 x p))
                (< 0 (find-root-of-poly1-but-not-poly2 poly1 poly2 x p))
                (<= (find-root-of-poly1-but-not-poly2 poly1 poly2 x p) x))))


(defthm bounds-for-witness-with-order-q^n
  (implies (not (null (witness-with-order-q^n q n p)))
           (and (integerp (witness-with-order-q^n q n p))
                (< 0 (witness-with-order-q^n q n p))
                (<= (witness-with-order-q^n q n p) (1- p)))))

(defthm n=0-when-expt-q-n-<-p
  (implies (and (natp p)
                (natp q)
                (natp n)
                (<= (expt q n) p)
                (< p q))
           (= n 0))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable expt))))

(local
 (defthm order-of-1
   (implies (dm::primep p)
            (equal (order 1 p) 1))
   :hints (("Goal"
            :in-theory (enable order all-powers-aux all-powers)
            ))))

(defthm expt-n-1-divides
  (implies (and (natp x)
                (natp q)
                (posp n)
                (dm::divides (expt q n) x))
           (dm::divides (expt q (1- n)) x))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance dm::divides-transitive
                            (x (expt q (1- n)))
                            (y (expt q n))
                            (z x)))
           :in-theory (enable dm::divides)
           )))

(defthmd expt-monotonic-prime-base
  (implies (and (dm::primep p)
                (posp n))
           (< (expt p (1- n))
              (expt p n))))

(defthm order-is-prime-power-lemma-3
  (implies (and (dm::primep p)
                (dm::primep q)
                (<= q p)
                (posp n)
                (dm::divides (expt q n) (1- p))
                )
           (and (fep (witness-with-order-q^n q n p) p)
                (not (= 0 (witness-with-order-q^n q n p)))
                (equal (order (witness-with-order-q^n q n p) p)
                       (expt q n))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance order-is-prime-power-lemma-2
                            (p p)
                            (q q)
                            (n n)
                            (a (witness-with-order-q^n q n p)))
                 (:instance expt-n-1-divides
                            (x (1- p))
                            (q q)
                            (n n)
                            )
                 (:instance natp-find-root-of-poly1-but-not-poly2
                            (poly1 (fermat-poly (expt q n)))
                            (poly2 (fermat-poly (expt q (1- n))))
                            (x (1- p))
                            (p p))
                 (:instance exists-natp-find-root-of-poly1-but-not-poly2
                            (poly1 (fermat-poly (expt q n)))
                            (poly2 (fermat-poly (expt q (1- n))))
                            (x (1- p))
                            (p p))
                 (:instance bound-for-find-root-of-poly1-but-not-poly2
                            (poly1 (fermat-poly (expt q n)))
                            (poly2 (fermat-poly (expt q (1- n))))
                            (x (1- p))
                            (p p))
                 (:instance num-roots-fermat-poly-divisor-implicit
                            (n (expt q n))
                            (p p))
                 (:instance num-roots-fermat-poly-divisor-implicit
                            (n (expt q (1- n)))
                            (p p))
                 )
           :in-theory (e/d (pfield-polynomial-num-roots
                            fep)
                           (fermat-poly
                            bound-for-find-root-of-poly1-but-not-poly2
                            acl2::expt-is-increasing-for-base->-1
                            ))
           )))

(defthm witnes-with-order-q^0
  (equal (witness-with-order-q^n q 0 p)
         (if (and (natp p) (<= 2 p) (natp q))
             1
           nil)))

(defthm order-is-prime-power
  (implies (and (dm::primep p)
                (dm::primep q)
                (natp n)
                (dm::divides (expt q n) (1- p))
                )
           (and (fep (witness-with-order-q^n q n p) p)
                (not (= 0 (witness-with-order-q^n q n p)))
                (equal (order (witness-with-order-q^n q n p) p)
                       (expt q n))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance order-is-prime-power-lemma-3)
                 (:instance n=0-when-expt-q-n-<-p
                            (p (1- p))
                            (q q)
                            (n n))
                 (:instance dm::divides-leq
                            (x (expt q n))
                            (y (1- p)))
                 ;; (:instance expt-monotonic-prime-base
                 ;;            (p q)
                 ;;            (n n))
                 )
           :in-theory (e/d (dm::divides)
                           (witness-with-order-q^n)))))


;;; ---------------------------------------------------------------------

(defthm divisor-decreases-count
  (implies (and (natp k)
                (< 1 k)
                (natp f)
                (dm::divides f k)
                (< 1 f))
           (and (integerp (/ k f))
                (< (/ k f) k)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable dm::divides))))

(defthm divisor-num-powers
  (implies (and (natp k)
                (< 1 k)
                (natp f)
                (dm::divides f k))
           (dm::divides (expt f (number-of-powers k f)) k))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :induct (number-of-powers k f)
           :in-theory (enable dm::divides)
           )
          ))

(defthm number-of-powers-not-zero-when-divides
  (implies (and (natp k)
                (< 1 k)
                (natp f)
                (< 1 f)
                (dm::divides f k)
                )
           (< 0 (number-of-powers k f)))
  :rule-classes nil
  :hints (("Goal"
           :expand ((number-of-powers k f)))))

(defthm integerp-least-divisor
  (implies (and (integerp k)
                (integerp n)
                (< 1 k)
                (<= k n))
           (integerp (dm::least-divisor k n))))

(defthm expt-least-divisor-number-of-powers
  (implies (and (integerp k)
                (< 1 k))
           (< 1 (expt (dm::least-divisor 2 k)
                      (number-of-powers k (dm::least-divisor 2 k)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance dm::least-divisor-divides
                            (k 2)
                            (n k))
                 (:instance divisor-num-powers
                            (f (dm::least-divisor 2 k))
                            (k k))
                 (:instance number-of-powers-not-zero-when-divides
                            (k k)
                            (f (dm::least-divisor 2 k)))
                 ))))

(defun primitive-root-aux (k p)
  (declare (xargs :hints (("Goal"
                           :do-not-induct t
                           :use ((:instance divisor-num-powers
                                            (k k)
                                            (f (dm::least-divisor 2 k)))
                                 (:instance divisor-decreases-count
                                            (k k)
                                            (f (expt (dm::least-divisor 2 k)
                                                     (number-of-powers k
                                                                       (dm::least-divisor
                                                                        2 k)))))))
                          ("Subgoal 5"
                           :use ((:instance dm::least-divisor-divides
                                            (k 2)
                                            (n k))))
                          ("Subgoal 4"
                           :in-theory (enable dm::divides))
                          ("Subgoal 3"
                           :use ((:instance expt-least-divisor-number-of-powers))
                           )
                          ("Subgoal 2"
                           :use ((:instance dm::least-divisor-divides
                                            (k 2)
                                            (n k))
                                 (:instance
                                  number-of-powers-not-zero-when-divides
                                  (k k)
                                  (f (dm::least-divisor 2 k)))))
                          ("Subgoal 1"
                           :use ((:instance dm::least-divisor-divides
                                            (k 2)
                                            (n k))
                                 (:instance
                                  number-of-powers-not-zero-when-divides
                                  (k k)
                                  (f (dm::least-divisor 2 k)))))
                          )))
  (if (or (zp k) (= 1 k))
      1
    (let* ((q (dm::least-divisor 2 k))
           (n (number-of-powers k q))
           (k1 (/ k (expt q n))))
      (mul (witness-with-order-q^n q n p)
           (primitive-root-aux k1 p)
           p))))

(defund primitive-root (p)
  (primitive-root-aux (1- p) p))

(defthm fep-primitive-root-aux
  (implies (and (posp p)
                (<= 2 p)
                (natp k)
                (< k p))
           (fep (primitive-root-aux k p) p)))

(in-theory (disable witness-with-order-q^n))

(defthm fep-primite-root-non-zero
  (implies (and (dm::primep p)
                (natp k)
                (dm::divides k (1- p)))
           (not (= 0 (primitive-root-aux k p))))
  :rule-classes nil
 :INSTRUCTIONS
 ((:INDUCT (PRIMITIVE-ROOT-AUX K P))
  (:CHANGE-GOAL NIL T)
  :BASH :PROMOTE
  (:USE (:INSTANCE DM::PRIMEP-LEAST-DIVISOR (N K)))
  :PROMOTE (:FORWARDCHAIN 1)
  (:USE (:INSTANCE DIVISOR-NUM-POWERS (K K)
                   (F (DM::LEAST-DIVISOR 2 K))))
  :PRO (:FORWARDCHAIN 1)
  (:USE (:INSTANCE DM::DIVIDES-TRANSITIVE
                   (X (EXPT (DM::LEAST-DIVISOR 2 K)
                            (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))
                   (Y K)
                   (Z (1- P))))
  :PRO (:FORWARDCHAIN 1)
  (:USE (:INSTANCE ORDER-IS-PRIME-POWER (P P)
                   (Q (DM::LEAST-DIVISOR 2 K))
                   (N (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K)))))
  :PRO (:FORWARDCHAIN 1)
  (:USE (:INSTANCE
             DM::DIVIDES-TRANSITIVE
             (X (* K
                   (/ (EXPT (DM::LEAST-DIVISOR 2 K)
                            (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))))
             (Y K)
             (Z (1- P))))
  :PRO (:IN-THEORY (ENABLE DM::DIVIDES))
  (:FORWARDCHAIN 1)
  (:FORWARDCHAIN 2)
  (:IN-THEORY (DISABLE DM::DIVIDES))
  (:DV 1)
  (:DV 2)
  :X :TOP
  (:USE
   (:INSTANCE
     FEP-EUCLIDEAN
     (A (WITNESS-WITH-ORDER-Q^N (DM::LEAST-DIVISOR 2 K)
                                (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))
                                P))
     (B (PRIMITIVE-ROOT-AUX
             (* K
                (EXPT (DM::LEAST-DIVISOR 2 K)
                      (- (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K)))))
             P))))
  :PRO (:DEMOTE 1)
  (:DV 1)
  (:DV 1)
  :TOP :PRO
  (:USE
      (:INSTANCE
           FEP-PRIMITIVE-ROOT-AUX (P P)
           (K (* K
                 (EXPT (DM::LEAST-DIVISOR 2 K)
                       (- (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))))))
  :PRO (:IN-THEORY (ENABLE DM::DIVIDES))
  (:DEMOTE 1)
  (:DV 1)
  (:DV 1)
  :S :TOP
  (:USE (:INSTANCE
             DM::DIVIDES-LEQ
             (X (* K
                   (/ (EXPT (DM::LEAST-DIVISOR 2 K)
                            (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))))
             (Y (1- P))))
  :PROMOTE (:FORWARDCHAIN 1)
  (:DV 1)
  (:DV 1)
  (:DV 2)
  (:= T)
  :UP
  :S (:IN-THEORY (ENABLE DM::DIVIDES))
  (:= T)
  (:IN-THEORY (DISABLE DM::DIVIDES))
  :UP :S :UP :PRO (:FORWARDCHAIN 13)
  :S))

  ;; :hints (("Goal"
  ;;          :do-not-induct t
  ;;          :induct (primitive-root-aux k p))
  ;;         ("Subgoal *1/2"
  ;;          :in-theory (enable dm::divides)
  ;;          :use ((:instance order-is-prime-power
  ;;                           (p p)
  ;;                           (q (dm::least-divisor 2 k))
  ;;                           (n (number-of-powers k (dm::least-divisor 2 k))))
  ;;                (:instance dm::primep-least-divisor (n k))
  ;;                (:instance divisor-num-powers
  ;;                           (k k)
  ;;                           (f (dm::least-divisor 2 k)))
  ;;                ;; (:instance dm::divides-transitive
  ;;                ;;            (x (expt (dm::least-divisor 2 k)
  ;;                ;;                     (number-of-powers k (dm::least-divisor 2 k))))
  ;;                ;;            (y k)
  ;;                ;;            (z (1- p)))
  ;;                (:instance dm::divides-transitive
  ;;                           (x (* K
  ;;                                 (/ (EXPT (DM::LEAST-DIVISOR 2 K)
  ;;                                          (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))))
  ;;                           (y k)
  ;;                           (z (1- p)))
  ;;                (:instance fep-euclidean
  ;;                           (a (witness-with-order-q^n (dm::least-divisor 2 k)
  ;;                                                      (number-of-powers k (dm::least-divisor 2 k))
  ;;                                                      p))
  ;;                           (b (primitive-root-aux
  ;;                               (* k
  ;;                                  (expt (dm::least-divisor 2 k)
  ;;                                        (- (number-of-powers k (dm::least-divisor 2 k)))))
  ;;                               p)))
  ;;                (:instance fep-primitive-root-aux
  ;;                           (p p)
  ;;                           (k (* k
  ;;                                 (expt (dm::least-divisor 2 k)
  ;;                                       (- (number-of-powers k
  ;;                                                            (dm::least-divisor 2 k)))))))
  ;;                (:instance dm::divides-leq
  ;;                           (x (* k
  ;;                                 (/ (expt (dm::least-divisor 2 k)
  ;;                                          (number-of-powers k
  ;;                                                            (dm::least-divisor 2 k))))))
  ;;                           (y (1- p)))
  ;;                )
  ;;          )
  ;;         )
  ;; )



;;; Todo

;;; Variables from definition of primitive-root:

;;; 0) q is prime
;;; 1) show that gcd(q^n, k1) = 1
;;; 2) show that if k|p-1, then k1|p-1

;;; The recursion will show that
;;; k|p-1 ==> primitive-root has order k

(defthm prime-does-not-divide-x/p^n
  (implies (and (dm::primep p)
                (posp k)
                )
           (not (dm::divides p (/ k (expt p (number-of-powers k p))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable dm::divides))
          ("Subgoal *1/4"
           :use (:instance
                 (:theorem (implies (and (= x 1) (posp p) (< 1 p))
                                    (not (integerp (* x (/ p))))))
                 (x (* k (/ p)))
                 (p p)))
          )
  )

(defthm prime-divides-non-trivial-divisor-of-prime-power
  (implies (and (dm::primep p)
                (natp x)
                (< 1 x)
                (natp n)
                (dm::divides x (expt p n)))
           (dm::divides p x))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance factors-of-prime-powers)
                 )))
  )

(defthm prime-divides-divisor-of-prime-powers
  (implies (and (dm::primep p)
                (posp x)
                (posp n)
                (dm::divides x (expt p n)))
           (or (= 1 x)
               (dm::divides p x)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance factors-of-prime-powers)))))

(defthm gcd-after-dividing-by-prime-power
  (implies (and (dm::primep p)
                (posp k)
                (< 1 k)
                )
           (= (dm::gcd (expt (dm::least-divisor 2 k)
                                (number-of-powers k (dm::least-divisor 2 k)))
                          (/ k (expt (dm::least-divisor 2 k)
                                     (number-of-powers k (dm::least-divisor 2
                                                                             k)))))
              1))
  :rule-classes nil
  :INSTRUCTIONS
  (:PROMOTE
   (:USE
    (:INSTANCE DM::GCD-DIVIDES
               (X (EXPT (DM::LEAST-DIVISOR 2 K)
                        (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))
               (Y (/ K
                     (EXPT (DM::LEAST-DIVISOR 2 K)
                           (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K)))))))
   :PROMOTE
   (:USE (:INSTANCE DM::PRIMEP-LEAST-DIVISOR (N K)))
   :PROMOTE (:FORWARDCHAIN 1)
   (:USE (:INSTANCE PRIME-DOES-NOT-DIVIDE-X/P^N
                    (P (DM::LEAST-DIVISOR 2 K))
                    (K K)))
   :PROMOTE (:FORWARDCHAIN 1)
   (:USE (:INSTANCE DIVISOR-NUM-POWERS (K K)
                    (F (DM::LEAST-DIVISOR 2 K))))
   :PROMOTE
   (:USE (:INSTANCE DM::LEAST-DIVISOR-DIVIDES (K 2)
                    (N K)))
   :PROMOTE (:FORWARDCHAIN 1)
   (:FORWARDCHAIN 1)
   (:IN-THEORY (ENABLE DM::DIVIDES))
   (:FORWARDCHAIN 1)
   (:IN-THEORY (DISABLE DM::DIVIDES))
   (:DEMOTE 8)
   (:DV 1)
   :S :TOP :PROMOTE
   (:USE
    (:INSTANCE
     PRIME-DIVIDES-DIVISOR-OF-PRIME-POWERS
     (P (DM::LEAST-DIVISOR 2 K))
     (X (DM::GCD
         (EXPT (DM::LEAST-DIVISOR 2 K)
               (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K)))
         (* K
            (EXPT (DM::LEAST-DIVISOR 2 K)
                  (- (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K)))))))
     (N (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K)))))
   :PROMOTE
   (:USE
    (:INSTANCE
     DM::GCD-POS
     (X (EXPT (DM::LEAST-DIVISOR 2 K)
              (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))
     (Y (* K
           (/ (EXPT (DM::LEAST-DIVISOR 2 K)
                    (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))))))
   :PROMOTE (:DEMOTE 1)
   (:DV 1)
   (:DV 1)
   :S (:IN-THEORY (ENABLE DM::DIVIDES))
   (:= T)
   (:IN-THEORY (DISABLE DM::DIVIDES))
   :UP :S :TOP :PROMOTE (:FORWARDCHAIN 1)
   (:USE
    (:INSTANCE
     DM::DIVIDES-TRANSITIVE
     (X (DM::LEAST-DIVISOR 2 K))
     (Y (DM::GCD
         (EXPT (DM::LEAST-DIVISOR 2 K)
               (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K)))
         (* K
            (EXPT (DM::LEAST-DIVISOR 2 K)
                  (- (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K)))))))
     (Z (* K
           (EXPT (DM::LEAST-DIVISOR 2 K)
                 (- (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))))))
   :BASH))
  ;; :hints (("Goal"
  ;;          :do-not-induct t
  ;;          :in-theory (e/d (dm::divides)
  ;;                          (acl2::|(/ (expt x n))|
  ;;                           ))
  ;;          :use ((:instance dm::primep-least-divisor
  ;;                           (n k))
  ;;                (:instance dm::gcd-divides
  ;;                           (x (expt (dm::least-divisor 2 k)
  ;;                                    (number-of-powers k (dm::least-divisor 2
  ;;                                                                            k))))
  ;;                           (y (/ k (expt (dm::least-divisor 2 k)
  ;;                                         (number-of-powers k (dm::least-divisor 2
  ;;                                                                                 k))))))
  ;;                (:instance prime-does-not-divide-x/p^n
  ;;                           (p (dm::least-divisor 2 k))
  ;;                           (k k))
  ;;                (:instance prime-divides-non-trivial-divisor-of-prime-power
  ;;                           (p (dm::least-divisor 2 k))
  ;;                           (x (dm::gcd (expt (dm::least-divisor 2 k)
  ;;                                                (number-of-powers k (dm::least-divisor 2 k)))
  ;;                                          (/ k (expt (dm::least-divisor 2 k)
  ;;                                                     (number-of-powers
  ;;                                                      k
  ;;                                                      (dm::least-divisor 2
  ;;                                                                          k)))))))
  ;;                (:instance dm::least-divisor-divides
  ;;                           (k 2)
  ;;                           (n k))
  ;;                (:instance divisor-num-powers
  ;;                           (k k)
  ;;                           (f (dm::least-divisor 2 k)))
  ;;                (:instance prime-divides-divisor-of-prime-powers
  ;;                           (p (dm::least-divisor 2 k))
  ;;                           (x (dm::gcd (expt (dm::least-divisor 2 k)
  ;;                                                (number-of-powers k (dm::least-divisor 2 k)))
  ;;                                          (* k
  ;;                                             (expt (dm::least-divisor 2 k)
  ;;                                                   (- (number-of-powers k
  ;;                                                                        (dm::least-divisor 2 k)))))))
  ;;                           (n (number-of-powers k (dm::least-divisor 2 k))))
  ;;                (:instance dm::gcd-pos
  ;;                           (x 1)
  ;;                           (y k))
  ;;                (:instance dm::gcd-pos
  ;;                           (x (expt (dm::least-divisor 2 k)
  ;;                                    (number-of-powers k (dm::least-divisor 2 k))))
  ;;                           (y (* k
  ;;                                 (/ (expt (dm::least-divisor 2 k)
  ;;                                          (number-of-powers k
  ;;                                                            (dm::least-divisor 2 k)))))))
  ;;                (:instance dm::divides-transitive
  ;;                           (x (dm::least-divisor 2 k))
  ;;                           (y (dm::gcd
  ;;                               (expt (dm::least-divisor 2 k)
  ;;                                     (number-of-powers k (dm::least-divisor 2 k)))
  ;;                               (* k
  ;;                                  (expt (dm::least-divisor 2 k)
  ;;                                        (- (number-of-powers k
  ;;                                                             (dm::least-divisor 2 k)))))))
  ;;                           (z (* k
  ;;                                 (expt (dm::least-divisor 2 k)
  ;;                                       (- (number-of-powers k (dm::least-divisor 2 k)))))))
  ;;                ))))



(defthm new-divisor-still-divides
  (implies (and (dm::primep p)
                (posp k)
                (< 1 k)
                (dm::divides k (1- p))
                )
           (dm::divides (/ k (expt (dm::least-divisor 2 k)
                                    (number-of-powers k (dm::least-divisor 2
                                                                            k))))
                         (1- p)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance dm::divides-transitive
                            (x (/ k (expt (dm::least-divisor 2 k)
                                    (number-of-powers k (dm::least-divisor 2
                                                                            k)))))
                            (y k)
                            (z (1- p)))
                 )
           :in-theory (enable dm::divides)
           )))

(defthm primes-have-primitive-roots-aux
  (Implies (and (dm::primep p)
                (natp k)
                (dm::divides k (1- p)))
           (equal (order (primitive-root-aux k p) p)
                  k))
  :rule-classes nil
 :INSTRUCTIONS
 ((:INDUCT (PRIMITIVE-ROOT-AUX K P))
  (:CHANGE-GOAL NIL T)
  :BASH (:DV 1)
  :X :PROMOTE
  (:USE (:INSTANCE (:INSTANCE DIVISOR-NUM-POWERS (K K)
                              (F (DM::LEAST-DIVISOR 2 K)))))
  (:USE (:INSTANCE DM::LEAST-DIVISOR-DIVIDES (K 2)
                   (N K)))
  :PRO (:FORWARDCHAIN 1)
  (:FORWARDCHAIN 1)
  (:USE (:INSTANCE NEW-DIVISOR-STILL-DIVIDES))
  :PRO (:FORWARDCHAIN 1)
  (:IN-THEORY (ENABLE DM::DIVIDES))
  (:FORWARDCHAIN 2)
  (:IN-THEORY (DISABLE DM::DIVIDES))
  (:DV 1)
  (:DV 1)
  :X :TOP
  (:USE (:INSTANCE ORDER-IS-PRIME-POWER
                   (Q (DM::LEAST-DIVISOR 2 K))
                   (N (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K)))
                   (P P)))
  :PRO
  (:USE (:INSTANCE DM::PRIMEP-LEAST-DIVISOR (N K)))
  :PROMOTE (:FORWARDCHAIN 1)
  (:USE (:INSTANCE DM::DIVIDES-TRANSITIVE
                   (X (EXPT (DM::LEAST-DIVISOR 2 K)
                            (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))
                   (Y K)
                   (Z (1- P))))
  :PROMOTE (:FORWARDCHAIN 1)
  (:FORWARDCHAIN 1)
  (:USE
   (:INSTANCE
     CONSTRUCT-PRODUCT-ORDER (P P)
     (A (WITNESS-WITH-ORDER-Q^N (DM::LEAST-DIVISOR 2 K)
                                (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))
                                P))
     (B (PRIMITIVE-ROOT-AUX
             (* K
                (EXPT (DM::LEAST-DIVISOR 2 K)
                      (- (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K)))))
             P))))
  :PROMOTE
  (:USE
      (:INSTANCE
           FEP-PRIMITIVE-ROOT-AUX (P P)
           (K (* K
                 (EXPT (DM::LEAST-DIVISOR 2 K)
                       (- (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))))))
  :PROMOTE (:DEMOTE 1)
  (:DV 1)
  (:DV 1)
  :S :TOP
  (:USE (:INSTANCE
             DM::DIVIDES-LEQ
             (X (* K
                   (EXPT (DM::LEAST-DIVISOR 2 K)
                         (- (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))))
             (Y (1- P))))
  :PROMOTE (:FORWARDCHAIN 1)
  (:IN-THEORY (ENABLE DM::DIVIDES))
  (:DV 1)
  (:DV 1)
  (:= T)
  :UP :S :TOP :PROMOTE
  (:USE
      (:INSTANCE
           FEP-PRIMITE-ROOT-NON-ZERO (P P)
           (K (* K
                 (EXPT (DM::LEAST-DIVISOR 2 K)
                       (- (NUMBER-OF-POWERS K (DM::LEAST-DIVISOR 2 K))))))))
  :PROMOTE (:FORWARDCHAIN 1)
  (:USE (:INSTANCE GCD-AFTER-DIVIDING-BY-PRIME-POWER))
  :PROMOTE (:FORWARDCHAIN 1)
  (:IN-THEORY (ENABLE RELATIVELY-PRIMEP))
  (:FORWARDCHAIN 1)
  :BASH))


(defthm primes-have-primitive-roots
  (implies (dm::primep p)
           (equal (order (primitive-root p) p)
                  (1- p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance primes-have-primitive-roots-aux
                            (k (1- p))
                            (p p))
                 )
           :in-theory (enable primitive-root)
           )))
