(in-package "DM")

(include-book "euclid")
(include-book "arithmetic-5/top" :dir :system)

(local (in-theory (enable divides)))

;; If x is relatively prime to both y and z, then x is relatively prime to (* y z).

(defthmd rel-prime-prod
  (implies (and (integerp x) (not (= x 0))
		(integerp y) (not (= y 0))
		(integerp z) (not (= z 0))
		(= (gcd x y) 1)
		(= (gcd x z) 1))
	   (equal (gcd x (* y z)) 1))
  :hints (("Goal" :use ((:instance primep-least-divisor (n (gcd x (* y z))))
                        (:instance least-divisor-divides (k 2) (n (gcd x (* y z))))
			(:instance gcd-divides (y (* y z)))
			(:instance gcd-pos (y (* y z)))
			(:instance divides-transitive (x (least-prime-divisor (gcd x (* y z)))) (y (gcd x (* y z))) (z x))
			(:instance divides-transitive (x (least-prime-divisor (gcd x (* y z)))) (y (gcd x (* y z))) (z (* y z)))
			(:instance euclid (p (least-prime-divisor (gcd x (* y z)))) (a y) (b z))
			(:instance divides-gcd (d (least-prime-divisor (gcd x (* y z)))))
			(:instance divides-gcd (d (least-prime-divisor (gcd x (* y z)))) (y z))))))

(defun rel-prime-all (x l)
  (if (consp l)
      (and (equal (gcd x (car l)) 1)
	   (rel-prime-all x (cdr l)))
    t))

(defun rel-prime-moduli (l)
  (if (consp l)
      (and (integerp (car l))
	   (>= (car l) 2)
	   (rel-prime-all (car l) (cdr l))
	   (rel-prime-moduli (cdr l)))
    (null l)))

(defun congruent-all (x a m)
  (declare (xargs :measure (acl2-count m)))
  (if (consp m)
      (and (equal (mod x (car m)) (mod (car a) (car m)))
	   (congruent-all x (cdr a) (cdr m)))
    t))

(defun int-list-p (l)
  (if (consp l)
      (and (integerp (car l))
	   (int-list-p (cdr l)))
    t))

(defun prod-list (l)
  (if (consp l)
      (* (car l) (prod-list (cdr l)))
    1))

(defund one-mod (x l) (* (s x (prod-list l)) (prod-list l)))

(defun crt1 (a m l)
  (if (consp a)
      (+ (* (car a) (one-mod (car m) (remove1-equal (car m) l)))
         (crt1 (cdr a) (cdr m) l))
    0))

(defund crt (a m) (crt1 a m m))

(local-defthmd pos-prod-list-rel-prime-moduli
  (implies (rel-prime-moduli l)
           (posp (prod-list l))))

(local-defthmd rel-prime-prod-list
  (implies (and (integerp x)
                (not (= x 0))
		(rel-prime-moduli l)
		(rel-prime-all x l))
	   (equal (gcd x (prod-list l)) 1))
  :hints (("Subgoal *1/5" :use ((:instance gcd-divides (y 1)) (:instance gcd-pos (y 1))))
          ("Subgoal *1/3" :use ((:instance pos-prod-list-rel-prime-moduli (l (cdr l)))
	                        (:instance rel-prime-prod (y (car l)) (z (prod-list (cdr l))))))))

(local-defthmd lin-comb-x-l
  (implies (and (integerp x)
                (not (= x 0))
		(rel-prime-moduli l)
		(rel-prime-all x l))
	   (and (integerp (r x (prod-list l)))
	        (integerp (s x (prod-list l)))
		(equal (+ (* (r x (prod-list l)) x)
		          (* (s x (prod-list l)) (prod-list l)))
		       1)))
  :hints (("Goal" :use (rel-prime-prod-list
		        (:instance gcd-linear-combination (y (prod-list l)))))))

(local-defthmd one-mod-rewrite-1
  (implies (and (integerp x)
                (not (= x 0))
		(rel-prime-moduli l)
		(rel-prime-all x l))
           (equal (one-mod x l)
	          (- 1 (* (r x (prod-list l)) x))))
  :hints (("Goal" :in-theory (enable one-mod)
                  :use (lin-comb-x-l))))

(local-defthmd mod-one-mod-1
  (implies (and (integerp x)
                (> x 1)
	        (rel-prime-moduli l)
	        (rel-prime-all x l))
	   (equal (mod (one-mod x l) x) 1))
  :hints (("Goal" :in-theory (enable one-mod-rewrite-1)
                  :use ((:instance rtl::mod-mult (acl2::m 1) (acl2::a (- (r x (prod-list l)))) (acl2::n x))))))

(local-defthmd prod-factor
  (implies (and (rel-prime-moduli l)
                (member m l))
	   (equal (prod-list l)
	          (* m (prod-list (remove1-equal m l))))))

(local-defthmd one-mod-rewrite-2
  (implies (and (integerp x)
                (not (= x 0))
		(rel-prime-moduli l)
		(rel-prime-all x l)
		(member m l))
	   (equal (one-mod x l)
	          (* (s x (prod-list l)) (prod-list (remove1-equal m l)) m)))
  :hints (("Goal" :in-theory (enable one-mod)
                  :use (prod-factor))))

(local-defthmd int-prod-list
    (implies (rel-prime-moduli l)
	     (integerp (prod-list (remove1-equal m l)))))

(local-defthmd mod-one-mod-0
  (implies (and (natp x)
		(> x 1)
		(rel-prime-moduli l)
		(rel-prime-all x l)
		(member m l))
	   (equal (mod (one-mod x l) m) 0))
  :hints (("Goal" :in-theory (enable one-mod-rewrite-2)
                  :use (int-prod-list
		        (:instance rtl::mod-mult (acl2::m 0)
			                         (acl2::a (* (s x (prod-list l)) (prod-list (remove1-equal m l))))
						 (acl2::n m))))))

(local-defthm modulus-pos
    (implies (and (rel-prime-moduli l)
		  (member x l))
	     (and (integerp x)
		  (> x 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rel-prime-moduli))))

(local-defthm rel-prime-all-remove
    (implies (rel-prime-all m l)
	     (rel-prime-all m (remove1-equal x l)))
  :hints (("Goal" :in-theory (enable rel-prime-all))))

(local-defthm rel-prime-remove
    (implies (rel-prime-moduli l)
	     (rel-prime-moduli (remove1-equal x l))))

(local-defthm member-remove
  (implies (and (member x l)
		(not (equal x y)))
	   (member x (remove1-equal y l))))

(local-defun sublistp (m l)
  (if (consp m)
      (and (member-equal (car m) l)
	   (sublistp (cdr m) l))
    t))

(local-defthm member-sublistp
  (implies (and (sublistp m l)
		(member x m))
	   (member x l)))

(local-defthmd rel-prime-all-rel-prime
    (implies (and (rel-prime-all x l)
		  (member-equal y l))
	     (equal (gcd x y) 1)))

(local-defthm rel-prime-all-moduli-remove
    (implies (and (rel-prime-moduli l)
		  (member x l))
	     (rel-prime-all x (remove1-equal x l)))
  :hints (("Subgoal *1/5''" :use ((:instance rel-prime-all-rel-prime
					     (x (car l))
					     (l (cdr l))
					     (y x))
				  (:instance gcd-commutative (y (car l)))))))

(local-defthmd mod0+0
    (implies (and (integerp a)
		  (integerp b)
		  (integerp c)
		  (integerp n)
		  (> n 0)
		  (= (mod a n) 0)
		  (= (mod c n) 0))
	     (equal (mod (+ (* a b) c) n) 0))
  :hints (("Goal" :use ((:instance rtl::mod-mod-times (acl2::a a) (acl2::b b) (acl2::n n))
			(:instance rtl::mod-sum (acl2::a c) (acl2::b (* a b)) (acl2::n n))))))

(local-defthm int-one-mod
  (implies (and (rel-prime-moduli l) (member-equal m l))
           (integerp (one-mod m (remove1-equal m l))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable one-mod)
                  :use (int-prod-list))))

(local-defthmd mod-crt1
  (implies (and (int-list-p a)
		(rel-prime-moduli m)
		(= (len a) (len m))
		(rel-prime-moduli l)
		(sublistp m l)
		(member x l)
		(not (member x m)))
	   (equal (mod (crt1 a m l) x) 0))
  :hints (("Subgoal *1/1" :use (modulus-pos))  
	  ("Subgoal *1/3" :use (modulus-pos
	                        (:instance mod0+0
					   (n x)
					   (a (one-mod (car m) (remove1-equal (car m) l)))
					   (b (car a))
					   (c (crt1 (cdr a) (cdr m) l)))
				(:instance mod-one-mod-0
					   (x (car m))
					   (m x)
					   (l (remove1-equal (car m) l)))))))

(local-defthmd mod0+1
    (implies (and (integerp a)
		  (integerp b)
		  (integerp c)
		  (integerp n)
		  (> n 0)
		  (= (mod b n) 1)
		  (= (mod c n) 0))
	     (= (mod (+ (* a b) c) n) (mod a n)))
  :hints (("Goal" :use ((:instance rtl::mod-mod-times (acl2::a a) (acl2::b b) (acl2::n n))
			(:instance rtl::mod-sum (acl2::a c) (acl2::b (* a b)) (acl2::n n))))))

(local-defthmd gcd-self
  (implies (posp x)
           (equal (gcd x x) x))
  :hints (("Goal" :in-theory (enable gcd)
                  :expand ((gcd-nat x x)))))

(local-defthm not-member-rel-prime-all
    (implies (and (natp x)
		  (> x 1)
		  (rel-prime-all x m))
	     (not (member x m)))	     
  :hints (("Subgoal *1/2" :expand ((REL-PRIME-ALL (CAR M) M))
                          :use ((:instance gcd-self (x (car m)))))))

(local-defun cong0-all (x l)
  (if (consp l)
      (and (= (mod x (car l)) 0)
	   (cong0-all x (cdr l)))
    t))

(local-defthmd cong0-1
    (implies (and (integerp a)
		  (integerp m)
		  (> m 1)
		  (sublistp l1 l)
		  (rel-prime-all m l1)
		  (rel-prime-moduli l1)
		  (rel-prime-all m l)
		  (rel-prime-moduli l))
	     (cong0-all (* a (one-mod m l)) l1))
  :hints (("Subgoal *1/5" :use ((:instance mod-one-mod-0 (x m) (m (car l1)))
				;(:instance one-mod-nat (x m))
				(:instance mod0+0 (c 0) (a (one-mod m l)) (b a) (n (car l1)))))))

(local-defthm sublistp-cons
  (implies (sublistp l m)
           (sublistp l (cons x m))))

(local-defthm sublistp-self
  (sublistp l l))

(local-defthm sublistp-remove
    (implies (and (sublistp m l)
		  (not (member x m)))
	     (sublistp m (remove1-equal x l))))
	     
(local-defun dlistp (l)
  (if (consp l)
      (and (not (member-equal (car l) (cdr l)))
	   (dlistp (cdr l)))
    (null l)))

(local-defthm sublistp-cdr-remove
    (implies (and (sublistp m l)
		  (dlistp m)
		  (consp m))
	     (sublistp (cdr m) (remove1-equal (car m) l))))

(local-defthmd rel-prime-sublist
    (implies (and (rel-prime-all x l)
		  (sublistp m l))
	     (rel-prime-all x m)))

(local-defthmd rel-prime-moduli-sublist
    (implies (and (rel-prime-moduli l)
		  (dlistp m)
		  (sublistp m l))
	     (rel-prime-moduli m))
  :hints (("Subgoal *1/6" :use ((:instance modulus-pos (x (car m)))))
	  ("Subgoal *1/5" :use ((:instance modulus-pos (x (car m)))))
	  ("Subgoal *1/4" :use ((:instance rel-prime-sublist (x (car m)) (m (cdr m)) (l (remove1-equal (car m) l)))))))

(local-defthm cong0-2
    (implies (and (integerp a)
		  (sublistp m l)
		  (dlistp m)
		  (rel-prime-moduli l))
	     (cong0-all (* a (one-mod (car m) (remove1-equal (car m) l))) (cdr m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance cong0-1 (m (car m)) (l (remove1-equal (car m) l)) (l1 (cdr m)))
			(:instance rel-prime-all-moduli-remove (x (car m)))
			(:instance rel-prime-moduli-sublist)
			(:instance modulus-pos (x (car m)))))))

(local-defthmd cong0-3
    (implies (and (rel-prime-moduli m)
		  (integerp x)
		  (integerp y)
		  (int-list-p a)
		  (cong0-all x m)
		  (= (len a) (len m))
		  (congruent-all y a m))
	     (congruent-all (+ x y) a m)))

(local-defthmd integerp-crt1
    (implies (and (int-list-p a)
		  (rel-prime-moduli m)
		  (= (len a) (len m))
		  (rel-prime-moduli l)
		  (dlistp m)
		  (sublistp m l))
	     (integerp (crt1 a m l))))

(local-defthmd crt1-lemma
    (implies (and (int-list-p a)
		  (rel-prime-moduli m)
		  (dlistp m)
		  (= (len a) (len m))
		  (rel-prime-moduli l)
		  (sublistp m l))
	     (congruent-all (crt1 a m l) a m))	     
  :hints (("Subgoal *1/7" :use ((:instance mod0+1
					   (a (car a))
					   (n (car m))
					   (b (one-mod (car m) (remove1-equal (car m) l)))
					   (c (crt1 (cdr a) (cdr m) l)))
				(:instance mod-one-mod-1
					   (x (car m))
					   (l (remove1-equal (car m) l)))
				(:instance mod-crt1
					   (a (cdr a))
					   (m (cdr m))
					   (x (car m)))))
	  ("subgoal *1/6" :use ((:instance integerp-crt1 (a (cdr a)) (m (cdr m)))
				(:instance cong0-2 (a (car a)))
				(:instance cong0-3
					   (y (crt1 (cdr a) (cdr m) l))
					   (a (cdr a))
					   (m (cdr m))
					   (x (* (car a) (one-mod (car m) (remove1-equal (car m) l)))))))))

(local-defthm dlistp-rel-prime-moduli
    (implies (rel-prime-moduli m)
	     (dlistp m)))

(local-defthmd crt1-thm
    (implies (and (int-list-p a)
		  (rel-prime-moduli m)
		  (= (len a) (len m))
		  (rel-prime-moduli l)
		  (sublistp m l))
	     (congruent-all (crt1 a m l) a m))
  :hints (("Goal" :in-theory (disable dlistp)
                  :use (crt1-lemma))))

(defthmd chinese-remainder-theorem
    (implies (and (int-list-p a)
		  (rel-prime-moduli m)
		  (= (len a) (len m)))
	     (and (integerp (crt a m))
		  (congruent-all (crt a m) a m)))
  :hints (("Goal" :in-theory (enable crt)
		  :use ((:instance integerp-crt1 (l m))
			(:instance crt1-thm (l m))))))

