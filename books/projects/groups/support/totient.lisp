(in-package "DM")

(include-book "products")

;; Euler's totient function:

(defun totient-comp (l)
  (if (consp l)
      (* (expt (caar l) (1- (cdar l)))
	 (1- (caar l))
	 (totient-comp (cdr l)))
    1))

(defund totient (n) (totient-comp (prime-fact n)))

;; We shall prove Euler's Theorem:

;; (defthmd euler-totient
;;   (implies (and (posp n) (> n 1)
;;                 (posp x) (< x n)
;; 		   (equal (gcd x n) 1))
;;            (equal (mod (expt x (totient n)) n)
;;                   1)))

;; Note that if n is prime, then (totient n) = p - 1.  Thus, Euler's Theorem is a
;; generalization of Fermat's Theorem:

;; (defthm fermat
;;   (implies (and (primep p)
;;		  (integerp m)
;;		  (not (divides p m)))
;;	     (equal (mod (expt m (1- p)) p)
;;		    1)))

;; Our strategy is to prove that (totient n) = (order (z* n)) and invoke power-order.
;; We begin by defining a homomorphism from (z* (* m n)) to (direct-product (list (z* m) (z* n))):

(defmap mod-map (m n) (ninit (* m n))
  (list (mod x m) (mod x n)))

(local-defthm mod-map-range
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(in x (z* (* m n))))
           (in (mapply (mod-map m n) x)
	       (direct-product (list (z* m) (z* n)))))
  :hints (("Goal" :in-theory (enable member-ninit member-rel-primes member-group-tuples)
                  :use ((:instance divides-gcd (d n) (y (* m n)))
                        (:instance divides-gcd (d m) (y (* m n)))))
	  ("Subgoal 2" :use ((:instance primep-least-divisor (n (gcd (mod x m) m)))
			     (:instance least-divisor-divides (k 2) (n (gcd (mod x m) m)))
			     (:instance gcd-pos (x (mod x m)) (y m))
			     (:instance gcd-divides (x (mod x m)) (y m))
			     (:instance divides-transitive (x (least-prime-divisor (gcd (mod x m) m))) (y (gcd (mod x m) m)) (z (mod x m)))
			     (:instance divides-transitive (x (least-prime-divisor (gcd (mod x m) m))) (y (gcd (mod x m) m)) (z m))
			     (:instance divides-gcd (d (least-prime-divisor (gcd (mod x m) m))) (y (* m n)))))
	  ("Subgoal 1" :use ((:instance primep-least-divisor (n (gcd (mod x n) n)))
			     (:instance least-divisor-divides (k 2) (n (gcd (mod x n) n)))
			     (:instance gcd-pos (x (mod x n)) (y n))
			     (:instance gcd-divides (x (mod x n)) (y n))
			     (:instance divides-transitive (x (least-prime-divisor (gcd (mod x n) n))) (y (gcd (mod x n) n)) (z (mod x n)))
			     (:instance divides-transitive (x (least-prime-divisor (gcd (mod x n) n))) (y (gcd (mod x n) n)) (z n))
			     (:instance divides-gcd (d (least-prime-divisor (gcd (mod x n) n))) (y (* m n)))))))

(local-defthm mod-map-codomain-cex
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1))
	   (not (codomain-cex (mod-map m n)
	                      (z* (* m n))
			      (direct-product (list (z* m) (z* n))))))
  :hints (("Goal" :use ((:instance codomain-cex-lemma (map (mod-map m n)) (g (z* (* m n))) (h (direct-product (list (z* m) (z* n)))))
                        (:instance mod-map-range (x (codomain-cex (mod-map m n) (z* (* m n)) (direct-product (list (z* m) (z* n))))))))))

(defthmd gcd-mod
  (implies (and (posp n) (integerp x) (= (gcd x n) 1))
           (equal (gcd (mod x n) n) 1))
  :hints (("Goal" :use ((:instance gcd-pos (x (mod x n)) (y n))
                        (:instance primep-least-divisor (n (gcd (mod x n) n)))
			(:instance least-divisor-divides (k 2) (n (gcd (mod x n) n)))
			(:instance gcd-divides (x (mod x n)) (y n))
			(:instance divides-gcd (d (least-prime-divisor (gcd (mod x n) n))) (y n))
			(:instance divides-transitive (x (least-prime-divisor (gcd (mod x n) n))) (y (gcd (mod x n) n)) (z n))
			(:instance divides-transitive (x (least-prime-divisor (gcd (mod x n) n))) (y (gcd (mod x n) n)) (z (mod x n)))
			(:instance rtl::mod-def (acl2::y n))))))

(defthmd rel-prime-mod
  (implies (and (posp n) (> n 1) (integerp x) (= (gcd x n) 1))
           (in (mod x n) (z* n)))
  :hints (("Goal" :in-theory (enable gcd gcd-nat member-ninit member-rel-primes)
                  :use (gcd-mod)
		  :expand ((gcd 0 n)))))

(local-defthmd mod-map-times
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
                (in x (z* (* m n)))
                (in y (z* (* m n))))
           (equal (mapply (mod-map m n) (op x y (z* (* m n))))
	          (dp-op (mapply (mod-map m n) x)
		         (mapply (mod-map m n) y)
			 (list (z* m) (z* n)))))
  :hints (("Goal" :in-theory (enable z*-op member-ninit member-rel-primes member-group-tuples))
          ("Subgoal 2" :use ((:instance rel-prime-mod (n m))
		             (:instance rel-prime-mod (x y) (n m))
			     (:instance gcd-divisor (d m) (y (* m n)))
		   	     (:instance gcd-divisor (d m) (x y) (y (* m n)))
			     (:instance rtl::mod-of-mod (acl2::k n) (acl2::n m))
			     (:instance rtl::mod-of-mod (acl2::k n) (acl2::n m) (x y))
			     (:instance rtl::mod-of-mod (acl2::k n) (acl2::n m) (x (* x y)))
			     ;(:instance rtl::mod-mod-times (acl2::a x) (acl2::b y))
			     ;(:instance rtl::mod-mod-times (acl2::a y) (acl2::b x))
			     (:instance rtl::mod-mod-times (acl2::a x) (acl2::b y) (acl2::n m))
			     (:instance rtl::mod-mod-times (acl2::a y) (acl2::b x) (acl2::n m))))
          ("Subgoal 1" :use ((:instance rel-prime-mod)
		             (:instance rel-prime-mod (x y))
			     (:instance gcd-divisor (d n) (y (* m n)))
		   	     (:instance gcd-divisor (d n) (x y) (y (* m n)))
			     (:instance rtl::mod-of-mod (acl2::k m) (acl2::n n))
			     (:instance rtl::mod-of-mod (acl2::k m) (acl2::n n) (x y))
			     (:instance rtl::mod-of-mod (acl2::k m) (acl2::n n) (x (* x y)))
			     (:instance rtl::mod-mod-times (acl2::a x) (acl2::b y) (acl2::n n))
			     (:instance rtl::mod-mod-times (acl2::a y) (acl2::b x) (acl2::n n))))))

(local-defthmd mod-map-dp-op
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
                (in x (z* (* m n)))
                (in y (z* (* m n))))
           (equal (op (mapply (mod-map m n) x)
		      (mapply (mod-map m n) y)
		      (direct-product (list (z* m) (z* n))))
		  (dp-op (mapply (mod-map m n) x)
		         (mapply (mod-map m n) y)
			 (list (z* m) (z* n)))))
  :hints (("Goal" :use (mod-map-range (:instance mod-map-range (x y))))))
	          
(local-defthm mod-map-homomorphismp-cex
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1))
	   (not (homomorphism-cex (mod-map m n)
	                          (z* (* m n))
			          (direct-product (list (z* m) (z* n))))))
  :hints (("Goal" :use ((:instance homomorphismp-cex-lemma (map (mod-map m n)) (g (z* (* m n))) (h (direct-product (list (z* m) (z* n)))))
                        (:instance mod-map-times (x (car (homomorphism-cex (mod-map m n) (z* (* m n)) (direct-product (list (z* m) (z* n))))))
			                         (y (cdr (homomorphism-cex (mod-map m n) (z* (* m n)) (direct-product (list (z* m) (z* n)))))))
                        (:instance mod-map-dp-op (x (car (homomorphism-cex (mod-map m n) (z* (* m n)) (direct-product (list (z* m) (z* n))))))
			                         (y (cdr (homomorphism-cex (mod-map m n) (z* (* m n)) (direct-product (list (z* m) (z* n)))))))))))

(local-defthm sublistp-rel-primes-ninit
  (implies (and (natp n) (> n 1) (sublistp l (rel-primes n)))
           (sublistp l (ninit n)))
  :hints (("Goal" :in-theory (e/d (member-ninit member-rel-primes) (ninit)))))

(local-defthmd member-1-ninit
  (implies (and (posp n) (> n 1))
           (member-equal 1 (ninit n))))

(local-defthmd mod-map-e
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1))
	   (equal (mapply (mod-map m n) (e (z* (* m n))))
	          (e (direct-product (list (z* m) (z* n))))))
  :hints (("Goal" :in-theory (enable e) :use ((:instance member-1-ninit (n (* m n)))))))

(defthm homomorphismp-z*mod
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1))
           (homomorphismp (mod-map m n)
	                  (z* (* m n))
			  (direct-product (list (z* m) (z* n)))))
  :hints (("Goal" :in-theory (enable homomorphismp)
                  :use (mod-map-e))))

(local-defthmd in-dp-z*
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1))
	   (iff (in x (direct-product (list (z* m) (z* n))))
	        (and (equal (list (car x) (cadr x)) x)
		     (in (car x) (z* m))
		     (in (cadr x) (z* n)))))
  :hints (("Goal" :in-theory (e/d (in-dp) (direct-product-elts)))))

(local-defthmd mod-map-preimage-1
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
		(in x (direct-product (list (z* m) (z* n)))))
	   (let ((c (crt x (list m n))))
	     (and (integerp c)
	          (equal (mod c m) (car x))
		  (equal (mod c n) (cadr x)))))
  :hints (("Goal" :use (in-dp-z*
                        (:instance member-rel-primes (k (car x)) (n m))
			(:instance member-rel-primes (k (cadr x)))
			(:instance chinese-remainder-theorem (m (list m n)) (a x))))))

(local-defthmd mod-map-preimage-2
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
		(in x (direct-product (list (z* m) (z* n)))))
	   (let ((c (mod (crt x (list m n)) (* m n))))
	     (and (natp c)
	          (< c (* m n))
	          (equal (mod c m) (car x))
		  (equal (mod c n) (cadr x)))))
  :hints (("Goal" :use (mod-map-preimage-1
                        (:instance rtl::mod-of-mod (x (crt x (list m n))) (acl2::k m) (acl2::n n))
			(:instance rtl::mod-of-mod (x (crt x (list m n))) (acl2::k n) (acl2::n m))))))

(local-defthmd mod-map-preimage-3
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
		(in x (direct-product (list (z* m) (z* n)))))
	   (not (equal (mod (crt x (list m n)) (* m n)) 0)))
  :hints (("Goal" :use (mod-map-preimage-2 in-dp-z*
                        (:instance member-rel-primes (k (car x)))
			(:instance member-rel-primes (k (cadr x)) (n m))))))

(local-defthmd mod-map-preimage-4
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
		(in x (direct-product (list (z* m) (z* n)))))
	   (let ((c (mod (crt x (list m n)) (* m n))))
	     (and (posp c)
	          (< c (* m n))
	          (equal (mapply (mod-map m n) c)
		         x))))
  :hints (("Goal" :use (in-dp-z* mod-map-preimage-2 mod-map-preimage-3
                        (:instance member-ninit (n (* m n)) (x (mod (crt x (list m n)) (* m n))))))))

(local-defthmd mod-map-preimage-5
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
		(in x (direct-product (list (z* m) (z* n)))))
	   (and (posp (car x)) (equal (gcd (car x) m) 1)
	        (posp (cadr x)) (equal (gcd (cadr x) n) 1)))
  :hints (("Goal" :use (in-dp-z*
                        (:instance member-rel-primes (k (cadr x)))
			(:instance member-rel-primes (k (car x)) (n m))))))

(local-defthmd mod-map-preimage-6
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
		(in x (direct-product (list (z* m) (z* n)))))
	   (let ((c (mod (crt x (list m n)) (* m n))))
	     (implies (not (equal (gcd c (* m n)) 1))
	              (and (primep (cpd c (* m n)))
		           (divides (cpd c (* m n)) c)
			   (or (divides (cpd c (* m n)) m)
			       (divides (cpd c (* m n)) n))))))
  :hints (("Goal" :use (mod-map-preimage-4
                        (:instance cpd-divides (x (mod (crt x (list m n)) (* m n))) (y (* m n)))
			(:instance euclid (p (cpd (mod (crt x (list m n)) (* m n)) (* m n))) (a m) (b n))))))

(local-defthmd mod-map-preimage-7
  (implies (and (integerp c)
                (posp n)
		(primep p)
		(divides p c)
		(divides p n))
	  (not (equal (gcd (mod c n) n) 1)))
  :hints (("Goal" :use ((:instance rtl::mod-def (x x) (acl2::y n))
                        (:instance divides-gcd (d p) (x (mod c n)) (y n))))))

(local-defthmd mod-map-preimage-8
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
		(in x (direct-product (list (z* m) (z* n)))))
	   (let ((c (mod (crt x (list m n)) (* m n))))
	     (equal (gcd c (* m n)) 1)))
  :hints (("Goal" :use (mod-map-preimage-2 mod-map-preimage-5 mod-map-preimage-6
                        (:instance mod-map-preimage-7 (c (mod (crt x (list m n)) (* m n)))
			                              (p (cpd (mod (crt x (list m n)) (* m n)) (* m n))))
			(:instance mod-map-preimage-7 (c (mod (crt x (list m n)) (* m n)))
			                              (p (cpd (mod (crt x (list m n)) (* m n)) (* m n)))
						      (n m))))))
						      
(defthmd mod-map-preimage
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
		(in x (direct-product (list (z* m) (z* n)))))
	   (let ((c (mod (crt x (list m n)) (* m n))))
	     (and (in c (z* (* m n)))
	          (equal (mapply (mod-map m n) c) x))))
  :hints (("Goal" :use (mod-map-preimage-4 mod-map-preimage-8
                        (:instance member-rel-primes (n (* m n)) (k (mod (crt x (list m n)) (* m n))))))))
  
(defthmd epimorphismp-mod-map
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1))
           (epimorphismp (mod-map m n)
	                 (z* (* m n))
			 (direct-product (list (z* m) (z* n)))))
  :hints (("Goal" :use (homomorphismp-z*mod
                        (:instance mod-map-preimage (x (scex1 (elts (direct-product (list (z* m) (z* n))))
			                                      (ielts (mod-map m n) (z* (* m n)) (direct-product (list (z* m) (z* n)))))))
			(:instance scex1-lemma (l (elts (direct-product (list (z* m) (z* n)))))
			                       (m (ielts (mod-map m n) (z* (* m n)) (direct-product (list (z* m) (z* n))))))
                        (:instance homomorphism-epimorphism (map (mod-map m n)) (g (z* (* m n))) (h (direct-product (list (z* m) (z* n)))))
			(:instance member-ielts (map (mod-map m n))
			                        (g (z* (* m n)))
						(h (direct-product (list (z* m) (z* n))))
						(x (mod (crt (scex1 (elts (direct-product (list (z* m) (z* n))))
			                                            (ielts (mod-map m n) (z* (* m n)) (direct-product (list (z* m) (z* n)))))
						             (list m n))
							(* m n))))))))

(local-defthmd e-z*-m-n
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1))
           (equal (e (direct-product (list (z* m) (z* n))))
	          (list 1 1)))		  
  :hints (("Subgoal 2" :in-theory (enable e))
          ("Subgoal 1" :in-theory (enable e))))

(local-defthmd kernel-mod-map-1
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
		(in x (z* (* m n)))
		(equal (mapply (mod-map m n) x)
		       (list 1 1)))
	   (and (posp x)
	        (< x (* m n))
		(equal (mod x m) 1)
		(equal (mod x n) 1)))
  :hints (("Goal" :use ((:instance member-rel-primes (k x) (n (* m n)))
                        (:instance member-ninit (n (* m n)))))))

(local-defthm kernel-mod-map-2
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
	        (posp x)
	        (< x (* m n))
		(equal (mod x m) 1)
		(equal (mod x n) 1))
	   (equal x 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rtl::mod-equal-int (acl2::a x) (acl2::b 1))
                        (:instance rtl::mod-equal-int (acl2::a x) (acl2::b 1) (acl2::n m))
			(:instance rtl::mod-equal-int-reverse (acl2::a x) (acl2::b 1) (acl2::n (* m n)))
			(:instance product-rel-prime-divides (x m) (y n) (m (1- x)))))))

(local-defthm kernel-mod-map-3
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1))
	   (equal (e (z* (* m n))) 1))
  :hints (("Goal" :in-theory (enable e))))

(defthmd kernel-mod-map
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1)
		(in x (z* (* m n)))
		(equal (mapply (mod-map m n) x)
		       (e (direct-product (list (z* m) (z* n))))))
	   (equal (e (z* (* m n))) x))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (e-z*-m-n kernel-mod-map-1 kernel-mod-map-2 kernel-mod-map-3))))

(defthmd endomorphismp-mod-map
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1))
           (endomorphismp (mod-map m n)
	                 (z* (* m n))
			 (direct-product (list (z* m) (z* n)))))
  :hints (("Goal" :use ((:instance homomorphism-endomorphism (map (mod-map m n))
                                                             (g (z* (* m n)))
							     (h (direct-product (list (z* m) (z* n)))))
		        (:instance kernel-mod-map (x (cadr (kelts (mod-map m n) (z* (* m n)) (direct-product (list (z* m) (z* n)))))))))))

(defthmd isomorphismp-mod-map
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1))
           (isomorphismp (mod-map m n)
	                 (z* (* m n))
			 (direct-product (list (z* m) (z* n)))))
  :hints (("Goal" :in-theory (enable isomorphismp)
                  :use (epimorphismp-mod-map endomorphismp-mod-map))))

(defthmd order-z*-prod
  (implies (and (posp m) (> m 1)
                (posp n) (> n 1)
		(equal (gcd m n) 1))
	   (equal (order (z* (* m n)))
	          (* (order (z* m)) (order (z* n)))))
  :hints (("Goal" :use (isomorphismp-mod-map
                         (:instance isomorphism-equal-orders (map (mod-map m n))
                                                             (g (z* (* m n)))
							     (h (direct-product (list (z* m) (z* n)))))))))

(defthmd rel-prime-prime-power
  (implies (and (primep p) (posp n) (posp k))
           (iff (equal (gcd k (expt p n)) 1)
	        (not (divides p k))))
  :hints (("Goal" :in-theory (disable divides-gcd)
                  :use ((:instance powerp-prime-divisor (q (cpd k (expt p n))) (n (expt p n)))
                        (:instance cpd-divides (x k) (y (expt p n)))
			(:instance p-divides-power-p (n (expt p n)))
			(:instance divides-gcd (d p) (x k) (y (expt p n)))))))

(local-defthmd fl-m/n-1
  (implies (and (posp m) (posp n) (> n 1) (divides n m))
           (equal (fl (/ (1- m) n))
	          (1- (/ m n))))		  
  :hints (("Goal" :use ((:instance rtl::fl-unique (x (/ -1 n)) (acl2::n -1))))))

(local-defthmd fl-m/n-2
  (implies (and (posp m) (posp n) (> n 1) (not (divides n m)))
           (equal (fl (/ (1- m) n))
	          (+ (fl (/ m n)))))
  :hints (("Goal" :use ((:instance rtl::mod-def (x m) (acl2::y n))
                        (:instance rtl::fl-unique (x (/ (1- (mod m n)) n)) (acl2::n 0))))))		  

(defthmd fl-m/n
  (implies (and (posp m) (posp n) (> n 1))
           (equal (fl (/ m n))
	          (if (divides n m)
		      (1+ (fl (/ (1- m) n)))
		    (fl (/ (1- m) n)))))
  :hints (("Goal" :use (fl-m/n-1 fl-m/n-2))))

(defthmd rel-primes-aux-prime-power
  (implies (and (primep p) (posp n) (natp k))
           (equal (+ (len (rel-primes-aux k (expt p n)))
	             (fl (/ k p)))
		  k))		  
  :hints (("Subgoal *1/7" :use (rel-prime-prime-power (:instance fl-m/n (m k) (n p))))
          ("Subgoal *1/4" :use (rel-prime-prime-power (:instance fl-m/n (m k) (n p))))))

(defthmd order-z*-prime-power
  (implies (and (primep p) (posp n))
           (equal (order (z* (expt p n)))
	          (* (expt p (1- n)) (1- p))))
  :hints (("Goal" :in-theory (enable rel-primes)
                  :use ((:instance rel-primes-aux-prime-power (k (expt p n)))))))

(defthmd gcd-primep-pow-list
  (implies (and (prime-pow-list-p l)
                (consp l))
	   (equal (gcd (expt (caar l) (cdar l))
	               (pow-prod (cdr l)))
		  1))
  :hints (("Goal" :use ((:instance cpd-divides (x (expt (caar l) (cdar l))) (y (pow-prod (cdr l))))
                        (:instance powerp-prime-divisor (n (expt (caar l) (cdar l)))
			                                (p (caar l))
							(q (cpd (expt (caar l) (cdar l)) (pow-prod (cdr l)))))
			(:instance caar-prime-pow-list (l (cdr l)))
			(:instance least-divisor-is-least (k 2) (n (pow-prod (cdr l))) (d (caar l)))))))

(local-defthmd pow-prod>=2
  (implies (and (prime-pow-list-p l) (consp l))
           (and (natp (pow-prod l))
	        (>= (pow-prod l) 2))))

(defthmd order-z*-totient-comp
  (implies (and (prime-pow-list-p l) (consp l))
           (equal (order (z* (pow-prod l)))
	          (totient-comp l)))
  :hints (("Subgoal *1/3" :use (gcd-primep-pow-list
                                (:instance pow-prod>=2 (l (cdr l)))
                                (:instance order-z*-prod (m (expt (caar l) (cdar l))) (n (pow-prod (cdr l))))
                                (:instance order-z*-prime-power (p (caar l)) (n (cdar l)))))
	  ("Subgoal *1/2" :use ((:instance order-z*-prime-power (p (caar l)) (n (cdar l)))))))
	  
(defthmd order-totient
  (implies (and (posp n) (> n 1))
	   (equal (order (z* n))
	          (totient n)))
  :hints (("Goal" :in-theory (enable totient)
                  :use (prime-fact-existence
		        (:instance order-z*-totient-comp (l (prime-fact n)))))))

(defthmd power-z*
  (implies (and (posp n) (> n 1)
                (in x (z* n))
		(natp k))
	   (equal (power x k (z* n))
	          (mod (expt x k) n)))
  :hints (("Subgoal *1/2" :in-theory (enable z*-op member-rel-primes)
                          :use ((:instance power-in-g (a x) (n (1- k)) (g (z* n)))
                                (:instance rtl::mod-mod-times (acl2::a (expt x (1- k))) (acl2::b x) (acl2::n n))))
          ("Subgoal *1/1" :in-theory (enable e))))

(defthmd euler-totient
  (implies (and (posp n) (> n 1)
                (posp x) (< x n)
		(equal (gcd x n) 1))
	   (equal (mod (expt x (totient n)) n)
	          1))
  :hints (("Goal" :in-theory (e/d (e member-rel-primes) (divides-ord))
                  :use (order-totient
		        (:instance power-order (g (z* n)))
			(:instance power-z* (k (totient n)))))))
