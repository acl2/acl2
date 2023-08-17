(in-package "DM")

(include-book "euclid")
(include-book "arithmetic-5/top" :dir :system)

(in-theory (enable divides))

;; Fundamental Theorem of Arithmetic

(defun prime-pow-list-p (l)
  (if (consp l)
      (and (primep (caar l))
	   (posp (cdar l))
	   (prime-pow-list-p (cdr l))
	   (or (null (cdr l)) (< (caar l) (caadr l))))
    (null l)))

(defun prime-fact (n)
  (declare (xargs :hints (("Goal" :use ((:instance least-divisor-divides (k 2)))))))
  (if (and (natp n) (> n 1))
      (let* ((p (least-prime-divisor n))
   	     (l (prime-fact (/ n p))))
	(if (and (consp l) (equal (caar l) p))
	    (cons (cons p (1+ (cdar l))) (cdr l))
	  (cons (cons p 1) l)))
    ()))

(defthmd caar-prime-fact
  (implies (and (natp n) (> n 1))
	   (equal (caar (prime-fact n))
		  (least-prime-divisor n))))

(local-defthmd case-6-hack
  (implies (and (integerp n) (integerp m))
	   (integerp (* n m))))

(local-defthmd case-6
  (implies (and (natp n)
	        (> n 1)
		(> (/ n (least-divisor 2 n)) 1))
           (<= (least-divisor 2 n)
               (caar (prime-fact (/ n (least-divisor 2 n))))))
  :hints (("Goal" :use (primep-least-divisor
			(:instance case-6-hack (n (* N (/ (LEAST-DIVISOR 2 N)) (/ (LEAST-DIVISOR 2 (* N (/ (LEAST-DIVISOR 2 N)))))))
				               (m (LEAST-DIVISOR 2 N)))
			(:instance caar-prime-fact (n (/ n (least-prime-divisor n))))
			(:instance primep-least-divisor (n (/ n (least-prime-divisor n))))
			(:instance least-divisor-divides (k 2))
			(:instance least-divisor-divides (k 2) (n (/ n (least-prime-divisor n))))
			(:instance least-divisor-is-least (k 2) (d (caar (prime-fact (/ n (least-prime-divisor n))))))))))

(defthmd prime-pow-list-prime-fact
  (implies (posp n)
	   (prime-pow-list-p (prime-fact n)))
  :hints (("Subgoal *1/6" :use (primep-least-divisor case-6))
	  ("Subgoal *1/5" :use (primep-least-divisor))
	  ("Subgoal *1/4" :use (primep-least-divisor))))

(defun pow-prod (l)
  (if (consp l)
      (* (expt (caar l) (cdar l))
	 (pow-prod (cdr l)))
    1))

(defthmd pow-prod-equal
  (implies (posp n)
	   (equal (pow-prod (prime-fact n))
		  n))
  :hints (("Subgoal *1/5" :use (primep-least-divisor (:instance least-divisor-divides (k 2))))
	  ("Subgoal *1/4" :use (primep-least-divisor (:instance least-divisor-divides (k 2))))
	  ("Subgoal *1/3" :use (prime-pow-list-prime-fact primep-least-divisor (:instance least-divisor-divides (k 2))))))

(defthmd prime-fact-existence
  (implies (posp n)
	   (let ((l (prime-fact n)))
	     (and (prime-pow-list-p l)
		  (equal (pow-prod l) n))))
  :hints (("Goal" :use (prime-pow-list-prime-fact pow-prod-equal))))

(defund reduce-prime-fact (l)
  (if (equal (cdar l) 1)
      (cdr l)
    (cons (cons (caar l) (1- (cdar l)))
	  (cdr l))))

(defun prime-fact-induct (n l)
  (declare (xargs :hints (("Goal" :use ((:instance least-divisor-divides (k 2)))))))
  (if (and (natp n) (> n 1))
      (list (prime-fact-induct (/ n (least-prime-divisor n))
                               (reduce-prime-fact l)))
    (list n l)))

(local-defthmd pow-prod-pos
  (implies (prime-pow-list-p l)
	   (if (null l)
	       (equal (pow-prod l) 1)
	     (> (pow-prod l) 1)))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd prime-pow-list-p-reduce
  (implies (and (consp l) (prime-pow-list-p l))
	   (prime-pow-list-p (reduce-prime-fact l)))
  :hints (("Goal" :in-theory (enable reduce-prime-fact))))

(local-defthmd pow-prod-reduce
  (implies (and (consp l) (prime-pow-list-p l))
	   (equal (pow-prod (reduce-prime-fact l))
		  (/ (pow-prod l) (caar l))))
  :hints (("Goal" :in-theory (enable reduce-prime-fact))))

(local-defthmd cdr-caar-prime-fact
  (implies (and (posp n) (> n 1) (> (cdar (prime-fact n)) 1))
           (and (equal (cdr (prime-fact n)) (cdr (prime-fact (/ n (least-prime-divisor n)))))
	        (equal (caar (prime-fact n)) (caar (prime-fact (/ n (least-prime-divisor n)))))
	        (equal (cdar (prime-fact (/ n (least-prime-divisor n)))) (1- (cdar (prime-fact n)))))))

(local-defthmd car-prime-fact-1
  (implies (and (posp n) (> n 1) (> (cdar (prime-fact n)) 1))
           (equal (car (prime-fact (/ n (least-prime-divisor n))))
	          (cons (caar (prime-fact (/ n (least-prime-divisor n))))
		        (cdar (prime-fact (/ n (least-prime-divisor n))))))))

(local-defthmd car-prime-fact
  (implies (and (posp n) (> n 1) (> (cdar (prime-fact n)) 1))
           (equal (car (prime-fact (/ n (least-prime-divisor n))))
	          (cons (caar (prime-fact n)) (1- (cdar (prime-fact n))))))
  :hints (("Goal" :use (cdr-caar-prime-fact car-prime-fact-1))))

(local-defthmd cdr-car-prime-fact-1
  (implies (and (posp n) (> n 1) (> (cdar (prime-fact n)) 1))
           (equal (prime-fact (/ n (least-prime-divisor n)))
	          (cons (car (prime-fact (/ n (least-prime-divisor n))))
		        (cdr (prime-fact (/ n (least-prime-divisor n))))))))

(local-defthmd cdr-car-prime-fact
  (implies (and (posp n) (> n 1) (> (cdar (prime-fact n)) 1))
           (equal (prime-fact (/ n (least-prime-divisor n)))
	          (cons (cons (caar (prime-fact n)) (1- (cdar (prime-fact n))))
		        (cdr (prime-fact n)))))
  :hints (("Goal" :use (car-prime-fact cdr-caar-prime-fact cdr-car-prime-fact-1))))

(local-defthmd reduce-prime-fact-prime-fact
  (implies (and (posp n) (> n 1))
	   (equal (reduce-prime-fact (prime-fact n))
		  (prime-fact (/ n (least-prime-divisor n)))))
  :hints (("Goal" :in-theory (enable reduce-prime-fact)  
                  :use (prime-fact-existence cdr-car-prime-fact
		        (:instance prime-fact-existence (n (/ n (least-prime-divisor n))))
			(:instance caar-prime-fact (n (/ n (least-prime-divisor n))))))))

(local-defthm reduce-reduce-equal
  (implies (and (prime-pow-list-p l) (consp l)
                (prime-pow-list-p m) (consp m)
		(equal (reduce-prime-fact l) (reduce-prime-fact m))
		(equal (caar l) (caar m)))
	   (equal l m))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable reduce-prime-fact))))

(defthm primep-divides-prime-power
  (implies (and (primep p)
                (primep q)
		(natp n)
		(divides q (expt p n)))
	   (equal q p))
  :rule-classes ()
  :hints (("Goal" :induct (fact n))
          ("Subgoal *1/2" :use ((:instance euclid (p q) (a p) (b (expt p (1- n))))
	                        (:instance primep-no-divisor (d q))))))

(defthm natp-pow-prod
  (implies (prime-pow-list-p l)
           (natp (pow-prod l)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd prime-divisor-prime-pow-list
  (implies (and (prime-pow-list-p l)
                (primep p)
		(divides p (pow-prod l)))
	   (>= p (caar l)))
  :hints (("Subgoal *1/1" :use ((:instance primep-divides-prime-power (q p) (p (caar l)) (n (cdar l)))
                                (:instance euclid (a (expt (caar l) (cdar l))) (b (pow-prod (cdr l))))))))

(defthmd caar-prime-pow-list
  (implies (and (prime-pow-list-p l) (consp l))
           (equal (caar l) (least-prime-divisor (pow-prod l))))
  :hints (("Goal" :use (pow-prod-pos
                        (:instance prime-divisor-prime-pow-list (p (least-prime-divisor (pow-prod l))))
			(:instance primep-least-divisor (n (pow-prod l)))
			(:instance least-divisor-divides (k 2) (n (pow-prod l)))
			(:instance least-divisor-is-least (k 2) (n (pow-prod l)) (d (caar l)))))))

(local-defthmd caar-reduce-prime-fact
  (implies (and (prime-pow-list-p l) (consp l))
           (if (equal (cdar l) 1)
	       (equal (reduce-prime-fact l) (cdr l))
             (equal (caar (reduce-prime-fact l))
	            (caar l))))
  :hints (("Goal" :in-theory (enable reduce-prime-fact))))

(local-defthmd prime-fact-uniqueness-subgoal
  (implies (and (primep (least-divisor 2 (pow-prod l)))
                (integerp (pow-prod l))
                (<= 0 (pow-prod l))
                (< 1 (pow-prod l))
                (equal (prime-fact (* (pow-prod l)
                                      (/ (least-divisor 2 (pow-prod l)))))
                       (reduce-prime-fact l))
                (< 0 (pow-prod l))
                (prime-pow-list-p l))
           (equal (prime-fact (pow-prod l)) l))
  :hints (("Goal" :use (prime-pow-list-p-reduce caar-prime-pow-list caar-reduce-prime-fact
                        (:instance reduce-reduce-equal (m (prime-fact (pow-prod l))))
                        (:instance reduce-prime-fact-prime-fact (n (pow-prod l)))
			(:instance caar-prime-fact (n (pow-prod l)))))))

(defthmd prime-fact-uniqueness
  (implies (and (posp n)
		(prime-pow-list-p l)
		(equal (pow-prod l) n))
	   (equal (prime-fact n) l))
  :hints (("Goal" :induct (prime-fact-induct n l))
	  ("Subgoal *1/1" :use (pow-prod-pos primep-least-divisor prime-pow-list-p-reduce caar-prime-pow-list
	                        prime-pow-list-p-reduce pow-prod-reduce caar-prime-pow-list prime-fact-uniqueness-subgoal))
	  ("Subgoal *1/2" :use (pow-prod-pos))))


(defund cpd (x y)
  (least-prime-divisor (gcd x y)))

(defthmd cpd-divides
  (implies (and (integerp x) (not (= x 0))
                (integerp y) (not (= y 0))
		(not (= (gcd x y) 1)))
	   (and (primep (cpd x y))
	        (divides (cpd x y) x)
	        (divides (cpd x y) y)))
  :hints (("Goal" :in-theory (enable cpd)
                  :use (gcd-pos gcd-divides
		        (:instance primep-least-divisor (n (gcd x y)))
			(:instance least-divisor-divides (k 2) (n (gcd x y)))
			(:instance divides-transitive (x (cpd x y)) (y (gcd x y)) (z x))
			(:instance divides-transitive (x (cpd x y)) (y (gcd x y)) (z y))))))

(defthmd cpd-divides
  (implies (and (integerp x) (not (= x 0))
                (integerp y) (not (= y 0))
		(not (= (gcd x y) 1)))
	   (and (primep (cpd x y))
	        (divides (cpd x y) x)
	        (divides (cpd x y) y))))

(defthmd rel-prime-pow-list
  (implies (and (prime-pow-list-p l) (>= (len l) 2))
	   (equal (gcd (expt (caar l) (cdar l))
		       (pow-prod (cdr l)))
		  1))
  :hints (("Subgoal *1/1" :use
    ((:instance cpd-divides (x (expt (caar l) (cdar l))) (y (pow-prod (cdr l))))
     (:instance primep-divides-prime-power (p (caar l)) (n (cdar l))
			                   (q (cpd (expt (caar l) (cdar l)) (pow-prod (cdr l)))))
     (:instance prime-divisor-prime-pow-list (l (cdr l)) (p (cpd (expt (caar l) (cdar l)) (pow-prod (cdr l)))))))))

(defthmd gcd-divisor
  (implies (and (integerp x) (integerp y)                
                (integerp d) (not (= d 0))
		(divides d y)
		(= (gcd x y) 1))
	   (equal (gcd x d) 1))
  :hints (("Goal" :use ((:instance gcd-pos (y d))
                        (:instance primep-least-divisor (n (gcd x d)))
			(:instance divides-gcd (d (least-prime-divisor (gcd x d))) (y d))
			(:instance divides-transitive (x (least-prime-divisor (gcd x d))) (y (gcd x d)) (z x))
			(:instance divides-transitive (x (least-prime-divisor (gcd x d))) (y (gcd x d)) (z d))
			(:instance divides-transitive (x (least-prime-divisor (gcd x d))) (y d) (z y))
			(:instance least-divisor-divides (k 2) (n (gcd x d)))
			(:instance divides-gcd (d (least-prime-divisor (gcd x d))))
			(:instance gcd-divides (y d))))))

(defthmd gcd-divisor-2
  (implies (and (integerp x) (integerp y)                
                (integerp c) (not (= c 0))
                (integerp d) (not (= d 0))
		(divides c x)
		(divides d y)
		(= (gcd x y) 1))
	   (equal (gcd c d) 1))
  :hints (("Goal" :use (gcd-divisor
			(:instance gcd-commutative (y d))
			(:instance gcd-divisor (x d) (y x) (d c))
			(:instance gcd-commutative (x c) (y d))))))
