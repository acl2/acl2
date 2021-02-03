(in-package "RTL")

(include-book "bits")
(include-book "log")
(include-book "float")
(include-book "add")

(local (include-book "arithmetic-5/top" :dir :system))

;; Replace ripple-carry with this in add.lisp:

(defund cbit (x y cin k)
  (if (zp k)
      cin
    (logior (logand (bitn x (1- k)) (bitn y (1- k)))
	    (logior (logand (bitn x (1- k)) (cbit x y cin (1- k)))
		    (logand (bitn y (1- k)) (cbit x y cin  (1- k)))))))

(defund partsum (x y cin i)
  (+ (bits x i 0) (bits y i 0) cin))

(defthm partsum-1
  (implies (and (integerp x) (integerp y) (bitp cin) (integerp i) (< i 0))
	   (equal (partsum x y cin i)
		  cin))
  :hints (("Goal" :in-theory (enable partsum))))

(defthmd partsum-2
  (implies (and (integerp x) (integerp y) (bitp cin) (natp i))
	   (equal (partsum x y cin i)
		  (+ (* (expt 2 i) (+ (bitn x i) (bitn y i)))
		     (partsum x y cin (1- i)))))
  :hints (("Goal" :in-theory (enable partsum)
	          :use ((:instance bitn-plus-bits (n i) (m 0))
		        (:instance bitn-plus-bits (x y) (n i) (m 0))))))

(defthmd partsum-3
  (implies (and (integerp x) (integerp y) (bitp cin) (natp i))
           (and (integerp (partsum x y cin i))
	        (<= 0 (partsum x y cin i))
	        (<  (partsum x y cin i)
	            (expt 2 (+ i 2)))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable partsum)
	          :use ((:instance bits-bounds (j 0))
		        (:instance bits-bounds (x y) (j 0))))))

(defthmd partsum-4
  (implies (and (integerp x) (integerp y) (bitp cin) (natp i))
	   (equal (cbit x y cin i)
	          (if (>= (partsum x y cin (1- i)) (expt 2 i))
	              1 0)))
  :hints (("Goal" :in-theory (enable cbit partsum-2))
          ("Subgoal *1/2" :nonlinearp t
	                  :use ((:instance bitn-0-1 (n (1- i)))
	                        (:instance bitn-0-1 (x y) (n (1- i)))
				(:instance partsum-3 (i (- i 2)))))))

(defthmd partsum-5
  (implies (and (integerp x) (integerp y) (bitp cin) (natp i))
	   (equal (cbit x y cin i)
	          (fl (/ (partsum x y cin (1- i)) (expt 2 i)))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable partsum-4)
		  :use ((:instance partsum-3 (i (- i 1)))))))

(defthmd rc-1
  (implies (and (integerp x) (integerp y) (bitp cin) (natp i))
           (equal (mod (partsum x y cin i) (expt 2 (1+ i)))
	          (mod (+ x y cin) (expt 2 (1+ i)))))
  :hints (("Goal" :in-theory (enable partsum bits-mod)
                  :use ((:instance mod-sum (a (+ cin (mod x (expt 2 (1+ i))))) (b y) (n (expt 2 (1+ i))))
		        (:instance mod-sum (a (+ y cin)) (b x) (n (expt 2 (1+ i))))))))

(defthmd rc-2
  (implies (and (integerp x) (integerp y) (bitp cin) (natp i))
           (equal (mod (fl (/ (partsum x y cin i) (expt 2 i))) 2)
	          (bitn (+ x y cin) i)))
  :hints (("Goal" :use (rc-1
                        (:instance bitn-mod (x (partsum x y cin i)) (n (1+ i)) (k i))
                        (:instance bitn-mod (x (+ x y cin)) (n (1+ i)) (k i))
			(:instance bitn-def (x (partsum x y cin i)) (n  i))))
	  ("Goal''" :in-theory '(natp))))

(defthmd rc-3
  (implies (and (integerp x) (integerp y) (bitp cin) (natp i))
           (equal (bitn (+ x y cin) i)
	          (mod (fl (+ (bitn x i) (bitn y i) (/ (partsum x y cin (1- i)) (expt 2 i)))) 2)))
  :hints (("Goal" :in-theory (enable partsum-2)
                  :use (rc-2 (:instance bitn-0-1 (n i)) (:instance bitn-0-1 (x y) (n i))))))

(defthmd rc-4
  (implies (and (integerp x) (integerp y) (bitp cin) (natp i))
           (equal (bitn (+ x y cin) i)
	          (mod (+ (bitn x i) (bitn y i) (fl (/ (partsum x y cin (1- i)) (expt 2 i)))) 2)))
  :hints (("Goal" :in-theory (disable fl+int-rewrite)
                  :use (rc-3
                        (:instance bitn-0-1 (n i))
			(:instance bitn-0-1 (x y) (n i))
			(:instance partsum-3 (i (1- i)))
			(:instance fl+int-rewrite (x (/ (partsum x y cin (1- i)) (expt 2 i))) (n (+ (bitn x i) (bitn y i))))))))

(defthmd rc-5
  (implies (and (integerp x) (integerp y) (bitp cin) (natp i))
           (equal (bitn (+ x y cin) i)
	          (mod (+ (bitn x i) (bitn y i) (cbit x y cin i)) 2)))
  :hints (("Goal" :in-theory (enable partsum-5)
                  :use (rc-4))))

(defthmd ripple-carry-lemma
  (implies (and (integerp x)
                (integerp y)
                (bitp cin)
		(natp i))
	   (equal (bitn (+ x y cin) i)
		  (logxor (logxor (bitn x i) (bitn y i))
			  (cbit x y cin i))))
  :hints (("Goal" :in-theory (enable partsum-4) :use (rc-5 (:instance bitn-0-1 (n i)) (:instance bitn-0-1 (x y) (n i))))))

;;--------------------------------------------------------------------------------------------------------------------------------------

(defthmd gen-i-i
  (implies (and (integerp x)
		(integerp y)
		(natp i))
	   (equal (gen x y i i)
		  (logand (bitn x i) (bitn y i))))
  :hints (("Goal" :in-theory (enable gen) :use ((:instance bitn-0-1 (n i)) (:instance bitn-0-1 (x y) (n i))))))

(defthmd prop-i-i
  (implies (and (integerp x)
		(integerp y)
		(natp i))
	   (equal (prop x y i i)
		  (logxor (bitn x i) (bitn y i))))
  :hints (("Goal" :expand ((prop x y i i))
                  :use ((:instance bitn-0-1 (n i)) (:instance bitn-0-1 (x y) (n i))))))

(defund gp (x y i j)
  (cons (gen x y i j) (prop x y i j)))

(defund gp0 (x y i)
  (gp x y i i))

(defund fco (gp1 gp2)
  (cons (logior (car gp1) (logand (cdr gp1) (car gp2)))
	(logand (cdr gp1) (cdr gp2))))

(defthmd fco-assoc
  (implies (and (bitp g1) (bitp p1)
		(bitp g2) (bitp p2)
		(bitp g3) (bitp p3))
	   (equal (fco (fco (cons g1 p1) (cons g2 p2))
		       (cons g3 p3))
		  (fco (cons g1 p1)
		       (fco (cons g2 p2) (cons g3 p3))))))

(defthmd gp-decomp
  (implies (and (integerp x)
		(integerp y)
		(natp j)
		(natp i)
		(natp k)
		(<= j k)
		(< k i))
	   (equal (fco (gp x y i (1+ k)) (gp x y k j))
		  (gp x y i j)))
  :hints (("Goal" :use (gen-extend prop-extend)
                  :in-theory (enable gp fco))))

(defthmd cbit-1
  (implies (and (integerp x)
		(integerp y)
		(bitp cin))
	   (equal (cbit x y cin 1)
	          (logior (gen x y 0 0)
		          (logand (prop x y 0 0) cin))))
  :hints (("Goal" :in-theory (enable gen-i-i prop-i-i cbit)
                  :use ((:instance bitn-0-1 (n 0))
		        (:instance bitn-0-1 (n 0) (x y))))))

(defthmd cbit-2
  (implies (and (integerp x)
		(integerp y)
		(bitp cin)
		(not (zp i)))
	   (equal (cons (gen x y i 0) (prop x y i 0))
	          (cons (logior (logand (bitn x i) (bitn y i))
		                (logand (logxor (bitn x i) (bitn y i))
		                        (gen x y (1- i) 0)))
			(logand (logxor (bitn x i) (bitn y i))
			        (prop x y (1- i) 0)))))
  :hints (("Goal" :in-theory (enable gen-i-i prop-i-i gp fco)
                  :use ((:instance gp-decomp (j 0) (k (1- i)))))))

(defthmd cbit-3
  (implies (and (integerp x)
		(integerp y)
		(bitp cin)
		(not (zp i))
		(equal (cbit x y cin i)
		       (logior (gen x y (1- i) 0)
		               (logand (prop x y (1- i) 0)
			               cin))))
	   (equal (cbit x y cin (1+ i))
	          (logior (gen x y i 0)
		          (logand (prop x y i 0)
			          cin))))
  :hints (("Goal" :in-theory (enable cbit)
                  :use ((:instance bitn-0-1 (n i))
		        (:instance bitn-0-1 (n i) (x y))))))

(defthmd cbit-rewrite
  (implies (and (integerp x)
		(integerp y)
		(bitp cin)
		(natp i))
	   (equal (cbit x y cin (1+ i))
		  (logior (gen x y i 0)
			  (logand (prop x y i 0) cin))))
  :hints (("Subgoal *1/2" :use (cbit-1 cbit-3
                                (:instance bitn-0-1 (n i))
		                (:instance bitn-0-1 (n i) (x y))))
	  ("Subgoal *1/1" :use ((:instance bitn-0-1 (n i))
		                (:instance bitn-0-1 (n i) (x y)))
			  :in-theory (enable cbit))))

(defun rc (x y i)
  (if (zp i)
      (gp0 x y 0)
    (fco (gp0 x y i) (rc x y (1- i)))))

(defthmd rc-correct
  (implies (and (integerp x)
		(integerp y)
		(natp i))
	   (equal (rc x y i)
		  (gp x y i 0)))
  :hints (("Subgoal *1/4" :in-theory (enable gp0) :use ((:instance gp-decomp (j 0) (k (1- i)))))
          ("Subgoal *1/1" :in-theory (enable gp0))))

(defun lf (x y i d)
  (if (zp d)
      (gp0 x y i)
    (if (< (mod i (expt 2 d)) (expt 2 (1- d)))
	(lf x y i (1- d))
      (fco (lf x y i (1- d))
	   (lf x y
	       (+ (chop i (- d)) (expt 2 (1- d)) -1)
	       (1- d))))))

(defthmd lf-1
  (implies (and (integerp x)
		(integerp y)
		(natp i))
	   (equal (lf x y i 0)
		  (gp x y i (chop i (- 0)))))
  :hints (("Goal" :in-theory (enable gp0 lf chop))))

(defthmd lf-2
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(< (mod i (expt 2 d)) (expt 2 (1- d))))
	   (equal (mod i (expt 2 (1- d)))
	          (mod i (expt 2 d))))
  :hints (("Goal" :in-theory (enable chop)
                  :use ((:instance mod-def (x i) (y (expt 2 d)))
			(:instance mod-force (m i) (n (expt 2 (1- d))) (a (* 2 (fl (/ i (expt 2 d))))))))))

(defthmd lf-3
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(equal (lf x y i (1- d))
		       (gp x y i (chop i (- 1 d))))
		(< (mod i (expt 2 d)) (expt 2 (1- d))))
	   (equal (lf x y i d)
	          (gp x y i (chop i (- d)))))
  :hints (("Goal" :in-theory (enable lf chop)
                  :use (lf-2
		        (:instance mod-def (x i) (y (expt 2 d)))
			(:instance mod-def (x i) (y (expt 2 (1- d))))))))

(defthmd lf-4
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(>= (mod i (expt 2 d)) (expt 2 (1- d))))
	   (equal (mod i (expt 2 (1- d)))
	          (- (mod i (expt 2 d))
		     (expt 2 (1- d)))))
  :hints (("Goal" :in-theory (enable chop)
                  :use ((:instance mod-def (x i) (y (expt 2 d)))
			(:instance mod-force (m i) (n (expt 2 (1- d))) (a (1+ (* 2 (fl (/ i (expt 2 d)))))))))))

(defthmd lf-5
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(>= (mod i (expt 2 d)) (expt 2 (1- d))))
	   (equal (chop i (- 1 d))
	          (+ (chop i (- d))
		     (expt 2 (1- d)))))
  :hints (("Goal" :in-theory (enable chop)
                  :use (lf-4
		        (:instance mod-def (x i) (y (expt 2 d)))
			(:instance mod-def (x i) (y (expt 2 (1- d))))))))

(defthmd lf-6
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(>= (mod i (expt 2 d)) (expt 2 (1- d))))
	   (equal (chop (1- (chop i (- 1 d))) (- 1 d))
	          (chop i (- d))))
  :hints (("Goal" :in-theory (enable chop)
                  :use (lf-5))))

(defthm int-chop
  (implies (and (rationalp x) (integerp n) (<= n 0))
           (integerp (chop x n)))
  :hints (("Goal" :in-theory (enable chop)))
  :rule-classes (:type-prescription :rewrite))

(defthmd lf-7
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(equal (lf x y (1- (chop i (- 1 d))) (1- d))
		       (gp x y (1- (chop i (- 1 d))) (chop (1- (chop i (- 1 d))) (- 1 d))))
		(>= (mod i (expt 2 d)) (expt 2 (1- d))))
	   (equal (lf x y (+ (chop i (- d)) (expt 2 (1- d)) -1) (1- d))
	          (gp x y (1- (chop i (- 1 d))) (chop i (- d)))))
  :hints (("Goal" :in-theory (enable chop) :use (lf-5 lf-6))))

(defthmd lf-8
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(equal (lf x y (1- (chop i (- 1 d))) (1- d))
		       (gp x y (1- (chop i (- 1 d))) (chop (1- (chop i (- 1 d))) (- 1 d))))
		(equal (lf x y i (1- d))
		       (gp x y i (chop i (- 1 d))))
		(>= (mod i (expt 2 d)) (expt 2 (1- d))))
	   (equal (lf x y i d)
		  (fco (gp x y i (chop i (- 1 d)))
		       (gp x y (1- (chop i (- 1 d))) (chop i (- d))))))
  :hints (("Goal" :use (lf-7)
                  :expand ((lf x y i d)))))

(defthmd lf-9
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d)))
	   (and (natp (chop i (- d)))
	        (natp (chop i (- 1 d)))
		(<= (chop i (- 1 d)) i)))
  :hints (("Goal" :in-theory (enable chop) :use ((:instance chop-down (x i) (n (- 1 d)))))))

(defthmd lf-10
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(equal (lf x y (1- (chop i (- 1 d))) (1- d))
		       (gp x y (1- (chop i (- 1 d))) (chop (1- (chop i (- 1 d))) (- 1 d))))
		(equal (lf x y i (1- d))
		       (gp x y i (chop i (- 1 d))))
		(>= (mod i (expt 2 d)) (expt 2 (1- d)))
		(< (chop i (- d)) (chop i (- 1 d))))
	   (equal (lf x y i d)
		  (gp x y i (chop i (- d)))))
  :hints (("Goal" :in-theory (enable lf-8)
                  :use (lf-9 (:instance gp-decomp (j (chop i (- d))) (k (1- (chop i (- 1 d)))))))))

(defthmd lf-11
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(equal (lf x y (1- (chop i (- 1 d))) (1- d))
		       (gp x y (1- (chop i (- 1 d))) (chop (1- (chop i (- 1 d))) (- 1 d))))
		(equal (lf x y i (1- d))
		       (gp x y i (chop i (- 1 d))))
		(>= (mod i (expt 2 d)) (expt 2 (1- d)))
		(>= (chop i (- d)) (chop i (- 1 d))))
	   (equal (lf x y i d)
		  (gp x y i (chop i (- d)))))
  :hints (("Goal" :in-theory (enable lf-8 fco gp gen prop chop)
                  :use (lf-9 (:instance chop-chop (x i) (k (- d)) (m (- 1 d)))))))

(defthmd lf-12
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(equal (lf x y (1- (+ (chop i (- d)) (expt 2 (1- d)))) (1- d))
		       (gp x y (1- (+ (chop i (- d)) (expt 2 (1- d)))) (chop (1- (+ (chop i (- d)) (expt 2 (1- d)))) (- 1 d))))
		(equal (lf x y i (1- d))
		       (gp x y i (chop i (- 1 d)))))
	   (equal (lf x y i d)
	          (gp x y i (chop i (- d)))))
  :hints (("Goal" :in-theory (enable lf chop)
                  :use (lf-3 lf-5 lf-10 lf-11))))

(defthmd lf-13
  (implies (and (natp i)
		(not (zp d)))
	   (>= (chop i (- d)) 0))
  :hints (("Goal" :in-theory (enable chop))))

(defthmd lf-correct-gen
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(natp d))
	   (equal (lf x y i d)
		  (gp x y i (chop i (- d)))))
  :hints (("Goal" :in-theory (enable lf))
          ("Subgoal *1/9" :use (lf-12))
	  ("Subgoal *1/8" :use (lf-12 lf-13))
	  ("Subgoal *1/4" :use (lf-3))
	  ("Subgoal *1/1" :in-theory (enable chop gp0))))

(defthmd lf-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(bvecp i n))
	   (equal (lf x y i n)
		  (gp x y i 0)))
  :hints (("Goal" :use ((:instance lf-correct-gen (d n)))
                  :nonlinearp t
                  :in-theory (enable chop bvecp))))

(defund ks (x y i d)
  (if (zp d)
      (gp0 x y i)
    (if (< i (expt 2 (1- d)))
	(ks x y i (1- d))
      (fco (ks x y i (1- d))
	   (ks x y (- i (expt 2 (1- d))) (1- d))))))

(defthmd ks-1
  (IMPLIES (AND (natp i)
                (NOT (ZP D))
                (< I (EXPT 2 (+ -1 D)))
                (<= (EXPT 2 (+ -1 D)) (+ 1 I))
                (< (+ 1 I) (EXPT 2 D)))
	   (equal (EXPT 2 (+ -1 D))
	          (1+ i))))

(defthmd ks-2
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(< i (expt 2 (1- d)))
		(equal (ks x y i (1- d))
		       (gp x y i (max 0 (1+ (- i (expt 2 (1- d))))))))
	   (equal (ks x y i d)
		  (gp x y i (max 0 (1+ (- i (expt 2 d)))))))
  :hints (("Goal" :in-theory (enable ks) :nonlinearp t)
          ("Subgoal 2" :use (ks-1))))

(defthmd ks-3
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(>= i (expt 2 (1- d)))
		(equal (ks x y i (1- d))
		       (gp x y i (max 0 (1+ (- i (expt 2 (1- d)))))))
		(equal (ks x y (- i (expt 2 (1- d))) (1- d))
		       (gp x y (- i (expt 2 (1- d))) (max 0 (1+ (- (- i (expt 2 (1- d))) (expt 2 (1- d))))))))
	   (equal (ks x y i d)
		  (fco (gp x y i (1+ (- i (expt 2 (1- d)))))
		       (gp x y (- i (expt 2 (1- d))) (max 0 (1+ (- i (expt 2 d))))))))
  :hints (("Goal" :in-theory (enable ks) :nonlinearp t)))

(defthmd ks-4
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(>= i (expt 2 (1- d)))
		(equal (ks x y i (1- d))
		       (gp x y i (max 0 (1+ (- i (expt 2 (1- d)))))))
		(equal (ks x y (- i (expt 2 (1- d))) (1- d))
		       (gp x y (- i (expt 2 (1- d))) (max 0 (1+ (- (- i (expt 2 (1- d))) (expt 2 (1- d))))))))
	   (equal (ks x y i d)
		  (gp x y i (max 0 (1+ (- i (expt 2 d)))))))
  :hints (("Goal" :in-theory (enable ks-3)
                  :nonlinearp t
                  :use ((:instance gp-decomp (j (max 0 (1+ (- i (expt 2 d))))) (k (- i (expt 2 (1- d)))))))))

(defthmd ks-correct-gen
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(natp d))
	   (equal (ks x y i d)
		  (gp x y i (max 0 (1+ (- i (expt 2 d)))))))
  :hints (("Goal" :in-theory (enable ks))
          ("Subgoal *1/3" :use (ks-4))
	  ("Subgoal *1/2" :use (ks-2))
	  ("Subgoal *1/1" :in-theory (enable ks gp0))))

(defthmd ks-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(bvecp i n))
	   (equal (ks x y i n)
		  (gp x y i 0)))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use ((:instance ks-correct-gen (d n))))))

(defund pi2 (k)
  (if (zp k)
      0
    (if (integerp (/ k 2))
	(1+ (pi2 (/ k 2)))
      0)))

(defthmd pi2-1
  (implies (not (zp k))
           (and (integerp (/ k (expt 2 (pi2 k))))
	        (not (integerp (/ k (expt 2 (1+ (pi2 k))))))))
  :hints (("Goal" :in-theory (enable pi2))))

(defthmd pi2-2
  (implies (and (integerp x) (integerp y))
           (integerp (* x y))))

(defthmd pi2-lemma
  (implies (and (not (zp k)) (integerp p))
           (iff (integerp (/ k (expt 2 p)))
	        (<= p (pi2 k))))
  :hints (("Goal" :use (pi2-1
                        (:instance pi2-2 (x (/ k (expt 2 (pi2 k)))) (y (expt 2 (- (pi2 k) p))))
                        (:instance pi2-2 (x (/ k (expt 2 p))) (y (expt 2 (- p (1+ (pi2 k))))))))))

(defund bk0 (x y i d)
  (if (zp d)
      (gp0 x y i)
    (if (< (pi2 (1+ i)) d)
	(bk0 x y i (1- d))
      (fco (bk0 x y i (1- d))
	   (bk0 x y (- i (expt 2 (1- d))) (1- d))))))

(defthmd pi2-upper
  (implies (not (zp k))
	   (<= (expt 2 (pi2 k)) k))
  :hints (("Goal" :in-theory (enable pi2))))

(defund bk (x y i n)
  (declare (xargs :hints (("Goal" :use ((:instance pi2-upper (k (1+ i))))))))
  (let ((p (pi2 (1+ i))))
    (if (or (zp n) (not (bvecp i n)) (= i (1- (expt 2 p))))
        (bk0 x y i n)
      (fco (bk0 x y i n)
	   (bk x y (- i (expt 2 p)) n)))))

(defthmd bk0-1
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(< (pi2 (1+ i)) d)
		(equal (bk0 x y i (1- d))
		       (gp x y i (1+ (- i (expt 2 (min (pi2 (1+ i)) (1- d))))))))
           (equal (bk0 x y i d)
	          (gp x y i (1+ (- i (expt 2 (min (pi2 (1+ i)) d)))))))
  :hints (("Goal" :in-theory (enable bk0))))

(defthmd bk0-2
  (implies (and (not (zp x)) (not (zp d)) (integerp (/ x (expt 2 d))))
           (and (not (integerp (/ (- x (expt 2 (1- d))) (expt 2 d))))
	        (>= x (expt 2 d)))))

(defthmd bk0-3
  (implies (and (natp i)
                (not (zp d))
		(>= (pi2 (1+ i)) d))
	   (equal (pi2 (1+ (- i (expt 2 (1- d)))))
	          (1- d)))
  :hints (("Goal" :nonlinearp t
                  :use ((:instance pi2-lemma (k (1+ i)) (p d))
		        (:instance pi2-lemma (k (1+ i)) (p (1- d)))
                        (:instance pi2-lemma (k (1+ (- i (expt 2 (1- d))))) (p d))
                        (:instance pi2-lemma (k (1+ (- i (expt 2 (1- d))))) (p (1- d)))
			(:instance bk0-2 (x (1+ i)))))))

(defthmd bk0-4
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(>= (pi2 (1+ i)) d)
		(equal (bk0 x y i (1- d))
		       (gp x y i (1+ (- i (expt 2 (min (pi2 (1+ i)) (1- d)))))))
		(equal (bk0 x y (- i (expt 2 (1- d))) (1- d))
		       (gp x y (- i (expt 2 (1- d))) (1+ (- (- i (expt 2 (1- d))) (expt 2 (min (pi2 (1+ (- i (expt 2 (1- d))))) (1- d))))))))
           (equal (bk0 x y i d)
	          (fco (gp x y i (1+ (- i (expt 2 (1- d)))))
		       (gp x y (- i (expt 2 (1- d))) (1+ (- i (expt 2 (min (pi2 (1+ i)) d))))))))
  :hints (("Goal" :use (bk0-3) :in-theory (enable bk0) :nonlinearp t)))

(defthmd bk0-5
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(>= (pi2 (1+ i)) d)
		(equal (bk0 x y i (1- d))
		       (gp x y i (1+ (- i (expt 2 (min (pi2 (1+ i)) (1- d)))))))
		(equal (bk0 x y (- i (expt 2 (1- d))) (1- d))
		       (gp x y (- i (expt 2 (1- d))) (1+ (- (- i (expt 2 (1- d))) (expt 2 (min (pi2 (1+ (- i (expt 2 (1- d))))) (1- d))))))))
           (equal (bk0 x y i d)
	          (gp x y i (1+ (- i (expt 2 (min (pi2 (1+ i)) d)))))))
  :hints (("Goal" :in-theory (enable bk0-4)
                  :nonlinearp t
                  :use ((:instance bk0-2 (x (1+ i)))
		        (:instance pi2-lemma (k (1+ i)) (p d))
			(:instance gp-decomp (j (1+ (- i (expt 2 (min (pi2 (1+ i)) d))))) (k (- i (expt 2 (1- d)))))))))

(defthmd bk0-6
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(not (zp d))
		(>= (pi2 (1+ i)) d))
	   (>= i (expt 2 (1- d))))
  :hints (("Goal" :use ((:instance pi2-lemma (k (1+ i)) (p d))
                        (:instance bk0-2 (x (1+ i))))
	          :nonlinearp t)))

(defthmd bk0-correct-gen
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(natp d))
	   (equal (bk0 x y i d)
	          (gp x y i (1+ (- i (expt 2 (min (pi2 (1+ i)) d)))))))
  :hints (("Goal" :in-theory (enable bk0))
          ("Subgoal *1/3" :use (bk0-5 bk0-6))
	  ("Subgoal *1/1'''" :in-theory (enable gp0))))

(defthmd bk0-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(bvecp i n))
	   (equal (bk0 x y i n)
		  (gp x y i (1+ (- i (expt 2 (pi2 (1+ i))))))))
  :hints (("Goal" :nonlinearp t
                  :use ((:instance pi2-lemma (k (1+ i)) (p (1+ n)))
                        (:instance bk0-2 (x (1+ i)) (d (1+ n)))
                        (:instance bk0-correct-gen (d n))))))

(defthmd bk-1
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(bvecp i n)
		(equal i (1- (expt 2 (pi2 (1+ i))))))
	   (equal (bk x y i n)
		  (gp x y i 0)))
  :hints (("Goal" :in-theory (enable bk bk0-correct))))

(defthmd bk-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(bvecp i n))
	   (equal (bk x y i n)
		  (gp x y i 0)))
  :hints (("Goal" :in-theory (enable bk bk0-correct))
          ("Subgoal *1/3" :use (bk-1
	                        (:instance pi2-upper (k (1+ i)))
				(:instance gp-decomp (j 0) (k (- i (expt 2 (pi2 (1+ i))))))))
          ("Subgoal *1/2" :in-theory (enable bvecp)
	                  :use (bk-1
	                        (:instance pi2-upper (k (1+ i)))
				(:instance gp-decomp (j 0) (k (- i (expt 2 (pi2 (1+ i))))))))))

(defund hc0 (x y i k d)
  (let ((p (pi2 (1+ i))))
    (if (or (zp d) (< p k))
	(bk0 x y i k)
      (if (< i (expt 2 (+ k d -1)))
	  (hc0 x y i k (1- d))
	(fco (hc0 x y i k (1- d))
	     (hc0 x y (- i (expt 2 (+ k d -1))) k (1- d)))))))

(defund hc (x y i k n)
  (declare (xargs :hints (("Goal" :use ((:instance pi2-upper (k (1+ i))))))))
  (let ((p (pi2 (1+ i))))
    (if (or (zp n) (not (bvecp i n)) (>= (pi2 (1+ i)) k) (= i (1- (expt 2 p))))
	(hc0 x y i k (- n k))
      (fco (hc0 x y i k (- n k))
           (hc x y (- i (expt 2 p)) k n)))))

(defthmd hack-1
  (implies (and (integerp i) (integerp (expt 2 (1- (+ k d))))
                (< i (expt 2 (1- (+ k d))))
		(<= (expt 2 (1- (+ k d))) (1+ i)))
           (equal (expt 2 (1- (+ k d))) (1+ i))))

(defthmd hc0-correct-gen
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(natp k)
		(natp d)
		(>= (pi2 (1+ i)) k))
	   (let ((m (max 0 (- (1+ i) (expt 2 (+ k d))))))
	     (equal (hc0 x y i k d)
		    (gp x y i m))))
  :hints (("Goal" :in-theory (enable hc0) :induct (hc0 x y i k d) :nonlinearp t)
          ("Subgoal *1/3" :use ((:instance pi2-lemma (k (1+ i)) (p k))
			        (:instance pi2-lemma (k (1+ (- i (expt 2 (1- (+ k d)))))) (p k))
				(:instance gp-decomp (j (max 0 (- (1+ i) (expt 2 (+ k d)))))
				                     (k (- i (expt 2 (1- (+ k d))))))))
	  ("Subgoal *1/2" :use (hack-1
			        (:instance pi2-upper (k (1+ i)))
		                (:instance bk0-correct-gen (d k))))
	  ("Subgoal *1/1" :use ((:instance pi2-upper (k (1+ i)))
		                (:instance bk0-correct-gen (d k))))))

(defthmd hc0-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(natp k)
		(<= k n)
		(bvecp i n)
		(integerp (/ (1+ i) (expt 2 k))))
	   (equal (hc0 x y i k (- n k))
		  (gp x y i 0)))
  :hints (("Goal" :use ((:instance hc0-correct-gen (d (- n k)))
                        (:instance pi2-lemma (k (1+ i)) (p k))))))

(defthmd hc-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(natp k)
		(<= k n)
		(bvecp i n))
	   (equal (hc x y i k n)
		  (gp x y i 0)))
  :hints (("Goal" :in-theory (enable hc) :nonlinearp t)
          ("Subgoal *1/1" :in-theory (enable hc hc0) :use (hc0-correct (:instance bk0-correct-gen (d k)) (:instance pi2-lemma (k (1+ i)) (p k))))
          ("Subgoal *1/2" :in-theory (enable bvecp) :use ((:instance pi2-upper (k (1+ i)))))
          ("Subgoal *1/3" :in-theory (enable hc hc0)
	                  :use (hc0-correct
			        (:instance gp-decomp (j 0) (k (- i (expt 2 (pi2 (1+ i))))))
			        (:instance pi2-upper (k (1+ i)))
				(:instance bk0-correct-gen (d k))
				(:instance pi2-lemma (k (1+ i)) (p k))))))

