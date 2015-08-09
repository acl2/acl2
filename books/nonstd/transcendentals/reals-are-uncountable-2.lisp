(in-package "ACL2")

(include-book "arithmetic/top" :dir :system)

(include-book "ihs/quotient-remainder-lemmas" :dir :system)
(in-theory (disable quotient-remainder-functions))


(encapsulate
 ( ((digit-seq *) => * :formals (n) :guard (posp n)))

 (local (defun digit-seq (n)
          (declare (xargs :guard (posp n))
                   (ignore n))
          0))

(defthm digit-seq-is-digit
  (implies (posp n)
	   (and (integerp (digit-seq n))
		(<= 0 (digit-seq n))
		(<= (digit-seq n) 9)))
  :rule-classes (:rewrite :type-prescription))

 )

(defun digit-seq-sum (min max)
  (declare (xargs :measure (nfix (- (1+ max) min))))
  (if (and (posp min)
	   (posp max)
	   (<= min max))
      (+ (/ (digit-seq min) (expt 10 min))
	 (digit-seq-sum (1+ min) max))
    0))

(defthm integer-expt-quotient
  (implies (and (posp min)
		(posp max)
		(<= min max))
	   (integerp (* (expt 10 max)
			(/ (expt 10 min))))))

(defthmd digit-seq-sum-multiple-of-expt-10-max
  (implies (and (posp min)
		(posp max)
		(<= min max))
	   (integerp (* (digit-seq-sum min max)
			(expt 10 max))))
  :hints (("Subgoal *1/3''"
	   :use ((:instance (:theorem (implies (and (integerp x)
						    (integerp y)
						    (integerp z))
					       (integerp (+ x (* y z)))))
			    (x (* (expt 10 max)
				  (digit-seq-sum (+ 1 min) max)))
			    (y (digit-seq min))
			    (z (* (expt 10 max)
				  (/ (expt 10 min)))))))))

(defun digit-seq-sum-alt (min max)
  (declare (xargs :measure (nfix (- (1+ max) min))))
  (if (and (posp min)
	   (posp max)
	   (<= min max))
      (+ (digit-seq min)
	 (/ (digit-seq-sum-alt (1+ min) max)
	    10))
    0))

(defthmd digit-seq-sum-regular-to-alt
  (implies (and (posp min)
		(posp max))
	   (equal (digit-seq-sum min max)
		   (/ (digit-seq-sum-alt min max)
		      (expt 10 min)))))

(defthmd digit-seq-sum-alt-upper-bound
  (implies (and (posp min)
		(posp max))
	   (< (digit-seq-sum-alt min max) 10))
  :hints (("Subgoal *1/2"
	   :use ((:instance digit-seq-is-digit (n min)))
	   :in-theory (disable digit-seq-is-digit))))

(defthmd digit-seq-sum-upper-bound
  (implies (and (posp min)
		(posp max)
		(<= min max))
	   (< (digit-seq-sum min max)
	      (/ (expt 10 (1- min)))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance digit-seq-sum-alt-upper-bound)
		 (:instance digit-seq-sum-regular-to-alt))
	   :in-theory (disable digit-seq-sum-alt
			       digit-seq-sum))))

(defthm digit-seq-sum-split-lemma
  (implies (and (posp min)
		(posp i)
		(not (posp (+ -1 i)))
		(<= min i))
	   (and (equal i 1)
		(equal min 1)))
  :rule-classes nil)

(defthmd digit-seq-sum-split
  (implies (and (posp min)
		(posp max)
		(posp i)
		(<= min i)
		(<= i max))
	   (equal (digit-seq-sum min max)
		  (+ (digit-seq-sum min (1- i))
		     (/ (digit-seq i) (expt 10 i))
		     (digit-seq-sum (1+ i) max))))
  :hints (("Subgoal *1/4.3"
	   :use ((:instance digit-seq-sum-split-lemma)))))


(encapsulate
 ( ((digit-seq-2 *) => * :formals (n) :guard (posp n)))

 (local (defun digit-seq-2 (n)
	  (declare (xargs :guard (posp n))
		   (ignore n))
	  0))

 (defthm digit-seq-2-is-digit
   (implies (posp n)
	    (and (integerp (digit-seq-2 n))
		 (<= 0 (digit-seq-2 n))
		 (<= (digit-seq-2 n) 9)))
   :rule-classes (:rewrite :type-prescription))

 )

(defun digit-seq-2-sum (min max)
  (declare (xargs :measure (nfix (- (1+ max) min))))
  (if (and (posp min)
	   (posp max)
	   (<= min max))
      (+ (/ (digit-seq-2 min) (expt 10 min))
	 (digit-seq-2-sum (1+ min) max))
    0))

(defthmd digit-seq-2-sum-multiple-of-expt-10-max
  (implies (and (posp min)
		(posp max)
		(<= min max))
	   (integerp (* (digit-seq-2-sum min max)
			(expt 10 max))))
  :hints (("Goal"
	   :by (:functional-instance digit-seq-sum-multiple-of-expt-10-max
				     (digit-seq-sum digit-seq-2-sum)
				     (digit-seq digit-seq-2)))))

(defthmd digit-seq-2-sum-upper-bound
  (implies (and (posp min)
		(posp max)
		(<= min max))
	   (< (digit-seq-2-sum min max)
	      (/ (expt 10 (1- min)))))
  :hints (("Goal"
	   :by (:functional-instance digit-seq-sum-upper-bound
				     (digit-seq-sum digit-seq-2-sum)
				     (digit-seq digit-seq-2)))))


(defthmd digit-seq-2-sum-split
  (implies (and (posp min)
		(posp max)
		(posp i)
		(<= min i)
		(<= i max))
	   (equal (digit-seq-2-sum min max)
		  (+ (digit-seq-2-sum min (1- i))
		     (/ (digit-seq-2 i) (expt 10 i))
		     (digit-seq-2-sum (1+ i) max))))
  :hints (("Goal"
	   :by (:functional-instance digit-seq-sum-split
				     (digit-seq-sum digit-seq-2-sum)
				     (digit-seq digit-seq-2)))))

(defthmd minimum-separation-lemma
  (implies (and (realp a)
		(realp b)
		(realp c)
		(< 0 c)
		(integerp (/ a c))
		(integerp (/ b c))
		(not (equal a b)))
	   (<= c (abs (- a b))))
  :hints (("Goal"
	   :use ((:instance (:theorem (implies (and (integerp a)
						    (integerp b)
						    (not (equal a b)))
					       (<= 1 (abs (- a b)))))
			    (a (/ a c))
			    (b (/ b c)))))
	  ("Subgoal 2.2"
	   :use ((:instance (:theorem (implies (and (realp x)
						    (realp y)
						    (realp z)
						    (< 0 z)
						    (<= x y))
					       (<= (* x z) (* y z))))
			    (x 1)
			    (y (+ (- (* A (/ C))) (* B (/ C))))
			    (z c))))
	  ("Subgoal 2.1"
	   :use ((:instance (:theorem (implies (and (realp x)
						    (realp y)
						    (realp z)
						    (< 0 z)
						    (<= x y))
					       (<= (* x z) (* y z))))
			    (x 1)
			    (y (+ (* A (/ C)) (- (* B (/ C)))))
			    (z c))))))

(defthmd minimum-separation
  (implies (and (posp min)
		(posp max)
		(<= min max)
		(not (equal (digit-seq-sum min max)
			    (digit-seq-2-sum min max))))
	   (<= (/ (expt 10 max))
	       (abs (- (digit-seq-sum min max)
		       (digit-seq-2-sum min max)))))
  :hints (("Goal"
	   :use ((:instance minimum-separation-lemma
			    (a (digit-seq-sum min max))
			    (b (digit-seq-2-sum min max))
			    (c (/ (expt 10 max))))
		 (:instance digit-seq-sum-multiple-of-expt-10-max)
		 (:instance digit-seq-2-sum-multiple-of-expt-10-max))
	   :in-theory (disable digit-seq-sum
			       digit-seq-2-sum
			       abs
			       expt))))


(defthmd abs-difference
  (implies (and (realp a)
		(realp b)
		(realp z1)
		(realp z2)
		(< z2 z1)
		(>= (abs a) z1)
		(<= (abs b) z2))
	   (<= (- z1 z2) (abs (+ a b)))))


(defthmd triangle-inequality
  (implies (and (realp a)
		(realp b))
	   (<= (abs (+ a b))
	       (+ (abs a) (abs b)))))

(defthm different-enough-digits-implies-different-numbers-lemma-1
  (implies (and (realp a)
		(realp b)
		(realp c)
		(realp d)
		(< 0 d)
		(>= (abs a) (* 10 d))
		(<= (abs b) (* 7 d))
		(<= (abs c) (* 2 d)))
	   (<= d (abs (+ a b c))))
  :hints (("Goal"
	   :use ((:instance abs-difference
			    (a a)
			    (b (+ b c))
			    (z1 (* 10 d))
			    (z2 (* 9 d)))
		 (:instance triangle-inequality
			    (a b)
			    (b c)))
	   :in-theory (disable abs)))
  :rule-classes nil)

(defthm different-enough-digits-implies-different-numbers-lemma-2
  (implies (and (realp b)
		(realp c)
		(realp d)
		(< 0 d)
		(>= (abs b) (* 3 d))
		(<= (abs c) (* 2 d)))
	   (<= d (abs (+ b c))))
  :hints (("Goal"
	   :use ((:instance abs-difference
			    (a b)
			    (b c)
			    (z1 (* 3 d))
			    (z2 (* 2 d))))
	   :in-theory (disable abs)))
  :rule-classes nil)

(defthmd digit-sum-difference-split
  (implies (and (posp i)
		(posp min)
		(posp max)
		(<= min i)
		(<= i max))
	   (equal (- (digit-seq-sum min max)
		     (digit-seq-2-sum min max))
		  (+ (- (digit-seq-sum min (1- i))    (digit-seq-2-sum min (1- i)))
		     (- (/ (digit-seq i) (expt 10 i)) (/ (digit-seq-2 i) (expt 10 i)))
		     (- (digit-seq-sum (1+ i) max)    (digit-seq-2-sum (1+ i) max)))))
  :hints (("Goal"
	   :use ((:instance digit-seq-sum-split)
		 (:instance digit-seq-2-sum-split)))))

(defthmd minimum-separation-of-prefix
  (implies (and (posp min)
		(posp i)
		(<= min i)
		(not (equal (digit-seq-sum min (1- i))
			    (digit-seq-2-sum min (1- i)))))
	   (>= (abs (- (digit-seq-sum min (1- i))
		       (digit-seq-2-sum min (1- i))))
	       (* 10 (/ (expt 10 i)))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance minimum-separation (min min) (max (1- i))))
	   )))

(defthmd maximum-separation-of-middle
  (implies (and (posp i)
		(<= (abs (- (digit-seq i) (digit-seq-2 i))) 7))
	   (<= (abs (- (/ (digit-seq i) (expt 10 i)) (/ (digit-seq-2 i) (expt 10 i))))
	       (* 7 (/ (expt 10 i)))))
  :hints (("Goal"
	   :use ((:instance (:theorem (implies (and (realp x)
						    (realp y)
						    (realp z)
						    (< 0 z)
						    (<= (abs x) y))
					       (<= (abs (/ x z)) (/ y z))))
			    (x (- (digit-seq i) (digit-seq-2 i)))
			    (y 7)
			    (z (expt 10 i)))))))

(defthmd minimum-separation-of-middle
  (implies (and (posp i)
		(>= (abs (- (digit-seq i) (digit-seq-2 i))) 3))
	   (>= (abs (- (/ (digit-seq i) (expt 10 i)) (/ (digit-seq-2 i) (expt 10 i))))
	       (* 3 (/ (expt 10 i)))))
  :hints (("Goal"
	   :use ((:instance (:theorem (implies (and (realp x)
						    (realp y)
						    (realp z)
						    (< 0 z)
						    (>= (abs x) y))
					       (>= (abs (/ x z)) (/ y z))))
			    (x (- (digit-seq i) (digit-seq-2 i)))
			    (y 3)
			    (z (expt 10 i)))))))

(defthmd maximum-separation-of-suffix
  (implies (and (posp i)
		(posp max)
		(<= i max))
	   (<= (abs (- (digit-seq-sum (1+ i) max) (digit-seq-2-sum (1+ i) max)))
	       (* 2 (/ (expt 10 i)))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance digit-seq-sum-upper-bound (min (1+ i)))
		 (:instance digit-seq-2-sum-upper-bound (min (1+ i)))
		 (:instance triangle-inequality
			    (a (digit-seq-sum (1+ i) max))
			    (b (- (digit-seq-2-sum (1+ i) max))))
		 ))))



(defthmd different-enough-digits-implies-different-numbers
  (implies (and (posp i)
		(posp min)
		(posp max)
		(<= min i)
		(<= i max)
		(<= (abs (- (digit-seq i) (digit-seq-2 i))) 7)
		(>= (abs (- (digit-seq i) (digit-seq-2 i))) 3))
	   (<= (/ (expt 10 i))
	       (abs (- (digit-seq-sum min max)
		       (digit-seq-2-sum min max)))))
  :hints (("Goal" :do-not-induct t
	   :cases ((equal (digit-seq-sum min (1- i))
			  (digit-seq-2-sum min (1- i)))))
	  ("Subgoal 2"
	   :use ((:instance minimum-separation-of-prefix)
		 (:instance maximum-separation-of-middle)
		 (:instance maximum-separation-of-suffix)
		 (:instance different-enough-digits-implies-different-numbers-lemma-1
			    (a (- (digit-seq-sum min (1- i))
				  (digit-seq-2-sum min (1- i))))
			    (b (- (/ (digit-seq i) (expt 10 i)) (/ (digit-seq-2 i) (expt 10 i))))
			    (c (- (digit-seq-sum (1+ i) max) (digit-seq-2-sum (1+ i) max)))
			    (d (/ (expt 10 i))))
		 (:instance digit-sum-difference-split))
	   :in-theory (disable abs))
	  ("Subgoal 1"
	   :use ((:instance minimum-separation-of-middle)
		 (:instance maximum-separation-of-suffix)
		 (:instance different-enough-digits-implies-different-numbers-lemma-2
			    (b (- (/ (digit-seq i) (expt 10 i)) (/ (digit-seq-2 i) (expt 10 i))))
			    (c (- (digit-seq-sum (1+ i) max) (digit-seq-2-sum (1+ i) max)))
			    (d (/ (expt 10 i))))
		 (:instance digit-sum-difference-split))
	   :in-theory (disable abs))))

(include-book "nonstd/nsa/nsa" :dir :system)

(defthm digit-seq-sum-limited
  (implies (posp max)
	   (i-limited (digit-seq-sum 1 max)))
  :hints (("Goal"
	   :use ((:instance large-if->-large
			    (x (digit-seq-sum 1 max))
			    (y 1))
		 (:instance digit-seq-sum-upper-bound
			    (min 1)
			    (max max))))))

(defthm digit-seq-2-sum-limited
  (implies (posp max)
	   (i-limited (digit-seq-2-sum 1 max)))
  :hints (("Goal"
	   :by (:functional-instance digit-seq-sum-limited
				     (digit-seq-sum digit-seq-2-sum)
				     (digit-seq digit-seq-2)))))


(defun-std digit-seq-sum-limit ()
  (standard-part (digit-seq-sum 1 (i-large-integer))))

(defun-std digit-seq-2-sum-limit ()
  (standard-part (digit-seq-2-sum 1 (i-large-integer))))

(defthmd expt-grows-quickly
  (implies (natp n)
	   (<= n (expt 10 n))))

(defthm expt-of-large-integer-is-large
  (implies (and (natp n)
		(i-large n))
	   (i-large (expt 10 n)))
  :hints (("Goal"
	   :use ((:instance expt-grows-quickly)))))

(defthmd digit-seq-sum-converges-lemma
  (implies (and (posp min)
		(posp max)
		(i-large min)
		(i-large max)
		(<= min max))
	   (i-small (digit-seq-sum min max)))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance digit-seq-sum-upper-bound)
		 (:instance expt-of-large-integer-is-large
			    (n (1- min)))
		 (:instance limited*large->large
			    (x (digit-seq-sum min max))
			    (y (expt 10 (1- min))))
		 (:instance large-if->-large
			    (x (* (expt 10 (+ -1 min))
				  (digit-seq-sum min max)))
			    (y 1))
		 )
	   :in-theory (disable digit-seq-sum-upper-bound
			       expt-of-large-integer-is-large
			       limited*large->large
			       large*limited->large
			       large-if->-large
			       digit-seq-sum))))

(defthmd digit-seq-sum-split-2
  (implies (and (posp min)
		(posp max)
		(posp i)
		(<= min i)
		(<= i max))
	   (equal (digit-seq-sum min max)
		  (+ (digit-seq-sum min i)
		     (digit-seq-sum (1+ i) max)))))


(defthmd digit-seq-sum-converges
  (implies (and (posp max1)
		(posp max2)
		(i-large max1)
		(i-large max2)
		(<= max1 max2))
	   (i-close (digit-seq-sum 1 max1)
		    (digit-seq-sum 1 max2)))
  :hints (("Goal"
	   :use ((:instance digit-seq-sum-split-2
			    (min 1)
			    (i max1)
			    (max max2))
		 (:instance digit-seq-sum-converges-lemma
			    (min (1+ max1))
			    (max max2)))
	   :in-theory (enable i-close)
	   )))


(defthmd digit-seq-2-sum-converges
  (implies (and (posp max1)
		(posp max2)
		(i-large max1)
		(i-large max2)
		(<= max1 max2))
	   (i-close (digit-seq-2-sum 1 max1)
		    (digit-seq-2-sum 1 max2)))
  :hints (("Goal"
	   :by (:functional-instance digit-seq-sum-converges
				     (digit-seq-sum digit-seq-2-sum)
				     (digit-seq digit-seq-2)))))

(defthm standard-part-abs
  (implies (realp x)
	   (equal (standard-part (abs x))
		  (abs (standard-part x)))))

(defthm limited-<-large-integer
  (implies (and (posp i)
		(standardp i))
	   (< i (i-large-integer)))
  :hints (("Goal"
	   :use ((:instance large->-non-large
			    (x (i-large-integer))
			    (y i)))
	   :in-theory (disable large->-non-large))))

(defthm realp-abs
  (implies (realp x)
	   (realp (abs x)))
  :rule-classes (:rewrite :type-prescription))

(defthm-std standard-expt
  (implies (and (standardp x)
		(standardp y))
	   (standardp (expt x y))))

(defthm-std different-enough-digits-implies-different-numbers-of-limit-lemma
  (implies (and (posp i)
		(<= (abs (- (digit-seq i) (digit-seq-2 i))) 7)
		(>= (abs (- (digit-seq i) (digit-seq-2 i))) 3))
	   (<= (/ (expt 10 i))
	       (abs (- (digit-seq-sum-limit)
		       (digit-seq-2-sum-limit)))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable abs))
	  ("Goal''"
	   :use ((:instance different-enough-digits-implies-different-numbers
			    (min 1)
			    (max (i-large-integer))))
	   :in-theory (disable abs))
	  ("Subgoal 2"
	   :use ((:instance limited-<-large-integer))
	   :in-theory (disable limited-<-large-integer))
	  ("Subgoal 1"
	   :use ((:instance standard-part-<=
			    (x (/ (expt 10 i)))
			    (y (abs (+ (- (digit-seq-2-sum 1 (i-large-integer)))
				       (digit-seq-sum 1 (i-large-integer)))))))
	   :in-theory (disable standard-part-<= abs))
	  )
  )

(defthm different-enough-digits-implies-different-numbers-of-limit
  (implies (and (posp i)
		(<= (abs (- (digit-seq i) (digit-seq-2 i))) 7)
		(>= (abs (- (digit-seq i) (digit-seq-2 i))) 3))
	   (not (equal (digit-seq-sum-limit)
		       (digit-seq-2-sum-limit))))
  :hints (("Goal"
	   :use ((:instance different-enough-digits-implies-different-numbers-of-limit-lemma))
	   :in-theory (disable different-enough-digits-implies-different-numbers-of-limit-lemma))))


(defun nth-digit (num n)
  (declare (xargs :guard (and (realp num) (posp n))))
  (mod (floor (* num (expt 10 n)) 1) 10))

(defun m-pi ()
  314159265358979323846/100000000000000000000)

(verify-guards m-pi)

(defun nth-digit-of-pi (n)
  (declare (xargs :guard (posp n)))
  (nth-digit (m-pi) n))

(defattach digit-seq nth-digit-of-pi)

(defun nth-digit-seq-sum (num min max)
  (declare (xargs :measure (nfix (- (1+ max) min))))
  (if (and (posp min)
	   (posp max)
	   (<= min max))
      (+ (/ (nth-digit num min) (expt 10 min))
	 (nth-digit-seq-sum num (1+ min) max))
    0))

#|

(defun nth-digit-seq-sum-alt (num min max)
  (declare (xargs :measure (nfix (- (1+ max) min))))
  (if (and (posp min)
	   (posp max)
	   (<= min max))
      (+ (nth-digit num min)
	 (/ (nth-digit-seq-sum-alt num (1+ min) max)
	    10))
    0))

(defthmd nth-digit-seq-sum-regular-to-alt
  (implies (and (posp min)
		(posp max))
	   (equal (nth-digit-seq-sum num min max)
		   (/ (nth-digit-seq-sum-alt num min max)
		      (expt 10 min))))
  :hints (("Goal"
	   :by (:functional-instance digit-seq-sum-regular-to-alt
				     (digit-seq-sum (lambda (min max) (nth-digit-seq-sum num min max)))
				     (digit-seq-sum-alt (lambda (min max) (nth-digit-seq-sum-alt num min max)))
				     (digit-seq (lambda (n) (nth-digit num n)))))))

(defthmd denominator-posp
  (implies (posp n)
	   (equal (denominator (/ n))
		  n))
  :hints (("Goal"
	   :use ((:instance Rational-implies2
			    (x (/ n))))
	   :in-theory (disable Rational-implies2))))

|#

(defthmd mod-floor-difference
  (implies (and (posp n)
		(realp x))
	   (equal (mod (floor x 1) 10)
		  (- (floor x 1)
		     (* 10 (floor (/ x 10) 1)))
		  )))

(defthmd nth-digit-seq-sum-and-nth-digit-are-inverses-lemma
  (implies (and (posp min)
		(posp max)
		(<= min max)
		(realp num)
		(<= 0 num)
		(< num 1))
	   (equal (nth-digit-seq-sum num min max)
		  (- (/ (floor (* num (expt 10 max)) 1)
			(expt 10 max))
		     (/ (floor (* num (expt 10 (1- min))) 1)
			(expt 10 (1- min)))
		     )))
  :hints (("Goal" :do-not-induct t
	   :induct (nth-digit-seq-sum num min max)
	   )
	  ("Subgoal *1/2"
	   :use ((:instance mod-floor-difference
			    (n max)
			    (x (* num (expt 10 max))))))
	  ("Subgoal *1/1"
	   :use ((:instance mod-floor-difference
			    (n min)
			    (x (* num (expt 10 min))))))
	  )
  )

(defthmd nth-digit-seq-sum-and-nth-digit-are-inverses-lemma-min-1
  (implies (and (posp max)
		(realp num)
		(<= 0 num)
		(< num 1))
	   (equal (nth-digit-seq-sum num 1 max)
		  (/ (floor (* num (expt 10 max)) 1)
		     (expt 10 max))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance nth-digit-seq-sum-and-nth-digit-are-inverses-lemma (min 1))))))

(defthmd maximum-floor-quotient-difference-1
  (implies (and (realp x)
		(realp y)
		(< 0 y)
		)
	   (< (- x (/ (floor (* x y) 1) y))
	      (/ y))))

(defthmd maximum-floor-quotient-difference-2
  (implies (and (realp x)
		(realp y)
		(< 0 y)
		)
	   (<= (/ (floor (* x y) 1) y)
	       x)))

(defthmd nth-digit-seq-sum-and-nth-digit-are-inverses-std
  (implies (and (posp max)
		(realp num)
		(<= 0 num)
		(< num 1))
	   (< (abs (- num (nth-digit-seq-sum num 1 max)))
	      (/ (expt 10 max))))
  :hints (("Goal"
	   :use ((:instance nth-digit-seq-sum-and-nth-digit-are-inverses-lemma-min-1)
		 (:instance maximum-floor-quotient-difference-1
			    (x num)
			    (y (expt 10 max)))
		 (:instance maximum-floor-quotient-difference-2
			    (x num)
			    (y (expt 10 max)))))))


(defthmd nth-digit-seq-sum-upper-bound
  (implies (and (posp min)
		(posp max)
		(<= min max))
	   (< (nth-digit-seq-sum num min max)
	      (/ (expt 10 (1- min)))))
  :hints (("Goal" :do-not-induct t
	   :by (:functional-instance digit-seq-sum-upper-bound
				     (digit-seq-sum (lambda (min max) (nth-digit-seq-sum num min max)))
				     (digit-seq (lambda (n) (nth-digit num n)))))))

(defthm nth-digit-seq-sum-limited
  (implies (posp max)
	   (i-limited (nth-digit-seq-sum num 1 max)))
  :hints (("Goal"
	   :use ((:instance large-if->-large
			    (x (nth-digit-seq-sum num 1 max))
			    (y 1))
		 (:instance nth-digit-seq-sum-upper-bound
			    (min 1)
			    (max max))))))

(defun-std nth-digit-seq-sum-limit (num)
  (standard-part (nth-digit-seq-sum num 1 (i-large-integer))))


(defthmd nth-digit-seq-sum-converges-lemma
  (implies (and (posp min)
		(posp max)
		(i-large min)
		(i-large max)
		(<= min max)
		(realp num))
	   (i-small (nth-digit-seq-sum num min max)))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance nth-digit-seq-sum-upper-bound)
		 (:instance expt-of-large-integer-is-large
			    (n (1- min)))
		 (:instance limited*large->large
			    (x (nth-digit-seq-sum num min max))
			    (y (expt 10 (1- min))))
		 (:instance large-if->-large
			    (x (* (expt 10 (+ -1 min))
				  (nth-digit-seq-sum num min max)))
			    (y 1))
		 )
	   :in-theory (disable nth-digit-seq-sum-upper-bound
			       expt-of-large-integer-is-large
			       limited*large->large
			       large*limited->large
			       large-if->-large
			       nth-digit-seq-sum))))

(defthmd nth-digit-seq-sum-split-2
  (implies (and (posp min)
		(posp max)
		(posp i)
		(<= min i)
		(<= i max)
		(realp num))
	   (equal (nth-digit-seq-sum num min max)
		  (+ (nth-digit-seq-sum num min i)
		     (nth-digit-seq-sum num (1+ i) max))))
  :hints (("Goal"
	   :use ((:functional-instance digit-seq-sum-split-2
				       (digit-seq (lambda (n) (nth-digit num n)))
				       (digit-seq-sum (lambda (min max) (nth-digit-seq-sum num min max))))))))

(defthmd nth-digit-seq-sum-converges
  (implies (and (posp max1)
		(posp max2)
		(i-large max1)
		(i-large max2)
		(<= max1 max2)
		(realp num))
	   (i-close (nth-digit-seq-sum num 1 max1)
		    (nth-digit-seq-sum num 1 max2)))
  :hints (("Goal"
	   :use ((:instance nth-digit-seq-sum-split-2
			    (min 1)
			    (i max1)
			    (max max2))
		 (:instance nth-digit-seq-sum-converges-lemma
			    (min (1+ max1))
			    (max max2)))
	   :in-theory (enable i-close)
	   )))

(defthmd small-diff-implies-close
  (implies (and (realp x)
		(realp y)
		(realp eps)
		(i-small eps)
		(< (abs (- x y)) eps))
	   (i-close x y))
  :hints (("Goal"
	   :in-theory (enable i-close))))

(defthm abs-close-same-standard-part
  (implies (and (realp x)
		(standardp x)
		(realp y)
		(realp eps)
		(i-small eps)
		(< (abs (- x y)) eps))
	   (equal (standard-part y) x))
  :hints (("Goal"
	   :use ((:instance close-x-y->same-standard-part
			    (x x)
			    (y y))
		 (:instance i-close-to-small-sum)
		 (:instance small-diff-implies-close)
		 )))
  :rule-classes nil)




(defthm-std nth-digit-seq-sum-and-nth-digit-are-inverses
  (implies (and (realp num)
		(<= 0 num)
		(< num 1))
	   (equal (nth-digit-seq-sum-limit num) num))
  :hints (("Goal''"
	   :use ((:instance nth-digit-seq-sum-and-nth-digit-are-inverses-std
			    (num num)
			    (max (i-large-integer)))
		 (:instance abs-close-same-standard-part
			    (x num)
			    (y (NTH-DIGIT-SEQ-SUM NUM 1 (I-LARGE-INTEGER)))
			    (eps (/ (expt 10 (i-large-integer)))))))))

(encapsulate
 ( ((seq *) => * :formals (n) :guard (posp n)) )

 (local (defun seq (n)
	  (declare (xargs :guard (posp n))
		   (ignore n))
	  0))

 (defthm seq-is-real
   (implies (posp n)
	    (realp (seq n)))
   :rule-classes (:rewrite :type-prescription))

 (defthm seq-bounded
   (implies (posp n)
	    (and (<= 0 (seq n))
		 (< (seq n) 1))))
 )

(defun diag-seq (n)
  (if (posp n)
      (if (< (nth-digit (seq n) n) 5)
	  7
	2)
    0))

(defthm diag-digits-are-different-enough
  (implies (posp i)
	   (and (<= (abs (- (diag-seq i) (nth-digit (seq i) i))) 7)
		(>= (abs (- (diag-seq i) (nth-digit (seq i) i))) 3))))


(defun diag-seq-sum (min max)
  (declare (xargs :measure (nfix (- (1+ max) min))))
  (if (and (posp min)
	   (posp max)
	   (<= min max))
      (+ (/ (diag-seq min) (expt 10 min))
	 (diag-seq-sum (1+ min) max))
    0))

(defthm diag-seq-sum-limited
  (implies (posp max)
	   (i-limited (diag-seq-sum 1 max)))
  :hints (("Goal" :do-not-induct t
	   :by (:functional-instance digit-seq-sum-limited
				     (digit-seq-sum diag-seq-sum)
				     (digit-seq diag-seq)))))

(defun-std diag-seq-sum-limit ()
  (standard-part (diag-seq-sum 1 (i-large-integer))))

(defthmd diag-seq-sum-converges
  (implies (and (posp max1)
		(posp max2)
		(i-large max1)
		(i-large max2)
		(<= max1 max2))
	   (i-close (diag-seq-sum 1 max1)
		    (diag-seq-sum 1 max2)))
  :hints (("Goal"
	   :by (:functional-instance digit-seq-sum-converges
				     (digit-seq-sum diag-seq-sum)
				     (digit-seq diag-seq)))))

(defthm different-enough-digits-implies-different-numbers-of-limit
  (implies (and (posp i)
		(<= (abs (- (digit-seq i) (digit-seq-2 i))) 7)
		(>= (abs (- (digit-seq i) (digit-seq-2 i))) 3))
	   (not (equal (digit-seq-sum-limit)
		       (digit-seq-2-sum-limit))))
  :hints (("Goal"
	   :use ((:instance different-enough-digits-implies-different-numbers-of-limit-lemma))
	   :in-theory (disable different-enough-digits-implies-different-numbers-of-limit-lemma))))


(local
 (defun posfix (i)
   (if (posp i)
       i
     1)))

(local
 (defthm-std standard-seq
   (implies (standardp i)
            (standardp (seq i)))))

#|
TODO: This theorem no longer works.  The substitution

    digit-seq-2-sum-limit -> (lambda () (seq (posfix i)))

is causing problems with the new algorithm for finding constraints (which
fixed the soundness bug related to missing constraints on defun-std functions).

(defthm diag-seq-sum-limit-not-in-sequence
  (and (realp (diag-seq-sum-limit))
       (implies (posp i)
		(not (equal (diag-seq-sum-limit) (seq i)))))
  :hints (("Goal"
	   :use ((:functional-instance different-enough-digits-implies-different-numbers-of-limit
				       (digit-seq diag-seq)
				       (digit-seq-sum diag-seq-sum)
				       (digit-seq-sum-limit diag-seq-sum-limit)
				       (digit-seq-2 (lambda (n) (nth-digit (seq (posfix i)) n)))
				       (digit-seq-2-sum (lambda (min max) (nth-digit-seq-sum (seq (posfix i)) min max)))
				       (digit-seq-2-sum-limit (lambda () (seq (posfix i)))))
		 (:instance diag-digits-are-different-enough)))
          ("Subgoal 3"
           :use ((:instance nth-digit-seq-sum-and-nth-digit-are-inverses
			    (num (seq (posfix i)))))
           :in-theory (disable nth-digit-seq-sum-and-nth-digit-are-inverses))
          ))


(defun-sk exists-in-sequence (x)
  (exists i
	  (and (posp i)
	       (equal (seq i) x))))

(defun-sk exists-in-interval-but-not-in-sequence ()
  (exists x
	  (and (realp x)
	       (not (exists-in-sequence x)))))

(in-theory (disable diag-seq-sum-limit))

(defthm diag-seq-not-in-sequence
  (not (exists-in-sequence (diag-seq-sum-limit))))

(defthm reals-are-not-countable
  (exists-in-interval-but-not-in-sequence)
  :hints (("Goal"
	   :use ((:instance exists-in-interval-but-not-in-sequence-suff
			    (x (diag-seq-sum-limit)))))))
|#
