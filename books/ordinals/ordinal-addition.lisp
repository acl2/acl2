;definitions and theorems about ordinal arithmetic
(in-package "ACL2")
(include-book "ordinal-basic-thms")
(local (include-book "top-with-meta"))
(local (disable-forcing))

(local (in-theory (disable o<)))

(defthm o+-o-finp
  (implies (and (o-finp a)
		(o-finp b))
	   (o-finp (o+ a b)))
  :rule-classes ((:type-prescription)
                 (:forward-chaining  :trigger-terms ((o+ a b)))))

#|

(defthm o+-atomic-2
  (implies (and (posp a)
		(natp b))
	   (posp (o+ a b)))
  :rule-classes ((:type-prescription)
                 (:forward-chaining :trigger-terms ((o+ a b)))))

|#

(defthm o-infp-o+
  (implies (and (o< 0 (o-first-expt a))
                (o-infp a))
	   (o-infp (o+ a b)))
  :rule-classes ((:forward-chaining :trigger-terms ((o+ a b)))
                 (:rewrite)))

(defthm o-infp-o+-2
  (implies (and (o< 0 (o-first-expt b))
                (o-infp b))
           (o-infp (o+ a b)))
  :rule-classes ((:forward-chaining  :trigger-terms ((o+ a b)))
                 (:rewrite)))

#|
(defthm not-o-finp-o-infp-fc
  (equal (not (o-finp a))
	 (o-infp a))
  :rule-classes ((:forward-chaining :trigger-terms ((o-finp a)))))
|#

(defthm o-infp-o+-3
  (implies (and (o-infp a)
		(o-infp b))
	   (o-infp (o+ a b)))
  :rule-classes ((:forward-chaining  :trigger-terms ((o+ a b)))
                 (:rewrite)))

(defthm o+-o-first-expt-1
  (implies (o< (o-first-expt a)
	       (o-first-expt b))
	   (equal (o-first-expt (o+ a b))
		  (o-first-expt b))))

(defthm o+-o-first-expt-2
  (implies (and (o<= (o-first-expt b)
		     (o-first-expt a))
                (o-p a)
		(o-p b))
	   (equal (o-first-expt (o+ a b))
		  (o-first-expt a))))

(defthm o+-o-first-coeff-1
 (implies (and (o< (o-first-expt a)
		   (o-first-expt b))
               (o-p a)
	       (o-p b))
	  (equal (o-first-coeff (o+ a b))
		 (o-first-coeff b))))

(defthm o+-o-first-coeff-2
  (implies (and (o< (o-first-expt b)
		    (o-first-expt a))
                (o-p a)
		(o-p b))
	   (equal (o-first-coeff (o+ a b))
		  (o-first-coeff a)))
  :hints (("goal"
	   :expand (o+ a b))))

(defthm o+-o-first-coeff-3
  (implies (and (equal (o-first-expt a)
		       (o-first-expt b))
                (o-p b))
	   (equal (o-first-coeff (o+ a b))
		  (+ (o-first-coeff a) (o-first-coeff b)))))

(defthm o-first-expt-o+-<
 (implies (and (o-p a)
	       (o-p b)
	       (o-p c))
	  (equal (o< (o-first-expt (o+ b c))
                     (o-first-expt a))
                 (and (o< (o-first-expt b)
                          (o-first-expt a))
                      (o< (o-first-expt c)
                          (o-first-expt a)))))
 :hints (("goal" :cases ((o< (o-first-expt b) (o-first-expt c))))))

(defthm o-p-o+
  (implies (and (o-p b)
		(o-p a))
	   (o-p (o+ b a))))

(verify-guards ob+)

(defthm |a+0 = a|
  (implies (o-p a)
           (equal (o+ a 0) a)))

(defthm |0+a = a|
  (implies (o-p a)
           (equal (o+ 0 a) a)))

#|
; Notice that <= is <= on numbers.
(defthm |0 <= a+b|
  (implies (and (o-p a)
                (o-p b))
           (<= 0 (o+ a b))))
|#

(defthm |a < a+1|
  (implies (o-p a)
           (o< a (o+ a 1))))

#|
(local
 (defun add-ind-1 (a b)
   (if (consp a)
       (add-ind-1 (cdr a) b)
     (list a b))))
|#

(defthm |a < b  <=>  a+1 <= b|
  (implies (and (o-p a)
                (o-p b))
           (equal (o<= (o+ a 1) b)
                  (o< a b)))
  :hints (("goal"
	   :in-theory (enable o<)
	   :induct (o< a b)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (and (o-p a)
                                (o-p b))
                           (equal (o< b (o+ a 1))
                                  (o<= b a))))))

(defthm |a < b+1  <=>  a <= b|
  (implies (and (o-p a)
                (o-p b))
           (equal (o< a (o+ b 1))
		  (o<= a b)))
  :hints (("goal"
	   :in-theory (enable o<)
	   :induct (o< a b))))

(defthm |a <= b+a|
  (implies (and (o-p a)
		(o-p b))
	   (o<= a (o+ b a)))
  :hints (("goal" :in-theory (enable o<))))

(encapsulate
 ()

 (local
  (defthm |a < a+b  <=>  ~(0 = b) :l1|
    (implies (and (o<= (o-first-expt b) (o-first-expt a))
		  (o<= (o-first-expt a) (o-first-expt b))
                  (not (o-finp a))
                  (o-p a)
		  (o-p b))
	     (o< a
		 (make-ord (o-first-expt a)
			   (+ (o-first-coeff a) (o-first-coeff b))
			   (o-rst b))))
    :hints (("goal"
	     :use ((:instance o-first-coeff-<
			      (b (make-ord (o-first-expt a)
					   (+ (o-first-coeff a) (o-first-coeff b))
					   (o-rst b)))))))))

 (defthm |a < a+b  <=>  ~(0 = b)| ;|a <= a+b|
   (implies (and (o-p a)
		 (o-p b))
	    (equal (o< a (o+ a b))
		   (not (equal b 0))))))

(defthm |a+b = 0  <=>  a=0 & b=0|
  (implies (and (o-p a)
                (o-p b))
           (equal (equal 0 (o+ a b))
                  (and (equal a 0)
                       (equal b 0)))))

(defthm o+-o-first-expt-smash
  (implies (o< (o-first-expt a)
	       (o-first-expt b))
	   (equal (o+ a b) b)))

(defthm o+-o-first-expt-smash-2
  (implies (and (o< (o-first-expt b) (o-first-expt a))
                (o-p a)
		(o-p b)
		(o-p c))
	   (equal (equal a (o+ b c))
		  (equal a c))))

(defthm o-first-expt-<-o+
  (implies (and (o-p b)
		(o-p c))
	   (equal (o< (o-first-expt a)
		      (o-first-expt (o+ b c)))
		  (or (o< (o-first-expt a)
			  (o-first-expt b))
		      (o< (o-first-expt a)
			  (o-first-expt c)))))
  :hints (("goal"
	   :cases ((o< (o-first-expt b)
		       (o-first-expt c))))))

(encapsulate

; This encapsulate is here just so that we do not have to give a
; subgoal hint to |(a+b)+c = a+(b+c)|.

 nil

 (local
  (defthm |(a+b)+c = a+(b+c) helper|
    (implies (and (not (o< (o-first-expt c) (o-first-expt a)))
                  (o-p a)
                  (o-p b)
                  (o-p c))
             (equal (o+ (o+ a b) c)
                    (o+ a (o+ b c))))
    :hints (("goal"
             :cases ((o< (o-first-expt b) (o-first-expt c))
                     (o< (o-first-expt c) (o-first-expt b)))))))

 (local
  (defun o+-induct (a b c)
    (if (and (o-p a)
	     (o-p b)
	     (o-p c)
	     (o< (o-first-expt b) (o-first-expt a))
	     (o< (o-first-expt c) (o-first-expt a)))
	(o+-induct (o-rst a) b c)
      (list a b c))))

 (defthm |(a+b)+c = a+(b+c)|
   (implies (and (o-p a)
                 (o-p b)
                 (o-p c))
            (equal (o+ (o+ a b) c)
                   (o+ a (o+ b c))))
   :hints (("goal"
            :induct (o+-induct a b c)))))



(defthm |a-a = 0|
  (equal (o- a a) 0))

(defthm o-p-o-
  (implies (and (o-p a)
                (o-p b))
           (o-p (o- a b)))
  :rule-classes ((:forward-chaining :trigger-terms ((o- a b)))))

(defthm |a-b <= a|
  (implies (and (o-p a)
                (o-p b))
           (o<= (o- a b) a))
  :hints (("goal"
	   :in-theory (enable o<)
           :induct (o- a b)))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((o- a b)))))

(defthm bad
  (implies (and (o<= a b)
                (o-p a)
                (o-p b))
           (o<= (o-first-expt a) (o-first-expt b)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((o< (o-first-expt a) (o-first-expt b))))))

#|
(defthm o--o-first-expt
  (implies (and (o-p a)
		(o-p b))
	   (not (o< (o-first-expt a)
		    (o-first-expt (o- a b))))))
|#

; The hints are not really needed, but they speed up the book.
(defthm o-first-expt-o--<
 (implies (and (o< (o-first-expt b) (o-first-expt a))
               (o-p a)
	       (o-p b)
	       (o-p c))
	  (o< (o-first-expt (o- b c))
	      (o-first-expt a)))
 :hints (("goal"
	  :in-theory
	  (disable |a <= b & b < c  =>  a < c|)
	  :use ((:instance |a <= b & b < c  =>  a < c|
			   (a (o-first-expt (o- b
					     c)))
			   (b (o-first-expt b))
			   (c (o-first-expt a)))))))

(local (in-theory (disable |a <= b & b <= c  =>  a <= c| ;; speed hint
                           |a <= b & b <= c  =>  a <= c|
                           |a < b & b <= c  =>  a < c|
                           |a <= b & b <= c  =>  a <= c|
                           |a <= b & b < c  =>  a < c|
                           |b <= a & a <= b  =>  a = b|
                           |a <= b  =>  (a < b <=> ~(a = b))|)))
(encapsulate
 ()
 (local (in-theory (enable o<)))
 (local (in-theory (disable make-ord-o<-3)))
 (local
  (defthm |a <= b  =>  a+(b-a) = b :l1|
    (implies (and (equal c (o-first-expt a))
                  (o-infp a)
                  (o-p a)
		  (o-p b))
	     (o< (o-first-expt (o- (o-rst a) b)) c))
  :hints (("goal"
	   :use ((:instance o-first-expt-o--<
			    (b (o-rst a))
			    (c b)))))))

 (defthm |a <= b  =>  a+(b-a) = b|
   (implies (and (o-p a)
		 (o-p b)
		 (o<= a b))
	    (equal (o+ a (o- b a))
		   b))))

(encapsulate
 ()
 (defthm |a < b  <=>  c+a < c+b :l1|
   (implies (and (natp a) (natp b) (natp c))
	    (equal (o< (+ a c) (+ b c)) (o< a b)))
   :hints (("goal"
	    :cases ((< a b)))))

 (defthm |a < b  <=>  c+a < c+b|
   (implies (and (o-p a)
		 (o-p b)
		 (o-p c))
	    (equal (o< (o+ c a)
		       (o+ c b))
		   (o< a b)))))

#|
The following theorem is worthless, since if you rewrite it as a
corollary, you get the above rule.
|#

(defthm |a <= b  <=>  c+a <= c+b|
   (implies (and (o-p a)
		 (o-p b)
		 (o-p c))
	    (equal (o<= (o+ c a)
			(o+ c b))
		   (o<= a b)))
   :rule-classes nil)

(defthm |a <= b  =>  a+c <= b+c|
  (implies (and (o<= a b)
		(o-p a)
		(o-p b)
		(o-p c))
	   (o<= (o+ a c) (o+ b c)))
  :hints (("goal"
	   :in-theory (enable o<
                              |a <= b & b <= c  =>  a <= c|
                              ))))

(defthm |a <= b & c < d  =>  a+c < b+d|
  (implies (and (o<= a b)
		(o< c d)
		(o-p a)
		(o-p b)
		(o-p c)
		(o-p d))
	   (o< (o+ a c) (o+ b d)))
  :hints (("goal"
	   :in-theory (disable |a <= b & b < c  =>  a < c|)
	   :use ((:instance |a <= b & b < c  =>  a < c|
			    (a (o+ a c))
			    (b (o+ b c))
			    (c (o+ b d)))))))

(defthm |a <= b & c <= d  =>  a+c <= b+d|
  (implies (and (o<= a b)
		(o<= c d)
		(o-p a)
		(o-p b)
		(o-p c)
		(o-p d))
	   (o<= (o+ a c) (o+ b d)))
  :hints (("goal" :use |a <= b & c < d  =>  a+c < b+d|
           :in-theory (enable |a <= b & b <= c  =>  a <= c|
                              |a < b & b <= c  =>  a < c|
                              |a <= b & b < c  =>  a < c|
                              |b <= a & a <= b  =>  a = b|
                              ))))

(defthm |c+a = b  =>  b-c = a|
  (implies (and (equal (o+ c a) b)
                (o-p a)
                (o-p b)
                (o-p c))
           (equal (o- b c) a))
  :rule-classes :forward-chaining)

(defthm |(b+a)-b = a|
  (implies (and (o-p a)
                (o-p b))
           (equal (o- (o+ b a) b)
                  a)))

(defthm |c+a = c+b  <=>  a=b|
  (implies (and (o-p a)
                (o-p b)
                (o-p c))
           (equal (equal (o+ c a)
                         (o+ c b))
                  (equal a b))))

(defthm o--0
 (implies (o< a b)
	  (equal (o- a b) 0))
 :hints (("goal"
	  :in-theory (enable o<))))


(defthm |a <= b  <=>  b-a = 0|
 (implies (and (o-p a)
	       (o-p b))
	  (equal (equal (o- b a) 0)
		 (o<= b a)))
 :hints (("goal"
	  :in-theory (enable o<))))

(defthm |a-c <= a+b|
  (implies (and (o-p a)
		(o-p b)
		(o-p c))
	   (o<= (o- a c)
		(o+ b a)))
  :hints (("goal"
	   :use ((:instance |a <= b & b <= c  =>  a <= c|
			    (a (o- a c))
			    (b a)
			    (c (o+ b a)))))))

(defthm |(b > 1)  =>  (a < b  <=>  a-1 < b-1|
   (implies (and (not (equal b 1))
                 (o-p a)
		 (o-p b))
	    (equal (o< (o- a 1)
		       (o- b 1))
		   (o< a b)))
   :hints (("goal"
	    :in-theory (enable o<))))

(verify-guards o-)

(defthm o+-atom-def
  (implies (and (atom a)
		(atom b))
	   (equal (o+ a b) (+ a b))))

(defthm o+-o-rst-1
  (implies (and (o< (o-first-expt b)
		    (o-first-expt a))
                (o-p a)
		(o-p b))
	   (equal (o-rst (o+ a b)) (o+ (o-rst a) b))))

(defthm o+-o-rst-2
  (implies (and (not (o< (o-first-expt b)
			 (o-first-expt a)))
                (o-p a)
		(o-p b))
	   (equal (o-rst (o+ a b)) (o-rst b))))

(defthm natpart-o+
  (implies (and (o-infp b)
		(o-p a)
		(o-p b))
	   (equal (natpart (o+ a b)) (natpart b))))


(defthm o+-consp-def-1
  (equal (o+ (make-ord x a2 a3)
             (make-ord x b2 b3))
         (make-ord x (+ a2 b2) b3)))

(defthm o+-o-rst-equal
  (implies (and (o-infp a)
		(o-p a))
	   (equal (o+ (make-ord (o-first-expt a) (o-first-coeff a) 0)
		      (o-rst a))
		  a)))

(defthm o+-inf
  (implies (o-p (make-ord a b c))
	   (equal (o+ (make-ord a b 0) c)
		  (make-ord a b c))))

(local
 (defun limitpart-ind (a)
   (if (o-infp a)
       (limitpart-ind (o-rst a))
     0)))

(defthm limitpart-o-finp
  (equal (o-finp (limitpart a))
	 (o-finp a))
  :hints (("goal"
	   :cases ((o-finp a)))))

(defthm limitpart-natpart-o+
 (implies (o-p a)
	  (equal (o+ (limitpart a)
		     (natpart a))
		 a))
 :hints (("goal"
	  :induct (limitpart-ind a))))

(defthm limitp-o+
   (implies (and (o-p a)
		 (limitp b))
	    (limitp (o+ a b)))
   :hints (("goal"
	    :induct (o+ a b))))
