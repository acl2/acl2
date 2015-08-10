;definitions and theorems about ordinal arithmetic
(in-package "ACL2")
(include-book "ordinal-multiplication")
(local (include-book "top-with-meta"))
(local (disable-forcing))
(local (in-theory (disable o- o+ o* o<)))

(defthm |a^0 = 1|
  (equal (o^ a 0) 1))

(defthm |a^1 = a|
  (implies (o-p a)
	   (equal (o^ a 1) a)))

(defthm |~(0 = a)  <=>  0^a = 0|
  (implies (o-p a)
	   (equal (equal (o^ 0 a) 0)
		  (not (equal a 0)))))

(defthm |0 < a  =>  0^a = 0 :a|
  (implies (posp a)
	   (equal (o^ 0 a) 0))
  :rule-classes ((:type-prescription)))

(defthm |0 < a  =>  0^a = 0 :b|
  (implies (o-infp a)
	   (equal (o^ 0 a) 0))
  :rule-classes ((:type-prescription)))

(defthm |1^a = 1|
  (equal (o^ 1 a) 1))

(local
 (defthm |(a-1 = 0)  <=>  a <= 1|
   (implies (o-p a)
	    (equal (equal (o- a 1) 0)
		   (or (equal a 1)
		       (equal a 0))))
   :hints (("goal"
	    :in-theory (enable o-)))))

(defthm o-p-o^
  (implies (and (o-p a)
                (o-p b))
           (o-p (o^ a b)))
  :hints (("goal"
           :induct (o^ a b)))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((o^ a b)))))

(defthm |(a = 0) & ~(b = 0)  <=>  (a^b = 0)|
  (implies (and (o-p a)
                (o-p b))
           (equal (equal (o^ a b) 0)
                  (and (equal a 0)
                       (not (equal b 0)))))
  :hints (("goal"
           :induct (o^ a b))))

(defthm o^-^
  (implies (and (natp a)
                (natp b))
           (equal (o^ a b)
                  (expt a b))))

(defthm o-infp-o^-1
 (implies (and (not (equal b 0))
               (o-infp a)
	       (o-p a)
	       (o-p b))
	  (o-infp (o^ a b)))
 :hints (("goal"
	  :do-not-induct t
	  :expand (o^ a b)))
 :rule-classes ((:forward-chaining :trigger-terms ((o^ a b)))
		(:rewrite)))

(defthm o-infp-o^-2
  (implies (and (not (equal a 0))
		(not (equal a 1))
		(o-infp b)
		(o-p a)
		(o-p b))
	   (o-infp (o^ a b)))
  :hints (("goal"
	   :do-not-induct t
	   :expand (o^ a b)))
  :rule-classes ((:forward-chaining :trigger-terms ((o^ a b)))))

(defthm o^-o-finp
  (implies (and (o-finp b)
                (o-finp a))
           (o-finp (o^ a b)))
  :rule-classes :type-prescription)

(defthm o-infp-o^
  (implies (and (natp a)
                (o-p b))
           (equal (o-infp (o^ a b))
                  (and (o-infp b)
                       (not (equal a 0))
                       (not (equal a 1)))))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((o^ a b)))))

(encapsulate

 ; This encapsulate is here to remove a subgoal hint.

 nil

 (local
  (defthm o^-o-first-expt-helper
    (implies (and (o-infp b)
                  (o-infp a)
                  (equal (o-first-expt (o^ a (o-rst b)))
                         (o* (o-first-expt a) (o-rst b)))
                  (o-p a)
                  (o-p b))
             (equal (o+ (make-ord (o+ (o-first-expt (o-first-expt a))
				      (o-first-expt b))
				  (o-first-coeff b)
				  0)
                        (o-first-expt (o^ a (o-rst b))))
                    (o* (o-first-expt a) b)))
    :hints (("goal"
             :in-theory (disable |a(b + c) = ab + ac|)
             :use ((:instance |a(b + c) = ab + ac|
                              (a (o-first-expt a))
                              (b (first-term b))
                              (c (o-rst b))))))))

 (defthm o^-o-first-expt
   (implies (and (o-infp a)
		 (o-p a)
                 (o-p b))
           (equal (o-first-expt (o^ a b))
                  (o* (o-first-expt a)
                      b)))
  :hints (("goal"
           :induct (o^ a b)))))

(local
 (defthm |~(a=0)  =>  (a < b  <=>  a-1 < b-1)|
   (implies (and (o-p a)
		 (o-p b)
		 (not (equal a 0)))
	    (equal (o< (o- a 1)
		       (o- b 1))
		   (o< a b)))
   :hints (("goal"
	    :in-theory (enable o- o<)))))

(defthm |a < 1  <=> a = 0|
  (implies (o-p a)
	   (equal (o< a 1)
		  (equal a 0)))
  :hints (("goal"
	   :in-theory (enable o<)))
  :rule-classes ((:forward-chaining :trigger-terms ((o< a 1)))))

(defthm o^-o-first-expt-2
  (implies (and (natp a)
		(not (equal a 0))
		(not (equal a 1))
		(o-p b))
	   (equal (o-first-expt (o-first-expt (o^ a b)))
		  (o- (o-first-expt b) 1))))

(defthm o^-o-first-expt-3
  (implies (and (not (equal b 0))
                (o-infp a)
                (o-p a)
                (o-p b))
           (equal (o-first-expt (o-first-expt (o^ a b)))
                  (o+ (o-first-expt (o-first-expt a)) (o-first-expt b)))))

(defthm |o-first-expt(b) < o-first-expt(c)  =>  (a^b)*(a^c) = a^c|
    (implies (and (o-p a)
		  (o-p b)
		  (o-p c)
		  (o< (o-first-expt b)
		      (o-first-expt c)))
	     (equal (o* (o^ a b) (o^ a c))
		    (o^ a c)))
    :hints (("goal"
	     :do-not-induct t
	     :expand (o^ a c)
	     :cases ((and (not (equal b 0))
			  (o-infp a))))))

(local (in-theory (disable o^-o-first-expt)))

(encapsulate

 ;this encapsulate is here so the lemmas we used to prove |a^(b+c)  =  a^b * a^c|
 ;don't slow down the other proofs in the book.

 ()

 (local
  (defun exp-ind-1 (a b c)
    (if (o-finp b)
	(if (not (posp b))
	    (list a b c)
	  (exp-ind-1 a (- b 1) c))
      (list a b c))))

 ;this theorem is here so we don't have to give a subgoal hint to
 ;|a^(b+c)  =  a^b * a^c :b|
 (local
  (defthm |a^(b+c)  =  a^b * a^c :b helper|
    (implies (and (o-infp b)
		  (equal (o-first-expt c) 1)
		  (o-p a)
		  (o-p b)
		  (o-p c)
		  (not (equal a 1))
		  (not (equal a 0))
		  (o-finp a)
		  (equal (o-first-expt b) 1))
             (equal (o* (make-ord (+ (o-first-coeff b) (o-first-coeff c))
				  1
				  0)
			(o^ a (o-rst c)))
                    (o* (o* (make-ord (o-first-coeff b) 1 0)
			    (o^ a (o-rst b)))
			(o^ a c))))
    :hints (("goal"
	     :do-not-induct t
	     :expand (o^ a c)
             :in-theory (disable |o-first-expt(b) < o-first-expt(c)  =>  (a^b)*(a^c) = a^c|
	                         o*-o-first-expt-smash-2b)
             :use ((:instance o*-o-first-expt-smash-2b
			      (a (omega-term (o-first-coeff b) 1))
			      (b (expt a (o-rst b)))
			      (c (omega-term (o-first-coeff c) 1))
			      (d (o^ a (o-rst c))))
		   (:instance |o-first-expt(b) < o-first-expt(c)  =>  (a^b)*(a^c) = a^c|
                              (b (o-rst b))))))
    :rule-classes :forward-chaining))

 (defthm o^-o-first-expt-o-first-expt-o<
   (implies (and (not (equal a 0))
		 (not (equal a 1))
		 (o-infp a)
		 (o-p a)
		 (o-p b)
		 (o-p c)
		 (o< (o-first-expt b) c))
	    (o< (o-first-expt (o-first-expt (o^ a b)))
		(o+ (o-first-expt (o-first-expt a)) c)))
   :hints (("goal"
	    :in-theory (e/d (o^-o-first-expt) (o^))
	    :cases ((and (o-finp b)
			 (equal b 0))))))

 (local
  (defthm |a^(b+c)  =  a^b * a^c :a|
    (implies (and (equal (o-first-expt c)
			 (o-first-expt b))
		  (o-p a)
		  (o-p b)
		  (o-p c))
	     (equal (o^ a (o+ b c))
		    (o* (o^ a b) (o^ a c))))
    :hints (("goal"
	     :expand ((o^ a (o+ b c))
		      (o^ a b))
	     :induct (exp-ind-1 a b c)))
  :rule-classes :forward-chaining))

 (local
  (defthm |a^(b+c)  =  a^b * a^c :b|
    (implies (and (o-p a)
		  (o-p b)
		  (o-p c)
		  (not (o< (o-first-expt c)
			   (o-first-expt b))))
	     (equal (o^ a (o+ b c))
		    (o* (o^ a b) (o^ a c))))
  :hints (("goal"
	   :do-not-induct t
	   :cases ((o< (o-first-expt b) (o-first-expt c)))))))

 (local
  (defun exp-ind-2 (a b c)
    (if (and (o-infp b)
	     (o< (o-first-expt c)
		 (o-first-expt b)))
	(exp-ind-2 a (o-rst b) c)
      (list a b c))))

 (defthm |a^(b+c)  =  a^b * a^c|
   (implies (and (o-p a)
		 (o-p b)
		 (o-p c))
	    (equal (o^ a (o+ b c))
		   (o* (o^ a b) (o^ a c))))
   :hints (("goal"
	    :induct (exp-ind-2 a b c)))))

(defthm |(a^b = 1)  <=>  (a = 1) V (b = 0)|
  (implies (and (o-p a)
                (o-p b))
           (equal (equal (o^ a b) 1)
		  (or (equal a 1)
		      (equal b 0)))))

(defthm o-+
 (implies (and (not (equal a 0))
	       (o-p a)
	       (o-p b))
	  (equal (o- (o+ a b) 1)
                 (o+ (o- a 1) b)))
 :hints (("goal"
	  :in-theory (enable o- o+))))

(encapsulate

 ;this encapsulate is here so the lemmas used to prove |a^(bc) = (a^b)^c|
 ;don't slow down the other proofs in the book.

 ()
 (local (in-theory (enable o^-o-first-expt)))

 (local
  (encapsulate

   ;this encapsulate is here because |a^(bc) = (a^b)^c :a lemma 3| causes problems
   ;with the proof of |a^(bc) = (a^b)^c|

   ()
   (local (in-theory (enable o^-o-first-expt)))

   (local
    (defthm |a^(bc) = (a^b)^c :a lemma 1a|
      (implies (and (o-infp b)
		    (not (equal a 0))
		    (not (equal a 1))
		    (o-infp c)
		    (equal (o-rst c) 0)
		    (o-p a)
		    (o-p b)
		    (o-p c))
	       (equal (o^ a (o* b c))
		      (o^ (o^ a b) c)))
      :hints (("goal"
	       :in-theory (disable |a <= b & b < c  =>  a < c|)
	       :use ((:instance |a <= b & b < c  =>  a < c|
				(a 1)
				(b (o-first-expt b))
				(c (o+ (o-first-expt b)
				       (o-first-expt c)))))))))

   (local
    (defthm |a^(bc) = (a^b)^c :a lemma 1|
      (implies (and (not (equal a 0))
		    (not (equal a 1))
		    (o-infp c)
		    (equal (o-rst c) 0)
		    (o-p a)
		    (o-p b)
		    (o-p c))
	       (equal (o^ a (o* b c))
		      (o^ (o^ a b) c)))
      :hints (("goal"
	       :do-not-induct t
	       :cases ((o-infp b))))))

   (local
    (defthm |a^(bc) = (a^b)^c :a lemma 2|
      (implies (and (o-infp c)
		    (o-p a)
		    (o-p b)
		    (o-p c))
	       (equal (o* (o^ a (o* b (first-term c)))
			  (o^ a (o* b (o-rst c))))
		      (o^ a (o* b c))))
      :hints (("goal"
	       :in-theory (disable |a^(b+c)  =  a^b * a^c|)
	       :use ((:instance |a^(b+c)  =  a^b * a^c|
				(b (o* b (first-term c)))
				(c (o* b (o-rst c))))
		     (:instance |a(b + c) = ab + ac|
				(a b)
				(b (first-term c))
				(c (o-rst c))))))))

   (local
    (defthm |a^(bc) = (a^b)^c :a lemma 3|
      (implies (and (not (equal a 0))
		    (not (equal a 1))
		    (o-infp c)
		    (o-p a)
		    (o-p b)
		    (o-p c))
	       (equal (o^ (o^ a b) c)
		      (o* (o^ (o^ a b) (first-term c))
			  (o^ (o^ a b) (o-rst c)))))))

   (defthm |a^(bc) = (a^b)^c :a|
     (implies (and (not (equal (o^ a b) 0))
		   (not (equal (o^ a b) 1))
		   (o-infp c)
		   (implies (and (o-p a) (o-p b) (o-p (o-rst c)))
			    (equal (o^ a (o* b (o-rst c)))
				   (o^ (o^ a b) (o-rst c))))
		   (o-p a)
		   (o-p b)
		   (o-p c))
	      (equal (o^ a (o* b c))
		     (o^ (o^ a b) c)))
     :hints (("goal"
	      :do-not-induct t
	      :in-theory (disable |a^(bc) = (a^b)^c :a lemma 1|
				  |a^(bc) = (a^b)^c :a lemma 2|
				  |a^(bc) = (a^b)^c :a lemma 3|)
	      :use ((:instance |a^(bc) = (a^b)^c :a lemma 1|
			       (c (first-term c)))
		    (:instance |a^(bc) = (a^b)^c :a lemma 2|)
		    (:instance |a^(bc) = (a^b)^c :a lemma 3|)))))))

 (local
  (defthm |a^(bc) = (a^b)^c :b|
    (implies (and (not (equal (o^ a b) 0))
		  (not (equal (o^ a b) 1))
		  (o-finp c)
		  (not (zp c))
		  (implies (and (o-p a) (o-p b) (o-p (+ -1 c)))
			   (equal (o^ a (o* b (+ -1 c)))
				  (o^ (o^ a b) (+ -1 c))))
		  (o-p a)
		  (o-p b)
		  (o-p c))
	     (equal (o^ a (o* b c))
		    (o^ (o^ a b) c)))
    :hints (("goal"
	     :do-not-induct t
	     :in-theory (disable |a^(b+c)  =  a^b * a^c|)
	     :use ((:instance |a^(b+c)  =  a^b * a^c|
			      (c (o* b (+ -1 c)))))
	     :expand (o^ (o^ a b) c)))))

 (local
  (defun exp-ind-3 (a b c)
    (cond ((equal (o^ a b) 0)
	   (list a b c))
	  ((equal (o^ a b) 1)
	   (list a b c))
	  ((o-finp c)
	   (if (zp c)
	       (list a b c)
	     (exp-ind-3 a b (- c 1))))
	  (t (exp-ind-3 a b (o-rst c))))))

 ;these "helper" lemmas are here to eliminate the need for subgoal hints

 (local
  (defthm |a^(bc) = (a^b)^c helper1|
    (implies (and (equal (o^ a b) 1)
                  (o-p a)
                  (o-p b)
                  (o-p c))
             (equal (o^ a (o* b c)) 1))
    :hints (("goal"
             :cases ((equal a 1))))))

 ;the following 3 theorems seem easy, but for some reason
 ;acl2 needs them to do the proof of |a^(bc) = (a^b)^c|

 (local
  (defthm posp-o-infp-0
    (implies (and (not (posp a))
		  (o-p a)
		  (o-finp a))
	     (equal a 0))
    :rule-classes (:forward-chaining)))

 (local
  (defthm o*-posp-o-infp-0
    (implies (and (not (posp (o* a b)))
		  (o-finp (o* a b))
		  (o-p a)
		  (o-p b))
	     (or (equal a 0)
		 (equal b 0)))
    :hints (("goal"
	     :in-theory (disable o*-0)
	     :use ((:instance o*-0))))
    :rule-classes (:forward-chaining)))

 (defthm |a^(bc) = (a^b)^c|
   (implies (and (o-p a)
		 (o-p b)
		 (o-p c))
	    (equal (o^ a (o* b c)) (o^ (o^ a b) c)))
   :hints (("goal"
	    :induct (exp-ind-3 a b c)))))

(defthm |0 < w^a|
  (implies (o-p a)
	   (o< 0 (o^ (omega) a))))

(in-theory (enable o^-o-first-expt))

(defthm o^-omega-o-first-expt
 (implies (o-p a)
	  (equal (o-first-expt (o^ (omega) a))
		 a)))


(defthm o^-o-rst
 (implies (and (o-infp y)
	       (natp x)
	       (not (equal x 0))
	       (not (equal x 1))
	       (o-p y))
	  (equal (o-rst (o^ x y)) 0)))

(defthm o^-limitp-o-rst
  (implies (and (o-p a)
		(limitp b))
	   (equal (equal (o-rst (o^ a b)) 0)
		  (and (not (equal a 0))
		       (not (equal a 1)))))
  :hints (("goal" :induct (o^ a b))))

(defthm o^-limitp-o-rst-2
  (implies (and (o-infp a)
		(equal (o-rst a) 0)
		(not (equal b 0))
		(o-p a)
		(o-p b))
	   (equal (o-rst (o^ a b)) 0)))

(defthm o^-o-infp
  (implies (and (o-p a)
		(o-p b))
	   (equal (o-infp (o^ a b))
		  (or (and (not (equal a 0))
			   (not (equal a 1))
			   (o-infp b))
		      (and (not (equal b 0))
			   (o-infp a))))))

(defthm o^-limitp-o-first-coeff
 (implies (and (o-infp a)
	       (equal (o-rst a) 0)
	       (o-p b)
	       (o-p a))
	  (equal (o-first-coeff (o^ a b))
		 (if (equal (natpart b) 0)
		     1
		   (o-first-coeff a)))))

(defthm o^-w-o-first-expt
 (implies (and (not (equal a 0))
	       (o-p a)
	       (o-p b))
	  (equal (o< (o-first-expt b) (o-first-expt (o^ (omega) a)))
		 (o< b (o^ (omega) a))))
 :hints (("goal"
	  :in-theory (disable o^)
	  :expand (o< b (o^ (omega) a)))))

;these hints aren't necessary, but speed up the proof
(defthm |b < w^a  =>  b + w^a = w^a|
  (implies (and (o-p b)
		(o-p a)
		(o< b (o^ (omega) a)))
	   (equal (o+ b (o^ (omega) a))
		  (o^ (omega) a)))
  :hints (("goal"
	   :in-theory (disable o^-w-o-first-expt)
	   :use o^-w-o-first-expt)))

(encapsulate

 ;this encapsulate is here so the lemmas used to prove |a < b  <=>  c^a < c^b|
 ;don't slow down the rest of the proofs in this book

 ()

 (local
  (defthm |a < b  =>  c^a < c^b :l1|
    (implies (and (not (equal c 1))
		  (not (equal c 0))
		  (o-p a)
		  (o-p b)
		  (o-p c)
		  (o< a b))
	     (equal (o^ c b)
		    (o* (o^ c a) (o^ c (o- b a)))))
    :hints (("goal"
	     :do-not-induct t
	     :in-theory (disable |a^(b+c)  =  a^b * a^c|)
	     :use ((:instance |a^(b+c)  =  a^b * a^c|
			      (a c)
			      (b a)
			      (c (o- b a))))))
    :rule-classes ((:rewrite :match-free :all))))

 (local
  (defthm |a < b  =>  c^a < c^b|
    (implies (and (not (equal c 1))
		  (not (equal c 0))
		  (o-p a)
		  (o-p b)
		  (o-p c)
		  (o< a b))
	     (o< (o^ c a) (o^ c b)))
    :hints (("goal"
	     :do-not-induct t
	     :in-theory (disable |a < b  =>  c^a < c^b :l1| |~(a=0) & b>1  <=>  a < ab|)
	     :use ((:instance |a < b  =>  c^a < c^b :l1|)
		   (:instance |~(a=0) & b>1  <=>  a < ab|
			      (a (o^ c a))
			      (b (o^ c (o- b a)))))))))

 (local
  (defthm |a < b  <=>  c^a < c^b helper|
    (implies (and (o< b a)
		  (not (equal c 1))
		  (not (equal c 0))
		  (o-p a)
		  (o-p b)
		  (o-p c))
	     (O<= (O^ C B)
              (O* (O^ C B) (O^ C (O- A B)))))
  :hints (("goal"
	   :in-theory (disable |a < b  =>  c^a < c^b|)
	   :use ((:instance |a < b  =>  c^a < c^b|
			    (a b)
			    (b a)))))))

 (defthm |a < b  <=>  c^a < c^b| ;a < b  =>  c^a < c^b
   (implies (and (not (equal c 1))
                 (not (equal c 0))
                 (o-p a)
                 (o-p b)
                 (o-p c))
            (equal (o< (o^ c a) (o^ c b))
                   (o< a b)))
   :hints (("goal"
	    :cases ((o< a b) (equal a b) (o< b a))))))

(defthm |a <= b  =>  c^a <= c^b|
 (implies (and (not (equal c 0))
	       (o<= a b)
	       (o-p a)
	       (o-p b)
	       (o-p c))
	  (o<= (o^ c a) (o^ c b)))
 :hints (("goal"
	  :use  |a < b  <=>  c^a < c^b|)))

(defthm |a < b  <=>  w^a + w^b = w^b|
  (implies (and (o-p a)
		(o-p b)
		(o< a b))
	   (equal (o+ (o^ (omega) a)
		      (o^ (omega) b))
		  (o^ (omega) b))))

;another proof that should be really simple for acl2, but is needed
;for another proof
(local
 (defthm |b-1 <= a+b|
   (implies (and (o-p a)
		 (o-p b))
	    (equal (o< (o- b 1)
		       (o+ a b))
		   (not (equal (o- b 1) (o+ a b)))))
   :hints (("goal"
	    :in-theory (enable o- o+)))))

(local
 (defthm |b-1 <= a+b:1|
   (implies (and (o-p a)
		 (o-p b))
            (o<= (o- b 1)
                 (o+ a b)))
   :hints (("goal"
	    :use ((:instance |b-1 <= a+b|))))))

(local
 (defun exp-ind-4 (a b c)
   (if (o-finp c)
       (if (zp c)
	   (list a b c)
	 (exp-ind-4 a b (1- c)))
     (cond ((o-finp a)
	    (if (equal (o-first-expt c) 1)
		(exp-ind-4 a b (o-rst c))
	      (exp-ind-4 a b (o-rst c))))
	   (t (exp-ind-4 a b (o-rst c)))))))

(encapsulate
 ()

 (local
  (defthm |a <= b  =>  a^c <= b^c :l1|
    (implies (and (o-infp c)
		  (o-p a)
		  (o-p b)
		  (o-p c)
		  (implies (and (o-p a)
				(o-p b)
				(o-p (o-rst c))
				(o<= a b))
			   (o<= (o^ a (o-rst c)) (o^ b (o-rst c))))
		  (o<= a b))
	     (o<= (o^ a c) (o^ b c)))
    :rule-classes :forward-chaining))

 (defthm |a <= b  =>  a^c <= b^c|
   (implies (and (o-p a)
		 (o-p b)
		 (o-p c)
		 (o<= a b))
	    (o<= (o^ a c) (o^ b c)))
   :hints (("goal"
	    :in-theory (enable o<)
	    :induct (exp-ind-4 a b c)))))

(defthm |a <= b & c < d  =>  a^c < b^d|
  (implies (and (not (equal b 0))
		(not (equal b 1))
		(o<= a b)
		(o< c d)
		(o-p a)
		(o-p b)
		(o-p c)
		(o-p d))
	   (o< (o^ a c) (o^ b d)))
  :hints (("goal"
	   :do-not-induct t
	   :in-theory (disable |a <= b & b < c  =>  a < c|)
	   :use ((:instance |a <= b & b < c  =>  a < c|
			    (a (o^ a c))
			    (b (o^ b c))
			    (c (o^ b d)))))))

(defthm |a <= b & c <= d  =>  a^c <= b^d|
  (implies (and (not (equal b 0))
		(not (equal b 1))
		(o<= a b)
		(o<= c d)
		(o-p a)
		(o-p b)
		(o-p c)
		(o-p d))
	   (o<= (o^ a c) (o^ b d)))
  :hints (("goal"
	   :in-theory (disable |a <= b & c < d  =>  a^c < b^d|)
	   :use |a <= b & c < d  =>  a^c < b^d|)))

;o^1

(local
 (encapsulate
  ()
  (local
   (defthm o^1c-l1
     (implies (and (not (o-finp y))
		   (not (equal (o-first-expt y) 1))
		   (equal (o^1 x (o-rst y)) (o^ x (o-rst y)))
		   (natp x)
		   (not (equal x 0))
		   (not (equal x 1))
		   (o-p y))
	      (equal (make-ord (make-ord (o- (o-first-expt y) 1)
					 (o-first-coeff y)
					 (o-first-expt (o^ x (o-rst y))))
			       (o-first-coeff (o^ x (o-rst y)))
			       0)
		     (o* (make-ord (make-ord (o- (o-first-expt y) 1) (o-first-coeff y) 0)
				   1 0)
			 (o^ x (o-rst y)))))
     :hints (("goal"
	      :in-theory (enable o+ o*)
	      :cases ((o-finp (o-rst y)))))))

  (defthm o^1c
    (implies (and (natp x)
		  (not (equal x 0))
		  (not (equal x 1))
		  (o-p y))
	     (equal (o^1 x y)
		    (o^ x y)))
    :hints (("goal"
	     :in-theory (enable o* o+)
	     :induct (o^1 x y))))))

(verify-guards o^1)

(local (in-theory (disable o^1c)))

;o^2

(local (in-theory (disable olen)))

(local
 (encapsulate
  ()

  (local
   (defthm o^2c-l1-l1
     (implies (and (natp y)
		   (not (equal y 0))
		   (not (equal y 1))
		   (not (equal y 2))
		   (limitp x))
	      (equal (o* x
			 (make-ord (o* (o-first-expt x) (+ -2 y))
				   1
				   0))
		     (make-ord (o* (o-first-expt x)
				   (+ -1 y))
			       1
			       0)))
     :hints (("goal"
	      :in-theory (enable o+ o*)
	      :cases ((o-infp (o-first-expt x)))))))

  (local
   (defthm o^2c-l1
     (implies (and (o-p x)
		   (limitp x)
		   (o-infp x)
		   (natp y)
		   (not (= y 0))
		   (not (= y 1))
		   (not (= y 2)))
	      (equal (o* x (o^2 x (+ -1 y)))
		     (o^2 x y)))
     :hints (("goal"
	      :in-theory (disable distributivity |(ab)c = a(bc)|)
	      :use ((:instance |(ab)c = a(bc)|
			       (a x)
			       (b (make-ord (o* (o-first-expt x) (+ -2 y))
					    1
					    0))
			       (c x)))))))

  (defthm o^2c
    (implies (and (natp y)
		  (limitp x))
	     (equal (o^2 x y)
		    (o^ x y)))
    :hints (("goal"
	     :induct (o^ x y))
	    ("subgoal *1/3"
	     :use ((:instance o^2c-l1)))))))

(verify-guards o^2)

(local (in-theory (disable o^2c)))

(local
 (defthm o^2-o-infp
   (implies (and (o-infp a)
		 (o-p a)
		 (posp b))
	    (o-infp (o^2 a b)))))

(local (in-theory (enable o^-o-first-expt)))

(local
 (defthm o-first-expt-o^2
   (implies (and (o-p a)
		 (limitp a)
		 (natp q))
	    (equal (o-first-expt (o^2 a q))
		   (o* (o-first-expt a) q)))
   :hints (("goal" :in-theory (enable o^2c)))))

(local
 (defthm o-last-expt-o^2
   (implies (and (posp q)
		 (limitp a))
	    (equal (o-last-expt (o^2 a q))
		   (o+ (o* (o-first-expt a)
			   (+ -1 q))
		       (o-last-expt a))))))

(local
 (defthm o-p-o^2
   (implies (and (natp q)
		 (limitp a))
	    (o-p (o^2 a q)))))

(defthm |a(b-1)+a = ab|
  (implies (and (posp b)
		(o-p a))
	   (equal (o+ (o* a (+ -1 b)) a)
		  (o* a b)))
  :hints (("goal"
	   :in-theory (disable |a(b + c) = ab + ac|)
	   :use ((:instance |a(b + c) = ab + ac|
			    (b (+ -1 b))
			    (c 1))))))

(defthm |a(b-2)+a = a(b-1)|
  (implies (and (posp b)
		(not (equal b 1))
		(o-p a))
	   (equal (o+ (o* a (+ -2 b)) a)
		  (o* a (+ -1 b))))
  :hints (("goal"
	   :use ((:instance |a(b-1)+a = ab|
			    (b (+ -1 b)))))))

(local
 (defthm o^2-count
   (implies (and (posp q)
		 (limitp a))
	    (equal (count1 (o^2 a q)
			   (o^2 a (+ -1 q)))
		   (olen (o^2 a q))))
   :hints (("goal"
	    :in-theory (disable o-last-expt-o-first-expt-count distributivity)
	    :use ((:instance o-last-expt-o-first-expt-count
			     (a (o^2 a q))
			     (b (o^2 a (+ -1 q)))))))))

;o^3h

(local (in-theory (disable padd)))

(local
 (defthm o^3h-o-first-expt
   (implies (and (natp q)
		 (posp p)
		 (posp n)
		 (limitp a))
	    (equal (o-first-expt (o^3h a p n q))
		   (o* (o-first-expt a) q)))))

(defthm limit-o-rst-p-o*
 (implies (and (o-p a)
	       (o-p b))
	  (equal (equal (natpart (o* a b)) 0)
		 (or (equal (natpart a) 0)
		     (equal (natpart b) 0))))
 :hints (("goal"
	  :in-theory (enable o*))))

(local
 (defthm o-p-o^3h
   (implies (and (natp q)
		 (posp p)
		 (natp n)
		 (limitp a))
	    (o-p (o^3h a p (olen a) q)))))

(verify-guards o^3h)

;o^3sum

(local
 (defun o^3sum (a q)
   (if (zp q)
       (natpart a)
     (o+ (o* (o^2 (limitpart a) q) (natpart a))
	 (o^3sum a (1- q))))))

(local
 (defthm o^3sum-def-0
   (equal (o^3sum a 0)
	  (natpart a))))

(local
 (defthm o-p-o^3sum
   (implies (and (o-p a)
		 (o-infp a)
		 (natp q))
	    (o-p (o^3sum a q)))))

(local
 (defthm o^3sum-o-first-expt
   (implies (and (o-p a)
		 (o-infp a)
		 (not (equal (natpart (o-rst a)) 0))
		 (natp q))
	    (equal (o-first-expt (o^3sum a q))
		   (o* (o-first-expt a) q)))
   :hints (("goal"
	    :in-theory (enable o^2c)))))

(local
 (defthm o^3sum-o-first-coeff
   (implies (and (o-p a)
		 (o-infp a)
		 (not (equal (natpart (o-rst a)) 0))
		 (posp q))
	    (equal (o-first-coeff (o^3sum a q))
		   (* (o-first-coeff a) (natpart a))))
   :hints (("goal"
	    :expand (o^3sum a q)))))

(local
 (defthm o^3h-padd-o+
   (implies (and (< 1 q)
		 (o-p a)
		 (o-infp a)
		 (posp q)
		 (not (equal (natpart (o-rst a)) 0)))
	    (equal (padd (o* (o^2 (limitpart a) q) (natpart a))
			 (o^3sum a (+ -1 q))
			 (olen a))
		   (o+ (o* (o^2 (limitpart a) q) (natpart a))
		       (o^3sum a (+ -1 q)))))))

(local
 (defthm o^3hc
   (implies (and (o-p a)
		 (o-infp a)
		 (posp q)
		 (not (equal (natpart a) 0)))
	    (equal (o^3h (limitpart a) (natpart a) (olen a) q)
		   (o^3sum a q)))))

;o^3

(verify-guards o^3)

(local
 (defthm o^3rw
   (implies (and (o-p a)
		 (o-infp a)
		 (natp q))
	    (equal (o^3 a q)
		   (cond ((= q 0) 1)
			 ((= q 1) a)
			 ((limitp a) (o^2 a q))
			 (t
			  (let ((c (limitpart a))
				(n (olen a)))
			    (o+ (o^2 c q) (o^3h c (natpart a) n (1- q))))))))
   :hints (("goal"
	    :in-theory (disable o+ count1 o^2c)))))

(local (in-theory (disable o^3h)))

(local
(defthm o^3c1
 (implies (and (o-p a)
	       (o-infp a)
	       (posp q)
	       (not (equal q 1))
	       (not (limitp a)))
	  (equal (o+ (o^2 (limitpart a) q) (o^3sum a (+ -1 q)))
		 (o^3 a q)))
 :hints (("goal"
	  :use ((:instance o^3h
			   (q (+ -1 q))))))))

(local
 (encapsulate
  ()
  (local
   (defthm o^-alt-def-l1
     (implies (and (o-p a)
		   (equal (o^ a (+ -1 q))
			  (o* (o^ a (+ -2 q)) a))
		   (o-infp a)
		   (posp q))
	      (equal (o^ a q)
		     (o* a (o^ a (+ -2 q)) a)))
     :hints (("goal"
	      :do-not-induct t
	      :in-theory (enable o^)))))

  (local
   (defthm o^-alt-def-l2
     (implies (and (o-p a)
		   (equal (o^ a (+ -1 q))
			  (o* (o^ a (+ -2 q)) a))
		   (o-infp a)
		   (posp q))
	      (equal (o^ a q)
		     (o* (o^ a (+ -1 q)) a)))
     :hints (("goal"
	      :do-not-induct t
	      :use o^-alt-def-l1
	      :in-theory (enable o^)))))

  (defthm o^-alt-def
    (implies (and (o-p a)
		  (o-infp a)
		  (posp q))
	     (equal (o^ a q)
		    (o* (o^ a (1- q)) a)))
    :hints (("goal"
	     :induct (o^ a q)
	     :in-theory (enable o^))))))

(defthm posp-<-1
  (implies (and (not (equal a 1))
		(posp a))
	   (< 1 a))
  :rule-classes :forward-chaining)

(local
 (encapsulate
  ()
  (local
   (defthm o^3c2-l1-l1
     (implies (and (o-p a)
		   (o-infp a)
		   (posp q)
		   (not (equal q 1))
		   (not (limitp a)))
	      (equal (o* (make-ord (o* (o-first-expt a) (+ -1 q)) 1 0)
			 (limitpart a))
		     (o* (o+ (o^2 (limitpart a) (+ -1 q)) (o^3sum a (+ -2 q)))
			 (limitpart a))))
     :hints (("goal"
	      :in-theory (disable omega-term-o*)
	      :use ((:instance omega-term-o*
			       (a (o+ (o^2 (limitpart a)
					   (+ -1 q))
				      (o^3sum a (+ -2 q))))
			       (b (limitpart a))))))))

  (local
   (defthm o^3c2-l1-l2
     (implies (and (o-p a)
		   (o-infp a)
		   (posp q)
		   (not (equal q 1))
		   (not (limitp a)))
	      (equal (o^2 (limitpart a) q)
		     (o* (o+ (o^2 (limitpart a) (+ -1 q)) (o^3sum a (+ -2 q)))
			 (limitpart a))))
     :hints (("goal"
	      :use o^3c2-l1-l1
	      :in-theory (enable o^2)))))

  (local (in-theory (enable o^2c)))

  (defthm o^3c2-l1
    (implies (and (o-p a)
		  (o-infp a)
		  (posp q)
		  (not (equal q 1))
		  (not (limitp a)))
	     (equal (o^ (limitpart a) q)
		    (o* (o+ (o^ (limitpart a) (+ -1 q)) (o^3sum a (+ -2 q)))
			(limitpart a))))
    :hints (("goal"
	     :use o^3c2-l1-l2
	     :in-theory (disable o^3c2-l1-l2 o^-alt-def)
	     :do-not-induct t)))))

(local
 (encapsulate
  ()
  (local
   (defthm posp-distributive
     (implies (and (posp c)
		   (o-p a)
		   (o-p b)
		   (o< (o-first-expt b)
		       (o-first-expt a)))
	      (equal (o* (o+ a b) c)
		     (o+ (o* a c) b)))
     :hints (("goal"
	      :in-theory (enable o+ o*)))))

  (local
   (defthm o^3c2-l2-l1
     (implies (and (o-p a)
		   (o-infp a)
		   (posp q)
		   (not (equal q 1))
		   (not (limitp a)))
	      (equal (o+ (o* (o^2 (limitpart a) (+ -1 q))
			     (natpart a))
			 (o^3sum a (+ -2 q)))
		     (o* (o+ (o^2 (limitpart a) (+ -1 q)) (o^3sum a (+ -2 q)))
			 (natpart a))))
     :hints (("goal"
	      :use ((:instance posp-distributive
			       (a (limitpart a))
			       (b (natpart a))
			       (c (natpart a))))))))

  (local (in-theory (disable posp-distributive)))

  (local
   (defthm o^3c2-l2-l2
     (implies (and (o-p a)
		   (o-infp a)
		   (posp q)
		   (not (equal q 1))
		   (not (limitp a)))
	      (equal (o^3sum a (+ -1 q))
		     (o* (o+ (o^2 (limitpart a) (+ -1 q)) (o^3sum a (+ -2 q)))
			 (natpart a))))
     :hints (("goal"
	      :in-theory (disable o^2)
	      :do-not-induct t))))

  (defthm o^3c2-l2
    (implies (and (o-p a)
		  (o-infp a)
		  (posp q)
		  (not (equal q 1))
		  (not (limitp a)))
	     (equal (o^3sum a (+ -1 q))
		    (o* (o+ (o^ (limitpart a) (+ -1 q)) (o^3sum a (+ -2 q)))
			(natpart a))))
    :hints (("goal"
	     :in-theory (enable o^2c)
	     :use o^3c2-l2-l2)))))

(local
 (defthm o^3c2-l4
   (implies (and (o-p a)
		 (o-infp a)
		 (posp q)
		 (not (equal q 1))
		 (not (limitp a)))
	    (equal (o+ (o* (o+ (o^ (limitpart a) (+ -1 q)) (o^3sum a (+ -2 q)))
			   (limitpart a))
		       (o* (o+ (o^ (limitpart a) (+ -1 q)) (o^3sum a (+ -2 q)))
			   (natpart a)))
		   (o* (o+ (o^ (limitpart a) (+ -1 q)) (o^3sum a (+ -2 q)))
		       a)))
   :hints (("goal"
	    :do-not-induct t
	    :in-theory (disable |a(b + c) = ab + ac| o^2)
	    :use ((:instance |a(b + c) = ab + ac|
			     (a (o+ (o^ (limitpart a) (+ -1 q))
				    (o^3sum a (+ -2 q))))
			     (b (limitpart a))
			     (c (natpart a))))))))
(local
 (defun new-ind-2 (a q)
   (cond ((zp q) 0)
	 ((equal q 1) 1)
	 (t (* a (new-ind-2 a (+ -1 q)))))))

(local
 (defthm o^3c2-l6
   (implies (and (not (equal q 1))
		 (equal (o+ (o* (o^ (limitpart a) (+ -2 q))
				(limitpart a))
			    (o^3sum a (+ -2 q)))
			(o* (o^ a (+ -2 q)) a))
		 (o-p a)
		 (o-infp a)
		 (posp q)
		 (not (limitp a)))
	    (equal (o+ (o* (o* (o^ a (+ -2 q)) a)
			   (limitpart a))
		       (o* (o* (o^ a (+ -2 q)) a)
			   (natpart a)))
		   (o* (o* (o^ a (+ -2 q)) a) a)))
   :hints (("goal"
	    :in-theory (disable |a(b + c) = ab + ac|
				|(ab)c = a(bc)|)
	    :use ((:instance |a(b + c) = ab + ac|
			     (a (o* (o^ a (+ -2 q)) a))
			     (b (limitpart a))
			     (c (natpart a))))))))

(local
 (defthm o^3c2
   (implies (and (o-p a)
		 (o-infp a)
		 (posp q)
		 (not (limitp a)))
	    (equal (o+ (o^ (limitpart a) q) (o^3sum a (+ -1 q)))
		   (o^ a q)))
   :hints (("goal"
	    :in-theory (disable |(ab)c = a(bc)|)
	    :induct (new-ind-2 a q)))))

(local (in-theory (e/d (o^2c) (o^-alt-def))))

(local
 (defthm o^3c
   (implies (and (natp q)
		 (o-p a)
		 (o-infp a))
	    (equal (o^3 a q)
		   (o^ a q)))
   :hints (("goal"
	    :do-not-induct t
	    :in-theory (disable o^3c1 o^3c2)
	    :use (o^3c1 o^3c2)))))

(local (in-theory (disable o^3)))

(verify-guards o^4)

(defthm o^-o-first-coeff-1
  (implies (and (not (equal a 0))
		(o-p a)
		(limitp b))
	   (equal (o-first-coeff (o^ a b))
		  1)))

(local
 (encapsulate
  ()

  (local
   (defthm o^4c-l1
     (implies (and (o-infp a)
		   (o-p a)
		   (limitp b))
	      (equal (omega-term (o* (o-first-expt a)
				     b)
				 1)
		     (o^ a b)))))

  (defthm o^4c
    (implies (and (o-infp a)
		  (o-infp b)
		  (o-p a)
		  (o-p b))
	     (equal (o^4 a b)
		    (o^ a b)))
    :hints (("goal"
	     :do-not-induct t
	     :use ((:instance |a^(b+c)  =  a^b * a^c|
			      (b (limitpart b))
			      (c (natpart b)))))))))

(local (in-theory (e/d (o^1c) (o^4))))

;o^

(verify-guards ob^)
