;definitions and theorems about ordinal arithmetic
(in-package "ACL2")
(include-book "ordinal-addition")
(local (include-book "top-with-meta"))
(local (disable-forcing))
(local (in-theory (disable o+ o<)))

(defthm count1-o<
  (implies (and (o-p a)
		(o-p b)
		(o-p c)
		(o< c b))
	   (<= (count1 a b)
	       (count1 a c))))

(defthm o-last-expt-o-first-expt-count
   (implies (and (o-p a)
		 (o-p b)
		 (o< (o-first-expt b)
		     (o-last-expt a)))
	    (equal (count1 a b)
		   (olen a)))
   :hints (("goal"
	    :in-theory (enable o-last-expt)
	    :induct (count1 a b))))

(defthm nat-count
  (implies (and (natp b)
		(o-p a))
	   (equal (count1 a b)
		  (olen a))))

(local
 (defun dropn-induct (n a)
   (if (or (o-finp a) (zp n))
       a
     (dropn-induct (1- n) (o-rst a)))))

(defthm count1-count2
  (implies (and (natp n)
		(<= n (count1 a b))
		(o-p a)
		(o-p b))
	   (equal (count2 a b n)
		  (count1 a b)))
  :hints (("goal"
	   :induct (dropn-induct n a))))

(defthm padd-o-first-expt
 (implies (and (posp n)
	       (o-infp a))
	  (equal (o-first-expt (padd a b n))
		 (o-first-expt a))))

(defthm padd-o+
  (implies (and (<= q (count1 a b))
		(o-p a)
		(o-p b))
	   (equal (padd a b q)
		  (o+ a b)))
  :hints (("goal" :in-theory (enable o+))))

(verify-guards padd)

(local (in-theory (disable padd o+ count1 count2 o-)))

;pmult, omul

(local
 (defthm pmult-o*
   (implies (and (natp n)
		 (<= n (count1 (o-first-expt a)
			       (o-first-expt b)))
		 (o-p a)
		 (o-p b))
	    (equal (pmult a b n)
		   (o* a b)))))

(defthm o*-finite
  (implies (and (o-finp a)
		(o-finp b))
	   (o-finp (o* a b)))
  :rule-classes ((:type-prescription)
                 (:forward-chaining :trigger-terms ((o* a b)))))

(defthm |a0 = 0|
  (equal (o* a 0) 0))

(defthm |0a = 0|
  (equal (o* 0 a) 0))

(defthm o-infp-o*
  (implies (and (not (equal b 0))
                (o-infp a)
                (o-p a)
                (o-p b))
           (o-infp (o* a b)))
  :rule-classes ((:rewrite :match-free :all)
                 (:forward-chaining :trigger-terms ((o* a b)))))

(defthm o-infp-o*-2
  (implies (and (not (equal b 0))
                (o-infp a)
                (o-p a)
                (o-p b))
           (o-infp (o* b a)))
  :rule-classes ((:rewrite :match-free :all)
                 (:forward-chaining :trigger-terms ((o* a b)))))

(defthm |a1 = a|
  (implies (o-p a)
           (equal (o* a 1) a)))

(defthm |1a = a|
  (implies (o-p a)
           (equal (o* 1 a) a)))

(defthm o*-0
 (implies (and (o-p a)
	       (o-p b))
	  (equal (equal (o* a b) 0)
                 (or (equal a 0)
                     (equal b 0)))))

(defthm o*-o-first-expt
 (implies (and (not (equal a 0))
	       (not (equal b 0))
	       (o-p a)
	       (o-p b))
	  (equal (o-first-expt (o* a b))
		 (o+ (o-first-expt a) (o-first-expt b)))))

(encapsulate

 ;this encapsulate is here so that o*-o-first-expt-< doesn't interfere with
 ;any other theorems in the book

 ()

 (local
  (defthm o*-o-first-expt-<
    (implies (and (o-p a)
                  (o-p b)
                  (o-p c)
                  (o< (o-first-expt a)
                      (o-first-expt b)))
             (o< (o-first-expt (o* c a))
                 (o+ (o-first-expt c) (o-first-expt b))))
  :rule-classes ((:forward-chaining :match-free :all))))

 (defthm o-p-o*
   (implies (and (o-p a)
                 (o-p b))
            (o-p (o* a b)))
   :hints (("goal"
            :in-theory (enable o*-o-first-expt-<)
            :induct (o* a b)))
   :rule-classes ((:rewrite)
		  (:forward-chaining :trigger-terms ((o* a b))))))

(verify-guards pmult)
(verify-guards ob*)

(defthm |~(a=0) & b>1  <=>  a < ab|
  (implies (and (o-p a)
                (o-p b))
           (equal (o< a (o* a b))
                  (and (not (equal a 0))
                       (not (equal b 0))
                       (not (equal b 1)))))
  :hints (("goal"
           :induct (o* a b))))

; Needed at least for the next lemma.
(local (in-theory (enable |a < b  =>  ~(a = b)|)))

(defthm |a = ab  <=>  (a = 0) V (b = 1)|
  (implies (and (o-p a)
                (o-p b))
           (equal (equal a (o* a b))
                  (or (equal a 0)
                      (equal b 1))))
  :hints (("goal"
           :cases ((equal a 0)
                   (equal b 0)
                   (equal b 1)))))

(defthm |(ab)c = a(bc)|
  (implies (and (o-p a)
		(o-p b)
		(o-p c))
	   (equal (o* (o* a b) c)
		  (o* a b c))))

(defthm o*-o-first-coeff
  (implies (and (not (equal a 0))
		(o-p a)
		(o-p b))
	   (equal (o-first-coeff (o* a b))
		  (if (o-infp b) (o-first-coeff b) (* (o-first-coeff a) b)))))

(defthm o-first-coeff-o*-omega
   (implies (o-p a)
	    (equal (o-first-coeff (o* (omega) a))
		   (o-first-coeff a)))
   :hints (("goal"
	    :cases ((o-infp a)))))

(defthm o*-o-rst
  (implies (and (or (and (o-infp a)
			 (not (equal b 0)))
		    (and (o-infp b)
			 (not (equal a 0))))
		(o-p a)
		(o-p b))
	   (equal (o-rst (o* a b))
		  (if (o-infp b)
		      (o* a (o-rst b))
		    (o-rst a)))))

(defthm o*-o-first-expt-<
  (implies (and (not (equal a 0))
		(o< (o-first-expt b)
		    (o-first-expt c))
		(o-p a)
		(o-p b)
		(o-p c))
	   (o< (o-first-expt (o* a b))
	       (o-first-expt (o* a c))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((o< (o-first-expt b)
                                      (o-first-expt c))))
		 (:rewrite :match-free :all)))

(encapsulate

; This encapsulate is here to avoid the use of subgoal hints.

 nil

 (local
  (defthm |a(b + c) = ab + ac helper1|
    (implies (and (o< (o-first-expt c) (o-first-expt b))
                  (implies (and (o-p a) (o-p (o-rst b)) (o-p c))
                           (equal (o* a (o+ (o-rst b) c))
                                  (o+ (o* a (o-rst b)) (o* a c))))
                  (o-p a)
                  (o-p b)
                  (o-p c))
             (equal (o* a (o+ b c))
                    (o+ (o* a b) (o* a c))))
    :hints (("goal"
             :in-theory (enable o+)
             :use ((:instance o*-o-first-expt-<
                              (c b)
                              (b c)))))))

 (local
  (defthm |a(b + c) = ab + ac helper2|
   (implies (and (o<= (o-first-expt c) (o-first-expt b))
                 (o<= (o-first-expt b) (o-first-expt c))
                 (o-p a)
                 (o-p b)
                 (o-p c))
            (equal (o* a (o+ b c))
                   (o+ (o* a b) (o* a c))))
   :hints (("goal"
            :in-theory (enable o+)))))

 (local
  (defun o*-ind-1 (a b c)
    (cond ((equal a 0)
	   (list a b c))
	  ((and (o-infp b)
		(o< (o-first-expt c)
		    (o-first-expt b)))
	   (o*-ind-1 a (o-rst b) c))
	  ((o< (o-first-expt b)
	       (o-first-expt c))
	   (list a b c))
	  (t (list a b c)))))

 (defthm |a(b + c) = ab + ac|
   (implies (and (o-p a)
                 (o-p b)
                 (o-p c))
            (equal (o* a (o+ b c))
                   (o+ (o* a b) (o* a c))))
   :hints (("goal"
            :induct (o*-ind-1 a b c)))))

(defthm |a+(a(b-1)) = ab|
  (implies (and (not (equal b 0))
		(o-p a)
		(o-p b))
	   (equal (o+ a (o* a (o- b 1)))
		  (o* a b)))
  :hints (("goal"
	   :in-theory (e/d (o<)
                           (|a <= b  =>  a+(b-a) = b|
			       |a(b + c) = ab + ac|
			       o*))
	   :use ((:instance |a(b + c) = ab + ac|
			    (b 1)
			    (c (o- b 1)))
		 (:instance |a <= b  =>  a+(b-a) = b|
			    (a 1))))))

(defthm |a <= b  =>  ac <= bc|
  (implies (and (o-p a)
		(o-p b)
		(o-p c)
		(o<= a b))
	   (o<= (o* a c) (o* b c)))
  :hints (("goal"
	   :in-theory (enable o<))))

(encapsulate

 ;this encapsulate is here so that the lemmas used to prove
 ;|(a < b) & ~(c = 0)  <=>  ca < cb| don't slow down the
 ;rest of the book

 ()

 (local
  (defthm |(a < b) & ~(c = 0)  <=>  ca < cb :a|
    (implies (and (o-p a)
                  (o-p b)
                  (o-p c)
                  (o< a b)
                  (not (equal c 0)))
             (o< (o* c a) (o* c b)))
    :hints (("goal"
	     :in-theory (enable o<)
             :induct (o< a b)))))

 (local
  (defthm |(a < b) & ~(c = 0)  <=>  ca < cb :b|
    (implies (and (o-p a)
                  (o-p b)
                  (o-p c)
                  (o< (o* c a) (o* c b)))
             (o< a b))
    :hints (("goal"
             :use (:instance |(a < b) & ~(c = 0)  <=>  ca < cb :a|  (b a) (a b)))
            ("goal'"
             :cases ((equal a b)
                     (o< a b))))
    :rule-classes ((:rewrite :match-free :all))))

 (defthm |(a < b) & ~(c = 0)  <=>  ca < cb| ;a < b  =>  ca < cb
   (implies (and (o-p a)
                 (o-p b)
                 (o-p c))
            (equal (o< (o* c a) (o* c b))
                   (and (o< a b)
                        (not (equal c 0)))))))

(defthm |ab = ac  <=>  (b=c) V (a = 0)|
  (implies (and (o-p a)
		(o-p b)
		(o-p c))
           (equal (equal (o* a b)
                         (o* a c))
                  (or (equal a 0)
                      (equal b c))))
  :hints (("goal"
           :do-not-induct t
           :use ((:instance |(a < b) & ~(c = 0)  <=>  ca < cb|
                            (c a)
                            (a b)
                            (b c))
                 (:instance |(a < b) & ~(c = 0)  <=>  ca < cb|
                            (c a)
                            (a c)))
           :in-theory (disable |(a < b) & ~(c = 0)  <=>  ca < cb|)))
  :rule-classes ((:rewrite :match-free :all)))

(defthm |(a <= b) & (c < d)  =>  ac < bd|
  (implies (and (not (equal b 0))
		(o<= a b)
		(o< c d)
		(o-p a)
		(o-p b)
		(o-p c)
		(o-p d))
	   (o< (o* a c) (o* b d)))
  :hints (("goal"
	   :in-theory (disable |a < b & b <= c  =>  a < c|)
	   :use ((:instance |a < b & b <= c  =>  a < c|
			    (a (o* a c))
			    (b (o* a d))
			    (c (o* b d)))))))

(defthm |(a <= b) & (c <= d)  =>  ac <= bd|
  (implies (and (not (equal b 0))
		(o<= a b)
		(o<= c d)
		(o-p a)
		(o-p b)
		(o-p c)
		(o-p d))
	   (o<= (o* a c) (o* b d)))
  :hints (("goal"
	   :in-theory (disable |(a <= b) & (c < d)  =>  ac < bd|)
	   :use |(a <= b) & (c < d)  =>  ac < bd|)))

(defthm |b<a & 2<=c  =>  a+b < a*c|
 (implies (and (o<= 2 c)
	       (o< b a)
	       (o-p a)
	       (o-p b)
	       (o-p c))
	  (o< (o+ a b)
	      (o* a c)))
 :hints (("goal"
	  :in-theory (disable o*)
	  :use ((:instance |a < b & b <= c  =>  a < c|
			   (a (o+ a b))
			   (b (o* a 2))
			   (c (o* a c)))
		(:instance |a+(a(b-1)) = ab|
			   (b 2))))))

(defthm |(a = 1) & (b = 1)  <=>  ab = 1|
  (implies (and (o-p a)
                (o-p b))
           (equal (equal (o* a b) 1)
                  (and (equal a 1)
                       (equal b 1))))
  :hints (("goal"
           :use |~(a=0) & b>1  <=>  a < ab|
           :in-theory (e/d (o<) (|~(a=0) & b>1  <=>  a < ab|)))))

(defthm o*-1
  (implies (and (o-p a)
		(posp b))
	   (equal (o+ a (o* a (+ -1 b)))
		  (o* a b)))
  :hints (("goal"
	   :in-theory (enable o+))))

;another seemingly obvious theorem that is needed to help acl2
;reason about equality
(defthm make-ord-equal-4
  (implies (and (o-infp a)
		(o-p a)
                (equal (o-first-coeff a) fca)
                (equal (o-first-expt a) fea)
                (equal (o-rst a) rsta))
           (equal (make-ord fea fca rsta)
                  a))
  :rule-classes ((:rewrite :match-free :all)))

(encapsulate
 ()
 (local
  (defthm o*-limitp-lemma1
    (implies (and (o-infp b)
		  (o-p a)
		  (o-p b))
	     (o-p (make-ord (o+ (o-first-expt a) (o-first-expt b))
                            (o-first-coeff b)
                            (o* a (o-rst b)))))
    :hints (("goal"
	     :cases ((equal a 0) (equal (o-rst b) 0))))))

 (defthm o*-limitp-1
   (implies (and (o-p b)
		 (not (equal b 0))
		 (limitp a))
	    (limitp (o* a b)))
   :hints (("goal"
	    :in-theory (enable o* natpart))))

 (defthm o*-limitp-2
   (implies (and (not (equal a 0))
		 (o-p a)
		 (limitp b))
	    (limitp (o* a b)))))

(defthm o*-o-first-expt-smash-1
  (implies (and (equal (o-rst b) 0)
                (not (equal a 0))
                (o-p a)
                (o-p b)
                (o< (o-first-expt (o-first-expt a))
                    (o-first-expt (o-first-expt b))))
           (equal (o* a b)
                  b))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((o< (o-first-expt (o-first-expt a))
				      (o-first-expt (o-first-expt b)))))))

(defthm o*-o-first-expt-smash-2
  (implies (and (not (equal a 0))
		(natp a)
		(limitp b))
	   (equal (o* a b) b))
  :hints (("goal"
	   :in-theory (enable natpart))))


(defthm o*-o-first-expt-smash-1a
  (implies (and (equal (o-rst b) 0)
		(not (equal a 0))
		(o-p a)
		(o-p b)
		(o-p c)
		(o< (o-first-expt (o-first-expt a))
		    (o-first-expt (o-first-expt b))))
	   (equal (o* a b c)
		  (o* b c)))
  :hints (("goal"
	   :in-theory (disable |(ab)c = a(bc)|)
	   :use ((:instance |(ab)c = a(bc)|)))))

(defthm o*-o-first-expt-smash-2a
  (implies (and (o-finp a)
		(not (equal a 0))
		(o-infp b)
		(equal (o-rst b) 0)
		(o-p a)
		(o-p b)
		(o-p c))
	   (equal (o* a b c) (o* b c)))
  :hints (("goal"
	   :in-theory (disable |(ab)c = a(bc)|)
	   :use ((:instance |(ab)c = a(bc)|)))))

(defthm o*-o-first-expt-smash-1b
  (implies (and (equal (o-rst c) 0)
		(not (equal b 0))
		(o-p a)
		(o-p b)
		(o-p c)
		(o-p d)
		(o< (o-first-expt (o-first-expt b))
		    (o-first-expt (o-first-expt c))))
	   (equal (o* (o* a b) (o* c d))
		  (o* (o* a c) d)))
  :hints (("goal"
	   :in-theory (disable o*))))

(defthm o*-o-first-expt-smash-2b
  (implies (and (o-finp b)
		(not (equal b 0))
		(o-infp c)
		(equal (o-rst c) 0)
		(o-p a)
		(o-p b)
		(o-p c)
		(o-p d))
	   (equal (o* (o* a b) (o* c d))
		  (o* (o* a c) d)))
  :hints (("goal"
	   :in-theory (disable o*))))

(defthm o*-len-1
 (implies (and (o-p a)
	       (posp b))
	  (equal (olen (o* a b))
		 (olen a))))

(defthm o*-len-2
 (implies (and (not (equal a 0))
	       (equal (natpart b) 0)
	       (o-p a)
	       (o-p b))
	  (equal (olen (o* a b))
		 (olen b))))

(encapsulate
 ()
 (local
  (defthm o*-o-last-expt-l1
    (implies (and (not (or (equal a 0) (equal b 0)))
		  (not (and (o-finp a) (o-finp b)))
		  (limitp b)
		  (implies (and (not (equal a 0))
				(o-p a)
				(limitp (o-rst b)))
			   (equal (o-last-expt (o* a (o-rst b)))
				  (o+ (o-first-expt a) (o-last-expt (o-rst b)))))
		  (not (equal a 0))
		  (o-p a))
	     (equal (o-last-expt (o* a b))
		    (o+ (o-first-expt a) (o-last-expt b))))
    :hints (("goal"
	     :cases ((o-infp (o-rst b)))))
    :rule-classes :forward-chaining))

 (defthm o*-o-last-expt
   (implies (and (not (equal a 0))
		 (o-p a)
		 (limitp b))
	    (equal (o-last-expt (o* a b))
		   (o+ (o-first-expt a) (o-last-expt b))))
   :hints (("goal"
	    :induct (o* a b)
	    :in-theory (enable o*)))))

(defthm o-first-expt-fc-o*
 (implies (and (equal (o-first-coeff a)
		      (o-first-coeff b))
	       (equal (o-first-expt a)
		      (o-first-expt b))
	       (o-p a)
	       (o-p b)
	       (limitp c))
	  (equal (o* a c)
		 (o* b c)))
 :rule-classes :forward-chaining)

(defthm omega-term-o*
 (implies (and (o-infp a)
	       (o-p a)
	       (limitp b))
	  (equal (o* (make-ord (o-first-expt a) 1 0) b)
		 (o* a b))))

(defthm o*-o-finp
  (implies (and (o-finp a)
		(o-finp b))
	   (equal (o* a b)
		  (* a b))))

(defthm o*-o-infp-def
  (implies (not (equal a 0))
           (equal (o* a (make-ord b1 b2 b3))
                  (make-ord (o+ (o-first-expt a) b1)
			    b2
			    (o* a b3)))))
