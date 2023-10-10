(in-package "ACL2S")

(definec uplog (base q :nat) :nat
  (if (< q (expt 2 base)) base (uplog (1+ base) q)))

(definec delta (eps :pos-rational) :nat (uplog 0 (denominator eps)))

(property uplog-ups (base q :nat) (< q (expt 2 (uplog base q))))
(property belowlow (q :pos) (< (/ 1 (expt 2 (uplog 0 q))) (/ 1 q)))

(property belowlog->0 (eps :pos-rational)
  (< (/ 1 (expt 2 (delta eps))) eps)
  :hints (("Goal" :instructions
	   (:pro (:claim (<= (/ 1 (denominator eps)) eps))
		 (:claim (< (/ 1 (expt 2 (delta eps)))
			    (/ 1 (denominator eps))))
		 :prove))))

(property 0<a<b->a^n<b^n (a b :pos-rational n :pos)
  :hyps (< a b)
  (< (expt a n) (expt b n))
  :instructions (:pro (:induct (nat-ind n))
                      :pro :prove :pro (:casesplit (equal n 1)) :prove
                      (:claim (< (expt a n) (* a (expt b (+ -1 n)))))
                      (:claim (< (* a (expt b (+ -1 n))) (expt b n)))
                      :prove :pro :prove))

(property 0<a<=b->a^n<=b^n (a b :pos-rational n :pos)
  :hyps (<= a b)
  (<= (expt a n) (expt b n))
  :hints (("Goal" :use ((:instance 0<a<b->a^n<b^n (a a) (b b) (n n))))))

(property k<=n^a<1->a^n<=a^k (a :pos-rational n k :pos)
  :hyps (and (<= k n) (< a 1))
  (<= (expt a n) (expt a k)))

(property 1/2^n=[1/2]^n (n :nat) (equal (/ 1 (expt 2 n)) (expt 1/2 n)))

(property a=1/2->a^n->0 (eps :pos-rational n :pos)
  :hyps (<= (delta eps) n)
  (< (expt 1/2 n) eps)
  :instructions ((:use (:instance k<=n^a<1->a^n<=a^k (a 1/2)
                                  (n n)
                                  (k (delta eps))))
                 (:use (:instance belowlog->0 (eps eps)))
                 (:use (:instance 1/2^n=[1/2]^n (n (delta eps))))
                 :pro
                 (:claim (<= (expt 1/2 n) (* 1 (/ (expt 2 (delta eps))))))
                 (:claim (< (* 1 (/ (expt 2 (delta eps)))) eps))
                 :prove))

(property p/q<1->p<q (p q :pos) (implies (< (/ p q) 1) (< p q)))

(property a<1->num-a<denom-a (a :pos-rational)
  (implies (< a 1) (< (numerator a) (denominator a))))

(property x<=y->a/y<a/x (x y a :pos)
  (implies (<= x y) (<= (/ a y) (/ a x))))

(property a<=1/2->a^n->0 (a eps :pos-rational n :pos)
  :hyps (and (<= a (/ 1 2)) (<= (delta eps) n))
  (< (expt a n) eps)
  :hints (("Goal" :use ((:instance a=1/2->a^n->0 (eps eps) (n n))
      (:instance 0<a<=b->a^n<=b^n (a a) (b 1/2) (n n))))))

(property a<=num[a]/[1+num[a]] (a :pos-rational)
  :hyps (< a 1)
  (<= a (/ (numerator a) (1+ (numerator a))))
 :instructions ((:use (:instance a<1->num-a<denom-a (a a)))
                 (:use (:instance x<=y->a/y<a/x (x (1+ (numerator a)))
                                  (y (denominator a))
                                  (a (numerator a))))
                 :pro
                 (:claim (< (numerator a) (denominator a)))
                 (:claim (<= (* (numerator a) (/ (denominator a)))
                             (* (numerator a)
                                (/ (+ 1 (numerator a))))))
                 :prove))

(include-book "arithmetic/binomial" :dir :system)

(property intp-choose (k n :all)
  :check-contracts? nil
  (intp (acl2::choose k n))
  :rule-classes :type-prescription)

(property natp-n-expt (x :nat k :int)
  :check-contracts? nil
  (natp (acl2::n-expt x k))
  :rule-classes :type-prescription)

(property nat-listp-binomial-expansion (x y :nat k n :all)
  :check-contracts? nil
  (nat-listp (acl2::binomial-expansion x y k n))
  :hints (("goal" :in-theory (disable acl2::choose)))
  :rule-classes :type-prescription)

(property natp-sumlist (l :nat-list)
  :check-contracts? nil
  (natp (acl2::sumlist l))
  :rule-classes :type-prescription)

(property expt-1+nn (n :pos)
  (>= (expt (+ 1 n) n) (* 2 (expt n n)))
  :hints (("goal'" :expand (acl2::binomial-expansion 1 n 1 n)))
  :rule-classes :linear)

(property a^b/c^b=[a/c]^b (a b c :pos)
  (equal (/ (expt a b) (expt c b)) (expt (/ a c) b)))

(property a/2a=1/2 (a :pos) (equal (/ a (* 2 a)) 1/2))

(property |a = p/q, p/q^p <= p/(p+1)^p <= 1/2| (a :pos-rational)
  (implies (< a 1) (<= (expt a (numerator a)) 1/2))
  :hints (("Goal" :use
	   ((:instance expt-1+nn (n (numerator a)))
	    (:instance x<=y->a/y<a/x
		       (a (expt (numerator a) (numerator a)))
		       (x (* 2 (expt (numerator a) (numerator a))))
		       (y (expt (+ 1 (numerator a))
				(numerator a))))
	    (:instance a<=num[a]/[1+num[a]] (a a))
	    (:instance a^b/c^b=[a/c]^b (a (numerator a))
		       (b (numerator a))
		       (c (1+ (numerator a))))
	    (:instance a/2a=1/2 (a (expt (numerator a) (numerator a))))
	    (:instance 0<a<=b->a^n<=b^n (a a)
			     (b (* (numerator a) (/ (+ 1 (numerator a)))))
			     (n (numerator a)))))))

(defun-sk lim-0 (a e n)
  (declare (xargs :guard (and (pos-rationalp a)
			      (< a 1)
			      (pos-rationalp e)
			      (natp n))
		  :verify-guards t))
  (exists (d)
    (and (natp d) (implies (and (pos-rationalp e)
				(< d n))
			   (< (expt a n) e)))))

(property a^n->0 (a e :pos-rational n :nat)
  :hyps (< a 1)
  (lim-0 a e n)
  :hints (("Goal" :use ((:instance lim-0-suff (d (* (numerator a) (delta eps))))
			(:instance |a = p/q, p/q^p <= p/(p+1)^p <= 1/2| (a a))
			(:instance a<=1/2->a^n->0 (a (expt a (numerator a))) (eps e) (n n))))))
			
