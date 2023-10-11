(in-package "ACL2S")

#|

 Let 0 < a=p/q < 1 (p, q are pos, p<q) (a=0 is trivial).
 Given any e>0 (e=x/y), we need to find n s.t. a^n < e. 

 Let b=p/(p+1)

 L1. a <= b
 L2. By the binomial theorem, (1 + x)^n = 1 + ... + nx^(n-1) + x^n
 L3. b^p <= p^p/(p+1)^p = {L2} p^p/(... + p^p + p^p) <= 1/2
 L4. 1/2^y < e 

 T1. a^py <= {L1} b^py <= {L3} 1/2^y < {L4} e 

|#

(include-book "make-event/proof-by-arith" :dir :system)

(acl2::proof-by-arith
 (property expt-monotonic (x y :pos-rational n :nat)
   (=> (<= x y)
       (<= (expt x n) (expt y n)))
   :hints (("goal" :induct (nat-ind n)))
   :rule-classes ((:linear :match-free :all)))
 t)

(property |n<2n| (n :nat)
  (< n (expt 2 n))
  :hints (("goal" :induct (nat-ind n)))
  :rule-classes :linear)

(property |1/2^n<1/n| (n :pos)
  (< (expt 1/2 n) (/ 1 n))
  :rule-classes :linear)

(property |1/(den e) < e| (e :pos-rational)
  (<= (/ 1 (denominator e)) e)
  :rule-classes :linear)

(property |a^d <= 1/2^d| (a :pos-rational d :pos)
  :h (<= a 1/2) 
  (<= (expt a d) (expt 1/2 d))
  :hints (("Goal" :use (:instance expt-monotonic (x a) (y 1/2) (n d))))
  :rule-classes ((:linear :match-free :all)))

(property l4 (a e :pos-rational)
  :h (<= a 1/2)
  (< (expt a (denominator e)) e)
  :rule-classes :linear)

(property |(num a)/(den a) = a| (a :rational)
  (= (/ (numerator a) (denominator a)) a)
  :rule-classes nil)

(property |(num a) < (den a)| (a :pos-rational)
  :h (< a 1)
  (b* ((p (numerator a))
       (q (denominator a)))
    (< p q))
  :hints (("goal" :use (:instance |(num a)/(den a) = a|)
           :in-theory (disable rational-implies2)))
  :rule-classes :linear)

(property l1 (a :pos-rational)
  :h (< a 1)
  (b* ((p (numerator a)))
    (<= a (/ p (1+ p))))
  :instructions (:bash (:use |(num a) < (den a)|)
                 :pro
                 (:demote 1)
                 (:dv 1)
                 (:= (< (numerator a) (denominator a)))
                 :up :pro (:dv 1)
                 (:= (/ (numerator a) (denominator a)))
                 :top 
                 (:in-theory (disable |(num a) < (den a)| rational-implies2))
                 :bash)
  :rule-classes :linear)

(include-book "arithmetic/binomial" :dir :system)

(property intp-choose (k n :all)
  :check-contracts? nil
  (intp (acl2::choose k n))
  :rule-classes :type-prescription)

(property intp-n-expt (x k :int)
  :check-contracts? nil
  (intp (acl2::n-expt x k))
  :rule-classes :type-prescription)

(property 0-n-expt (x :nat k :int)
  :check-contracts? nil
  (<= 0 (acl2::n-expt x k))
  :rule-classes :linear)

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

(property l3 (a :pos-rational)
  :h (< a 1)
  (b* ((p (numerator a)))
    (<= (expt (/ p (1+ p)) p) 1/2))
  :hints (("goal"
           :in-theory (disable acl2::binomial-theorem
                               acl2::n-expt-expt
                               expt-1+nn)
           :use (:instance expt-1+nn (n (numerator a)))))
  :rule-classes :linear)

(defthm main
 (=> (^ (pos-rationalp a)
        (pos-rationalp e)
        (< a 1))
     (b* ((p (numerator a)) (y (denominator e)))
       (< (expt a (* p y)) e)))
 :hints (("goal"
          :in-theory (disable acl2::n-expt-expt)
          :use ((:instance expt-monotonic (x a)
                           (y (/ (numerator a) (+ 1 (numerator a))))
                           (n (* (numerator a) (denominator e))))
                (:instance l3)
                (:instance expt-monotonic
                           (x (expt (/ (numerator a) (+ 1 (numerator a)))
                                    (numerator a)))
                           (y 1/2)
                           (n (denominator e)))
                (:instance l4 (a 1/2))))))

(definec induct-N<M->a^N<e^M (a :pos-rational n m :nat) :nat
  :ic (<= n m)
  (if (equal n m) 0 (1+ (induct-N<M->a^N<e^M a (1+ n) m))))

(property a<1->ab<b (a b :pos-rational)
  :hyps (< a 1)
  (< (* a b) b))

(property a^N+1<a^N (a :pos-rational n :nat)
  :hyps (< a 1)
  (< (expt a (1+ n)) (expt a n))
  :hints (("Goal" :instructions (:pro (:use (:instance a<1->ab<b (a a)
                                       (b (expt a n))))
                      :pro
                      (:claim (< (* a (expt a n)) (expt a n)))
                      :prove))))

(property N<M->a^N<e^M (a :pos-rational n m :nat)
  :hyps (and (< a 1) (<= n m))
  (<= (expt a m) (expt a n))
  :hints (("Goal" :instructions (:pro (:induct (induct-n<m->a^n<e^m a n m))
                      :pro (:casesplit (equal n m))
                      :prove
                      (:claim (<= (expt a m) (expt a (+ 1 n))))
                      (:use (:instance a^n+1<a^n (a a) (n n)))
                      :prove :prove))))

(property a^n->0-helper (a e :pos-rational n :nat)
  :hyps (and (< a 1) (< (* (numerator a) (denominator e)) n))
  (< (expt a n) e)
  :hints (("Goal" :use ((:instance main (a a) (e e))
			(:instance N<M->a^N<e^M
				   (a a)
				   (n (* (numerator a) (denominator e)))
				   (m n))))))

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
  :hints (("Goal" :use ((:instance lim-0-suff (d (* (numerator a) (denominator e))))
			(:instance a^n->0-helper (a a) (e e) (n n))))))
