;  This files contains some theorems about limit ordinals.  The
;  purpose is to show how to define and prove theorems about
;  limit ordinals, but the theory of limit ordinals is not
;  developed fully.

(in-package "ACL2")

(include-book "ordinal-exponentiation")
(local (include-book "top-with-meta"))

(defthm limit-+
  (implies (o-p a)
           (not (limitp (o+ a 1))))
  :hints (("goal"
	   :in-theory (e/d (limitp) (natpart-o-rst)))))

(local (in-theory (disable o+)))

(defthm |limitp.b  =>  a<b   <=>  a+1 < b|
  (implies (and (limitp b)
                (o-p a))
           (equal (o< (o+ a 1) b)
                  (o< a b))))

(defthm |limitp.b  =>   c<b  <=>  a+c+1 < a+b|
  (implies (and (limitp b)
                (o-p a)
                (o-p c))
           (equal (o< (o+ a c 1) (o+ a b))
                  (o< c b))))

(encapsulate
 ()
 (local
  (defthm |limitp.b &  a < w^b   =>   a < w^[fe.a +1]  &  [fe.a + 1] < w^b :l1|
    (implies (and (not (equal b 0))
		  (o-p a)
		  (o-p b)
		  (o< a (o^ (omega) b)))
	     (o< (o-first-expt a) b))
    :hints (("goal"
	     :cases ((o-infp a))))
    :rule-classes :forward-chaining))

 (defthm |limitp.b &  a < w^b   =>   a < w^[fe.a +1]  &  [fe.a + 1] < w^b|
   (implies (and (limitp b)
		 (o-p a)
		 (o< a (o^ (omega) b)))
	    (and (o< a
		     (o^ (omega) (o+ (o-first-expt a) 1)))
		 (o< (o^ (omega) (o+ (o-first-expt a) 1))
		     (o^ (omega) b))))
   :rule-classes ((:rewrite :match-free :all))))

(defthm o*-o-first-expt-equal
  (implies (and (not (equal a 0))
		(not (equal b 0))
		(equal (o-first-expt a)
		       (o-first-expt b))
		(limitp c)
		(o-p a)
		(o-p b))
	   (equal (o* a c)
		  (o* b c)))
  :rule-classes ((:forward-chaining :trigger-terms ((o* a c) (o* b c)))))
