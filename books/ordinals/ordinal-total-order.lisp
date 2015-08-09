(in-package "ACL2")
(include-book "ordinal-definitions")
(local (disable-forcing))

(defthm ocmp-lt
 (equal (equal (ocmp a b) 'lt)
	(o< a b)))

(defthm ocmp-gt
  (equal (equal (ocmp a b) 'gt)
	 (o> a b)))

(defthm o-rst-<-fc
  (implies (and (o< (o-rst a) (o-rst b))
		(equal (o-first-coeff a) (o-first-coeff b))
		(equal (o-first-expt a) (o-first-expt b))
		(o-p a)
		(o-p b))
	   (o< a b))
  :rule-classes :forward-chaining)

(defthm make-ord-o<-3
  (equal (o< (make-ord a b c)
	     (make-ord x y z))
	 (cond ((not (equal a x))
		(o< a x))
	       ((not (equal b y))
		(< b y))
	       (t
		(o< c z))))
  :hints (("goal" :in-theory (enable o-rst o-first-expt o-first-coeff o< make-ord))))

(defthm o-rst-<
  (implies (o< rst1 rst2)
           (o< (make-ord o-first-expt o-first-coeff rst1)
               (make-ord o-first-expt o-first-coeff rst2)))
  :hints (("goal" :in-theory (enable o<))))

(defthm o-first-coeff-<-fc
  (implies (and (< (o-first-coeff a)
		   (o-first-coeff b))
		(equal (o-first-expt a) (o-first-expt b))
		(o-p a)
		(o-p b))
	   (o< a b))
  :rule-classes :forward-chaining)

(defthm o<-o-first-expt=-o-first-coeff<=
  (implies (and (not (equal (o-first-coeff a) (o-first-coeff b)))
                (o< a b)
                (o-p b)
                (equal (o-first-expt a) (o-first-expt b)))
           (< (o-first-coeff a) (o-first-coeff b)))
  :rule-classes :forward-chaining)

(defthm o-first-coeff-<
  (implies (and (o-infp b)
		(< (o-first-coeff a)
		   (o-first-coeff b))
		(equal (o-first-expt a) (o-first-expt b)))
	   (o< a b))
  :rule-classes ((:rewrite :backchain-limit-lst (3 3 3))
		 (:forward-chaining :trigger-terms ((< (o-first-coeff a) (o-first-coeff b))))))

(defthm |~(a < a)|
  (not (o< a a)))

(defthm o-first-expt-<
  (implies (and (o< (o-first-expt a)
		    (o-first-expt b))
		(o-p a))
	   (o< a b))
  :rule-classes ((:forward-chaining)
                 (:rewrite :backchain-limit-lst 3)))

(defthm o-finp-cr
  (equal (o-finp x)
         (atom x))
  :rule-classes :compound-recognizer)


(defthm o-finp-<
  (implies (and (o-finp a)
		(o-finp b)
		(< a b))
	   (o< a b))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(defthm o-finp-<-fc
  (implies (and (o< a b)
		(o-finp a)
		(o-finp b))
	   (< a b))
  :rule-classes :forward-chaining)

(defthm o<-o-finp-o-finp
  (implies (and (o< a b)
		(o-finp b))
	   (o-finp a))
  :rule-classes :forward-chaining)

(defthm ac-<
  (implies (and (o-finp a)
		(o-infp b))
	   (o< a b))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(defthm o<=-o-finp-def
  (implies (and (o-finp a)
		(o-finp b)
		(<= a b))
	   (o<= a b))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(local (in-theory (disable o-first-coeff-< o-first-expt-< o-finp-< ac-<)))

(defthm |~(a<0)|
  (implies (o-p a)
	   (not (o< a 0)))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(defthm |a <= b & ~(a = b)  =>  a < b|
  (implies (and (not (equal a b))
		(o<= a b)
		(o-p a)
		(o-p b))
	   (o< a b))
  :rule-classes :forward-chaining)

(defthm |a <= b  =>  (a < b <=> ~(a = b))|
  (implies (and (o<= a b)
		(o-p a)
		(o-p b))
	   (equal (o< a b)
		  (not (equal a b))))
  :rule-classes :forward-chaining)

(defthm |a < b  =>  a <= b & ~(a = b)|
  (implies (o< a b)
           (and (o<= a b)
                (not (equal a b))))
  :rule-classes :forward-chaining)

; The above rule is not enough to prove |~(b = 0)  =>  a <= ab|,
; and the next one is needed
(defthm |a < b  =>  ~(a = b)|
 (implies (o< a b)
	  (not (equal a b))))

(defthm |a<b => a<=b|
  (implies (o< a b)
	   (o<= a b))
  :rule-classes :forward-chaining)

(defthm o-infp-o-finp-o<=
  (implies (and (o-infp a)
		(o-finp b))
	   (o<= b a))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(defthm |a <= b & b <= c  =>  a <= c|
  (implies (and (o<= a b)
		(o<= b c)
		(o-p a)
		(o-p b))
	   (o<= a c))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((o< b a) (o< c b)))))

(defthm |a < b & b < c  =>  a < c|
  (implies (and (o< a b)
                (o< b c))
           (o< a c))
  :rule-classes ((:forward-chaining)
                 (:rewrite :match-free :all
                           :backchain-limit-lst 3)))

(defthm |a < b & b <= c  =>  a < c|
  (implies (and (o< a b)
		(o<= b c)
		(o-p b)
		(o-p c))
	   (o< a c))
  :hints (("goal"
	   :use (:instance |a <= b & ~(a = b)  =>  a < b|
			   (b b)
			   (a c))))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((o< a b) (o< c b)))))

(defthm |a <= b & b < c  =>  a < c|
  (implies (and (o< b c)
		(o<= a b)
		(o-p a)
		(o-p c))
	   (o< a c))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((o< b a) (o< b c)))))

(defthm |b <= a & a <= b  =>  a = b|
  (implies (and (o<= a b)
		(o-p a)
                (o-p b)
                (o<= b a))
           (equal a b))
  :rule-classes ((:forward-chaining)))

(local
 (defthm ocmp-aux-equal
   (implies (and (o-p a)
		 (o-p b))
	    (equal (equal (ocmp-aux a b) 'eq)
		   (equal a b)))
   :rule-classes :forward-chaining))

(local
 (defthm ocmp-aux-lt
   (implies (and (o-p a)
		 (o-p b))
	    (equal (equal (ocmp-aux a b) 'lt)
		   (o< a b)))
   :hints (("goal"
	    :induct (ocmp-aux a b)))))

(verify-guards ocmp)

(in-theory (disable ocmp))

(defthm |a = b  =>  (a <= b)|
  (implies (equal a b)
           (o<= a b))
  :rule-classes ((:forward-chaining)))

(defthm |0 < a  =  ~(a = 0)|
 (implies (o-p a)
          (equal (o< 0 a)
                 (not (equal a 0))))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(defthm omega-o<
   (implies (o-p a)
	    (equal (o< a (omega))
		   (o-finp a)))
   :hints (("goal" :in-theory (enable o<)))
   :rule-classes ((:rewrite :backchain-limit-lst 3)))

; The rule we now disable slowed down the regression suite by several percent
; when left enabled.
(in-theory (disable |a < b  =>  ~(a = b)|))
