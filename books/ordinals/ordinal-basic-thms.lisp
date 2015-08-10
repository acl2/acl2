; Some basic, easy theorems about the definitions in ordinal-definitions.lisp
(in-package "ACL2")

(include-book "ordinal-total-order")
(local (include-book "top-with-meta"))
(local (disable-forcing))

(defthm olen-posp
  (equal (posp (olen a))
	 (o-infp a)))

;theorems about the constructor and destructors

(defthm make-ord-o-first-expt
  (equal (o-first-expt (make-ord a b c))
	 a))

(defthm make-ord-o-first-coeff
  (equal (o-first-coeff (make-ord a b c))
	 b))

(defthm make-ord-o-rst
  (equal (o-rst (make-ord a b c))
	 c))

(defthm make-ord-o-infp
  (o-infp (make-ord a b c)))

(defthm make-ord-o-p
  (equal (o-p (make-ord o-first-expt o-first-coeff o-rst))
	 (and (not (equal o-first-expt 0))
	      (posp o-first-coeff)
	      (o-p o-first-expt)
	      (o-p o-rst)
	      (o< (o-first-expt o-rst) o-first-expt))))

(defthm o-first-expt-o-first-coeff-o-rst-elim
  (implies (and (o-infp x)
                (o-p x))
           (equal (make-ord (o-first-expt x) (o-first-coeff x) (o-rst x))
                  x))
  :rule-classes (:rewrite :elim))

(defthm make-ord-equal-2
 (equal (equal (make-ord a b c)
	       (make-ord x y z))
	(and (equal a x)
	     (equal b y)
	     (equal c z)))
 :hints (("goal" :in-theory (enable make-ord))))

(local
 (defthm make-ord-car
   (implies (and (o-infp a)
		 (consp (car a)))
	    (equal (cons (car a) b)
		   (make-ord (o-first-expt a) (o-first-coeff a) b)))))

(local
 (defthm make-ord-def-consp
   (equal (cons (cons a b) c)
	  (make-ord a b c))))

(in-theory (disable make-ord))

;theorems about omega

(defthm omega-o-infp
  (o-infp (omega)))

(defthm omega-o-p
  (o-p (omega)))

(defthm omega-o-first-expt
  (equal (o-first-expt (omega)) 1))

(defthm omega-o-first-coeff
  (equal (o-first-coeff (omega)) 1))

(defthm omega-o-rst
  (equal (o-rst (omega)) 0))

(defthm omega-limitp
  (limitp (omega)))

(in-theory (disable omega (:executable-counterpart omega)))

; theorems involving o-rst

(defthm o-finp-o-rst
  (implies (o-finp a)
	   (equal (o-rst a) nil)))

(defthm acl2-count-o-rst
   (implies (o-infp a)
	    (o< (acl2-count (o-rst a))
		(acl2-count a))))

(defthm acl2-count-o-rst-2
   (implies (o-infp a)
	    (< (acl2-count (o-rst a))
	       (acl2-count a))))

(defthm o-first-expt-1-o-finp-o-rst
  (implies (and (equal (o-first-expt a) 1)
                (o-p a))
	   (o-finp (o-rst a)))
  :rule-classes :forward-chaining)

(local
 (defthm cdr-o-rst
   (equal (cdr a)
	  (o-rst a))))

(in-theory (disable o-rst))

;theorems about o-first-expt

(defthm o-first-expt-o-p
  (implies (o-p a)
	   (o-p (o-first-expt a)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((o-first-expt a)))
                 (:rewrite :backchain-limit-lst (5))))

(defthm |(o-first-expt a) < a|
 (implies (o-p a)
	  (equal (o< (o-first-expt a) a)
		 (not (equal a 0)))))

(defthm o-first-expt-<=
  (implies (o-p b)
           (<= 0 (o-first-expt b)))
  :rule-classes ((:linear)))

(defthm o-first-expt-0-natp
 (implies (o-p a)
	  (equal (equal (o-first-expt a) 0)
		 (o-finp a))))

(defthm <=-o-first-expt-<=
  (implies (and (o<= a b)
		(o-p b))
	   (o<= (o-first-expt a) (o-first-expt b)))
  :rule-classes ((:forward-chaining)))

(defthm o-first-expt-natp
  (implies (and (equal (o-first-expt a) 0)
                (o-p a))
	   (natp a))
  :rule-classes :forward-chaining)

(defthm o-first-expt-o-infp
 (implies (not (equal 0 (o-first-expt b)))
	  (o-infp b))
 :rule-classes (:forward-chaining
		:rewrite))

(defthm o-first-expt-o-infp-2
  (implies (and (o< (o-first-expt b) (o-first-expt a))
		(o-p a)
		(o-p b))
	   (o-infp a))
  :rule-classes :forward-chaining)

(defthm o-first-expt-def-o-finp
  (implies (o-finp a)
	   (equal (o-first-expt a)
		  0)))

(defthm o-first-expt-equal-o-finp
  (implies (and (equal (o-first-expt b) 0)
		(o-p b))
	   (o-finp b))
  :rule-classes :forward-chaining)

(defthm acl2-count-o-first-expt
  (implies (o-infp a)
           (< (acl2-count (o-first-expt a))
              (acl2-count a)))
  :hints (("goal"
           :in-theory (disable cdr-o-rst make-ord-def-consp))))

(in-theory (disable o-first-expt))

;theorems about o-first-coeff

(defthm natp-o-first-coeff
  (implies (o-p a)
	   (natp (o-first-coeff a)))
  :rule-classes ((:forward-chaining :trigger-terms ((o-first-coeff a)))))

(defthm posp-o-first-coeff
  (implies (o-p a)
	   (equal (posp (o-first-coeff a))
		  (not (equal a 0))))
  :rule-classes ((:rewrite :backchain-limit-lst 3)
		 (:forward-chaining :trigger-terms ((o-first-coeff a)))))

(defthm o-first-coeff-0
  (implies (o-p a)
	   (equal (equal (o-first-coeff a) 0)
		  (equal a 0)))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(defthm posp-o-first-coeff-2
  (implies (o-p a)
	   (or (equal a 0)
	       (posp (o-first-coeff a))))
  :rule-classes ((:forward-chaining :trigger-terms ((o-first-coeff a)))))

(defthm o-first-coeff-def-o-finp
  (implies (o-finp a)
	   (equal (o-first-coeff a) a))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(in-theory (disable o-first-coeff))

(defthm o-p-o-infp-car
  (implies (o-p a)
	   (equal (consp (car a))
		  (o-infp a)))
  :rule-classes ((:rewrite :backchain-limit-lst 3)
		 (:forward-chaining :trigger-terms ((consp (car a))))))

(defthm o-p-o-infp-car-2
  (implies (o-p (cons a b))
	   (consp a))
  :rule-classes :forward-chaining)

(defthm o-p-o-first-expt-neq-0
  (implies (and (o-infp a)
		(o-p a))
	   (not (equal (o-first-expt a) 0)))
  :rule-classes ((:rewrite  :backchain-limit-lst 3)
		 (:forward-chaining :trigger-terms ((o-first-expt a)))))

(defthm o-p-o-p-o-rst
  (implies (and (o-infp a)
		(o-p a))
	   (o-p (o-rst a)))
  :rule-classes ((:forward-chaining :trigger-terms ((o-rst a)))))

(defthm o-p-<-o-first-expt-o-first-expt-o-rst
  (implies (and (o-infp a)
		(o-p a))
	   (o< (o-first-expt (o-rst a))
	       (o-first-expt a)))
  :rule-classes ((:forward-chaining :trigger-terms ((o-rst a)))))

(defthm o-p-def-o-finp-1
  (implies (o-finp a)
	   (equal (o-p a)
		  (natp a)))
  :rule-classes ((:rewrite :backchain-limit-lst 3)
		 (:forward-chaining)))

(defthm o-p-def-o-finp-2
  (implies (and (o-finp a)
		(o-p a))
	   (natp a))
  :rule-classes :forward-chaining)

(in-theory (disable o-p))

;theorems about o-finp and o-infp

(defthm o-infp->neq-0
  (implies (o-infp a)
	   (not (equal a 0)))
  :rule-classes ((:forward-chaining)
                 (:rewrite :backchain-limit-lst 3)))

(in-theory (disable o-finp))

;theorems about limitp

(defthm limitp-o-p
  (implies (limitp a)
           (o-p a))
  :rule-classes :forward-chaining)

(defthm limitp-o-infp
  (implies (limitp a)
           (o-infp a))
  :rule-classes :forward-chaining)

(defthm limitp-natpart
  (implies (limitp a)
	   (equal (natpart a) 0))
  :rule-classes :forward-chaining)

(defthm not-limitp-natp
  (implies (and (o-infp a)
		(o-p a)
		(not (limitp a)))
	   (not (equal (natpart a) 0))))

(defthm limitp-o-rst
  (implies (limitp b)
	   (or (equal (o-rst b) 0)
	       (limitp (o-rst b))))
  :rule-classes :forward-chaining)

(defthm limitp-o-infp-o-rst
  (implies (limitp a)
           (equal (limitp (o-rst a))
		  (o-infp (o-rst a))))
  :rule-classes :forward-chaining)

(defthm limitp-def
  (implies (and (o-infp a)
		(equal (natpart a) 0)
		(o-p a))
	   (limitp a)))

(defthm limitp-def-2
  (equal (limitp (make-ord a b c))
	 (and (o-p (make-ord a b c))
	      (equal (natpart c) 0))))

(in-theory (disable limitp))

;theorems about limpart and natpart

(defthm natpart-o-finp
  (o-finp (natpart a))
  :hints (("goal"
	   :in-theory (enable natpart))))

(defthm natpart-natp
  (implies (o-p a)
	   (natp (natpart a)))
  :rule-classes :type-prescription)

(defthm natpart-def-o-finp
  (implies (o-finp a)
	   (equal (natpart a)
		  a)))

(defthm natpart-o-rst
  (implies (o-infp a)
	   (equal (natpart a)
		  (natpart (o-rst a))))
  :rule-classes ((:forward-chaining :trigger-terms ((natpart (o-rst a))))))

(defthm natpart-make-ord
  (equal (natpart (make-ord a b c))
	 (natpart c)))

(defthm limitpart-o-first-expt
 (equal (o-first-expt (limitpart a))
	(o-first-expt a))
 :hints (("goal"
	  :expand (limitpart a))))

(defthm limitpart-o-first-coeff
 (implies (o-infp a)
	  (equal (o-first-coeff (limitpart a))
		 (o-first-coeff a)))
 :hints (("goal"
	  :expand (limitpart a))))

(defthm limitpart-o-rst
  (implies (o-infp a)
	   (equal (o-rst (limitpart a))
		  (limitpart (o-rst a))))
  :hints (("goal"
	   :expand (limitpart a))))

(defthm limitpart-def-o-finp
 (implies (o-finp a)
	  (equal (limitpart a)
		 0)))

(defthm limitpart-olen
  (equal (olen (limitpart a))
	      (olen a)))

(defthm limitpart-o-finp
  (equal (o-finp (limitpart a))
	 (o-finp a)))

(defthm limitpart-o-p
  (implies (o-p a)
	   (o-p (limitpart a)))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(verify-guards limitpart)

(defthm natpart-limitpart
 (equal (natpart (limitpart a)) 0))

(defthm limitpart-limitp
   (implies (o-p a)
	    (equal (limitp (limitpart a))
		   (o-infp a))))

(defthm limitpart-limitp-tp
  (implies (and (o-infp a)
		(o-p a))
	   (limitp (limitpart a))))

(in-theory (disable limitpart natpart))

;theorems about o-last-expt-le

(defthm o-p-o-last-expt
  (implies (o-p a)
	   (o-p (o-last-expt a)))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(defthm o-last-expt-o-first-expt-2
  (implies (o-p a)
	   (o<= (o-last-expt a)
		(o-first-expt a)))
  :rule-classes ((:forward-chaining :trigger-terms ((o-last-expt a)))
		 (:rewrite)))

(defthm o-last-expt-0
  (implies (o-p a)
	   (equal (equal (o-last-expt a) 0)
		  (o-finp a))))

(defthm o-last-expt-def-o-infp-1
  (implies (o-infp (o-rst a))
	   (equal (o-last-expt a) (o-last-expt (o-rst a))))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(defthm o-last-expt-def-o-infp-2
  (implies (and (o-infp a)
		(o-finp (o-rst a)))
	   (equal (o-last-expt a) (o-first-expt a))))

(in-theory (disable o-last-expt))

;theorems about dropn and firstn

(defthm o-p-dropn
 (implies (o-p a)
	  (o-p (dropn n a))))

(defthm dropn-new-def
  (equal (dropn n a)
	 (if (or (o-finp a) (zp n))
	     a
	   (dropn (1- n) (o-rst a))))
  :hints (("goal"
	   :in-theory (enable o-finp)))
  :rule-classes :definition)

(in-theory (disable dropn))

(verify-guards count2)

