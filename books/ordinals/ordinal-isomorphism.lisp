#|
This book proves the isomorphism between the old acl2 ordinals
and the new acl2 ordinals under their respective < relations. the
goal is to represent the high level ideas of bijection and
homomorphism in acl2. To that end, we define ctoa: oc -> ac
(where oc is the set of ordinals in the the new representation
and ac is the set of ordinals in the old representation) and show it
to be an isomorphism in the following manner:

ctoa is well-defined:
That is, we show that x in oc  =>  ctoa.x in oa.
In acl2, this translates in acl2 to the following:

(implies (o-p x)
	 (e0-ordinalp (ctoa x)))

ctoa is surjective:
That is, y in oa  => there exists x in oc s.t. ctoa.x = y.

To accomplish this, we define atoc: ac -> oc and show that
it is the inverse of ctoa. In acl2, this translates to:

(implies (e0-ordinalp x)
	 (o-p (atoc x)))

and

(implies (o-p x)
	 (equal (atoc (ctoa x))
		x))

and

(implies (e0-ordinalp x)
	 (equal (ctoa (atoc x))
		x))

Hence, ctoa is surjective since for any y in oa, there exists
x = atoc.y such that ctoa.x = ctoa(atoc.y) = y.

ctoa is injective:
That is, x,y in oc  =>  [ctoa.x = ctoa.y  =>  x = y]

This translates in acl2 to

(implies (and (o-p x)
	      (o-p y))
	 (equal (equal (ctoa x) (ctoa y))
		(equal x y)))

we also proved the equivalent theorem for atoc

(implies (and (e0-ordinalp x)
	      (e0-ordinalp y))
	 (equal (equal (atoc x) (atoc y))
		(equal x y)))

ctoa is homomorphic with respect to c<:
That is, x,y in oc s.t. x c< y  =>  ctoa.x a< ctoa.y
This translates easily into acl2 as

(implies (and (o-p x)
	      (o-p y))
	 (equal (e0-ord-< (ctoa x)
			  (ctoa y))
		(o< x y)))

and equivalently for atoc

(implies (and (e0-ordinalp x)
	      (e0-ordinalp y))
	 (equal (o< (atoc x)
		    (atoc y))
		(e0-ord-< x y)))

Therefore, the above acl2 theorems, which are exported from this file, show
the new acl2 representation of ordinals to be equivalent to acl2's old ordinal
representation.

As an added bonus, the above theorems also imply that e0-ord-< is
a well-founded relation. Therefore, we can continue to use the
old version of the ordinals as acl2's well-founded relation. At
the end of this file we use the set-well-founded-relation command
to tell acl2 to use our relation for termination proofs. |#

(in-package "ACL2")
(include-book "ordinal-addition")
(local (include-book "top-with-meta"))

(local (disable-forcing))

(local (in-theory (disable zp-open o+ o<)))

(defun e0-ord-< (x y)

  "< for the old acl2 ordinals"

  (declare (xargs :guard t))
  (if (consp x)
      (if (consp y)
          (if (e0-ord-< (car x) (car y))
              t
              (if (equal (car x) (car y))
                  (e0-ord-< (cdr x) (cdr y))
                  nil))
          nil)
      (if (consp y)
          t
          (< (if (real/rationalp x) x 0)
             (if (real/rationalp y) y 0)))))

(defun e0-ordinalp (x)

   "The old acl2 ordinal definition"

  (declare (xargs :guard t))
  (if (consp x)
      (and (e0-ordinalp (car x))
           (not (equal (car x) 0))
           (e0-ordinalp (cdr x))
           (or (atom (cdr x))
               (not (e0-ord-< (car x) (cadr x)))))
    (and (integerp x)
         (>= x 0))))

(local
 (defthm open-zp
   (implies (syntaxp (not (variablep x)))
	    (equal (zp x)
		   (not (posp x))))))

;makes a list of copies of a that is n elements
(defun copyn (a n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (cons a (copyn a (1- n)))))

(local
 (defthm acl2-count-o-first-expt
   (implies (o-infp a)
	    (< (acl2-count (o-first-expt a))
	       (acl2-count a)))
   :hints (("goal"
	    :in-theory (enable o-first-expt)))))

;converts an o-p to e0-ordinal
(defun ctoa (x)
  (declare (xargs :guard (o-p x)))
  (if (o-finp x)
      x
    (append (copyn (ctoa (o-first-expt x))
		   (o-first-coeff x))
            (ctoa (o-rst x)))))

(local
 (defthm |x a<  y  =>  ~(y a< x)|
   (implies (e0-ord-< x y)
	    (not (e0-ord-< y x)))
   :rule-classes :forward-chaining))

(local
 (defthm car-app-copyn
   (implies (posp n)
	    (equal (car (append (copyn x n) y)) x))
   :hints (("goal" :expand (copyn x n)))))

(local
 (defthm posp-consp
   (implies (posp x)
	    (consp (copyn y x)))
   :hints (("goal" :expand (copyn y x)))
   :rule-classes ((:type-prescription)
		  (:rewrite))))

(local
 (defthm consp-append
   (implies (consp a)
	    (consp (append a b)))))

(local
 (defthm cnf-cons
   (implies (and (o-p y)
		 (o-infp y))
	    (consp (ctoa y)))
   :hints (("goal"
	    :expand (ctoa y)))
   :rule-classes ((:type-prescription)
		  (:rewrite))))

(defthm ctoa-def-atom
  (implies (and (o-p a)
		(atom (ctoa a)))
	   (equal (ctoa a)
		  a))
  :hints (("goal"
	   :expand (ctoa a)
	   :do-not-induct t)))

(local
 (defthm ctoa-car
   (implies (and (o-infp a)
		 (o-p a))
	    (equal (car (ctoa a))
		   (ctoa (o-first-expt a))))))

(local
 (defthm cnf-l1
   (implies (and (o-infp x)
		 (o-infp y)
		 (e0-ord-< (ctoa (o-first-expt x))
			   (ctoa (o-first-expt y)))
		 (o-p x)
		 (o-p y)
		 (o< (o-first-expt x) (o-first-expt y)))
	    (e0-ord-< (ctoa x)
		      (ctoa y)))
   :hints (("goal"
	    :expand ((ctoa x) (ctoa y))))))

; Don't really need the hints above.

(local
 (defun i2 (n1 n2)
   (if (zp n2)
       n1
     (i2 (- n1 1) (- n2 1)))))

(local
 (defthm copyn-<-2
   (implies (and (<= w v)
		 (natp w)
		 (natp v))
	    (equal (e0-ord-< (append (copyn z w)
				     cx)
			     (append (copyn z v)
				     cy))
		   (e0-ord-< cx (append (copyn z (- v w)) cy))))
   :hints (("goal" :induct (i2 v w)))))

(defthm acl2-count-o-infp
  (implies (o-infp a)
	   (< 0 (acl2-count a))))

(local
 (defthm i1-lemma-1
   (implies (o-infp a)
	    (< (acl2-count (o-first-expt (o-rst a)))
	       (acl2-count a)))
   :instructions (promote
		  (claim (< (acl2-count (o-rst a))
			    (acl2-count a)))
		  (casesplit (o-finp (o-rst a)))
		  bash
		  (claim (< (acl2-count (o-first-expt (o-rst a)))
			     (acl2-count (o-rst a))))
		  bash)))

(local
 (defun i1 (x y)
   (if (and (o-infp x)
	    (o-infp y))
       (if (equal (o-first-expt x) (o-first-expt y))
	   (if (equal (o-first-coeff x) (o-first-coeff y))
	       (i1 (o-rst x) (o-rst y))
	     (i1 (o-first-expt (o-rst x)) (o-first-expt y)))
	 (i1 (o-first-expt x) (o-first-expt y)))
     (cons x y))))

(local
 (defthm app-copyn-1
   (implies (consp (copyn z x))
	    (equal (car (append (copyn z x) y))
		   z))))


(local
 (encapsulate
  ;this encapsulate is here so we can eliminate subgoal hints
  ()

  (local
   (defthm o<-e0-ord-<-helper2
     (implies (and (o-infp y)
		   (equal (o-first-expt x) (o-first-expt y))
		   (not (equal (o-first-coeff x) (o-first-coeff y)))
		   (e0-ord-< (ctoa (o-first-expt (o-rst x)))
			     (ctoa (o-first-expt x)))
		   (o-p x)
		   (o-p y)
		   (< (o-first-coeff x) (o-first-coeff y)))
	      (e0-ord-< (append (copyn (ctoa (o-first-expt x))
				       (o-first-coeff x))
				(ctoa (o-rst x)))
			(ctoa y)))
     :hints (("goal"
	      :expand ((ctoa y)
		       (ctoa (o-rst x)))))))

  (defthm o<-e0-ord-<
    (implies (and (o-p x)
		  (o-p y)
		  (o< x y))
	     (e0-ord-< (ctoa x)
		       (ctoa y)))
    :hints (("goal" :induct (i1 x y))))))

(local
 (encapsulate

  ;this encapsulate is here to eliminate the need for subgoal hints

  ()
  (local
   (defthm e0-ord-app-copyn-helper
     (implies (and (e0-ordinalp (append (copyn z (+ -1 x)) n))
		   (posp x)
		   (natp n)
		   (not (equal z 0))
		   (e0-ordinalp z)
		   (consp (append (copyn z (+ -1 x)) n)))
	      (not (e0-ord-< z
			     (car (append (copyn z (+ -1 x)) n)))))
     :hints (("goal"
	      :cases ((posp (+ -1 x)))))
     :rule-classes ((:rewrite :match-free :all))))


   (defthm e0-ord-app-copyn
     (implies (and (posp x)
		   (natp n)
		   (not (equal z 0))
		   (e0-ordinalp z))
	      (e0-ordinalp (append (copyn z x) n))))))

(local
 (defun nat-ind (n)
   (if (zp n)
       1
     (cons n (nat-ind (1- n))))))

(local
 (encapsulate

  ;this encapsulate is here to get rid of subgoal hints

  ()

  (local
   (defthm e0-ordp-app-copy-helper
     (implies (and (not (zp n))
		   (e0-ordinalp (append (copyn x (+ -1 n)) y))
		   (not (equal x 0))
		   (e0-ordinalp x)
		   (e0-ordinalp y)
		   (e0-ord-< (car y) x)
		   (consp (append (copyn x (+ -1 n)) y)))
	      (not (e0-ord-< x
			     (car (append (copyn x (+ -1 n)) y)))))
     :hints (("goal"
	      :cases ((zp (+ -1 n)))))
     :rule-classes ((:rewrite :match-free :all))))

  (defthm e0-ordp-app-copy
    (implies (and (not (equal x 0))
		  (e0-ordinalp x)
		  (e0-ordinalp y)
		  (e0-ord-< (car y) x))
	     (e0-ordinalp (append (copyn x n) y)))
    :hints (("goal" :induct (nat-ind n))))))

;oddly enough. this is necessary for the next theorem.
(local
 (defthm consp-neq-0
   (implies (consp a)
	    (not (equal a 0)))))

(local
 (defthm cnf-0
   (implies (o-p x)
	    (equal (equal (ctoa x) 0)
		   (equal x 0)))))

(encapsulate

 ()

 (local
  (defthm |oc.x  <=>  oa(ctoa.x) :helper|
    (implies (and (o-infp x)
		  (e0-ordinalp (ctoa (o-first-expt x)))
		  (e0-ordinalp (ctoa (o-rst x)))
		  (o-p x))
	     (e0-ordinalp (append (copyn (ctoa (o-first-expt x))
					 (o-first-coeff x))
				  (ctoa (o-rst x)))))
    :hints (("goal"
	     :cases ((o-infp (o-rst x)))))))

 (defthm |oc.x  <=>  oa(ctoa.x)|
   (implies (o-p x)
	    (e0-ordinalp (ctoa x)))
   :rule-classes ((:forward-chaining)
		  (:rewrite))))

(defun atoc (a)
  (declare (xargs :guard (e0-ordinalp a)
		  :verify-guards nil))
  (if (atom a)
      a
    (o+ (omega-term (atoc (car a))
		    1)
	(atoc (cdr a)))))

(local (in-theory (enable o+)))

(local
 (defthm o-infp-o-finp-o<=-2
   (implies (and (o-infp a)
		 (o-finp b))
	    (o<= b a))
   :hints (("goal"
	    :in-theory (enable o<)))))

(local
 (defthm ateo-neq-0
   (implies (and (not (equal a 0))
		 (e0-ordinalp a))
	    (not (equal 0 (atoc a))))))

(local (in-theory (disable o+)))

(defthm |oa.x  <=>  oc(atoc.x)|
  (implies (e0-ordinalp x)
	   (o-p (atoc x)))
  :hints (("goal"
	   :induct (atoc x))))

(verify-guards atoc)

(local
 (defthm consp-atoc
   (implies (and (consp a)
		 (e0-ordinalp a))
	    (o-infp (atoc a)))))

(local
 (defthm e0-total-order
   (implies (and (not (equal a b))
		 (not (e0-ord-< a b))
		 (e0-ordinalp a)
		 (e0-ordinalp b))
	    (e0-ord-< b a))
   :rule-classes :forward-chaining))

(local
 (defun ci (x y)
   (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
   (if (and (consp x)
	    (consp y))
       (list (ci (cdr x) y)
	     (ci x (cdr y))
	     (ci (cadr x)
		 (car x))
	     (ci (cadr y)
		 (car y))
	     (ci (car x)
		 (car y))
	     (ci (cdr x)
		 (cdr y))
	     )
     (list x y))))

(local
 (defthm |x a< y  =>  ~(y a< y)|
   (implies (e0-ord-< x y)
	    (not (e0-ord-< y x)))
   :rule-classes :forward-chaining))

(local
 (encapsulate

  ()

  (local
   (encapsulate

    ;this encapsulate is here to get rid of the subgoal hints for help1

    ()

    (local
     (defthm e0-ord-<-o<-help1a
       (implies (and (equal (o-first-expt (atoc (cdr x)))
			    (atoc (cadr x)))
                     (not (e0-ord-< (car x) (cadr x)))
                     (not (e0-ord-< (cadr x) (car x)))
                     (consp x)
		     (consp y)
		     (e0-ordinalp (car x))
		     (not (equal (car x) 0))
		     (e0-ordinalp (cdr x))
                     (e0-ordinalp y))
		(equal (o-first-expt (o+ (make-ord (atoc (car x)) 1 0)
                                         (atoc (cdr x))))
		       (atoc (car x))))
       :hints (("goal"
		:use ((:instance e0-total-order
				 (a (cadr x))
				 (b (car x)))
		      (:instance o+-o-first-expt-2
				 (a (make-ord (atoc (car x)) 1 0))
				 (b (atoc (cdr x)))))
		:in-theory (disable e0-total-order o+-o-first-expt-2)))
       :rule-classes ((:rewrite :match-free :all))))

    (defthm e0-ord-<-o<-help1
      (implies (and (consp x)
		    (consp y)
		    (e0-ordinalp x)
		    (e0-ordinalp y)
		    (implies (and (consp (cdr x))
				  (consp y)
				  (e0-ordinalp (cdr x))
				  (e0-ordinalp y))
			     (equal (o-first-expt (atoc (cdr x)))
				    (atoc (cadr x))))
		    (implies (and (consp (cadr x))
				  (consp (car x))
				  (e0-ordinalp (cadr x))
				  (e0-ordinalp (car x)))
			     (implies (e0-ord-< (cadr x) (car x))
				      (o< (atoc (cadr x))
					  (atoc (car x))))))
	       (equal (o-first-expt (atoc x))
		      (atoc (car x))))
      :hints (("goal"
	       :do-not-induct t))
      :rule-classes nil)))



  (local
   (defthm e0-ord-<-o<-help2a
     (implies (and (equal (o-first-expt (o+ (make-ord (atoc (car x)) 1 0)
                                            (cdr x)))
			  (atoc (car x)))
		   (equal (o-first-expt (o+ (make-ord (atoc (car y)) 1 0)
                                            (atoc (cdr y))))
			  (atoc (car y)))
                   (equal (car x) (car y))
		   (not (e0-ord-< (car x) (car y)))
		   (e0-ordinalp (car x))
		   (not (equal (car x) 0))
		   (e0-ordinalp (cdr x))
		   (not (consp (cdr x)))
		   (e0-ordinalp (car y))
		   (not (equal (car y) 0))
		   (e0-ordinalp (cdr y))
		   (not (e0-ord-< (car y) (cadr y)))
                   (consp (cdr y))
		   (o-infp (atoc (cdr y)))
                   (consp x)
		   (consp y))
	      (o< (o+ (make-ord (atoc (car x)) 1 0)
		      (cdr x))
		  (o+ (make-ord (atoc (car x)) 1 0)
		      (atoc (cdr y)))))
     :hints (("goal"
	      :use ((:instance |a < b  <=>  c+a < c+b|
			       (a (cdr x))
			       (b (atoc (cdr y)))
			       (c (make-ord (atoc (car x)) 1 0))))))))

  (local
   (defthm e0-ord-<-o<-help2
     (implies (and (consp x)
		   (consp y)
		   (e0-ordinalp x)
		   (e0-ordinalp y)
		   (equal (o-first-expt (atoc x))
			  (atoc (car x)))
		   (equal (o-first-expt (atoc y))
			  (atoc (car y)))
		   (implies (e0-ord-< (car x) (car y))
			    (o< (atoc (car x)) (atoc (car y))))

		   (implies (e0-ord-< (cdr x) (cdr y))
			    (o< (atoc (cdr x)) (atoc (cdr y))))
		   (e0-ord-< x y))
	      (o< (atoc x) (atoc y)))
     :rule-classes nil))

  (local
   (defthm e0-ord-<-o<-lemma
     (implies (and (e0-ordinalp x)
		   (e0-ordinalp y)
                   (consp x)
		   (consp y))
	      (and (equal (o-first-expt (atoc x))
			  (atoc (car x)))
		   (equal (o-first-expt (atoc y))
			  (atoc (car y)))
		   (implies (e0-ord-< x y)
			    (o< (atoc x)
				(atoc y)))))
     :rule-classes ((:rewrite :match-free :all))
     :instructions
     ((induct (ci x y))
      (promote)
      (claim (equal (o-first-expt (atoc x))
		    (atoc (car x)))
	     :hints (("goal"
		      :by e0-ord-<-o<-help1)))

      (claim (equal (o-first-expt (atoc y))
		    (atoc (car y)))
	     :hints (("goal"
		      :by (:instance e0-ord-<-o<-help1 (x y) (y x)))))
      (s)
      (promote)

      (use e0-ord-<-o<-help2)
      (promote)
      (drop 2 3 4 5 6 7)
      (demote 1)
      (dive 1 1)
      (s-prop)
      (top)
      (casesplit (equal (car x) (car y)))
      (bash)
      (demote 9)
      (dv 1)
      (expand)
      (s)
      (top)
      (promote)
      (dive 1 1 1)
      (s)
      (up)
      (s)
      (top)
      (casesplit (consp (car x)))
      (claim (consp (car y)))
      (bash)
      (drop 1 2)
      (bash))))

  (defthm e0-ord-<-o<
    (implies (and (e0-ordinalp x)
		  (e0-ordinalp y)
		  (e0-ord-< x y))
	     (o< (atoc x)
		 (atoc y)))
    :hints (("goal"
	     :do-not-induct t
	     :use e0-ord-<-o<-lemma)))

  (defthm o-first-expt-atoc
    (implies (and (consp x)
		  (e0-ordinalp x))
	     (equal (o-first-expt (atoc x))
		    (atoc (car x)))))))

(local
 (defthm atoc-not-<
   (implies (and (not (e0-ord-< a b))
                 (e0-ordinalp a)
		 (e0-ordinalp b))
	    (not (o< (atoc a)
		     (atoc b))))
   :instructions(pro
		 (casesplit (equal a b))
		 (= a b)
		 bash
		 (claim (e0-ord-< b a)
			:hints (("goal" :use e0-total-order)))
		 (claim (o< (atoc b) (atoc a)))
		 bash)))

(local
 (defun ind (x y)
   (if (atom y)
       (cons x y)
     (ind x (cdr y)))))

(local
 (defthm ctoa-o+
   (implies (and (o-p a)
		 (not (equal a 0))
		 (o-p b)
		 (not (o< a (o-first-expt b))))
	    (equal (ctoa (o+ (make-ord a 1 0) b))
		   (cons (ctoa a) (ctoa b))))
   :instructions(pro
		 (claim (o-p (make-ord a 1 0)))
		 (claim (not (o< (o-first-expt (make-ord a 1 0)) (o-first-expt b))))
		 (induct (ind a b))
		 pro
		 (casesplit (equal (o-first-expt b) a))
		 (claim (equal (o-first-expt (make-ord a 1 0)) (o-first-expt b)))
		 (dv 1)
		 x
		 top
		 bash
		 (claim (o< (o-first-expt b) (o-first-expt (make-ord a 1 0))))
		 (dv 1)
		 x
		 (dv 1)
		 x
		 top
		 bash
		 bash)))

(defthm |oa.x  =>  ctoa(atoc.x) = x|
  (implies (e0-ordinalp x)
	   (equal (ctoa (atoc x))
		  x))
  :instructions((induct (atoc x))
		(pro)
		(claim (e0-ordinalp (car x)))
		(claim (e0-ordinalp (cdr x)))
		(dv 1 1)
		x
		up
		(rewrite ctoa-o+)
		top
		bash
		bash
		bash
		bash
		bash
		(casesplit (atom (cdr x)))
		bash
		(dive 1 2)
		(rewrite o-first-expt-atoc)
		(claim (not (e0-ord-< (car x) (cadr x))))
		(claim (e0-ordinalp (cadr x)))
		top
		bash
		bash))

(defthm ctoa-=-equiv
  (implies (and (o-p x)
		(o-p y))
	   (equal (equal (ctoa x)
			 (ctoa y))
		  (equal x y)))
  :hints (("goal"
	   :do-not-induct t
	   :use ((:instance o<-e0-ord-<
			    (x y)
			    (y x))
		 (:instance o<-e0-ord-<)))))

(defthm atoc-=-equiv
 (implies (and (e0-ordinalp x)
	       (e0-ordinalp y))
	  (equal (equal (atoc x)
			(atoc y))
		 (equal x y)))
 :hints (("goal"
	  :do-not-induct t
	  :use ((:instance e0-ord-<-o<
			   (x y)
			   (y x))
		(:instance e0-ord-<-o<)))))

(defthm |oc.x  =>  atoc(ctoa.x) = x|
  (implies (o-p x)
	   (equal (atoc (ctoa x))
		  x))
  :hints (("goal"
	   :in-theory (disable ctoa-=-equiv)
	   :use ((:instance ctoa-=-equiv
			    (x (atoc (ctoa x)))
			    (y x))))))

(defthm ctoa-<-equiv
  (implies (and (o-p x)
		(o-p y))
	   (equal (e0-ord-< (ctoa x)
			    (ctoa y))
		  (o< x y)))
  :hints (("goal"
	   :use ((:instance e0-ord-<-o<
			    (x (ctoa x))
			    (y (ctoa y)))))))

(defthm atoc-<-equiv
  (implies (and (e0-ordinalp x)
		(e0-ordinalp y))
	   (equal (o< (atoc x)
		      (atoc y))
		  (e0-ord-< x y)))
  :hints (("goal"
	   :use ((:instance o<-e0-ord-<
			    (x (atoc x))
			    (y (atoc y)))))))

(defthm e0-ordinal-well-founded
  (and (implies (e0-ordinalp x) (o-p (atoc x)))
       (implies (and (e0-ordinalp x)
                     (e0-ordinalp y)
                     (e0-ord-< x y))
                (o< (atoc x) (atoc y))))
  :rule-classes :well-founded-relation)
