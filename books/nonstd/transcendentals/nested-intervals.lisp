(in-package "ACL2")

(include-book "nonstd/nsa/nsa" :dir :system)
(include-book "arithmetic/top" :dir :system)

(encapsulate
 ( ((nested-interval *) => * :formals (n) :guard (posp n))
   )

 (local
  (defun nested-interval (n)
    (cons (realfix (- (/ n))) (realfix (/ n)))
    ))

 (defthm nested-interval-reals
   (and (consp (nested-interval n))
	(realp (car (nested-interval n)))
	(realp (cdr (nested-interval n))))
   :rule-classes (:rewrite :type-prescription))

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (realp y))
	     (equal (< (- x) (- y))
		    (< y x)))
    :hints (("Goal"
	     :use ((:instance <-*-right-cancel
			      (x x)
			      (y y)
			      (z -1)))
	     :in-theory (disable <-*-right-cancel)))
    ))

 (defthm nested-intervals-are-intervals
   (implies (posp n)
	    (<= (car (nested-interval n)) (cdr (nested-interval n))))
   :rule-classes (:linear :rewrite))

 (defthm nested-intervals-are-nested
   (implies (and (posp m)
		 (posp n)
		 (< m n))
	    (and (<= (car (nested-interval m)) (car (nested-interval n)))
		 (>= (cdr (nested-interval m)) (cdr (nested-interval n)))))
   :rule-classes (:linear :rewrite))

)

(local
 (defun natural-induction (n)
   (if (zp n)
       n
     (natural-induction (1- n)))))

(local
 (defthm posp-boundary-must-be-one
   (implies (and (not (posp (+ -1 n)))
		 (posp n))
	    (equal n 1))
   :rule-classes nil
   ))

(defthm cdr-nested-interval-bounded-above
  (implies (posp n)
	   (<= (cdr (nested-interval n))
	       (cdr (nested-interval 1))))
  :hints (("Goal"
	   :induct (natural-induction n))
	  ("Subgoal *1/2"
	   :use ((:instance posp-boundary-must-be-one)
		 (:instance nested-intervals-are-nested
			    (m (1- n))
			    (n n)))
	   :in-theory (disable nested-intervals-are-nested))
	  )
)

(defthm car-nested-interval-bounded-above
  (implies (posp n)
	   (<= (car (nested-interval n))
	       (cdr (nested-interval 1))))
  :hints (("Goal"
	   :use ((:instance nested-intervals-are-intervals)
		 (:instance cdr-nested-interval-bounded-above))
	   :in-theory (disable nested-intervals-are-intervals
			       cdr-nested-interval-bounded-above)))

  )

(defthm-std nested-interval-bound-is-standard
  (standardp (cdr (nested-interval 1))))

(defthm-std nested-interval-car-is-standard
  (implies (standardp n)
	   (standardp (car (nested-interval n)))))

(defthm-std nested-interval-cdr-is-standard
  (implies (standardp n)
	   (standardp (cdr (nested-interval n)))))

(local
 (defthm car-nested-interval-bounded-below
   (implies (posp n)
	    (<= (car (nested-interval 1))
		(car (nested-interval n))))
   :hints (("Goal"
	    :use ((:instance nested-intervals-are-nested
			     (m 1)
			     (n n)))
	    :in-theory (disable nested-intervals-are-nested)))
   :rule-classes (:rewrite :linear)
   ))

(local
 (defthm cdr-nested-interval-bounded-below
   (implies (posp n)
	    (<= (car (nested-interval 1))
		(cdr (nested-interval n))))
   :hints (("Goal"
	    :use ((:instance nested-intervals-are-intervals)
		  (:instance car-nested-interval-bounded-below))
	    :in-theory (disable nested-intervals-are-intervals
				car-nested-interval-bounded-below)))
   :rule-classes (:rewrite :linear)
   ))

(local
 (defthm abs-bound
   (implies (and (realp x)
		 (realp l)
		 (realp u)
		 (<= l x)
		 (<= x u))
	    (<= (abs x)
		(max (abs l)
		     (abs u))))))

(local
 (defun double-bound ()
   (max (abs (car (nested-interval 1)))
	(abs (cdr (nested-interval 1))))))


(local
 (defthm car-nested-interval-bounded
   (implies (posp n)
	    (<= (abs (car (nested-interval n)))
		(double-bound)))
   :hints (("Goal"
	    :use ((:instance abs-bound
			     (x (car (nested-interval n)))
			     (l (car (nested-interval 1)))
			     (u (cdr (nested-interval 1))))
		  )
	    :in-theory (disable abs-bound)))
   ))

(local
 (defthm-std standard-double-bound
   (standardp (double-bound))))

(local
 (defthm realp-double-bound
   (and (realp (double-bound))
	(<= 0 (double-bound)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (in-theory (disable (double-bound))))

(local
 (defthm realp-car-nested-interval-n
   (realp (car (nested-interval n)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm realp-cdr-nested-interval-n
   (realp (cdr (nested-interval n)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm limited-double-bound
   (i-limited (double-bound))
 :hints (("Goal"
	  :use ((:instance standards-are-limited
			   (x (double-bound))))
	  :in-theory (disable standards-are-limited)))
 ))

(defthm car-nested-interval-is-limited
  (implies (posp n)
	   (i-limited (car (nested-interval n))))
  :hints (("Goal"
	   :use ((:instance large-if->-large
			    (x (car (nested-interval n)))
			    (y (double-bound)))
		 (:instance car-nested-interval-bounded)
		 )
	   :in-theory (disable large-if->-large
			       car-nested-interval-bounded
			       double-bound))
	  ))

(local
 (encapsulate
  ( ((car-interval-any-bound) => *) )

  (local
   (defun car-interval-any-bound ()
     (cdr (nested-interval 1))))

 (defthm car-interval-any-bound-is-real
   (realp (car-interval-any-bound))
   :rule-classes (:rewrite :type-prescription))

 (defthm car-interval-any-bound-is-bound-for-standards
   (implies (and (posp n)
		 (standardp n))
	    (<= (car (nested-interval n))
		(car-interval-any-bound))))
 ))

(local
 (defthm-std car-interval-any-bound-is-bound
   (implies (posp n)
	    (<= (car (nested-interval n))
		(car-interval-any-bound)))))

(defthm standard-element-less-than-standard-part-of-large-element
  (implies (and (posp m)
		(posp n)
		(standardp m)
		(i-large n))
	   (<= (car (nested-interval m))
	       (standard-part (car (nested-interval n)))))
  :hints (("Goal"
	   :use ((:instance standard-part-<=
			    (x (car (nested-interval m)))
			    (y (car (nested-interval n))))
		 (:instance large->-non-large
			    (x n)
			    (y m))
		 (:instance nested-intervals-are-nested))
	   :in-theory (disable standard-part-<=
			       large->-non-large
			       large-if->-large
			       nested-intervals-are-nested))))

(defun standard-part-car-interval-large ()
  (standard-part (car (nested-interval (i-large-integer)))))

(defthm standard-part-car-interval-large-is-standard
  (standardp (standard-part-car-interval-large))
  :hints (("Goal"
	   :use ((:instance standardp-standard-part
			    (x (car (nested-interval (i-large-integer))))))
	   :in-theory (disable standardp-standard-part)))
  )

(defun-std standard-part-car-interval-large-classical ()
  (standard-part-car-interval-large))

(defthm standard-part-car-interval-large-is-same
  (equal (standard-part-car-interval-large-classical)
	 (standard-part-car-interval-large)))

(local
 (defthm standard-part-car-interval-large-is-upper-bound-of-cars
   (implies (posp n)
	    (<= (car (nested-interval n))
		(standard-part-car-interval-large)))
   :hints (("Goal"
	    :use ((:functional-instance car-interval-any-bound-is-bound
					(car-interval-any-bound
					 standard-part-car-interval-large-classical)))))))




(local
 (encapsulate
  ( ((cdr-interval-any-bound) => *) )

  (local
   (defun cdr-interval-any-bound ()
     (car (nested-interval 1))))

  (defthm cdr-interval-any-bound-is-real
    (realp (cdr-interval-any-bound))
    :rule-classes (:rewrite :type-prescription))

  (defthm cdr-interval-any-bound-is-bound-for-standards
    (implies (and (posp n)
		  (standardp n))
	     (<= (cdr-interval-any-bound)
		 (cdr (nested-interval n)))))
  ))

(local
 (defthm-std cdr-interval-any-bound-is-bound
   (implies (posp n)
	    (<= (cdr-interval-any-bound)
		(cdr (nested-interval n))))))

(defthm standard-element-more-than-standard-part-of-large-element
  (implies (and (posp m)
		(posp n)
		(standardp m)
		(i-large n))
	   (<= (standard-part (cdr (nested-interval n)))
	       (cdr (nested-interval m))))
  :hints (("Goal"
	   :use ((:instance standard-part-<=
			    (x (cdr (nested-interval n)))
			    (y (cdr (nested-interval m))))
		 (:instance large->-non-large
			    (x n)
			    (y m))
		 (:instance nested-intervals-are-nested))
	   :in-theory (disable standard-part-<=
			       large->-non-large
			       large-if->-large
			       nested-intervals-are-nested))))

(local
 (defthm standard-part-car-interval-lower-bound-lemma
   (<= (standard-part (car (nested-interval (i-large-integer))))
       (standard-part (cdr (nested-interval (i-large-integer)))))
   :hints (("Goal"
	    :use ((:instance standard-part-<=
			    (x (car (nested-interval (i-large-integer))))
			    (y (cdr (nested-interval (i-large-integer)))))
		  (:instance nested-intervals-are-intervals (n (i-large-integer))))
	    :in-theory (disable standard-part-<=
				nested-intervals-are-intervals)))
   ))


(local
 (defthm standard-part-car-interval-satisfies-cdr-interval-any-bound-is-bound-for-standards
   (implies (and (posp n)
		 (standardp n))
	    (<= (standard-part-car-interval-large-classical)
		(cdr (nested-interval n))))
   :hints (("Goal"
	    :use ((:instance standard-part-car-interval-lower-bound-lemma)
		  (:instance standard-element-more-than-standard-part-of-large-element
			     (m n)
			     (n (i-large-integer))))
	    :in-theory (disable standard-part-car-interval-lower-bound-lemma
				standard-element-more-than-standard-part-of-large-element
				nested-intervals-are-intervals)))))

(local
 (defthm standard-part-car-interval-large-is-lower-bound-of-cdrs
   (implies (posp n)
	    (<= (standard-part-car-interval-large)
		(cdr (nested-interval n))))
   :hints (("Goal"
	    :use ((:functional-instance cdr-interval-any-bound-is-bound
					(cdr-interval-any-bound
					 standard-part-car-interval-large-classical))))
	   ("Subgoal 1"
	    :use ((:instance standard-part-car-interval-satisfies-cdr-interval-any-bound-is-bound-for-standards))
	    :in-theory (disable standard-part-car-interval-satisfies-cdr-interval-any-bound-is-bound-for-standards))
	   )))



(defthm standard-part-car-interval-in-intersection
  (and (realp (standard-part-car-interval-large))
       (implies (posp n)
		(and (<= (car (nested-interval n))
			 (standard-part-car-interval-large))
		     (<= (standard-part-car-interval-large)
			 (cdr (nested-interval n))))))
  :hints (("Goal"
	   :use ((:instance standard-part-car-interval-large-is-lower-bound-of-cdrs)
		 (:instance standard-part-car-interval-large-is-upper-bound-of-cars))
	   :in-theory (disable standard-part-car-interval-large-is-lower-bound-of-cdrs
			       standard-part-car-interval-large-is-upper-bound-of-cars)))
  :rule-classes nil)



