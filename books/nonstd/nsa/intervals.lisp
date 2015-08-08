(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "nsa")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(defun weak-interval-p (interval)
  (and (consp interval)
       (or (realp (car interval))
	   (and (consp (car interval))
		(realp (car (car interval))))
	   (equal (car interval) nil))
       (or (realp (cdr interval))
	   (and (consp (cdr interval))
		(realp (car (cdr interval))))
	   (equal (cdr interval) nil))))

(defun interval-left-inclusive-p (interval)
  (realp (car interval)))

(defun interval-right-inclusive-p (interval)
  (realp (cdr interval)))

(defun interval-left-endpoint (interval)
  (if (realp (car interval))
      (car interval)
      (if (consp (car interval))
	  (car (car interval))
	  nil)))

(defun interval-right-endpoint (interval)
  (if (realp (cdr interval))
      (cdr interval)
      (if (consp (cdr interval))
	  (car (cdr interval))
	  nil)))

(defthm weak-interval-left-endpoint-type-prescription
    (implies (weak-interval-p interval)
	     (or (realp (interval-left-endpoint interval))
		 (equal (interval-left-endpoint interval) nil)))
  :rule-classes (:type-prescription))

(defthm weak-interval-right-endpoint-type-prescription
    (implies (weak-interval-p interval)
	     (or (realp (interval-right-endpoint interval))
		 (equal (interval-right-endpoint interval) nil)))
  :rule-classes (:type-prescription))

(defthm weak-interval-inclusive-left-endpoint-type-prescription
    (implies (and (weak-interval-p interval)
		  (interval-left-inclusive-p interval))
	     (realp (interval-left-endpoint interval)))
  :rule-classes (:type-prescription))

(defthm weak-interval-inclusive-right-endpoint-type-prescription
    (implies (and (weak-interval-p interval)
		  (interval-right-inclusive-p interval))
	     (realp (interval-right-endpoint interval)))
  :rule-classes (:type-prescription))

(defun interval-p (interval)
  (and (weak-interval-p interval)
       (or (equal (interval-left-endpoint  interval) nil)
	   (equal (interval-right-endpoint interval) nil)
	   (if (and (interval-left-inclusive-p interval)
		    (interval-right-inclusive-p interval))
	       (<= (interval-left-endpoint interval)
		   (interval-right-endpoint interval))
	       (< (interval-left-endpoint interval)
		  (interval-right-endpoint interval))))))

(defthm interval-left-<=-right
    (implies (and (interval-p interval)
		  (interval-left-endpoint interval)
		  (interval-right-endpoint interval))
	     (<= (interval-left-endpoint interval)
		 (interval-right-endpoint interval)))
  :rule-classes (:rewrite :linear))

(defun interval (a b)
  (cons a b))

(defthm weak-interval-p-interval
    (implies (and (or (equal a nil)
		      (realp a)
		      (realp (car a)))
		  (or (equal b nil)
		      (realp b)
		      (realp (car b))))
	     (weak-interval-p (interval a b)))
  :rule-classes (:rewrite :type-prescription)
  )

(defthm interval-p-interval-inf-left
    (implies (and (equal a nil)
		  (or (equal b nil)
		      (realp b)
		      (realp (car b))))
	     (interval-p (interval a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm interval-p-interval-inf-right
    (implies (and (or (equal a nil)
		      (realp a)
		      (realp (car a)))
		  (equal b nil))
	     (interval-p (interval a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm interval-p-interval-closed-closed
    (implies (and (realp a)
		  (realp b)
		  (<= a b))
	     (interval-p (interval a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm interval-p-interval-closed-open
    (implies (and (realp a)
		  (realp (car b))
		  (< a (car b)))
	     (interval-p (interval a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm interval-p-interval-open-closed
    (implies (and (realp (car a))
		  (realp b)
		  (< (car a) b))
	     (interval-p (interval a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm interval-p-interval-open-open
    (implies (and (realp (car a))
		  (realp (car b))
		  (< (car a) (car b)))
	     (interval-p (interval a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm interval-left-inclusive-interval
    (implies (realp a)
	     (interval-left-inclusive-p (interval a b)))
  :rule-classes (:type-prescription))

(defthm interval-right-inclusive-interval
    (implies (realp b)
	     (interval-right-inclusive-p (interval a b)))
  :rule-classes (:type-prescription))

(defthm interval-p-is-weak-interval-p
    (implies (interval-p interval)
	     (weak-interval-p interval))
  :rule-classes (:type-prescription :forward-chaining))

(defthm interval-left-endpoint-interval
    (equal (interval-left-endpoint (interval a b))
	   (if (realp a)
	       a
	       (if (consp a)
		   (car a)
		   nil))))

(defthm interval-right-endpoint-interval
    (equal (interval-right-endpoint (interval a b))
	   (if (realp b)
	       b
	       (if (consp b)
		   (car b)
		   nil))))

(defun inside-interval-p (x interval)
  (and (realp x)
       (or (equal (interval-left-endpoint interval) nil)
	   (if (interval-left-inclusive-p interval)
	       (<= (interval-left-endpoint interval) x)
	       (< (interval-left-endpoint interval) x)))
       (or (equal (interval-right-endpoint interval) nil)
	   (if (interval-right-inclusive-p interval)
	       (<= x (interval-right-endpoint interval))
	       (< x (interval-right-endpoint interval))))))

(defthm inside-interval-is-real
    (implies (inside-interval-p x interval)
	     (realp x))
  :rule-classes (:forward-chaining))

(defthm inside-interval-p-contains-left-endpoint
    (implies (and (interval-left-inclusive-p interval)
		  (interval-p interval))
	     (inside-interval-p (interval-left-endpoint interval) interval))
  :rule-classes (:rewrite :type-prescription))

(defthm inside-interval-p-contains-right-endpoint
    (implies (and (interval-right-inclusive-p interval)
		  (interval-p interval))
	     (inside-interval-p (interval-right-endpoint interval) interval))
  :rule-classes (:rewrite :type-prescription))

(defthm inside-interval-p->=-left-endpoint
    (implies (and (inside-interval-p x interval)
		  (interval-left-endpoint interval))
	     (<= (interval-left-endpoint interval) x))
  :rule-classes (:rewrite :linear))

(defthm inside-interval-p-<=-right-endpoint
    (implies (and (inside-interval-p x interval)
		  (interval-right-endpoint interval))
	     (<= x (interval-right-endpoint interval)))
  :rule-classes (:rewrite :linear))

(defthm inside-interval-p-squeeze
    (implies (and (inside-interval-p a interval)
		  (inside-interval-p b interval)
		  (realp a)
		  (realp b)
		  (realp c)
		  (<= a c)
		  (<= c b))
	     (inside-interval-p c interval)))

(defthm inside-trivial-interval
    (implies (and (realp b)
		  (inside-interval-p a (interval b b)))
	     (equal a b))
  :rule-classes (:forward-chaining))

(defun before-interval-p (x interval)
  (and (realp x)
       (not (equal (interval-left-endpoint interval) nil))
       (if (interval-left-inclusive-p interval)
	   (< x (interval-left-endpoint interval))
	   (<= x (interval-left-endpoint interval)))))

(defthm before-interval-is-real
    (implies (before-interval-p x interval)
	     (realp x))
  :rule-classes (:forward-chaining))

(defthm before-interval-p-<=-left-endpoint
    (implies (before-interval-p x interval)
	     (<= x (interval-left-endpoint interval)))
  :rule-classes (:rewrite :linear))

(defthm before-interval-p-squeeze
    (implies (and (before-interval-p y interval)
		  (realp x)
		  (< x y))
	     (before-interval-p x interval))
  :rule-classes (:rewrite :type-prescription))

(defun after-interval-p (x interval)
  (and (realp x)
       (not (equal (interval-right-endpoint interval) nil))
       (if (interval-right-inclusive-p interval)
	   (> x (interval-right-endpoint interval))
	   (>= x (interval-right-endpoint interval)))))

(defthm after-interval-is-real
    (implies (after-interval-p x interval)
	     (realp x))
  :rule-classes (:forward-chaining))

(defthm after-interval-p->=-right-endpoint
    (implies (after-interval-p x interval)
	     (>= x (interval-right-endpoint interval)))
  :rule-classes (:rewrite :linear))

(defthm after-interval-p-squeeze
    (implies (and (after-interval-p y interval)
		  (realp x)
		  (> x y))
	     (after-interval-p x interval))
  :rule-classes (:rewrite :type-prescription))

(defthm inverse-before-inside-after-trichotomy
    (implies (and (realp x)
		  (not (before-interval-p x interval))
		  (not (after-interval-p x interval)))
	     (inside-interval-p x interval))
  :rule-classes (:rewrite :type-prescription))

(defthm before-exclusive-with-inside-and-after
    (implies (and (before-interval-p x interval)
		  (interval-p interval))
	     (and (not (inside-interval-p x interval))
		  (not (after-interval-p x interval))))
  :rule-classes (:forward-chaining))

(defthm inside-exclusive-with-before-and-after
    (implies (and (inside-interval-p x interval)
		  (interval-p interval))
	     (and (not (before-interval-p x interval))
		  (not (after-interval-p x interval))))
  :rule-classes (:forward-chaining))

(defthm after-exclusive-with-before-and-inside
    (implies (and (after-interval-p x interval)
		  (interval-p interval))
	     (and (not (before-interval-p x interval))
		  (not (inside-interval-p x interval))))
  :rule-classes (:forward-chaining))


(defun subinterval-p (subinterval interval)
  (and (interval-p subinterval)
       (interval-p interval)
       (or (equal (interval-left-endpoint interval) nil)
	   (and (realp (interval-left-endpoint subinterval))
		(if (and (not (interval-left-inclusive-p interval))
			 (interval-left-inclusive-p subinterval))
		    (< (interval-left-endpoint interval)
		       (interval-left-endpoint subinterval))
		    (<= (interval-left-endpoint interval)
			(interval-left-endpoint subinterval)))))
       (or (equal (interval-right-endpoint interval) nil)
	   (and (realp (interval-right-endpoint subinterval))
		(if (and (not (interval-right-inclusive-p interval))
			 (interval-right-inclusive-p subinterval))
		    (> (interval-right-endpoint interval)
		       (interval-right-endpoint subinterval))
		    (>= (interval-right-endpoint interval)
			(interval-right-endpoint subinterval)))))))

(defthm inside-subinterval
    (implies (and (inside-interval-p x subinterval)
		  (subinterval-p subinterval interval))
	     (inside-interval-p x interval))
  :rule-classes (:rewrite :forward-chaining))

(defthm inside-subinterval-2
    (implies (and (not (inside-interval-p x interval))
		  (subinterval-p subinterval interval))
	     (not (inside-interval-p x subinterval)))
  :rule-classes (:forward-chaining))

(defthm subinterval-interval-closed-closed
    (implies (and (realp a)
		  (realp b)
		  (<= a b)
		  (interval-p interval)
		  (inside-interval-p a interval)
		  (inside-interval-p b interval))
	     (subinterval-p (interval a b) interval)))

(defthm subinterval-interval-closed-open
    (implies (and (realp a)
		  (realp (car b))
		  (< a (car b))
		  (interval-p interval)
		  (inside-interval-p a interval)
		  (or (equal (interval-right-endpoint interval) nil)
		      (<= (car b) (interval-right-endpoint interval))))
	     (subinterval-p (interval a b) interval)))

(defthm subinterval-interval-open-closed
    (implies (and (realp (car a))
		  (realp b)
		  (< (car a) b)
		  (interval-p interval)
		  (or (equal (interval-left-endpoint interval) nil)
		      (<= (interval-left-endpoint interval) (car a)))
		  (inside-interval-p b interval))
	     (subinterval-p (interval a b) interval)))

(defthm subinterval-interval-open-open
    (implies (and (realp (car a))
		  (realp (car b))
		  (< (car a) (car b))
		  (interval-p interval)
		  (or (equal (interval-left-endpoint interval) nil)
		      (<= (interval-left-endpoint interval) (car a)))
		  (or (equal (interval-right-endpoint interval) nil)
		      (<= (car b) (interval-right-endpoint interval))))
	     (subinterval-p (interval a b) interval)))

(defthm subinterval-interval-inf-left
    (implies (and (equal a nil)
		  (or (equal b nil)
		      (realp b)
		      (realp (car b)))
		  (interval-p interval)
		  (equal (interval-left-endpoint interval) nil)
		  (or (equal (interval-right-endpoint interval) nil)
		      (and (not (equal b nil))
			   (if (and (not (interval-right-inclusive-p interval))
				    (realp b))
			       (<  b (interval-right-endpoint interval))
			       (<= (if (realp b) b (car b))
				   (interval-right-endpoint interval))))))
	     (subinterval-p (interval a b) interval)))

(defthm subinterval-interval-inf-right
    (implies (and (or (equal a nil)
		      (realp a)
		      (realp (car a)))
		  (equal b nil)
		  (interval-p interval)
		  (equal (interval-right-endpoint interval) nil)
		  (or (equal (interval-left-endpoint interval) nil)
		      (and (not (equal a nil))
			   (if (and (not (interval-left-inclusive-p interval))
				    (realp a))
			       (<  (interval-left-endpoint interval) a)
			       (<= (interval-left-endpoint interval)
				   (if (realp a) a (car a)))))))
	     (subinterval-p (interval a b) interval)))

(defthm not-inside-empty-interval
    (implies (and (or (realp a) (realp (car a)))
		  (or (realp b) (realp (car b)))
		  (< (if (realp b) b (car b))
		     (if (realp a) a (car a))))
	     (not (inside-interval-p x (interval a b)))))

(local
 (defthm close-squeeze
     (implies (and (realp x)
		   (realp y)
		   (realp z)
		   (<= x y)
		   (<= y z)
		   (i-close x z))
	      (i-close y z))
   :hints (("Goal"
	    :use ((:instance standard-part-squeeze))
	    :in-theory (enable nsa-theory)))
   :rule-classes nil))

(local
 (defthm close-standards-are-equal
     (implies (and (standardp x)
		   (standardp y)
		   (i-close x y))
	      (equal x y))
   :hints (("Goal" :in-theory (enable nsa-theory)))
   :rule-classes nil))

(defthm-std standard-interval-left-endpoint
    (implies (standardp interval)
	     (standardp (interval-left-endpoint interval)))
    :rule-classes (:rewrite :type-prescription))

(defthm-std standard-interval-right-endpoint
    (implies (standardp interval)
	     (standardp (interval-right-endpoint interval)))
    :rule-classes (:rewrite :type-prescription))

(defthm close-left-endpoint
    (implies (and (interval-p interval)
		  (before-interval-p x interval)
		  (inside-interval-p y interval)
		  (i-close x y))
	     (i-close (interval-left-endpoint interval) y))
  :hints (("Goal"
	   :use ((:instance close-squeeze
			    (x x)
			    (y (interval-left-endpoint interval))
			    (z y)))))
  )

(defthm close-left-and-right-endpoints
    (implies (and (interval-p interval)
		  (before-interval-p x interval)
		  (after-interval-p y interval)
		  (i-close x y))
	     (i-close (interval-left-endpoint interval)
		      (interval-right-endpoint interval)))
  :hints (("Goal"
	   :use ((:instance close-squeeze
			    (x x)
			    (y (interval-left-endpoint interval))
			    (z y))
		 (:instance close-squeeze
			    (x x)
			    (y (interval-right-endpoint interval))
			    (z y))
		 )))
  )

(defthm equal-left-and-right-endpoints
    (implies (and (interval-p interval)
		  (standardp interval)
		  (before-interval-p x interval)
		  (after-interval-p y interval)
		  (i-close x y))
	     (equal (interval-left-endpoint interval)
		    (interval-right-endpoint interval)))
  :hints (("Goal"
	   :use ((:instance close-standards-are-equal
			    (x (interval-left-endpoint interval))
			    (y (interval-right-endpoint interval)))
		 )
	   :in-theory (disable interval-p before-interval-p after-interval-p interval-left-endpoint interval-right-endpoint)
	   ))
  )

(defthm close-right-endpoint
    (implies (and (interval-p interval)
		  (inside-interval-p x interval)
		  (after-interval-p y interval)
		  (i-close x y))
	     (i-close (interval-right-endpoint interval) x))
  :hints (("Goal"
	   :use ((:instance close-squeeze
			    (x x)
			    (y (interval-right-endpoint interval))
			    (z y)))))
  )

(defthm-std standard-left-endpoint
    (implies (standardp interval)
	     (standardp (interval-left-endpoint interval))))


(defthm-std standard-right-endpoint
    (implies (standardp interval)
	     (standardp (interval-right-endpoint interval))))


(defthm standard-part-inside-interval
    (implies (and (interval-p interval)
		  (standardp interval)
		  (or (equal (interval-left-endpoint interval) nil)
		      (interval-left-inclusive-p interval))
		  (or (equal (interval-right-endpoint interval) nil)
		      (interval-right-inclusive-p interval))
		  (inside-interval-p x interval)
		  (i-limited x))
	     (inside-interval-p (standard-part x) interval))
  :hints (("Goal"
	   :use ((:instance STANDARD-PART-<=
			    (x (interval-left-endpoint interval))
			    (y x))
		 (:instance STANDARD-PART-<=
			    (x x)
			    (y (interval-right-endpoint interval)))
		 (:instance STANDARD-PART-OF-STANDARDP
			    (x (interval-left-endpoint interval)))
		 (:instance STANDARD-PART-OF-STANDARDP
			    (x (interval-right-endpoint interval)))
		 (:instance standard-left-endpoint)
		 (:instance standard-right-endpoint)
		 )
	   :in-theory (disable STANDARD-PART-<=
			       STANDARD-PART-OF-STANDARDP
			       standard-left-endpoint
			       standard-right-endpoint)))
  )

(defthm inside-standard-bounded-intervals-are-limited
    (implies (and (interval-p interval)
		  (standardp interval)
		  (interval-left-inclusive-p interval)
		  (interval-right-inclusive-p interval)
		  (inside-interval-p x interval))
	     (i-limited x))
  :hints (("Goal"
	   :use ((:instance large-if->-large
			    (x x)
			    (y (interval-right-endpoint interval)))
		 (:instance large-if->-large
			    (x (- x))
			    (y (- (interval-left-endpoint interval))))
		 (:instance standard-left-endpoint)
		 (:instance standard-right-endpoint)
		 (:instance standards-are-limited
			    (x (interval-left-endpoint interval)))
		 (:instance standards-are-limited
			    (x (interval-right-endpoint interval))))
	   :in-theory (disable large-if->-large standards-are-limited standard-left-endpoint standard-right-endpoint))))

(defthm interval-inside-infinite-interval
    (implies (and (realp x)
		  (realp y)
		  (< x y))
	     (subinterval-p (interval x y) (interval nil nil))))

(deftheory interval-definition-theory
    '(weak-interval-p
      interval-left-inclusive-p
      interval-right-inclusive-p
      interval-left-endpoint
      interval-right-endpoint
      interval-p
      interval
      (interval)
      inside-interval-p
      before-interval-p
      after-interval-p
      subinterval-p))

(in-theory (disable interval-definition-theory))


