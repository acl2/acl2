(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(include-book "nonstd/nsa/intervals" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(local (include-book "nonstd/integrals/split-integral-by-subintervals" :dir :system))

(encapsulate
 ( ((rifn-small *) => *)
   ((strict-int-rifn-small * *) => *)
   ((rifn-big *) => *)
   ((strict-int-rifn-big * *) => *)
   ((domain-rifn-cmp) => *)
   )

 (local
  (defun rifn-small (x)
    (declare (ignore x))
    0))

 (local
  (defun rifn-big (x)
    (declare (ignore x))
    0))

 (defthm rifn-small-real
   (implies (realp x)
	    (realp (rifn-small x))))
  (defthm rifn-big-real
   (implies (realp x)
	    (realp (rifn-big x))))

 (local
  (defun domain-rifn-cmp ()
    (interval nil nil)))

 (defthm domain-rifn-cmp-is-non-trivial-interval
   (and (interval-p (domain-rifn-cmp))
	(implies (and (interval-left-inclusive-p (domain-rifn-cmp))
		      (interval-right-inclusive-p (domain-rifn-cmp)))
		 (not (equal (interval-left-endpoint (domain-rifn-cmp))
			     (interval-right-endpoint (domain-rifn-cmp)))))))

 (defun map-rifn-small (p)
   ;; map rifn over the list p
   (if (consp p)
       (cons (rifn-small (car p))
	     (map-rifn-small (cdr p)))
     nil))
  (defun map-rifn-big (p)
   ;; map rifn over the list p
   (if (consp p)
       (cons (rifn-big (car p))
	     (map-rifn-big (cdr p)))
     nil))

  (defun riemann-rifn-small (p)
   ;; for partition p, take the Riemann sum of rifn over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-small (cdr p))))
  (defun riemann-rifn-big (p)
   ;; for partition p, take the Riemann sum of rifn over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-big (cdr p))))

  (local
   (defthm riemann-rifn-big-zero
     (implies (partitionp p)
	      (equal (riemann-rifn-big p) 0))))
  (local
   (defthm riemann-rifn-small-zero
     (implies (partitionp p)
	      (equal (riemann-rifn-small p) 0))))

  (local
   (defun-std strict-int-rifn-small (a b)
     (if (and (realp a)
	      (realp b)
	      (inside-interval-p a (domain-rifn-cmp))
	      (inside-interval-p b (domain-rifn-cmp))
	      (< a b))
	 (standard-part (riemann-rifn-small (make-small-partition a b)))
       0)))

  (local
   (defun-std strict-int-rifn-big (a b)
     (if (and (realp a)
	      (realp b)
	      (inside-interval-p a (domain-rifn-cmp))
	      (inside-interval-p b (domain-rifn-cmp))
	      (< a b))
	 (standard-part (riemann-rifn-big (make-small-partition a b)))
       0)))

  (defthm riemann-rifn-small-real
    (implies (partitionp p)
	     (realp (riemann-rifn-small p))))

  (defthm riemann-rifn-big-real
    (implies (partitionp p)
	     (realp (riemann-rifn-big p))))

  (defthm-std strict-int-rifn-small-real
    (implies (and (realp a)
		  (realp b))
	     (realp (strict-int-rifn-small a b))))

  (defthm-std strict-int-rifn-big-real
    (implies (and (realp a)
		  (realp b))
	     (realp (strict-int-rifn-big a b))))

 (local
  (defthm map-rifn-small-zero
    (implies (consp p)
	     (equal (car (map-rifn-small p)) 0))))
 (local
  (defthm map-rifn-big-zero
    (implies (consp p)
	     (equal (car (map-rifn-big p)) 0))))

 (defun int-rifn-small (a b)
   (if (<= a b)
       (strict-int-rifn-small a b)
     (- (strict-int-rifn-small b a))))

 (defun int-rifn-big (a b)
   (if (<= a b)
       (strict-int-rifn-big a b)
     (- (strict-int-rifn-big b a))))

 (defthm strict-int-rifn-small-is-integral-of-rifn-small
   (implies (and (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn-cmp))
		 (inside-interval-p b (domain-rifn-cmp))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rifn-small p)
		     (strict-int-rifn-small a b))))

 (defthm strict-int-rifn-big-is-integral-of-rifn-big
   (implies (and (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn-cmp))
		 (inside-interval-p b (domain-rifn-cmp))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rifn-big p)
		     (strict-int-rifn-big a b))))

 (defthm rifn-small-<=-rifn-big
   (implies (inside-interval-p x (domain-rifn-cmp))
	    (<= (rifn-small x)
		(rifn-big x))))
 )

(defthmd riemann-rifn-small-alternative
  (equal (riemann-rifn-small p)
	 (if (and (consp p) (consp (cdr p)))
	     (+ (riemann-rifn-small (cdr p))
		(* (- (cadr p) (car p))
		   (rifn-small (cadr p))))
	   0))
  :rule-classes :definition)

(defthmd riemann-rifn-big-alternative
  (equal (riemann-rifn-big p)
	 (if (and (consp p) (consp (cdr p)))
	     (+ (riemann-rifn-big (cdr p))
		(* (- (cadr p) (car p))
		   (rifn-big (cadr p))))
	   0))
  :rule-classes :definition)

(local (in-theory (enable riemann-rifn-small-alternative riemann-rifn-big-alternative)))
(local (in-theory (disable riemann-rifn-small riemann-rifn-big)))

(local
 (encapsulate
  nil

  (local
   (defthmd lemma-1
     (implies (<= x1 x2)
	      (<= (+ x1 y) (+ x2 y)))))

  (local
   (defthmd lemma-2
     (implies (and (realp y1)
		   (realp y2)
		   (realp z)
		   (<= y1 y2)
		   (<= 0 z))
	      (<= (* y1 z) (* y2 z)))))

  (local
   (defthmd lemma-3
     (implies (and (realp x1)
		   (realp x2)
		   (realp y1)
		   (realp y2)
		   (realp z)
		   (<= x1 x2)
		   (<= y1 y2)
		   (<= 0 z))
	      (<= (+ x1 (* y1 z)) (+ x2 (* y2 z))))
     :hints (("Goal"
	      :use ((:instance lemma-1
			       (x1 x1)
			       (x2 x2)
			       (y (* y1 z)))
		    (:instance lemma-2)
		    )
	      ))))

  (defthm member-partition->=-car-partition
    (implies (and (partitionp p)
		  (member x p))
	     (<= (car p) x)))

  (defthm car-partition-<=-car-last-partition
    (implies (partitionp p)
	     (<= (car p)
		 (car (last p)))))

  (defthm member-partition-<=-car-last-partition
    (implies (and (partitionp p)
		  (member x p))
	     (<= x (car (last p))))
    :hints (("Subgoal *1/2"
	     :use ((:instance car-partition-<=-car-last-partition))
	     :in-theory (disable car-partition-<=-car-last-partition))
	    ))

  (defthm realp-member-partition
    (implies (and (partitionp p)
		  (member x p))
	     (realp x)))

  (defthm member-partition-in-interval
    (implies (and (partitionp p)
		  (interval-p interval)
		  (inside-interval-p (first p) interval)
		  (inside-interval-p (car (last p)) interval)
		  (member x p))
	     (inside-interval-p x interval))
    :hints (("Goal"
	     :do-not-induct t
	     :use ((:instance inside-interval-p-squeeze
			      (a (first p))
			      (b (car (last p)))
			      (c x))
		   (:instance member-partition->=-car-partition)
		   (:instance member-partition-<=-car-last-partition)
		   )
	     :in-theory (disable inside-interval-p-squeeze
				 partitionp
				 member-partition->=-car-partition
				 member-partition-<=-car-last-partition))))


  (defthm member-cadr-p
    (implies (and ;(partitionp p)
	      (consp (cdr p)))
	     (member (cadr p) p)))

  (defthm real-riemann-rifn-small
    (implies (and (partitionp p)
		  (inside-interval-p (first p) (domain-rifn-cmp))
		  (inside-interval-p (car (last p)) (domain-rifn-cmp)))
	     (realp (riemann-rifn-small p))))

  (defthm real-riemann-rifn-big
    (implies (and (partitionp p)
		  (inside-interval-p (first p) (domain-rifn-cmp))
		  (inside-interval-p (car (last p)) (domain-rifn-cmp)))
	     (realp (riemann-rifn-big p))))

  (defthm riemann-rifn-small-<=-riemann-rifn-big
    (implies (and (partitionp p)
		  (inside-interval-p (first p) (domain-rifn-cmp))
		  (inside-interval-p (car (last p)) (domain-rifn-cmp)))
	     (<= (riemann-rifn-small p)
		 (riemann-rifn-big p)))
    :hints (("Subgoal *1/2"
	     :use ((:instance rifn-small-<=-rifn-big
			      (x (cadr p)))
		   (:instance lemma-3
			      (x1 (riemann-rifn-small (cdr p)))
			      (x2 (riemann-rifn-big (cdr p)))
			      (y1 (rifn-small (cadr p)))
			      (y2 (rifn-big (cadr p)))
			      (z (+ (- (car p)) (cadr p))))
		   (:instance real-riemann-rifn-small
			      (p (cdr p)))
		   (:instance real-riemann-rifn-big
			      (p (cdr p)))
		   )
	     :in-theory (disable rifn-small-<=-rifn-big
				 real-riemann-rifn-small
				 real-riemann-rifn-big
				 |(* x (+ y z))|)))
    )
  )
 )

(local
 (defthm riemann-rifn-small-partition-<=-riemann-rifn-big-partition
  (implies (and (inside-interval-p a (domain-rifn-cmp))
		(inside-interval-p b (domain-rifn-cmp))
		(< a b))
	    (<= (riemann-rifn-small (make-small-partition a b))
		(riemann-rifn-big (make-small-partition a b))))
  :hints (("Goal"
	   :use ((:instance riemann-rifn-small-<=-riemann-rifn-big
			    (p (make-small-partition a b))))
	   :in-theory (disable riemann-rifn-small-<=-riemann-rifn-big
			       riemann-rifn-small
			       riemann-rifn-big)))))

(local
 (defthm-std standard-strict-int-rifn-small
   (implies (and (standardp a)
		 (standardp b))
	    (standardp (strict-int-rifn-small a b)))))

(local
 (defthm-std standard-strict-int-rifn-big
   (implies (and (standardp a)
		 (standardp b))
	    (standardp (strict-int-rifn-big a b)))))

(local
 (defthm standards-not-large
   (implies (standardp x)
	    (not (i-large x)))
   :hints (("Goal"
	    :in-theory (enable i-large i-small)))
   ))

(local
 (defthm-std strict-integral-rifn-small-<=-strict-integral-rifn-big-1
   (implies (and (inside-interval-p a (domain-rifn-cmp))
		 (inside-interval-p b (domain-rifn-cmp))
		 (< a b))
	    (<= (strict-int-rifn-small a b)
		(strict-int-rifn-big a b)
		))
   :hints (("Goal"
	    :use ((:instance standard-part-<=
			     (x (riemann-rifn-small (make-small-partition a b)))
			     (y (riemann-rifn-big (make-small-partition a b))))
		  (:instance close-x-y->same-standard-part
			     (x (strict-int-rifn-small a b))
			     (y (riemann-rifn-small (make-small-partition a b))))
		  (:instance close-x-y->same-standard-part
			     (x (strict-int-rifn-big a b))
			     (y (riemann-rifn-big (make-small-partition a b))))
		  (:instance strict-int-rifn-small-is-integral-of-rifn-small
			     (p (make-small-partition a b)))
		  (:instance strict-int-rifn-big-is-integral-of-rifn-big
			     (p (make-small-partition a b)))
		  )
	    :in-theory (disable mesh
				standard-part-<=
				close-x-y->same-standard-part
				strict-int-rifn-small-is-integral-of-rifn-small
				strict-int-rifn-big-is-integral-of-rifn-big)))
   ))

(defthm integral-of-single-point-for-rifn-small
  (implies (and ;(realp a)
		(inside-interval-p a (domain-rifn-cmp)))
	   (equal (strict-int-rifn-small a a) 0))
  :hints (("Goal"
	   :use ((:functional-instance integral-of-single-point
				       (domain-rifn domain-rifn-cmp)
				       (rifn rifn-small)
				       (strict-int-rifn strict-int-rifn-small)
				       (map-rifn map-rifn-small)
				       (riemann-rifn riemann-rifn-small)))
	   :in-theory (enable riemann-rifn-small))
	  ("Subgoal 4"
	   :use ((:instance strict-int-rifn-small-is-integral-of-rifn-small))
	   :in-theory (disable strict-int-rifn-small-is-integral-of-rifn-small))
	  ))

(defthm integral-of-single-point-for-rifn-big
  (implies (and ;(realp a)
		(inside-interval-p a (domain-rifn-cmp)))
	   (equal (strict-int-rifn-big a a) 0))
  :hints (("Goal"
	   :use ((:functional-instance integral-of-single-point
				       (domain-rifn domain-rifn-cmp)
				       (rifn rifn-big)
				       (strict-int-rifn strict-int-rifn-big)
				       (map-rifn map-rifn-big)
				       (riemann-rifn riemann-rifn-big)))
	   :in-theory (enable riemann-rifn-big))
	  ("Subgoal 4"
	   :use ((:instance strict-int-rifn-big-is-integral-of-rifn-big))
	   :in-theory (disable strict-int-rifn-big-is-integral-of-rifn-big))
	  ))


(local
 (defthm strict-integral-rifn-small-<=-strict-integral-rifn-big-2
   (implies (and (inside-interval-p a (domain-rifn-cmp))
		 (inside-interval-p b (domain-rifn-cmp))
		 (<= a b))
	    (<= (strict-int-rifn-small a b)
		(strict-int-rifn-big a b)
		))
   :hints (("Goal"
	    :use ((:instance strict-integral-rifn-small-<=-strict-integral-rifn-big-1))
	    :in-theory (disable mesh
				strict-integral-rifn-small-<=-strict-integral-rifn-big-1)))))


(defthm integral-rifn-small-<=-integral-rifn-big
  (implies (and (inside-interval-p a (domain-rifn-cmp))
		(inside-interval-p b (domain-rifn-cmp))
		(<= a b)
		)
	   (<= (int-rifn-small a b)
	       (int-rifn-big a b)
	       ))
  )


;--------------------------

(encapsulate
 ( ((rifn-const) => *)
   ((rifn-const-fn *) => *)
   ((strict-int-rifn-const-fn * *) => *)
   ((domain-rifn-const-fn) => *)
   )

 (local
  (defun rifn-const ()
    0))

 (local
  (defun rifn-const-fn (x)
    (declare (ignore x))
    0))

 (defthm rifn-const-real
   (realp (rifn-const)))

 (defthm rifn-const-fn-real
   (implies (realp x)
	    (realp (rifn-const-fn x))))

 (local
  (defun domain-rifn-const-fn ()
    (interval nil nil)))

 (defthm domain-rifn-const-fn-is-non-trivial-interval
   (and (interval-p (domain-rifn-const-fn))
	(implies (and (interval-left-inclusive-p (domain-rifn-const-fn))
		      (interval-right-inclusive-p (domain-rifn-const-fn)))
		 (not (equal (interval-left-endpoint (domain-rifn-const-fn))
			     (interval-right-endpoint (domain-rifn-const-fn)))))))

 (defun map-rifn-const-fn (p)
   ;; map rifn over the list p
   (if (consp p)
       (cons (rifn-const-fn (car p))
	     (map-rifn-const-fn (cdr p)))
     nil))

 (local
  (defthm map-rifn-const-fn-zero
    (implies (consp p)
	     (equal (car (map-rifn-const-fn p)) 0))))

 (defun riemann-rifn-const-fn (p)
   ;; for partition p, take the Riemann sum of rifn over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-const-fn (cdr p))))

 (local
  (defthm riemann-rifn-const-fn-zero
    (implies (partitionp p)
	     (equal (riemann-rifn-const-fn p) 0))))

 (local
  (defun-std strict-int-rifn-const-fn (a b)
    (if (and (realp a)
	     (realp b)
	     (inside-interval-p a (domain-rifn-const-fn))
	     (inside-interval-p b (domain-rifn-const-fn))
	     (< a b))
	(standard-part (riemann-rifn-const-fn (make-small-partition a b)))
      0)))

 (defthm-std strict-int-rifn-const-fn-real
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-const-fn a b))))

 (defun int-rifn-const-fn (a b)
   (if (<= a b)
       (strict-int-rifn-const-fn a b)
     (- (strict-int-rifn-const-fn b a))))

 (defthm strict-int-rifn-const-fn-is-integral-of-rifn-const-fn
   (implies (and (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn-const-fn))
		 (inside-interval-p b (domain-rifn-const-fn))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rifn-const-fn p)
		     (strict-int-rifn-const-fn a b))))
 )


(defun rifn-const*const-fn (x)
  (* (rifn-const)
     (rifn-const-fn x)))

(defun map-rifn-const*const-fn (p)
  (if (consp p)
      (cons (rifn-const*const-fn (car p))
	    (map-rifn-const*const-fn (cdr p)))
    nil))

(defun riemann-rifn-const*const-fn (p)
  (dotprod (deltas p)
	   (map-rifn-const*const-fn (cdr p))))

(local
 (defun scale-list (s l)
   (if (consp l)
       (cons (* s (car l))
	     (scale-list s (cdr l)))
     nil)))

(local
 (defthm reduce-map-rifn-const*const-fn
   (equal (map-rifn-const*const-fn p)
	  (scale-list (rifn-const)
		      (map-rifn-const-fn p)))))

(local
 (defthm maptimes-scale-2
   (equal (map-times xs (scale-list s ys))
	  (scale-list s (map-times xs ys)))))

(local
 (defthm sumlist-scale
   (equal (sumlist (scale-list s l))
	  (* s (sumlist l)))))

(local
 (defthm dotprod-scale-2
   (equal (dotprod xs (scale-list s ys))
	  (* s (dotprod xs ys)))))

(local
 (defthm reduce-riemann-rifn-const*const-fn
   (equal (riemann-rifn-const*const-fn p)
	  (* (rifn-const)
	     (riemann-rifn-const-fn p)))))

(local
 (defthm-std strict-int-rifn-const-fn-standard
   (implies (and (standardp a)
		 (standardp b))
	    (standardp (strict-int-rifn-const-fn a b)))))

(local
 (defthm limited-riemann-rifn-const-fn
   (implies (and (standardp a)
		 (standardp b)
		 (< a b)
		 (inside-interval-p a (domain-rifn-const-fn))
		 (inside-interval-p b (domain-rifn-const-fn)))
	    (i-limited (riemann-rifn-const-fn (make-small-partition a b))))
   :hints (("Goal"
	    :use ((:instance strict-int-rifn-const-fn-is-integral-of-rifn-const-fn
			     (p (make-small-partition a b)))
		  (:instance i-close-limited
			     (x (strict-int-rifn-const-fn a b))
			     (y (riemann-rifn-const-fn (make-small-partition a b))))
		  (:instance strict-int-rifn-const-fn-standard)
		  )
	    :in-theory (disable strict-int-rifn-const-fn-is-integral-of-rifn-const-fn
				i-close-limited
				i-close-large
				i-close-large-2
				riemann-rifn-const-fn
				strict-int-rifn-const-fn-standard
				mesh)))))

(local
 (defthm-std standard-rifn-const
   (standardp (rifn-const))))

(defthm limited-riemann-rifn-const*const-fn
  (implies (and (standardp a)
		(standardp b)
		(< a b)
		(inside-interval-p a (domain-rifn-const-fn))
		(inside-interval-p b (domain-rifn-const-fn)))
	   (i-limited (riemann-rifn-const*const-fn (make-small-partition a b))))
  :hints (("Goal"
	   :use ((:instance limited-riemann-rifn-const-fn)
		 (:instance reduce-riemann-rifn-const*const-fn
			    (p (make-small-partition a b))))
	   :in-theory (disable limited-riemann-rifn-const-fn
			       reduce-riemann-rifn-const*const-fn
			       riemann-rifn-const-fn
			       riemann-rifn-const*const-fn
			       make-small-partition))))

(encapsulate
 nil

 (local (in-theory (disable riemann-rifn-const*const-fn reduce-riemann-rifn-const*const-fn)))

 (defun-std strict-int-rifn-const*const-fn (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (domain-rifn-const-fn))
	    (inside-interval-p b (domain-rifn-const-fn))
	    (< a b))
       (standard-part (riemann-rifn-const*const-fn (make-small-partition a b)))
     0)))

(local
 (defthmd close-times
   (implies (and (i-close y1 y2)
		 (i-limited x))
	    (i-close (* x y1) (* x y2)))
   :hints (("Goal"
	    :use ((:instance limited*small->small
			     (x x)
			     (y (- y1 y2))))
	    :in-theory (e/d (i-close)
			    (limited*small->small))))))

(encapsulate
 nil

 (local
  (defthmd lemma-1
    (implies (and (inside-interval-p a (domain-rifn-const-fn))
		  (inside-interval-p b (domain-rifn-const-fn))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (i-close (strict-int-rifn-const*const-fn a b)
		      (riemann-rifn-const*const-fn (make-small-partition a b))))
    :hints (("Goal"
	     :use ((:instance standard-part-close
			      (x (riemann-rifn-const*const-fn (make-small-partition a b))))
		   (:instance limited-riemann-rifn-const*const-fn))
	     :in-theory (disable standard-part-close)))))

 (local
  (defthmd lemma-2
    (implies (and (inside-interval-p a (domain-rifn-const-fn))
		  (inside-interval-p b (domain-rifn-const-fn))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (i-close (strict-int-rifn-const*const-fn a b)
		      (* (rifn-const)
			 (riemann-rifn-const-fn (make-small-partition a b)))))
    :hints (("Goal"
	     :use ((:instance lemma-1))))))

 (local
  (defthmd lemma-3
    (implies (and (inside-interval-p a (domain-rifn-const-fn))
		  (inside-interval-p b (domain-rifn-const-fn))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (i-close (strict-int-rifn-const*const-fn a b)
		      (* (rifn-const)
			 (strict-int-rifn-const-fn a b))))
    :hints (("Goal"
	     :use ((:instance lemma-2)
		   (:instance close-times
			      (x (rifn-const))
			      (y1 (riemann-rifn-const-fn (make-small-partition a b)))
			      (y2 (strict-int-rifn-const-fn a b)))
		   (:instance strict-int-rifn-const-fn-is-integral-of-rifn-const-fn
			      (p (make-small-partition a b))))
	     :in-theory (disable strict-int-rifn-const*const-fn
				 riemann-rifn-const-fn
				 strict-int-rifn-const-fn-is-integral-of-rifn-const-fn
				 mesh)))))

 (local
  (defthm-std lemma-4
    (implies (and (standardp a)
		  (standardp b))
	     (STANDARDP (+ (STRICT-INT-RIFN-CONST*CONST-FN A B)
			   (- (* (RIFN-CONST)
				 (STRICT-INT-RIFN-CONST-FN A B))))))))

 (local
  (defthmd lemma-5
    (implies (and (inside-interval-p a (domain-rifn-const-fn))
		  (inside-interval-p b (domain-rifn-const-fn))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (equal (strict-int-rifn-const*const-fn a b)
		    (* (rifn-const)
		       (strict-int-rifn-const-fn a b))))
    :hints (("Goal"
	     :use ((:instance lemma-3)
		   (:instance standard-small-is-zero
			      (x (- (strict-int-rifn-const*const-fn a b)
				    (* (rifn-const)
				       (strict-int-rifn-const-fn a b))))))
	     :in-theory (e/d (i-close)
			     (strict-int-rifn-const*const-fn))))))

 (local
  (defthmd close-to-standard-is-close-1
    (implies (and (i-close x y)
		  (standardp x)
		  (standardp y))
	     (equal (equal x y) t))
    :hints (("Goal"
	     :in-theory (enable i-close i-small)))))

 (local
  (defthm-std strict-int-rifn-const-fn-of-single-point
    (implies (and (realp a)
		  (inside-interval-p a (domain-rifn-const-fn)))
	     (equal (strict-int-rifn-const-fn a a) 0))
    :hints (("Goal'"
	     :use ((:instance strict-int-rifn-const-fn-is-integral-of-rifn-const-fn
			      (a a)
			      (b a)
			      (p (list a)))
		   (:instance close-to-standard-is-close-1
			      (x 0)
			      (y (strict-int-rifn-const-fn a a)))
		   )
	     :in-theory (disable
			 strict-int-rifn-const-fn-is-integral-of-rifn-const-fn)))))

 (local
  (defthm-std strict-int-rifn-const*const-fn-of-single-point
    (implies (and (realp a)
		  (inside-interval-p a (domain-rifn-const-fn)))
	     (equal (strict-int-rifn-const*const-fn a a) 0))
    :hints (("Goal'"
	     :use ((:instance strict-int-rifn-const-fn-is-integral-of-rifn-const-fn
			      (a a)
			      (b a)
			      (p (list a)))
		   (:instance close-to-standard-is-close-1
			      (x 0)
			      (y (strict-int-rifn-const*const-fn a a)))
		   )
	     :in-theory (disable
			 strict-int-rifn-const-fn-is-integral-of-rifn-const-fn)))))

 (local
  (defun zero-deltas (p)
    (if (consp p)
	(cons 0 (zero-deltas (cdr p)))
      nil)))

 (local
  (defthmd lemma-6
    (implies (and (acl2-numberp a)
		  (natp n))
	     (equal (car (make-partition-rec a 0 n))
		    a))))

 (local
  (defthmd lemma-7
    (implies (and (acl2-numberp a)
		  (natp n))
	     (equal (deltas (make-partition-rec a 0 n))
		    (zero-deltas (cdr (make-partition-rec a 0 n)))))
    :hints (("Goal"
	     :in-theory (enable lemma-6)))))

 (local
  (defthmd lemma-8
    (implies (and (inside-interval-p a (domain-rifn-const-fn))
		  (natp n))
	     (equal (riemann-rifn-const*const-fn (make-partition-rec a 0 n))
		    0))
    :hints (("Goal"
	     :in-theory (enable lemma-7)))))


 (local
  (defthmd lemma-9
    (implies (and (inside-interval-p a (domain-rifn-const-fn))
		  (inside-interval-p b (domain-rifn-const-fn))
		  (= a b)
		  (standardp a)
		  (standardp b))
	     (equal (strict-int-rifn-const*const-fn a b)
		    (* (rifn-const)
		       (strict-int-rifn-const-fn a b))))
    :hints (("Goal"
	     :use ((:instance lemma-5)
		   (:instance lemma-7))))))

 (defthm-std reduce-strict-integral-rifn-const*const-fn
   (implies (and (inside-interval-p a (domain-rifn-const-fn))
		 (inside-interval-p b (domain-rifn-const-fn))
		 (<= a b))
	    (equal (strict-int-rifn-const*const-fn a b)
		   (* (rifn-const)
		      (strict-int-rifn-const-fn a b))))
   :hints (("Goal"
	    :use ((:instance lemma-5)
		  (:instance lemma-9))
	    :in-theory (disable riemann-rifn-const-fn
				strict-int-rifn-const*const-fn)
	    )))
 )

(defun int-rifn-const*const-fn (a b)
  (if (<= a b)
      (strict-int-rifn-const*const-fn a b)
    (- (strict-int-rifn-const*const-fn b a))))

(defthm reduce-integral-rifn-const*const-fn
  (implies (and (inside-interval-p a (domain-rifn-const-fn))
		(inside-interval-p b (domain-rifn-const-fn)))
	   (equal (int-rifn-const*const-fn a b)
		  (* (rifn-const)
		     (int-rifn-const-fn a b))))
  :hints (("Goal"
	   :cases ((<= a b)))))

(defthm strict-int-rifn-const*const-fn-is-integral-of-rifn-const*const-fn
  (implies (and (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (domain-rifn-const-fn))
		(inside-interval-p b (domain-rifn-const-fn))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rifn-const*const-fn p)
		    (strict-int-rifn-const*const-fn a b)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance close-times
			    (x (rifn-const))
			    (y1 (RIEMANN-RIFN-CONST-FN P))
			    (y2 (STRICT-INT-RIFN-CONST-FN a b)))
		 (:instance strict-int-rifn-const-fn-is-integral-of-rifn-const-fn))
	   :in-theory (disable strict-int-rifn-const*const-fn
			       riemann-rifn-const-fn
			       riemann-rifn-const*const-fn
			       strict-int-rifn-const-fn-is-integral-of-rifn-const-fn))))

;--------------------------

(encapsulate
 ( ((rifn-left *) => *)
   ((strict-int-rifn-left * *) => *)
   ((rifn-right *) => *)
   ((strict-int-rifn-right * *) => *)
   ((domain-rifn-op) => *)
   )

 (local
  (defun rifn-left (x)
    (declare (ignore x))
    0))

 (local
  (defun rifn-right (x)
    (declare (ignore x))
    0))

 (defthm rifn-left-real
   (implies (realp x)
	    (realp (rifn-left x))))
  (defthm rifn-right-real
   (implies (realp x)
	    (realp (rifn-right x))))

 (local
  (defun domain-rifn-op ()
    (interval nil nil)))

 (defthm domain-rifn-op-is-non-trivial-interval
   (and (interval-p (domain-rifn-op))
	(implies (and (interval-left-inclusive-p (domain-rifn-op))
		      (interval-right-inclusive-p (domain-rifn-op)))
		 (not (equal (interval-left-endpoint (domain-rifn-op))
			     (interval-right-endpoint (domain-rifn-op)))))))

 (defun map-rifn-left (p)
   ;; map rifn over the list p
   (if (consp p)
       (cons (rifn-left (car p))
	     (map-rifn-left (cdr p)))
     nil))
  (defun map-rifn-right (p)
   ;; map rifn over the list p
   (if (consp p)
       (cons (rifn-right (car p))
	     (map-rifn-right (cdr p)))
     nil))

  (defun riemann-rifn-left (p)
   ;; for partition p, take the Riemann sum of rifn over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-left (cdr p))))
  (defun riemann-rifn-right (p)
   ;; for partition p, take the Riemann sum of rifn over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-right (cdr p))))

  (local
   (defthm riemann-rifn-right-zero
     (implies (partitionp p)
	      (equal (riemann-rifn-right p) 0))))
  (local
   (defthm riemann-rifn-left-zero
     (implies (partitionp p)
	      (equal (riemann-rifn-left p) 0))))

  (local
   (defun-std strict-int-rifn-left (a b)
     (if (and (realp a)
	      (realp b)
	      (inside-interval-p a (domain-rifn-op))
	      (inside-interval-p b (domain-rifn-op))
	      (< a b))
	 (standard-part (riemann-rifn-left (make-small-partition a b)))
       0)))

  (local
   (defun-std strict-int-rifn-right (a b)
     (if (and (realp a)
	      (realp b)
	      (inside-interval-p a (domain-rifn-op))
	      (inside-interval-p b (domain-rifn-op))
	      (< a b))
	 (standard-part (riemann-rifn-right (make-small-partition a b)))
       0)))

  (defthm riemann-rifn-left-real
    (implies (partitionp p)
	     (realp (riemann-rifn-left p))))

  (defthm riemann-rifn-right-real
    (implies (partitionp p)
	     (realp (riemann-rifn-right p))))

  (defthm-std strict-int-rifn-left-real
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-left a b))))
  (defthm-std strict-int-rifn-right-real
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-right a b))))

 (local
  (defthm map-rifn-left-zero
    (implies (consp p)
	     (equal (car (map-rifn-left p)) 0))))
 (local
  (defthm map-rifn-right-zero
    (implies (consp p)
	     (equal (car (map-rifn-right p)) 0))))

 (defun int-rifn-left (a b)
   (if (<= a b)
       (strict-int-rifn-left a b)
     (- (strict-int-rifn-left b a))))

 (defun int-rifn-right (a b)
   (if (<= a b)
       (strict-int-rifn-right a b)
     (- (strict-int-rifn-right b a))))

 (defthm strict-int-rifn-left-is-integral-of-rifn-left
   (implies (and (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn-op))
		 (inside-interval-p b (domain-rifn-op))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rifn-left p)
		     (strict-int-rifn-left a b))))

 (defthm strict-int-rifn-right-is-integral-of-rifn-right
   (implies (and (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn-op))
		 (inside-interval-p b (domain-rifn-op))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rifn-right p)
		     (strict-int-rifn-right a b))))

 )

(defthmd riemann-rifn-left-alternative
  (equal (riemann-rifn-left p)
	 (if (and (consp p) (consp (cdr p)))
	     (+ (riemann-rifn-left (cdr p))
		(* (- (cadr p) (car p))
		   (rifn-left (cadr p))))
	   0))
  :rule-classes :definition)

(defthmd riemann-rifn-right-alternative
  (equal (riemann-rifn-right p)
	 (if (and (consp p) (consp (cdr p)))
	     (+ (riemann-rifn-right (cdr p))
		(* (- (cadr p) (car p))
		   (rifn-right (cadr p))))
	   0))
  :rule-classes :definition)

(local (in-theory (enable riemann-rifn-left-alternative
			  riemann-rifn-right-alternative)))
(local (in-theory (disable riemann-rifn-left riemann-rifn-right)))

(defun rifn-left+right (x)
  (+ (rifn-left x)
     (rifn-right x)))

(defun map-rifn-left+right (p)
  (if (consp p)
      (cons (rifn-left+right (car p))
	    (map-rifn-left+right (cdr p)))
    nil))

(defun riemann-rifn-left+right (p)
  (dotprod (deltas p)
	   (map-rifn-left+right (cdr p))))

(defthmd riemann-rifn-left+right-alternative
  (equal (riemann-rifn-left+right p)
	 (if (and (consp p) (consp (cdr p)))
	     (+ (riemann-rifn-left+right (cdr p))
		(* (- (cadr p) (car p))
		   (rifn-left+right (cadr p))))
	   0))
  :rule-classes :definition)

(local (in-theory (enable riemann-rifn-left+right-alternative)))
(local (in-theory (disable riemann-rifn-left+right)))

(local
 (defun reduce-riemann-rifn-left+right-induction (p)
   (if (and (consp p) (consp (cdr p)))
       (1+ (reduce-riemann-rifn-left+right-induction (cdr p)))
     0)))


(local
 (defthm reduce-riemann-rifn-left+right
   (equal (riemann-rifn-left+right p)
	  (+ (riemann-rifn-left p)
	     (riemann-rifn-right p)))
   :hints (("Goal"
	    :induct (reduce-riemann-rifn-left+right-induction p)))
   ))

(local
 (defthm-std strict-int-rifn-left-standard
   (implies (and (standardp a)
		 (standardp b))
	    (standardp (strict-int-rifn-left a b)))))

(local
 (defthm limited-riemann-rifn-left
   (implies (and (standardp a)
		 (standardp b)
		 (< a b)
		 (inside-interval-p a (domain-rifn-op))
		 (inside-interval-p b (domain-rifn-op)))
	    (i-limited (riemann-rifn-left (make-small-partition a b))))
   :hints (("Goal"
	    :use ((:instance strict-int-rifn-left-is-integral-of-rifn-left
			     (p (make-small-partition a b)))
		  (:instance i-close-limited
			     (x (strict-int-rifn-left a b))
			     (y (riemann-rifn-left (make-small-partition a b))))
		  (:instance strict-int-rifn-left-standard)
		  )
	    :in-theory (disable strict-int-rifn-left-is-integral-of-rifn-left
				i-close-limited
				i-close-large
				i-close-large-2
				riemann-rifn-left
				strict-int-rifn-left-standard
				mesh)))))


(local
 (defthm-std strict-int-rifn-right-standard
   (implies (and (standardp a)
		 (standardp b))
	    (standardp (strict-int-rifn-right a b)))))

(local
 (defthm limited-riemann-rifn-right
   (implies (and (standardp a)
		 (standardp b)
		 (< a b)
		 (inside-interval-p a (domain-rifn-op))
		 (inside-interval-p b (domain-rifn-op)))
	    (i-limited (riemann-rifn-right (make-small-partition a b))))
   :hints (("Goal"
	    :use ((:instance strict-int-rifn-right-is-integral-of-rifn-right
			     (p (make-small-partition a b)))
		  (:instance i-close-limited
			     (x (strict-int-rifn-right a b))
			     (y (riemann-rifn-right (make-small-partition a b))))
		  (:instance strict-int-rifn-right-standard)
		  )
	    :in-theory (disable strict-int-rifn-right-is-integral-of-rifn-right
				i-close-limited
				i-close-large
				i-close-large-2
				riemann-rifn-right
				strict-int-rifn-right-standard
				mesh)))))

(defthm limited-riemann-rifn-left+right
  (implies (and (standardp a)
		(standardp b)
		(< a b)
		(inside-interval-p a (domain-rifn-op))
		(inside-interval-p b (domain-rifn-op)))
	   (i-limited (riemann-rifn-left+right (make-small-partition a b)))))

(encapsulate
 nil

 (local (in-theory (disable riemann-rifn-left+right
			    reduce-riemann-rifn-left+right)))

 (defun-std strict-int-rifn-left+right (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (domain-rifn-op))
	    (inside-interval-p b (domain-rifn-op))
	    (< a b))
       (standard-part (riemann-rifn-left+right (make-small-partition a b)))
     0)))

(local
 (defthmd close-plus
   (implies (and (i-close x1 y1)
		 (i-close x2 y2))
	    (i-close (+ x1 x2) (+ y1 y2)))
   :hints (("Goal"
	    :in-theory (enable i-close)))))

(encapsulate
 nil

 (local
  (defthmd lemma-1
    (implies (and (inside-interval-p a (domain-rifn-op))
		  (inside-interval-p b (domain-rifn-op))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (i-close (strict-int-rifn-left+right a b)
		      (riemann-rifn-left+right (make-small-partition a b))))
    :hints (("Goal"
	     :use ((:instance standard-part-close
			      (x (riemann-rifn-left+right (make-small-partition a b))))
		   (:instance limited-riemann-rifn-left+right))
	     :in-theory (disable standard-part-close)))))

 (local
  (defthmd lemma-2
    (implies (and (inside-interval-p a (domain-rifn-op))
		  (inside-interval-p b (domain-rifn-op))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (i-close (strict-int-rifn-left+right a b)
		      (+ (riemann-rifn-left (make-small-partition a b))
			 (riemann-rifn-right (make-small-partition a b)))))
    :hints (("Goal"
	     :use ((:instance lemma-1))))))

 (local
  (defthmd lemma-3
    (implies (and (inside-interval-p a (domain-rifn-op))
		  (inside-interval-p b (domain-rifn-op))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (i-close (strict-int-rifn-left+right a b)
		      (+ (strict-int-rifn-left a b)
			 (strict-int-rifn-right a b))))
    :hints (("Goal"
	     :use ((:instance lemma-2)
		   (:instance strict-int-rifn-left-is-integral-of-rifn-left
			      (p (make-small-partition a b)))
		   (:instance strict-int-rifn-right-is-integral-of-rifn-right
			      (p (make-small-partition a b)))
		   (:instance close-plus
			      (x1 (riemann-rifn-left (make-small-partition a b)))
			      (y1 (strict-int-rifn-left a b))
			      (x2 (riemann-rifn-right (make-small-partition a b)))
			      (y2 (strict-int-rifn-right a b)))
		   )
	     :in-theory (disable strict-int-rifn-left+right
				 riemann-rifn-left
				 riemann-rifn-right
				 strict-int-rifn-left-is-integral-of-rifn-left
				 strict-int-rifn-right-is-integral-of-rifn-right
				 mesh)))))

 (local
  (defthm-std lemma-4
    (implies (and (standardp a)
		  (standardp b))
	     (STANDARDP (+ (- (STRICT-INT-RIFN-LEFT A B))
			   (STRICT-INT-RIFN-LEFT+RIGHT A B)
			   (- (STRICT-INT-RIFN-RIGHT A B)))))))

 (local
  (defthmd lemma-5
    (implies (and (inside-interval-p a (domain-rifn-op))
		  (inside-interval-p b (domain-rifn-op))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (equal (strict-int-rifn-left+right a b)
		    (+ (strict-int-rifn-left a b)
		       (strict-int-rifn-right a b))))
    :hints (("Goal"
	     :use ((:instance lemma-3)
		   (:instance standard-small-is-zero
			      (x (- (strict-int-rifn-left+right a b)
				    (+ (strict-int-rifn-left a b)
				       (strict-int-rifn-right a b))))))
	     :in-theory (e/d (i-close)
			     (strict-int-rifn-left+right))))))



 (local
  (defthmd close-to-standard-is-close-1
    (implies (and (i-close x y)
		  (standardp x)
		  (standardp y))
	     (equal (equal x y) t))
    :hints (("Goal"
	     :in-theory (enable i-close i-small)))))

 (local
  (defthm-std strict-int-rifn-left-of-single-point
    (implies (and (realp a)
		  (inside-interval-p a (domain-rifn-op)))
	     (equal (strict-int-rifn-left a a) 0))
    :hints (("Goal'"
	     :use ((:instance strict-int-rifn-left-is-integral-of-rifn-left
			      (a a)
			      (b a)
			      (p (list a)))
		   (:instance close-to-standard-is-close-1
			      (x 0)
			      (y (strict-int-rifn-left a a)))
		   )
	     :in-theory (disable
			 strict-int-rifn-left-is-integral-of-rifn-left)))))


 (local
  (defthm-std strict-int-rifn-right-of-single-point
    (implies (and (realp a)
		  (inside-interval-p a (domain-rifn-op)))
	     (equal (strict-int-rifn-right a a) 0))
    :hints (("Goal'"
	     :use ((:instance strict-int-rifn-right-is-integral-of-rifn-right
			      (a a)
			      (b a)
			      (p (list a)))
		   (:instance close-to-standard-is-close-1
			      (x 0)
			      (y (strict-int-rifn-right a a)))
		   )
	     :in-theory (disable
			 strict-int-rifn-right-is-integral-of-rifn-right)))))

 (local
  (defthm-std strict-int-rifn-left+right-of-single-point
    (implies (and (realp a)
		  (inside-interval-p a (domain-rifn-op)))
	     (equal (strict-int-rifn-left+right a a) 0))
    :hints (("Goal'"
	     :use ((:instance strict-int-rifn-left-is-integral-of-rifn-left
			      (a a)
			      (b a)
			      (p (list a)))
		   (:instance strict-int-rifn-right-is-integral-of-rifn-right
			      (a a)
			      (b a)
			      (p (list a)))
		   (:instance close-to-standard-is-close-1
			      (x 0)
			      (y (strict-int-rifn-left+right a a)))
		   )
	     :in-theory (disable strict-int-rifn-left-is-integral-of-rifn-left
				 strict-int-rifn-right-is-integral-of-rifn-right)))))

 (local
  (defthmd lemma-6
    (implies (and (inside-interval-p a (domain-rifn-op))
		  (inside-interval-p b (domain-rifn-op))
		  (= a b)
		  (standardp a)
		  (standardp b))
	     (equal (strict-int-rifn-left+right a b)
		    (+ (strict-int-rifn-left a b)
		       (strict-int-rifn-right a b))))))

 (defthm-std reduce-strict-integral-rifn-left+right
  (implies (and (inside-interval-p a (domain-rifn-op))
		(inside-interval-p b (domain-rifn-op))
		(<= a b))
	   (equal (strict-int-rifn-left+right a b)
		  (+ (strict-int-rifn-left a b)
		     (strict-int-rifn-right a b))))
  :hints (("Goal"
	   :use ((:instance lemma-5)
		 (:instance lemma-6)))))

)


(defun int-rifn-left+right (a b)
  (if (<= a b)
      (strict-int-rifn-left+right a b)
    (- (strict-int-rifn-left+right b a))))

(defthm reduce-integral-rifn-left+right
  (implies (and (inside-interval-p a (domain-rifn-op))
		(inside-interval-p b (domain-rifn-op)))
	   (equal (int-rifn-left+right a b)
		  (+ (int-rifn-left a b)
		     (int-rifn-right a b))))
  :hints (("Goal"
	   :cases ((<= a b)))))


(defthm strict-int-rifn-left+right-is-integral-of-rifn-left+right
  (implies (and (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (domain-rifn-op))
		(inside-interval-p b (domain-rifn-op))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rifn-left+right p)
		    (strict-int-rifn-left+right a b)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance close-plus
			    (x1 (riemann-rifn-left p))
			    (x2 (riemann-rifn-right p))
			    (y1 (strict-int-rifn-left a b))
			    (y2 (strict-int-rifn-right a b)))
		 (:instance strict-int-rifn-left-is-integral-of-rifn-left)
		 (:instance strict-int-rifn-right-is-integral-of-rifn-right))
	   :in-theory (disable strict-int-rifn-left+right
			       riemann-rifn-left+right))))

;----------------

(defun rifn-left-right (x)
  (- (rifn-left x)
     (rifn-right x)))

(defun map-rifn-left-right (p)
  (if (consp p)
      (cons (rifn-left-right (car p))
	    (map-rifn-left-right (cdr p)))
    nil))

(defun riemann-rifn-left-right (p)
  (dotprod (deltas p)
	   (map-rifn-left-right (cdr p))))

(defthmd riemann-rifn-left-right-alternative
  (equal (riemann-rifn-left-right p)
	 (if (and (consp p) (consp (cdr p)))
	     (+ (riemann-rifn-left-right (cdr p))
		(* (- (cadr p) (car p))
		   (rifn-left-right (cadr p))))
	   0))
  :rule-classes :definition)

(local (in-theory (enable riemann-rifn-left-right-alternative)))
(local (in-theory (disable riemann-rifn-left-right)))

(local
 (defun reduce-riemann-rifn-left-right-induction (p)
   (if (and (consp p) (consp (cdr p)))
       (1+ (reduce-riemann-rifn-left-right-induction (cdr p)))
     0)))


(local
 (defthm reduce-riemann-rifn-left-right
   (equal (riemann-rifn-left-right p)
	  (- (riemann-rifn-left p)
	     (riemann-rifn-right p)))
   :hints (("Goal"
	    :induct (reduce-riemann-rifn-left-right-induction p)))
   ))

(defthm limited-riemann-rifn-left-right
  (implies (and (standardp a)
		(standardp b)
		(< a b)
		(inside-interval-p a (domain-rifn-op))
		(inside-interval-p b (domain-rifn-op)))
	   (i-limited (riemann-rifn-left-right (make-small-partition a b)))))

(encapsulate
 nil

 (local (in-theory (disable riemann-rifn-left-right
			    reduce-riemann-rifn-left-right)))

 (defun-std strict-int-rifn-left-right (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (domain-rifn-op))
	    (inside-interval-p b (domain-rifn-op))
	    (< a b))
       (standard-part (riemann-rifn-left-right (make-small-partition a b)))
     0)))

(encapsulate
 nil

 (local
  (defthmd lemma-1
    (implies (and (inside-interval-p a (domain-rifn-op))
		  (inside-interval-p b (domain-rifn-op))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (i-close (strict-int-rifn-left-right a b)
		      (riemann-rifn-left-right (make-small-partition a b))))
    :hints (("Goal"
	     :use ((:instance standard-part-close
			      (x (riemann-rifn-left-right (make-small-partition a b))))
		   (:instance limited-riemann-rifn-left-right))
	     :in-theory (disable standard-part-close)))))

 (local
  (defthmd lemma-2
    (implies (and (inside-interval-p a (domain-rifn-op))
		  (inside-interval-p b (domain-rifn-op))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (i-close (strict-int-rifn-left-right a b)
		      (- (riemann-rifn-left (make-small-partition a b))
			 (riemann-rifn-right (make-small-partition a b)))))
    :hints (("Goal"
	     :use ((:instance lemma-1))))))

 (local
  (defthmd close-minus
    (implies (and (i-close x1 y1)
		  (i-close x2 y2))
	     (i-close (- x1 x2) (- y1 y2)))
    :hints (("Goal"
	     :use ((:instance i-small-uminus
			      (x (- x2 y2)))
		   (:instance i-small-plus
			      (x (- x1 y1))
			      (y (- y2 x2))))
	     :in-theory (e/d (i-close)
			     (i-small-plus
			      i-small-uminus
			      i-close-small
			      i-close-small-2))))))

 (local
  (defthmd lemma-3
    (implies (and (inside-interval-p a (domain-rifn-op))
		  (inside-interval-p b (domain-rifn-op))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (i-close (strict-int-rifn-left-right a b)
		      (- (strict-int-rifn-left a b)
			 (strict-int-rifn-right a b))))
    :hints (("Goal"
	     :use ((:instance lemma-2)
		   (:instance strict-int-rifn-left-is-integral-of-rifn-left
			      (p (make-small-partition a b)))
		   (:instance strict-int-rifn-right-is-integral-of-rifn-right
			      (p (make-small-partition a b)))
		   (:instance close-minus
			      (x1 (riemann-rifn-left (make-small-partition a b)))
			      (y1 (strict-int-rifn-left a b))
			      (x2 (riemann-rifn-right (make-small-partition a b)))
			      (y2 (strict-int-rifn-right a b)))
		   )
	     :in-theory (disable strict-int-rifn-left-right
				 riemann-rifn-left
				 riemann-rifn-right
				 strict-int-rifn-left-is-integral-of-rifn-left
				 strict-int-rifn-right-is-integral-of-rifn-right
				 mesh)))))

 (local
  (defthm-std lemma-4
    (implies (and (standardp a)
		  (standardp b))
	     (STANDARDP (+ (- (STRICT-INT-RIFN-LEFT A B))
			   (STRICT-INT-RIFN-LEFT-RIGHT A B)
			   (STRICT-INT-RIFN-RIGHT A B))))))

 (local
  (defthmd lemma-5
    (implies (and (inside-interval-p a (domain-rifn-op))
		  (inside-interval-p b (domain-rifn-op))
		  (< a b)
		  (standardp a)
		  (standardp b))
	     (equal (strict-int-rifn-left-right a b)
		    (- (strict-int-rifn-left a b)
		       (strict-int-rifn-right a b))))
    :hints (("Goal"
	     :use ((:instance lemma-3)
		   (:instance standard-small-is-zero
			      (x (- (strict-int-rifn-left-right a b)
				    (- (strict-int-rifn-left a b)
				       (strict-int-rifn-right a b))))))
	     :in-theory (e/d (i-close)
			     (strict-int-rifn-left-right
			      i-close-limited-2
			      i-close-limited
			      small-if-<-small
			      ))))))

 (local
  (defthmd close-to-standard-is-close-1
    (implies (and (i-close x y)
		  (standardp x)
		  (standardp y))
	     (equal (equal x y) t))
    :hints (("Goal"
	     :in-theory (enable i-close i-small)))))

 (local
  (defthm-std strict-int-rifn-left-of-single-point
    (implies (and (realp a)
		  (inside-interval-p a (domain-rifn-op)))
	     (equal (strict-int-rifn-left a a) 0))
    :hints (("Goal'"
	     :use ((:instance strict-int-rifn-left-is-integral-of-rifn-left
			      (a a)
			      (b a)
			      (p (list a)))
		   (:instance close-to-standard-is-close-1
			      (x 0)
			      (y (strict-int-rifn-left a a)))
		   )
	     :in-theory (disable
			 strict-int-rifn-left-is-integral-of-rifn-left)))))


 (local
  (defthm-std strict-int-rifn-right-of-single-point
    (implies (and (realp a)
		  (inside-interval-p a (domain-rifn-op)))
	     (equal (strict-int-rifn-right a a) 0))
    :hints (("Goal'"
	     :use ((:instance strict-int-rifn-right-is-integral-of-rifn-right
			      (a a)
			      (b a)
			      (p (list a)))
		   (:instance close-to-standard-is-close-1
			      (x 0)
			      (y (strict-int-rifn-right a a)))
		   )
	     :in-theory (disable
			 strict-int-rifn-right-is-integral-of-rifn-right)))))

 (local
  (defthm-std strict-int-rifn-left-right-of-single-point
    (implies (and (realp a)
		  (inside-interval-p a (domain-rifn-op)))
	     (equal (strict-int-rifn-left-right a a) 0))
    :hints (("Goal'"
	     :use ((:instance strict-int-rifn-left-is-integral-of-rifn-left
			      (a a)
			      (b a)
			      (p (list a)))
		   (:instance strict-int-rifn-right-is-integral-of-rifn-right
			      (a a)
			      (b a)
			      (p (list a)))
		   (:instance close-to-standard-is-close-1
			      (x 0)
			      (y (strict-int-rifn-left-right a a)))
		   )
	     :in-theory (disable strict-int-rifn-left-is-integral-of-rifn-left
				 strict-int-rifn-right-is-integral-of-rifn-right)))))

 (local
  (defthmd lemma-6
    (implies (and (inside-interval-p a (domain-rifn-op))
		  (inside-interval-p b (domain-rifn-op))
		  (= a b)
		  (standardp a)
		  (standardp b))
	     (equal (strict-int-rifn-left-right a b)
		    (- (strict-int-rifn-left a b)
		       (strict-int-rifn-right a b))))))

 (defthm-std reduce-strict-integral-rifn-left-right
  (implies (and (inside-interval-p a (domain-rifn-op))
		(inside-interval-p b (domain-rifn-op))
		(<= a b))
	   (equal (strict-int-rifn-left-right a b)
		  (- (strict-int-rifn-left a b)
		     (strict-int-rifn-right a b))))
  :hints (("Goal"
	   :use ((:instance lemma-5)
		 (:instance lemma-6)))))

)


(defun int-rifn-left-right (a b)
  (if (<= a b)
      (strict-int-rifn-left-right a b)
    (- (strict-int-rifn-left-right b a))))

(defthm reduce-integral-rifn-left-right
  (implies (and (inside-interval-p a (domain-rifn-op))
		(inside-interval-p b (domain-rifn-op)))
	   (equal (int-rifn-left-right a b)
		  (- (int-rifn-left a b)
		     (int-rifn-right a b))))
  :hints (("Goal"
	   :cases ((<= a b)))))



(local
 (defthm close-uminus
   (implies (and (acl2-numberp x)
		 (acl2-numberp y))
	    (equal (i-close (- x) (- y))
		   (i-close x y)))
   :hints (("Goal"
	    :use ((:instance i-small-uminus
			     (x (+ (- X) Y))))
	    :in-theory (enable i-close
			       i-small-uminus)))
   ))

(defthm strict-int-rifn-left-right-is-integral-of-rifn-left-right
  (implies (and (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (domain-rifn-op))
		(inside-interval-p b (domain-rifn-op))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rifn-left-right p)
		    (strict-int-rifn-left-right a b)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance close-plus
			    (x1 (riemann-rifn-left p))
			    (x2 (- (riemann-rifn-right p)))
			    (y1 (strict-int-rifn-left a b))
			    (y2 (- (strict-int-rifn-right a b))))
		 (:instance close-uminus
			    (x (- (riemann-rifn-right p)))
			    (y (- (strict-int-rifn-right a b))))
		 (:instance strict-int-rifn-left-is-integral-of-rifn-left)
		 (:instance strict-int-rifn-right-is-integral-of-rifn-right))
	   :in-theory (disable strict-int-rifn-left-right
			       riemann-rifn-left-right
			       close-plus
			       close-uminus))))
