(in-package "ACL2")


(local (include-book "arithmetic-5/top" :dir :system))
(include-book "integrable-functions")
(include-book "continuous-function")
(include-book "equivalence-integrals")
(include-book "nonstd/nsa/equivalence-continuity" :dir :system)



(defun map-rcfn-hyper (p)
  (if (consp p)
      (cons (rcfn-hyper (car p))
	    (map-rcfn-hyper (cdr p)))
    nil))

(defthm real-listp-map-rcfn-hyper
  (implies (partitionp p)
           (real-listp (map-rcfn-hyper p))))

(defun riemann-rcfn-hyper (p)
  (dotprod (deltas p)
	   (map-rcfn-hyper (cdr p))))

(defthm real-riemann-rcfn-hyper
  (implies (partitionp p)
           (realp (riemann-rcfn-hyper p))))

(defthm limited-riemann-rcfn-hyper-small-partition
  (implies (and (realp a) (standardp a)
		(realp b) (standardp b)
		(inside-interval-p a (rcfn-hyper-domain))
		(inside-interval-p b (rcfn-hyper-domain))
		(< a b))
	   (i-limited (riemann-rcfn-hyper (make-small-partition a b))))
  :hints (("Goal"
           :by (:functional-instance limited-riemann-rcfn-small-partition
                                     (rcfn rcfn-hyper)
                                     (rcfn-domain rcfn-hyper-domain)
                                     (map-rcfn map-rcfn-hyper)
                                     (riemann-rcfn riemann-rcfn-hyper)))
          ("Subgoal 3"
           :use ((:instance rcfn-hyper-is-continuous-using-nonstandard-criterion
                            (x0 x)
                            (x y))))
          ("Subgoal 2"
           :use ((:instance rcfn-hyper-domain-non-trivial)))
          ))


(encapsulate
 nil

 (local (in-theory (disable riemann-rcfn-hyper)))

 (defun-std strict-int-rcfn-hyper (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (rcfn-hyper-domain))
	    (inside-interval-p b (rcfn-hyper-domain))
	    (< a b))
       (standard-part (riemann-rcfn-hyper (make-small-partition a b)))
     0))
 )

(defthm-std realp-strict-int-rcfn-hyper
  (implies (and (realp a)
                (realp b))
           (realp (strict-int-rcfn-hyper a b)))
  :hints (("Goal"
           :use ((:instance real-riemann-rcfn-hyper
                            (p (make-small-partition a b))))
           :in-theory (disable riemann-rcfn-hyper
                               real-riemann-rcfn-hyper))))

(defun int-rcfn-hyper (a b)
  (if (<= a b)
      (strict-int-rcfn-hyper a b)
    (- (strict-int-rcfn-hyper b a))))

(defthm realp-int-rcfn-nyper
  (implies (and (realp a)
                (realp b))
           (realp (int-rcfn-hyper a b))))

(defthm strict-int-rcfn-hyper-is-integral-of-rcfn-hyper
  (implies (and (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (rcfn-hyper-domain))
		(inside-interval-p b (rcfn-hyper-domain))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rcfn-hyper p)
		    (strict-int-rcfn-hyper a b)))
  :hints (("Goal"
	   :do-not-induct t
	   :by (:functional-instance strict-int-rcfn-is-integral-of-rcfn
                                     (rcfn rcfn-hyper)
                                     (rcfn-domain rcfn-hyper-domain)
                                     (map-rcfn map-rcfn-hyper)
                                     (riemann-rcfn riemann-rcfn-hyper)
                                     (strict-int-rcfn strict-int-rcfn-hyper)))
          ))

(defun-sk forall-partitions-riemann-sum-is-close-to-int-rcfn-hyper (a b eps delta)
  (forall (p)
          (implies (and (<= a b)
                        (partitionp p)
                        (equal (car p) a)
                        (equal (car (last p)) b)
                        (< (mesh p) delta))
                   (< (abs (- (riemann-rcfn-hyper p)
                              (strict-int-rcfn-hyper a b)))
                      eps)))
  :rewrite :direct)

(defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rcfn-hyper (a b eps)
  (exists (delta)
          (implies (and (inside-interval-p a (rcfn-hyper-domain))
                        (inside-interval-p b (rcfn-hyper-domain))
                        (<= a b)
                        (realp eps)
                        (< 0 eps))
                   (and (realp delta)
                        (< 0 delta)
                        (forall-partitions-riemann-sum-is-close-to-int-rcfn-hyper a b eps delta)))))

(defthm rcfn-hyper-is-integrable-hyperreal
  (implies (and (inside-interval-p a (rcfn-hyper-domain))
                (inside-interval-p b (rcfn-hyper-domain))
                (<= a b)
                (realp eps)
                (< 0 eps))
           (exists-delta-so-that-riemann-sum-is-close-to-int-rcfn-hyper a b eps))
  :hints (("Goal"
           :by (:functional-instance rifn-is-integrable-hyperreal
                                     (rifn rcfn-hyper)
                                     (domain-rifn rcfn-hyper-domain)
                                     (map-rifn map-rcfn-hyper)
                                     (riemann-rifn riemann-rcfn-hyper)
                                     (strict-int-rifn strict-int-rcfn-hyper)
                                     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn
                                      exists-delta-so-that-riemann-sum-is-close-to-int-rcfn-hyper)
                                     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-witness
                                      exists-delta-so-that-riemann-sum-is-close-to-int-rcfn-hyper-witness)
                                     (forall-partitions-riemann-sum-is-close-to-int-rifn
                                      forall-partitions-riemann-sum-is-close-to-int-rcfn-hyper)
                                     (forall-partitions-riemann-sum-is-close-to-int-rifn-witness
                                      forall-partitions-riemann-sum-is-close-to-int-rcfn-hyper-witness)
                                     ))
          ("Subgoal 8"
           :use ((:instance EXISTS-DELTA-SO-THAT-RIEMANN-SUM-IS-CLOSE-TO-INT-RCFN-HYPER-suff)))
          ("Subgoal 6"
           :use ((:instance FORALL-PARTITIONS-RIEMANN-SUM-IS-CLOSE-TO-INT-RCFN-HYPER-necc)))
          ("Subgoal 4"
           :use ((:instance strict-int-rcfn-hyper-is-integral-of-rcfn-hyper)))
          ("Subgoal 3"
           :use ((:instance rcfn-hyper-domain-non-trivial)))
          ))


