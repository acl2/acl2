;; Proof of the sum rule for definite integrals of infinite series.

;; Cuong Chau                             April, 2015

(in-package "ACL2")

(include-book "riemann-integral/ftc-1-2")
(include-book "utils")

(local (include-book "nonstd/nsa/overspill" :dir :system))
(local (include-book "nonstd/integrals/ftc-2" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;; ======================================================================

(encapsulate
 ((low () t)
  (fi-prime (x i) t)
  (fi-domain () t))

 (local (defun low () 0))
 (local (defun fi-prime (x i) (declare (ignore x i)) 0))
 (local (defun fi-domain () (interval nil nil)))

 (defthm inside-interval-p-low
   (inside-interval-p (low) (fi-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm realp-fi-prime
   (realp (fi-prime x i))
   :rule-classes :type-prescription)

 (defthm intervalp-fi-domain
   (interval-p (fi-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm fi-domain-real
   (implies (inside-interval-p x (fi-domain))
            (realp x))
   :rule-classes (:forward-chaining))

 (defthm fi-domain-non-trivial
   (or (null (interval-left-endpoint (fi-domain)))
       (null (interval-right-endpoint (fi-domain)))
       (< (interval-left-endpoint (fi-domain))
          (interval-right-endpoint (fi-domain))))
   :rule-classes nil)

 (defthm fi-prime-continuous
   (implies (and (standardp i)
                 (standardp x)
                 (inside-interval-p x (fi-domain))
                 (inside-interval-p y (fi-domain))
                 (i-close x y))
            (i-close (fi-prime x i) (fi-prime y i))))

 (defun sum-fi-prime (x i)
   (if (zp i)
       (fi-prime x 0)
     (+ (fi-prime x i)
        (sum-fi-prime x (1- i)))))

 (defthm monotonic-sum-fi-prime
   (implies (and (<= (ifix n) (ifix m))
                 ;;(integerp m)
                 ;;(integerp n)
                 (inside-interval-p x (fi-domain)))
            (<= (sum-fi-prime x n)
                (sum-fi-prime x m)))
   :rule-classes :linear)

 (defthm i-limited-sum-fi-prime
   (implies (and (inside-interval-p x (fi-domain))
                 (natp i)
                 (i-large i))
            (i-limited (sum-fi-prime x i))))

 (defun-std sum-fi-prime-infinity (x)
   (if (inside-interval-p x (fi-domain))
       (standard-part (sum-fi-prime x (i-large-integer)))
     0))

 (local
  (defthm sum-fi-prime-equals-0
    (equal (sum-fi-prime x i)
           0)))

 (defthm sum-fi-prime-pointwise-converge
   (implies (and (standardp x)
                 (inside-interval-p x (fi-domain))
                 (i-large i)
                 (natp i))
            (i-close (sum-fi-prime-infinity x)
                     (sum-fi-prime x i))))

 (local
  (defthm-std sum-fi-prime-infinity-equals-0
    (equal (sum-fi-prime-infinity x)
           0)))

 (defthm sum-fi-prime-infinity-continuous
   (implies (and (standardp x)
                 (inside-interval-p x (fi-domain))
                 (inside-interval-p y (fi-domain))
                 (i-close x y))
            (i-close (sum-fi-prime-infinity x)
                     (sum-fi-prime-infinity y)))))

(defthm-std standardp-fi-prime
  (implies (and (standardp x)
                (standardp i))
           (standardp (fi-prime x i)))
  :rule-classes (:rewrite :type-prescription))

(defthm-std standardp-sum-fi-prime
  (implies (and (standardp x)
                (standardp i))
           (standardp (sum-fi-prime x i)))
  :rule-classes (:rewrite :type-prescription))

(defthm-std standardp-fi-domain
  (standardp (fi-domain))
  :rule-classes (:rewrite :type-prescription))

(defthm realp-sum-fi-prime
  (realp (sum-fi-prime x i))
  :rule-classes :type-prescription)

(defthm sum-fi-prime-continuous
  (implies (and (standardp i)
                (standardp x)
                (inside-interval-p x (fi-domain))
                (inside-interval-p y (fi-domain))
                (i-close x y))
           (i-close (sum-fi-prime x i) (sum-fi-prime y i))))

;; ======================================================================

;; Define the Riemann integral of fi-prime.

(defun map-fi-prime (p i)
  (if (consp p)
      (cons (fi-prime (car p) i)
	    (map-fi-prime (cdr p) i))
    nil))

(defun riemann-fi-prime (p i)
  (dotprod (deltas p)
	   (map-fi-prime (cdr p) i)))

(local
 (defthm limited-riemann-fi-prime-small-partition
   (implies (and (standardp i)
                 (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (< a b))
            (i-limited (riemann-fi-prime (make-small-partition a b)
                                         i)))
   :hints (("Goal"
            :by (:functional-instance limited-riemann-rcfn-2-small-partition
                                      (rcfn-2
                                       (lambda (x i)
                                         (fi-prime x i)))
                                      (rcfn-2-domain fi-domain)
                                      (map-rcfn-2
                                       (lambda (p i)
                                         (map-fi-prime p i)))
                                      (riemann-rcfn-2
                                       (lambda (p i)
                                         (riemann-fi-prime p i)))))
           ("Subgoal 2"
            :use (fi-domain-non-trivial)))))

(encapsulate
 ()

 (local (in-theory (disable riemann-fi-prime)))

 (defun-std strict-int-fi-prime (a b i)
   (if (and (realp a)
            (realp b)
            (inside-interval-p a (fi-domain))
            (inside-interval-p b (fi-domain))
            (< a b))
       (standard-part (riemann-fi-prime (make-small-partition a b) i))
     0)))

(defun int-fi-prime (a b i)
  (if (<= a b)
      (strict-int-fi-prime a b i)
    (- (strict-int-fi-prime b a i))))

(local
 (defthm fi-prime-ftc-1-2
   (implies (and (standardp i)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p x (fi-domain))
                 (inside-interval-p x1 (fi-domain))
                 (standardp x)
                 (i-close x x1)
                 (not (equal x x1)))
            (i-close (/ (- (int-fi-prime a x i)
                           (int-fi-prime a x1 i))
                        (- x x1))
                     (fi-prime x i)))
   :hints
   (("goal"
     :by (:functional-instance ftc-1-2
                               (rcfn-2
                                (lambda (x i)
                                  (fi-prime x i)))
                               (rcfn-2-domain fi-domain)
                               (map-rcfn-2
                                (lambda (p i)
                                  (map-fi-prime p i)))
                               (riemann-rcfn-2
                                (lambda (p i)
                                  (riemann-fi-prime p i)))
                               (strict-int-rcfn-2
                                (lambda (a b i)
                                  (strict-int-fi-prime a b i)))
                               (int-rcfn-2
                                (lambda (a b i)
                                  (int-fi-prime a b i))))))))

;; ======================================================================

;; Define the Riemann integral of sum-fi-prime.

(defun map-sum-fi-prime (p i)
  (if (consp p)
      (cons (sum-fi-prime (car p) i)
	    (map-sum-fi-prime (cdr p) i))
    nil))

(defun riemann-sum-fi-prime (p i)
  (dotprod (deltas p)
	   (map-sum-fi-prime (cdr p) i)))

(local
 (defthm limited-riemann-sum-fi-prime-small-partition
   (implies (and (standardp i)
                 (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (< a b))
            (i-limited (riemann-sum-fi-prime (make-small-partition a b)
                                             i)))
   :hints (("Goal"
            :by (:functional-instance limited-riemann-rcfn-2-small-partition
                                      (rcfn-2
                                       (lambda (x i)
                                         (sum-fi-prime x i)))
                                      (rcfn-2-domain fi-domain)
                                      (map-rcfn-2
                                       (lambda (p i)
                                         (map-sum-fi-prime p i)))
                                      (riemann-rcfn-2
                                       (lambda (p i)
                                         (riemann-sum-fi-prime p i)))))
           ("Subgoal 2"
            :use (fi-domain-non-trivial)))))

(encapsulate
 ()

 (local (in-theory (disable riemann-sum-fi-prime)))

 (defun-std strict-int-sum-fi-prime (a b i)
   (if (and (realp a)
            (realp b)
            (inside-interval-p a (fi-domain))
            (inside-interval-p b (fi-domain))
            (< a b))
       (standard-part (riemann-sum-fi-prime (make-small-partition a b)
                                            i))
     0)))

(defun int-sum-fi-prime (a b i)
  (if (<= a b)
      (strict-int-sum-fi-prime a b i)
    (- (strict-int-sum-fi-prime b a i))))

(local
 (defthm sum-fi-prime-ftc-1-2
   (implies (and (standardp i)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p x (fi-domain))
                 (inside-interval-p x1 (fi-domain))
                 (standardp x)
                 (i-close x x1)
                 (not (equal x x1)))
            (i-close (/ (- (int-sum-fi-prime a x i)
                           (int-sum-fi-prime a x1 i))
                        (- x x1))
                     (sum-fi-prime x i)))
   :hints
   (("goal"
     :by (:functional-instance ftc-1-2
                               (rcfn-2
                                (lambda (x i)
                                  (sum-fi-prime x i)))
                               (rcfn-2-domain fi-domain)
                               (map-rcfn-2
                                (lambda (p i)
                                  (map-sum-fi-prime p i)))
                               (riemann-rcfn-2
                                (lambda (p i)
                                  (riemann-sum-fi-prime p i)))
                               (strict-int-rcfn-2
                                (lambda (a b i)
                                  (strict-int-sum-fi-prime a b i)))
                               (int-rcfn-2
                                (lambda (a b i)
                                  (int-sum-fi-prime a b i))))))))

;; ======================================================================

;; Prove that the integral of the sum equals the sum of the integrals.

(defun sum-int-fi-prime (a b i)
  (if (zp i)
      (int-fi-prime a b 0)
    (+ (int-fi-prime a b i)
       (sum-int-fi-prime a b (1- i)))))

(local
 (defthm sum-int-fi-prime-derivative
   (implies (and (standardp i)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p x (fi-domain))
                 (inside-interval-p x1 (fi-domain))
                 (standardp x)
                 (i-close x x1)
                 (not (equal x x1)))
            (i-close (/ (- (sum-int-fi-prime a x i)
                           (sum-int-fi-prime a x1 i))
                        (- x x1))
                     (sum-fi-prime x i)))
   :hints (("Goal"
            :in-theory (disable int-fi-prime))
           ("Subgoal *1/3"
            :use (fi-prime-ftc-1-2
                  (:instance i-close-plus
                             (x1 (/ (- (int-fi-prime a x i)
                                       (int-fi-prime a x1 i))
                                    (- x x1)))
                             (x2 (fi-prime x i))
                             (y1 (/ (- (sum-int-fi-prime a x (1- i))
                                       (sum-int-fi-prime a x1 (1- i)))
                                    (- x x1)))
                             (y2 (sum-fi-prime x (1- i))))))
           ("Subgoal *1/1"
            :use (:instance fi-prime-ftc-1-2
                            (i 0))))))

(local
 (encapsulate
  (((i) => *))

  (local (defun i () 0))

  (defthm natp-i
    (natp (i))
    :rule-classes :type-prescription)))

(local
 (defthm-std standardp-i
   (standardp (i))
   :rule-classes (:rewrite :type-prescription)))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm realp-riemann-fi-prime
   (implies (partitionp p)
            (realp (riemann-fi-prime p i)))
   :rule-classes :type-prescription))

(defthm-std realp-int-fi-prime
  (realp (int-fi-prime a b i))
  :hints (("Goal"
           :use ((:instance realp-riemann-fi-prime
                            (p (make-small-partition a b)))
                 (:instance realp-riemann-fi-prime
                            (p (make-small-partition b a))))))
  :rule-classes :type-prescription)

(defthm-std realp-sum-int-fi-prime
  (realp (sum-int-fi-prime a b i))
  :hints (("Goal"
           :in-theory (disable int-fi-prime)))
  :rule-classes :type-prescription)

(local
 (defthm sum-rule-of-int-sum-fi-prime-lemma-1
   (implies (and (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain)))
            (equal (int-sum-fi-prime a b (i))
                   (- (sum-int-fi-prime (low) b (i))
                      (sum-int-fi-prime (low) a (i)))))
   :hints (("Goal"
            :by (:functional-instance ftc-2
                                      (rcdfn
                                       (lambda (x)
                                         (sum-int-fi-prime (low) x (i))))
                                      (rcdfn-prime
                                       (lambda (x)
                                         (sum-fi-prime x (i))))
                                      (rcdfn-domain fi-domain)
                                      (map-rcdfn-prime
                                       (lambda (p)
                                         (map-sum-fi-prime p (i))))
                                      (riemann-rcdfn-prime
                                       (lambda (p)
                                         (riemann-sum-fi-prime p (i))))
                                      (strict-int-rcdfn-prime
                                       (lambda (a b)
                                         (strict-int-sum-fi-prime a b
                                                                  (i))))
                                      (int-rcdfn-prime
                                       (lambda (a b)
                                         (int-sum-fi-prime a b (i))))))
           ("Subgoal 7"
            :use (:instance sum-int-fi-prime-derivative
                            (a (low))
                            (i (i))))
           ("Subgoal 6"
            :use fi-domain-non-trivial))))

(local
 (defthm-std sum-rule-of-int-sum-fi-prime-lemma-2
   (equal (sum-int-fi-prime a a i) 0)))

(defthm sum-rule-of-int-sum-fi-prime
  (implies (and (natp i)
                (inside-interval-p a (fi-domain))
		(inside-interval-p b (fi-domain)))
	   (equal (int-sum-fi-prime a b i)
		  (sum-int-fi-prime a b i)))
  :hints (("Goal"
           :use (:functional-instance
                 sum-rule-of-int-sum-fi-prime-lemma-1
                 (low (lambda ()
                      (if (inside-interval-p a (fi-domain)) a (low))))
                 (i (lambda ()
                      (if (natp i) i (i))))))))

;; ======================================================================

;; Infinite series.

(local
 (defthmd standard-<-large
   (implies (and (standardp i)
                 (integerp i)
                 (natp j)
                 (i-large j))
            (< i j))
   :hints (("Goal" :use ((:instance STANDARDS-ARE-LIMITED
                                    (x i))
                         (:instance LARGE->-NON-LARGE
                                    (x j)
                                    (y i)))))))

(local
 (defthm-std sum-fi-prime-<=-sum-fi-prime-infinity
   (implies (inside-interval-p x (fi-domain))
            (<= (sum-fi-prime x i)
                (sum-fi-prime-infinity x)))
   :hints (("Goal"
            :use ((:instance standard-<-large
                             (i (ifix i))
                             (j (i-large-integer)))
                  (:instance monotonic-sum-fi-prime
                             (m (i-large-integer))
                             (n i))
                  (:instance STANDARD-PART-<=
                             (x (sum-fi-prime x i))
                             (y (sum-fi-prime x (i-large-integer)))))))
   :rule-classes :linear))

;; ======================================================================

;; Prove Dini Uniform Convergence Theorem.

(local
 (defun diff-sum-small (n x y)
   (< (abs (- (sum-fi-prime x n) (sum-fi-prime y n)))
      (/ (1+ n)))))

(local
 (encapsulate
  ()

  (local
   (defthm lemma-1
     (implies (and (i-close x y)
                   (realp x)
                   (realp y)
                   (standardp a)
                   (realp a)
                   (< 0 a))
              (< (abs (- x y)) a))
     :hints (("Goal"
              :in-theory (e/d (i-close) (SMALL-<-NON-SMALL))
              :use ((:instance STANDARD-SMALL-IS-ZERO
                               (x a))
                    (:instance SMALL-<-NON-SMALL
                               (x (- x y))
                               (y a)))))))

  (defthm diff-sum-small-on-std-n
    (implies (and (standardp n)
                  (natp n)
                  (standardp x)
                  (inside-interval-p x (fi-domain))
                  (inside-interval-p y (fi-domain))
                  (i-close x y))
             (diff-sum-small n x y))
    :hints (("Goal"
             :use (:instance lemma-1
                             (x (sum-fi-prime x n))
                             (y (sum-fi-prime y n))
                             (a (/ (1+ n)))))))))

(local (in-theory (disable diff-sum-small)))

(local (overspill diff-sum-small (x y)))

(local
 (defthm diff-sum-small-holds-on-i-large
   (let ((n (diff-sum-small-witness x y)))
     (implies (and (standardp x)
                   (inside-interval-p x (fi-domain))
                   (inside-interval-p y (fi-domain))
                   (i-close x y))
              (and (natp n)
                   (i-large n)
                   (implies (and (natp m)
                                 (<= m n))
                            (diff-sum-small m x y)))))
   :hints (("Goal"
            :use (:instance diff-sum-small-overspill
                            (x (list x y)))))
   :rule-classes nil))

(local
 (encapsulate
  ()

  (local
   (defthm lemma-2
     (implies (and (natp n)
                   (i-large n))
              (i-close (/ (1+ n)) 0))
     :hints (("Goal" :in-theory (enable i-close)))))

  (local
   (defthm lemma-3
     (realp (abs (- (sum-fi-prime x n)
                    (sum-fi-prime y n))))
     :rule-classes :type-prescription))

  (local
   (defthm lemma-4
     (implies (and (natp n)
                   (i-large n)
                   (diff-sum-small n x y))
              (i-close (abs (- (sum-fi-prime x n)
                               (sum-fi-prime y n)))
                       0))
     :hints (("Goal"
              :in-theory (e/d (diff-sum-small) (abs))
              :use (:instance close-squeeze
                              (x 0)
                              (y (abs (- (sum-fi-prime x n)
                                         (sum-fi-prime y n))))
                              (z (/ (1+ n))))))))

  (local
   (defthm lemma-5
     (implies (and (natp n)
                   (i-large n)
                   (diff-sum-small n x y))
              (i-close (sum-fi-prime x n)
                       (sum-fi-prime y n)))
     :hints (("Goal"
              :in-theory (enable i-close)
              :use lemma-4))))

  (defthm sum-fi-prime-continuous-overspill
    (let ((n (diff-sum-small-witness x y)))
      (implies (and (i-large m)
                    (natp m)
                    (<= m n)
                    (standardp x)
                    (inside-interval-p x (fi-domain))
                    (inside-interval-p y (fi-domain))
                    (i-close x y))
               (i-close (sum-fi-prime x m)
                        (sum-fi-prime y m))))
    :hints (("Goal"
             :in-theory (disable abs)
             :use (diff-sum-small-holds-on-i-large))))))

(encapsulate
 ()

 (local
  (defthm lemma-6
    (implies (and (<= n m)
                  (integerp m)
                  (integerp n)
                  (inside-interval-p x (fi-domain)))
             (<= (abs (- (sum-fi-prime-infinity x)
                         (sum-fi-prime x m)))
                 (abs (- (sum-fi-prime-infinity x)
                         (sum-fi-prime x n)))))
    :hints (("Goal"
             :use monotonic-sum-fi-prime
             :in-theory (disable sum-fi-prime)))
    :rule-classes :linear))

 (local
  (defthm sum-fi-prime-uniformly-converge-lemma-1
    (let ((n (diff-sum-small-witness (standard-part x) x)))
      (implies (and (interval-left-inclusive-p (fi-domain))
                    (interval-right-inclusive-p (fi-domain))
                    (inside-interval-p x (fi-domain))
                    (<= i n)
                    (i-large i)
                    (natp i))
               (i-close (sum-fi-prime-infinity x)
                        (sum-fi-prime x i))))
    :hints (("Goal"
             :use ((:instance sum-fi-prime-infinity-continuous
                              (x (standard-part x))
                              (y x))
                   (:instance sum-fi-prime-continuous-overspill
                              (m i)
                              (x (standard-part x))
                              (y x))
                   (:instance sum-fi-prime-pointwise-converge
                              (x (standard-part x)))
                   (:instance i-close-transitive
                              (x (sum-fi-prime-infinity x))
                              (y (sum-fi-prime-infinity (standard-part x)))
                              (z (sum-fi-prime (standard-part x) i)))
                   (:instance i-close-transitive
                              (x (sum-fi-prime-infinity x))
                              (y (sum-fi-prime (standard-part x) i))
                              (z (sum-fi-prime x i))))))))

 (local
  (defthm lemma-7
    (let ((n (diff-sum-small-witness (standard-part x) x)))
      (implies (and (interval-left-inclusive-p (fi-domain))
                    (interval-right-inclusive-p (fi-domain))
                    (inside-interval-p x (fi-domain))
                    (<= i n)
                    (i-large i)
                    (natp i))
               (i-close (abs (- (sum-fi-prime-infinity x)
                                (sum-fi-prime x i)))
                        0)))
    :hints (("Goal"
             :in-theory (e/d (i-close)
                             (sum-fi-prime-uniformly-converge-lemma-1))
             :use sum-fi-prime-uniformly-converge-lemma-1))))

 (local
  (defthm-std lemma-8
    (realp (abs (- (sum-fi-prime-infinity x)
                   (sum-fi-prime x i))))
    :rule-classes :type-prescription))

 (local
  (defthm lemma-9
    (let ((n (diff-sum-small-witness (standard-part x) x)))
      (implies (and (interval-left-inclusive-p (fi-domain))
                    (interval-right-inclusive-p (fi-domain))
                    (inside-interval-p x (fi-domain))
                    (< n i)
                    (i-large i)
                    (natp i))
               (i-close (abs (- (sum-fi-prime-infinity x)
                                (sum-fi-prime x i)))
                        0)))
    :hints (("Goal"
             :in-theory (disable abs sum-fi-prime)
             :use ((:instance diff-sum-small-holds-on-i-large
                              (m (diff-sum-small-witness
                                  (standard-part x) x))
                              (x (standard-part x))
                              (y x))
                   (:instance close-squeeze
                              (x 0)
                              (y (abs (- (sum-fi-prime-infinity x)
                                         (sum-fi-prime x i))))
                              (z (abs (- (sum-fi-prime-infinity x)
                                         (sum-fi-prime x
                                                       (diff-sum-small-witness
                                                        (standard-part x) x))))))
                   (:instance lemma-6
                              (m i)
                              (n (diff-sum-small-witness
                                  (standard-part x) x)))))
            ("Subgoal 6"
            :use diff-sum-small-witness))))

 (local
  (defthm sum-fi-prime-uniformly-converge-lemma-2
    (let ((n (diff-sum-small-witness (standard-part x) x)))
      (implies (and (interval-left-inclusive-p (fi-domain))
                    (interval-right-inclusive-p (fi-domain))
                    (inside-interval-p x (fi-domain))
                    (< n i)
                    (i-large i)
                    (natp i))
               (i-close (sum-fi-prime-infinity x)
                        (sum-fi-prime x i))))
    :hints (("Goal"
             :in-theory (e/d (i-close)
                             (lemma-9))
             :use lemma-9))))

 (defthm sum-fi-prime-uniformly-converge
   (implies (and (interval-left-inclusive-p (fi-domain))
                 (interval-right-inclusive-p (fi-domain))
                 (inside-interval-p x (fi-domain))
                 (i-large i)
                 (natp i))
            (i-close (sum-fi-prime-infinity x)
                     (sum-fi-prime x i)))
   :hints (("Goal"
            :cases ((<= i (diff-sum-small-witness
                           (standard-part x) x))
                    (< (diff-sum-small-witness
                        (standard-part x) x)
                       i))))))

;; ======================================================================

(local
 (defun diff-sum-fi-primes (x i)
   (- (sum-fi-prime-infinity x)
      (sum-fi-prime x i))))

(local
 (defthm realp-diff-sum-fi-primes
   (realp (diff-sum-fi-primes x i))
   :rule-classes :type-prescription))

(local
 (defthm diff-sum-fi-primes-continuous
   (implies (and (standardp i)
                 (standardp x)
                 (inside-interval-p x (fi-domain))
                 (inside-interval-p y (fi-domain))
                 (i-close x y))
            (i-close (diff-sum-fi-primes x i)
                     (diff-sum-fi-primes y i)))
   :hints (("Goal"
            :in-theory (disable sum-fi-prime-infinity)))))

(local
 (defthm diff-sum-fi-primes-approaches-0
   (implies (and (interval-left-inclusive-p (fi-domain))
                 (interval-right-inclusive-p (fi-domain))
                 (inside-interval-p x (fi-domain))
                 (i-large i)
                 (natp i))
            (i-close (diff-sum-fi-primes x i)
                     0))
   :hints (("Goal"
            :in-theory (e/d (i-close) (sum-fi-prime-uniformly-converge))
            :use (sum-fi-prime-uniformly-converge)))))

;; ======================================================================

;; Find max diff-sum-fi-primes.

(local
 (defun find-max-diff-sum-fi-primes-x-n (a max-x step n eps i)
   (declare (xargs :measure (nfix (1+ (- n step)))))
   (if (and (integerp step)
            (integerp n)
            (<= step n)
            (realp a)
            (realp eps)
            (< 0 eps))
       (if (> (diff-sum-fi-primes (+ a (* step eps)) i)
              (diff-sum-fi-primes max-x i))
           (find-max-diff-sum-fi-primes-x-n a
                                            (+ a (* step eps))
                                            (1+ step) n eps
                                            i)
         (find-max-diff-sum-fi-primes-x-n a max-x (1+ step) n
                                          eps i))
     max-x)))

(local
 (defthm find-max-diff-sum-fi-primes-x-n-limited
   (implies (and (realp a)
                 (i-limited a)
                 (realp b)
                 (i-limited b)
                 (< a b))
            (i-limited (find-max-diff-sum-fi-primes-x-n
                        a a
                        0 (i-large-integer)
                        (+ (- (* (/ (i-large-integer)) a))
                           (* (/ (i-large-integer)) b))
                        i)))
   :hints (("Goal"
            :by (:functional-instance
                 find-max-rcfn-2-x-n-limited
                 (rcfn-2 diff-sum-fi-primes)
                 (rcfn-2-domain fi-domain)
                 (find-max-rcfn-2-x-n
                  find-max-diff-sum-fi-primes-x-n)))
           ("Subgoal 3"
            :use (:instance diff-sum-fi-primes-continuous
                            (i arg)))
           ("Subgoal 2"
            :use fi-domain-non-trivial))))

(local
 (defun-std find-max-diff-sum-fi-primes-x (a b i)
   (if (and (realp a)
            (realp b)
            (< a b))
       (standard-part
        (find-max-diff-sum-fi-primes-x-n a
                                         a
                                         0
                                         (i-large-integer)
                                         (/ (- b a)
                                            (i-large-integer))
                                         i))
     0)))

(local
 (defthm find-max-diff-sum-fi-primes-x-inside-interval
   (implies (and (inside-interval-p a interval)
                 (inside-interval-p b interval)
                 (< a b))
            (inside-interval-p
             (find-max-diff-sum-fi-primes-x a b i)
             interval))
   :hints (("Goal"
            :by (:functional-instance
                 find-max-rcfn-2-x-inside-interval
                 (rcfn-2 diff-sum-fi-primes)
                 (rcfn-2-domain fi-domain)
                 (find-max-rcfn-2-x-n
                  find-max-diff-sum-fi-primes-x-n)
                 (find-max-rcfn-2-x
                  find-max-diff-sum-fi-primes-x))))))

(local
 (defthm find-max-diff-sum-fi-primes-is-maximum
   (implies (and (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (realp x)
                 (<= a x)
                 (<= x b)
                 (< a b))
            (<= (diff-sum-fi-primes x i)
                (diff-sum-fi-primes
                 (find-max-diff-sum-fi-primes-x a b i)
                 i)))
   :hints (("Goal"
            :by (:functional-instance
                 find-max-rcfn-2-is-maximum
                 (rcfn-2 diff-sum-fi-primes)
                 (rcfn-2-domain fi-domain)
                 (find-max-rcfn-2-x-n
                  find-max-diff-sum-fi-primes-x-n)
                 (find-max-rcfn-2-x
                  find-max-diff-sum-fi-primes-x))))))

;; Find min diff-sum-fi-primes.

(local
 (defun find-min-diff-sum-fi-primes-x-n (a min-x step n eps i)
   (declare (xargs :measure (nfix (1+ (- n step)))))
   (if (and (integerp step)
            (integerp n)
            (<= step n)
            (realp a)
            (realp eps)
            (< 0 eps))
       (if (< (diff-sum-fi-primes (+ a (* step eps)) i)
              (diff-sum-fi-primes min-x i))
           (find-min-diff-sum-fi-primes-x-n a
                                            (+ a (* step eps))
                                            (1+ step) n eps
                                            i)
         (find-min-diff-sum-fi-primes-x-n a min-x (1+ step) n
                                          eps i))
     min-x)))

(local
 (defthm find-min-diff-sum-fi-primes-x-n-limited
   (implies (and (realp a)
                 (i-limited a)
                 (realp b)
                 (i-limited b)
                 (< a b))
            (i-limited (find-min-diff-sum-fi-primes-x-n
                        a a
                        0 (i-large-integer)
                        (+ (- (* (/ (i-large-integer)) a))
                           (* (/ (i-large-integer)) b))
                        i)))
   :hints (("Goal"
            :by (:functional-instance
                 find-min-rcfn-2-x-n-limited
                 (rcfn-2 diff-sum-fi-primes)
                 (rcfn-2-domain fi-domain)
                 (find-min-rcfn-2-x-n
                  find-min-diff-sum-fi-primes-x-n)))
           ("Subgoal 3"
            :use (:instance diff-sum-fi-primes-continuous
                            (i arg)))
           ("Subgoal 2"
            :use fi-domain-non-trivial))))

(local
 (defun-std find-min-diff-sum-fi-primes-x (a b i)
   (if (and (realp a)
            (realp b)
            (< a b))
       (standard-part
        (find-min-diff-sum-fi-primes-x-n a
                                         a
                                         0
                                         (i-large-integer)
                                         (/ (- b a)
                                            (i-large-integer))
                                         i))
     0)))

(local
 (defthm find-min-diff-sum-fi-primes-x-inside-interval
   (implies (and (inside-interval-p a interval)
                 (inside-interval-p b interval)
                 (< a b))
            (inside-interval-p
             (find-min-diff-sum-fi-primes-x a b i)
             interval))
   :hints (("Goal"
            :by (:functional-instance
                 find-min-rcfn-2-x-inside-interval
                 (rcfn-2 diff-sum-fi-primes)
                 (rcfn-2-domain fi-domain)
                 (find-min-rcfn-2-x-n
                  find-min-diff-sum-fi-primes-x-n)
                 (find-min-rcfn-2-x
                  find-min-diff-sum-fi-primes-x))))))

(local
 (defthm find-min-diff-sum-fi-primes-is-minimum
   (implies (and (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (realp x)
                 (<= a x)
                 (<= x b)
                 (< a b))
            (<= (diff-sum-fi-primes
                 (find-min-diff-sum-fi-primes-x a b i)
                 i)
                (diff-sum-fi-primes x i)))
   :hints (("Goal"
            :by (:functional-instance
                 find-min-rcfn-2-is-minimum
                 (rcfn-2 diff-sum-fi-primes)
                 (rcfn-2-domain fi-domain)
                 (find-min-rcfn-2-x-n
                  find-min-diff-sum-fi-primes-x-n)
                 (find-min-rcfn-2-x
                  find-min-diff-sum-fi-primes-x))))))

(local (in-theory (disable diff-sum-fi-primes)))

;; ======================================================================

(local
 (defun map-diff-sum-fi-primes (p i)
   (if (consp p)
       (cons (diff-sum-fi-primes (car p) i)
             (map-diff-sum-fi-primes (cdr p) i))
     nil)))

(local
 (defun riemann-diff-sum-fi-primes (p i)
   (dotprod (deltas p)
            (map-diff-sum-fi-primes (cdr p) i))))

(local
 (defun diff-sum-fi-primes-max-x (a b i)
   (if (and (realp a) (realp b))
       (if (< a b)
           (find-max-diff-sum-fi-primes-x a b i)
         (if (< b a)
             (find-max-diff-sum-fi-primes-x b a i)
           b))
     b)))

(local
 (defthm riemann-diff-sum-fi-primes-bounded-above
   (implies (and (partitionp p)
                 (inside-interval-p (car p) (fi-domain))
                 (inside-interval-p (car (last p)) (fi-domain)))
            (<= (riemann-diff-sum-fi-primes p i)
                (* (diff-sum-fi-primes
                    (diff-sum-fi-primes-max-x (car p)
                                              (car (last p))
                                              i)
                    i)
                   (- (car (last p))
                      (car p)))))
   :hints (("Goal"
            :by (:functional-instance
                 riemann-rcfn-2-bounded-above
                 (rcfn-2 diff-sum-fi-primes)
                 (rcfn-2-domain fi-domain)
                 (find-max-rcfn-2-x-n
                  find-max-diff-sum-fi-primes-x-n)
                 (find-max-rcfn-2-x
                  find-max-diff-sum-fi-primes-x)
                 (map-rcfn-2 map-diff-sum-fi-primes)
                 (riemann-rcfn-2 riemann-diff-sum-fi-primes)
                 (rcfn-2-max-x diff-sum-fi-primes-max-x))))
   :rule-classes :linear))

(local (in-theory (disable diff-sum-fi-primes-max-x)))

(local
 (defun diff-sum-fi-primes-min-x (a b i)
   (if (and (realp a) (realp b))
       (if (< a b)
           (find-min-diff-sum-fi-primes-x a b i)
         (if (< b a)
             (find-min-diff-sum-fi-primes-x b a i)
           b))
     b)))

(local
 (defthm riemann-diff-sum-fi-primes-bounded-below
   (implies (and (partitionp p)
                 (inside-interval-p (car p) (fi-domain))
                 (inside-interval-p (car (last p)) (fi-domain)))
            (<= (* (diff-sum-fi-primes
                    (diff-sum-fi-primes-min-x (car p)
                                              (car (last p))
                                              i)
                    i)
                   (- (car (last p))
                      (car p)))
                (riemann-diff-sum-fi-primes p i)))
   :hints (("Goal"
            :by (:functional-instance
                 riemann-rcfn-2-bounded-below
                 (rcfn-2 diff-sum-fi-primes)
                 (rcfn-2-domain fi-domain)
                 (find-min-rcfn-2-x-n
                  find-min-diff-sum-fi-primes-x-n)
                 (find-min-rcfn-2-x
                  find-min-diff-sum-fi-primes-x)
                 (map-rcfn-2 map-diff-sum-fi-primes)
                 (riemann-rcfn-2 riemann-diff-sum-fi-primes)
                 (rcfn-2-min-x diff-sum-fi-primes-min-x))))
   :rule-classes :linear))

(local (in-theory (disable diff-sum-fi-primes-min-x)))

;; Define the upper bound function of riemann-diff-sum-fi-primes.

(local
 (defun riemann-diff-sum-fi-primes-upper-bound (a b i)
   (* (diff-sum-fi-primes
       (diff-sum-fi-primes-max-x a b i)
       i)
      (- b a))))

(local
 (defthm realp-riemann-diff-sum-fi-primes-upper-bound
   (implies (and (realp a)
                 (realp b))
            (realp (riemann-diff-sum-fi-primes-upper-bound a b i)))
   :rule-classes :type-prescription))

(local
 (defthm-std standardp-riemann-diff-sum-fi-primes-upper-bound
   (implies (and (standardp i)
                 (standardp a)
                 (standardp b))
            (standardp (riemann-diff-sum-fi-primes-upper-bound a b i)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm riemann-diff-sum-fi-primes-upper-bound-approaches-0
   (implies (and (interval-left-inclusive-p (fi-domain))
                 (interval-right-inclusive-p (fi-domain))
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (i-large i)
                 (natp i))
            (i-close (riemann-diff-sum-fi-primes-upper-bound
                      a b i)
                     0))
   :hints (("Goal"
            :in-theory (e/d (diff-sum-fi-primes-max-x)
                            (DISTRIBUTIVITY))
            :use (:instance i-close-times
                            (x (- b a))
                            (y1 (diff-sum-fi-primes
                                 (diff-sum-fi-primes-max-x
                                  a b i)
                                 i))
                            (y2 0))))))

;; Define the lower bound function of riemann-diff-sum-fi-primes.

(local
 (defun riemann-diff-sum-fi-primes-lower-bound (a b i)
   (* (diff-sum-fi-primes
       (diff-sum-fi-primes-min-x a b i)
       i)
      (- b a))))

(local
 (defthm realp-riemann-diff-sum-fi-primes-lower-bound
   (implies (and (realp a)
                 (realp b))
            (realp (riemann-diff-sum-fi-primes-lower-bound a b i)))
   :rule-classes :type-prescription))

(local
 (defthm-std standardp-riemann-diff-sum-fi-primes-lower-bound
   (implies (and (standardp i)
                 (standardp a)
                 (standardp b))
            (standardp (riemann-diff-sum-fi-primes-lower-bound a b i)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm riemann-diff-sum-fi-primes-lower-bound-approaches-0
   (implies (and (interval-left-inclusive-p (fi-domain))
                 (interval-right-inclusive-p (fi-domain))
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (i-large i)
                 (natp i))
            (i-close (riemann-diff-sum-fi-primes-lower-bound
                      a b i)
                     0))
   :hints (("Goal"
            :in-theory (e/d (diff-sum-fi-primes-min-x)
                            (DISTRIBUTIVITY))
            :use (:instance i-close-times
                            (x (- b a))
                            (y1 (diff-sum-fi-primes
                                 (diff-sum-fi-primes-min-x
                                  a b i)
                                 i))
                            (y2 0))))))

(local
 (defthm riemann-diff-sum-fi-primes-lower-bound-approaches-upper-bound
   (implies (and (interval-left-inclusive-p (fi-domain))
                 (interval-right-inclusive-p (fi-domain))
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (i-large i)
                 (natp i))
            (i-close (riemann-diff-sum-fi-primes-lower-bound
                      a b i)
                     (riemann-diff-sum-fi-primes-upper-bound
                      a b i)))
   :hints (("Goal"
            :in-theory (disable riemann-diff-sum-fi-primes-lower-bound
                                riemann-diff-sum-fi-primes-upper-bound)
            :use (:instance i-close-transitive
                            (x (riemann-diff-sum-fi-primes-lower-bound
                                a b i))
                            (y 0)
                            (z (riemann-diff-sum-fi-primes-upper-bound
                                a b i)))))))

(local
 (defthm strict-int-diff-sum-fi-primes-bounded
   (implies (and (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (< a b))
            (and (<= (riemann-diff-sum-fi-primes-lower-bound a b i)
                     (riemann-diff-sum-fi-primes (make-small-partition a b) i))
                 (<= (riemann-diff-sum-fi-primes (make-small-partition a b) i)
                     (riemann-diff-sum-fi-primes-upper-bound a b i))))
   :hints (("Goal"
	    :use ((:instance riemann-diff-sum-fi-primes-bounded-below
			     (p (make-small-partition a b)))
		  (:instance riemann-diff-sum-fi-primes-bounded-above
			     (p (make-small-partition a b)))
		  (:instance car-make-small-partition)
		  (:instance car-last-make-small-partition)
		  (:instance partitionp-make-small-partition))
	    :in-theory (disable car-make-small-partition
				car-last-make-small-partition
				partitionp-make-small-partition)))
   :rule-classes :linear))

(local (in-theory (disable riemann-diff-sum-fi-primes-upper-bound
                           riemann-diff-sum-fi-primes-lower-bound)))

;; ======================================================================

;; Define the Riemann integral of diff-sum-fi-primes.

(local
 (encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm realp-riemann-diff-sum-fi-primes
    (implies (partitionp p)
             (realp (riemann-diff-sum-fi-primes p i)))
    :rule-classes :type-prescription)))

(local
 (defthm limited-riemann-diff-sum-fi-primes-small-partition
   (implies (and (standardp i)
                 (standardp a)
                 (standardp b)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (< a b))
            (i-limited (riemann-diff-sum-fi-primes
                        (make-small-partition a b) i)))
   :hints (("Goal"
            :use ((:instance standards-are-limited
                             (x (riemann-diff-sum-fi-primes-upper-bound
                                 a b i)))
                  (:instance standards-are-limited
                             (x (riemann-diff-sum-fi-primes-lower-bound
                                 a b i)))
                  (:instance limited-squeeze
                             (a (riemann-diff-sum-fi-primes-lower-bound
                                 a b i))
                             (b (riemann-diff-sum-fi-primes-upper-bound
                                 a b i))
                             (x (riemann-diff-sum-fi-primes
                                 (make-small-partition a b) i)))
                  (:instance strict-int-diff-sum-fi-primes-bounded)
                  (:instance realp-riemann-diff-sum-fi-primes
                             (p (make-small-partition a b))))
            :in-theory (disable limited-squeeze
                                standards-are-limited
                                standards-are-limited-forward
                                riemann-diff-sum-fi-primes)))))

(local (in-theory (disable riemann-diff-sum-fi-primes)))

(local
 (defun-std strict-int-diff-sum-fi-primes (a b i)
   (if (and (inside-interval-p a (fi-domain))
            (inside-interval-p b (fi-domain))
            (< a b))
       (standard-part (riemann-diff-sum-fi-primes
                       (make-small-partition a b) i))
     0)))

(local
 (defun int-diff-sum-fi-primes (a b i)
   (if (<= a b)
       (strict-int-diff-sum-fi-primes a b i)
     (- (strict-int-diff-sum-fi-primes b a i)))))

;; ======================================================================

(local
 (defthm-std int-diff-sum-fi-primes-bounded-1
   (implies (and (<= a b)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain)))
            (and (<= (riemann-diff-sum-fi-primes-lower-bound
                      a b i)
                     (int-diff-sum-fi-primes a b i))
                 (<= (int-diff-sum-fi-primes a b i)
                     (riemann-diff-sum-fi-primes-upper-bound
                      a b i))))
   :hints (("Goal"
            :expand ((riemann-diff-sum-fi-primes-lower-bound a a i)
                     (riemann-diff-sum-fi-primes-upper-bound a a i))
            :use ((:instance realp-riemann-diff-sum-fi-primes
                             (p (make-small-partition a b)))
                  (:instance strict-int-diff-sum-fi-primes-bounded)
                  (:instance STANDARD-PART-<=
                             (x (riemann-diff-sum-fi-primes-lower-bound
                                 a b i))
                             (y (riemann-diff-sum-fi-primes
                                 (make-small-partition a b) i)))
                  (:instance STANDARD-PART-<=
                             (x (riemann-diff-sum-fi-primes
                                 (make-small-partition a b) i))
                             (y (riemann-diff-sum-fi-primes-upper-bound
                                 a b i))))))
   :rule-classes :linear))

(local
 (defthm-std int-diff-sum-fi-primes-bounded-2
   (implies (and (< b a)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain)))
            (and (<= (- (riemann-diff-sum-fi-primes-upper-bound
                         b a i))
                     (int-diff-sum-fi-primes a b i))
                 (<= (int-diff-sum-fi-primes a b i)
                     (- (riemann-diff-sum-fi-primes-lower-bound
                         b a i)))))
   :hints (("Goal"
            :use ((:instance realp-riemann-diff-sum-fi-primes
                             (p (make-small-partition b a)))
                  (:instance strict-int-diff-sum-fi-primes-bounded
                             (a b)
                             (b a))
                  (:instance STANDARD-PART-<=
                             (x (- (riemann-diff-sum-fi-primes-upper-bound
                                    b a i)))
                             (y (- (riemann-diff-sum-fi-primes
                                    (make-small-partition b a) i))))
                  (:instance STANDARD-PART-<=
                             (x (- (riemann-diff-sum-fi-primes
                                    (make-small-partition b a) i)))
                             (y (- (riemann-diff-sum-fi-primes-lower-bound
                                    b a i)))))))
   :rule-classes :linear))

(local
 (defthm-std realp-int-diff-sum-fi-primes
   (realp (int-diff-sum-fi-primes a b i))
   :hints (("Goal"
            :use ((:instance realp-riemann-diff-sum-fi-primes
                             (p (make-small-partition a b)))
                  (:instance realp-riemann-diff-sum-fi-primes
                             (p (make-small-partition b a))))))
   :rule-classes :type-prescription))

(local
 (encapsulate
  ()

  (local
   (defthm int-diff-sum-fi-primes-approaches-0-lemma-1
     (implies (and (<= a b)
                   (interval-left-inclusive-p (fi-domain))
                   (interval-right-inclusive-p (fi-domain))
                   (inside-interval-p a (fi-domain))
                   (inside-interval-p b (fi-domain))
                   (i-large i)
                   (natp i))
              (i-close (int-diff-sum-fi-primes a b i)
                       0))
     :hints (("Goal"
              :in-theory (disable int-diff-sum-fi-primes)
              :use ((:instance close-squeeze
                               (x (riemann-diff-sum-fi-primes-lower-bound
                                   a b i))
                               (y (int-diff-sum-fi-primes
                                   a b i))
                               (z (riemann-diff-sum-fi-primes-upper-bound
                                   a b i))))))))

  (local
   (defthm int-diff-sum-fi-primes-approaches-0-lemma-2
     (implies (and (< b a)
                   (interval-left-inclusive-p (fi-domain))
                   (interval-right-inclusive-p (fi-domain))
                   (inside-interval-p a (fi-domain))
                   (inside-interval-p b (fi-domain))
                   (i-large i)
                   (natp i))
              (i-close (int-diff-sum-fi-primes a b i)
                       0))
     :hints (("Goal"
              :in-theory (disable int-diff-sum-fi-primes)
              :use ((:instance close-squeeze
                               (x (- (riemann-diff-sum-fi-primes-upper-bound
                                      b a i)))
                               (y (int-diff-sum-fi-primes
                                   a b i))
                               (z (- (riemann-diff-sum-fi-primes-lower-bound
                                      b a i))))
                    (:instance i-close-times
                               (x -1)
                               (y1 (riemann-diff-sum-fi-primes-lower-bound
                                    b a i))
                               (y2 0))
                    (:instance i-close-times
                               (x -1)
                               (y1 (riemann-diff-sum-fi-primes-upper-bound
                                    b a i))
                               (y2 0)))))))

  (defthm int-diff-sum-fi-primes-approaches-0
    (implies (and (interval-left-inclusive-p (fi-domain))
                  (interval-right-inclusive-p (fi-domain))
                  (inside-interval-p a (fi-domain))
                  (inside-interval-p b (fi-domain))
                  (i-large i)
                  (natp i))
             (i-close (int-diff-sum-fi-primes a b i)
                      0))
    :hints (("Goal"
             :cases ((<= a b) (< b a))
             :use ((:instance int-diff-sum-fi-primes-approaches-0-lemma-1)
                   (:instance int-diff-sum-fi-primes-approaches-0-lemma-2)))))))

;; ======================================================================

(defun map-sum-fi-prime-infinity (p)
  (if (consp p)
      (cons (sum-fi-prime-infinity (car p))
	    (map-sum-fi-prime-infinity (cdr p)))
    nil))

(defun riemann-sum-fi-prime-infinity (p)
  (dotprod (deltas p)
	   (map-sum-fi-prime-infinity (cdr p))))

(local
 (defthm limited-riemann-sum-fi-prime-infinity-small-partition
   (implies (and (standardp a)
                 (standardp b)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (< a b))
            (i-limited (riemann-sum-fi-prime-infinity
                        (make-small-partition a b))))
   :hints (("Goal"
            :use (:functional-instance limited-riemann-rcfn-small-partition
                                       (rcfn sum-fi-prime-infinity)
                                       (rcfn-domain fi-domain)
                                       (map-rcfn map-sum-fi-prime-infinity)
                                       (riemann-rcfn
                                        riemann-sum-fi-prime-infinity)))
           ("Subgoal 3"
            :use sum-fi-prime-infinity-continuous)
           ("Subgoal 2"
            :use fi-domain-non-trivial))))

(encapsulate
 ()

 (local (in-theory (disable riemann-sum-fi-prime-infinity)))

 (defun-std strict-int-sum-fi-prime-infinity (a b)
   (if (and (inside-interval-p a (fi-domain))
            (inside-interval-p b (fi-domain))
            (< a b))
       (standard-part (riemann-sum-fi-prime-infinity
                       (make-small-partition a b)))
     0)))

(defun int-sum-fi-prime-infinity (a b)
  (if (<= a b)
      (strict-int-sum-fi-prime-infinity a b)
    (- (strict-int-sum-fi-prime-infinity b a))))

(local
 (defthm sum-fi-prime-infinity-ftc-1
   (implies (and (inside-interval-p a (fi-domain))
                 (inside-interval-p x (fi-domain))
                 (inside-interval-p x1 (fi-domain))
                 (standardp x)
                 (i-close x x1)
                 (not (equal x x1)))
            (i-close (/ (- (int-sum-fi-prime-infinity a x)
                           (int-sum-fi-prime-infinity a x1))
                        (- x x1))
                     (sum-fi-prime-infinity x)))
   :hints
   (("goal"
     :by (:functional-instance
          ftc-1
          (rcfn sum-fi-prime-infinity)
          (rcfn-domain fi-domain)
          (map-rcfn map-sum-fi-prime-infinity)
          (riemann-rcfn riemann-sum-fi-prime-infinity)
          (strict-int-rcfn strict-int-sum-fi-prime-infinity)
          (int-rcfn int-sum-fi-prime-infinity))))))

;; ======================================================================

(local
 (defun diff-int-sum-fi-primes (a b i)
   (- (int-sum-fi-prime-infinity a b)
      (int-sum-fi-prime a b i))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm realp-riemann-sum-fi-prime
   (implies (partitionp p)
            (realp (riemann-sum-fi-prime p i)))
   :rule-classes :type-prescription)

 (defthm realp-riemann-sum-fi-prime-infinity
   (implies (partitionp p)
            (realp (riemann-sum-fi-prime-infinity p)))
   :rule-classes :type-prescription))

(local
 (defthm-std realp-diff-int-sum-fi-primes
   (realp (diff-int-sum-fi-primes a b i))
   :hints (("Goal"
            :in-theory (disable riemann-sum-fi-prime-infinity
                                riemann-sum-fi-prime)
            :use ((:instance realp-riemann-sum-fi-prime-infinity
                             (p (make-small-partition a b)))
                  (:instance realp-riemann-sum-fi-prime-infinity
                             (p (make-small-partition b a)))
                  (:instance realp-riemann-sum-fi-prime
                             (p (make-small-partition a b)))
                  (:instance realp-riemann-sum-fi-prime
                             (p (make-small-partition b a))))))
   :rule-classes :type-prescription))

(local
 (defthm diff-int-sum-fi-primes-derivative
   (implies (and (standardp i)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p x (fi-domain))
                 (inside-interval-p x1 (fi-domain))
                 (standardp x)
                 (i-close x x1)
                 (not (equal x x1)))
            (i-close (/ (- (diff-int-sum-fi-primes a x i)
                           (diff-int-sum-fi-primes a x1 i))
                        (- x x1))
                     (diff-sum-fi-primes x i)))
   :hints (("Goal"
            :in-theory (e/d (diff-sum-fi-primes)
                            (sum-fi-prime-infinity
                             sum-fi-prime
                             int-sum-fi-prime-infinity
                             int-sum-fi-prime))
            :use (sum-fi-prime-infinity-ftc-1
                  sum-fi-prime-ftc-1-2
                  (:instance i-close-times
                             (x -1)
                             (y1 (/ (- (int-sum-fi-prime a x i)
                                       (int-sum-fi-prime a x1 i))
                                    (- x x1)))
                             (y2 (sum-fi-prime x i)))
                  (:instance i-close-plus
                             (x1 (/ (- (int-sum-fi-prime-infinity a x)
                                       (int-sum-fi-prime-infinity a x1))
                                    (- x x1)))
                             (x2 (sum-fi-prime-infinity x))
                             (y1 (- (/ (- (int-sum-fi-prime a x i)
                                          (int-sum-fi-prime a x1 i))
                                       (- x x1))))
                             (y2 (- (sum-fi-prime x i)))))))))

(local
 (defthm sum-rule-of-int-diff-sum-fi-primes-lemma-1
   (implies (and (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain)))
            (equal (int-diff-sum-fi-primes a b (i))
                   (- (diff-int-sum-fi-primes (low) b (i))
                      (diff-int-sum-fi-primes (low) a (i)))))
   :hints (("Goal"
            :in-theory (enable riemann-diff-sum-fi-primes)
            :by (:functional-instance
                 ftc-2
                 (rcdfn
                  (lambda (x)
                    (diff-int-sum-fi-primes (low) x (i))))
                 (rcdfn-prime
                  (lambda (x)
                    (diff-sum-fi-primes x (i))))
                 (rcdfn-domain fi-domain)
                 (map-rcdfn-prime
                  (lambda (p)
                    (map-diff-sum-fi-primes p (i))))
                 (riemann-rcdfn-prime
                  (lambda (p)
                    (riemann-diff-sum-fi-primes p (i))))
                 (strict-int-rcdfn-prime
                  (lambda (a b)
                    (strict-int-diff-sum-fi-primes a b (i))))
                 (int-rcdfn-prime
                  (lambda (a b)
                    (int-diff-sum-fi-primes a b (i))))))
           ("Subgoal 7"
            :use (:instance diff-int-sum-fi-primes-derivative
                            (a (low))
                            (i (i))))
           ("Subgoal 6"
            :use fi-domain-non-trivial))))

(local
 (defthm-std sum-rule-of-int-diff-sum-fi-primes-lemma-2
   (equal (diff-int-sum-fi-primes a a i) 0)))

(local
 (defthm sum-rule-of-int-diff-sum-fi-primes
   (implies (and (natp i)
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain)))
            (equal (int-diff-sum-fi-primes a b i)
                   (diff-int-sum-fi-primes a b i)))
   :hints (("Goal"
            :use (:functional-instance
                  sum-rule-of-int-diff-sum-fi-primes-lemma-1
                  (low (lambda ()
                         (if (inside-interval-p a (fi-domain)) a (low))))
                  (i (lambda ()
                       (if (natp i) i (i)))))))))

;; ======================================================================

(local
 (defthm int-sum-fi-prime-infinity-lemma-1
   (implies (and (interval-left-inclusive-p (fi-domain))
                 (interval-right-inclusive-p (fi-domain))
                 (inside-interval-p a (fi-domain))
                 (inside-interval-p b (fi-domain))
                 (i-large i)
                 (natp i))
            (i-close (int-sum-fi-prime-infinity a b)
                     (int-sum-fi-prime a b i)))
   :hints (("Goal"
            :in-theory (enable i-close)
            :use int-diff-sum-fi-primes-approaches-0))))

(defthm-std standardp-int-sum-fi-prime-infinity
  (implies (and (standardp a)
                (standardp b))
           (standardp (int-sum-fi-prime-infinity a b)))
  :rule-classes (:rewrite :type-prescription))

(encapsulate
 ()

 (local (in-theory (disable int-sum-fi-prime-infinity
                            int-sum-fi-prime
                            sum-rule-of-int-sum-fi-prime)))

 (local
  (defthm limited-int-sum-fi-prime-with-large-index
    (implies (and (standardp a)
                  (standardp b)
                  (interval-left-inclusive-p (fi-domain))
                  (interval-right-inclusive-p (fi-domain))
                  (inside-interval-p a (fi-domain))
                  (inside-interval-p b (fi-domain))
                  (i-large i)
                  (natp i))
             (i-limited (int-sum-fi-prime a b i)))
    :hints (("Goal"
             :use ((:instance standards-are-limited
                              (x (int-sum-fi-prime-infinity a b)))
                   (:instance i-close-limited
                              (x (int-sum-fi-prime-infinity a b))
                              (y (int-sum-fi-prime a b i))))))))

 (defun-std int-sum-fi-prime-with-large-index (a b)
   (if (and (interval-left-inclusive-p (fi-domain))
            (interval-right-inclusive-p (fi-domain))
            (inside-interval-p a (fi-domain))
            (inside-interval-p b (fi-domain)))
       (standard-part (int-sum-fi-prime a b (i-large-integer)))
     0))

 (local
  (defthm limited-sum-int-fi-prime-with-large-index
    (implies (and (standardp a)
                  (standardp b)
                  (interval-left-inclusive-p (fi-domain))
                  (interval-right-inclusive-p (fi-domain))
                  (inside-interval-p a (fi-domain))
                  (inside-interval-p b (fi-domain))
                  (i-large i)
                  (natp i))
             (i-limited (sum-int-fi-prime a b i)))
    :hints (("Goal"
             :in-theory (disable sum-rule-of-int-sum-fi-prime)
             :use sum-rule-of-int-sum-fi-prime))))

 (defun-std sum-int-fi-prime-with-large-index (a b)
   (if (and (interval-left-inclusive-p (fi-domain))
            (interval-right-inclusive-p (fi-domain))
            (inside-interval-p a (fi-domain))
            (inside-interval-p b (fi-domain)))
       (standard-part (sum-int-fi-prime a b (i-large-integer)))
     0)))

(defthm-std int-sum-fi-prime-infinity-lemma-2
  (implies (and (interval-left-inclusive-p (fi-domain))
                (interval-right-inclusive-p (fi-domain))
                (inside-interval-p a (fi-domain))
                (inside-interval-p b (fi-domain)))
           (equal (int-sum-fi-prime-infinity a b)
                  (int-sum-fi-prime-with-large-index a b)))
  :hints (("Goal"
           :in-theory (disable int-sum-fi-prime-infinity
                               int-sum-fi-prime
                               sum-rule-of-int-sum-fi-prime)
           :use (int-sum-fi-prime-infinity-lemma-1
                 (:instance close-x-y->same-standard-part
                            (x (int-sum-fi-prime-infinity a b))
                            (y (int-sum-fi-prime a b (i-large-integer))))))))

(defthm-std sum-rule-of-int-sum-fi-prime-infinity
  (implies (and (interval-left-inclusive-p (fi-domain))
                (interval-right-inclusive-p (fi-domain))
                (inside-interval-p a (fi-domain))
                (inside-interval-p b (fi-domain)))
           (equal (int-sum-fi-prime-infinity a b)
                  (sum-int-fi-prime-with-large-index a b))))
