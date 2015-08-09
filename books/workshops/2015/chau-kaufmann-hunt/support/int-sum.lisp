;; Proof of the sum rule for definite integrals of indexed sums using FTC-1,
;; FTC-2 and the sum rule for differentiation.

;; Cuong Chau                             March, 2015

(in-package "ACL2")

(include-book "riemann-integral/ftc-1-2")
(include-book "utils")

(local (include-book "nonstd/integrals/ftc-2" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;; ======================================================================

(encapsulate
 ((low () t)
  (fi-prime (x i) t)
  (fi-domain () t))

 (local (defun low () 0))
 (local (defun fi-prime (x i) (declare (ignore x i)) 1))
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
            (i-close (fi-prime x i) (fi-prime y i)))))

(defthm-std standardp-fi-domain
  (standardp (fi-domain))
  :rule-classes (:rewrite :type-prescription))

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

;; Define sum-fi-prime.

(defun sum-fi-prime (x i)
  (if (zp i)
      (fi-prime x 0)
    (+ (fi-prime x i)
       (sum-fi-prime x (1- i)))))

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

;; (defthm sum-fi-prime-ftc-1-2
;;   (implies (and (standardp i)
;;                 (inside-interval-p a (fi-domain))
;;                 (inside-interval-p x (fi-domain))
;;                 (inside-interval-p x1 (fi-domain))
;;                 (standardp x)
;;                 (i-close x x1)
;;                 (not (equal x x1)))
;;            (i-close (/ (- (int-sum-fi-prime a x i)
;;                           (int-sum-fi-prime a x1 i))
;;                        (- x x1))
;;                     (sum-fi-prime x i)))
;;   :hints
;;   (("goal"
;;     :by (:functional-instance ftc-1-2
;;                               (rcfn-2
;;                                (lambda (x i)
;;                                  (sum-fi-prime x i)))
;;                               (rcfn-2-domain fi-domain)
;;                               (map-rcfn-2
;;                                (lambda (p i)
;;                                  (map-sum-fi-prime p i)))
;;                               (riemann-rcfn-2
;;                                (lambda (p i)
;;                                  (riemann-sum-fi-prime p i)))
;;                               (strict-int-rcfn-2
;;                                (lambda (a b i)
;;                                  (strict-int-sum-fi-prime a b i)))
;;                               (int-rcfn-2
;;                                (lambda (a b i)
;;                                  (int-sum-fi-prime a b i)))))))

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


