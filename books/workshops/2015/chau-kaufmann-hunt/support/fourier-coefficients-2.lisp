;; Proof of Fourier coefficient formulas.

;; Cuong Chau                             August, 2015

(in-package "ACL2")

(include-book "fourier-inner-product")

(local (include-book "int-sum"))
(local (include-book "sines-orthog"))
(local (include-book "cosines-orthog"))
(local (include-book "sine-cosine-orthog"))
(local
 (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal" :dir :system))
(local (include-book "nonstd/integrals/ftc-2" :dir :system))

;; ======================================================================

;; Define fn*cos-i and fn*cos-i-prime.

(local
 (defun fn*cos-i (x i k c)
   (+ (* (r i)
         (cos-orthog x i k c))
      (* (s i)
         (sin-cos-orthog x i k c)))))

(local
 (defun fn*cos-i-prime (x i k c)
   (+ (* (r i)
         (cos-orthog-prime x i k c))
      (* (s i)
         (sin-cos-orthog-prime x i k c)))))

(local
 (defthm realp-fn*cos-i
   (realp (fn*cos-i x i k c))
   :rule-classes :type-prescription))

(local
 (defthm realp-fn*cos-i-prime
   (realp (fn*cos-i-prime x i k c))
   :rule-classes :type-prescription))

(local
 (defthm fn*cos-i-prime-continuous
   (implies (and (standardp i)
                 (standardp k)
                 (standardp c)
                 (standardp x)
                 (inside-interval-p x (fn-domain))
                 (inside-interval-p y (fn-domain))
                 (i-close x y))
            (i-close (fn*cos-i-prime x i k c)
                     (fn*cos-i-prime y i k c)))
   :hints (("Goal"
            :use ((:instance i-close-times
                             (x (r i))
                             (y1 (cos-orthog-prime x i k c))
                             (y2 (cos-orthog-prime y i k c)))
                  (:instance i-close-times
                             (x (s i))
                             (y1 (sin-cos-orthog-prime x i k c))
                             (y2 (sin-cos-orthog-prime y i k c))))))))

(local
 (defthm fn*cos-i-derivative
   (implies (and (standardp i)
                 (natp i)
                 (standardp k)
                 (natp k)
                 (standardp c)
                 (realp c)
                 (not (equal c 0))
                 (standardp x)
                 (inside-interval-p x (fn-domain))
                 (inside-interval-p x1 (fn-domain))
                 (i-close x x1)
                 (not (equal x x1)))
            (i-close (/ (- (fn*cos-i x i k c)
                           (fn*cos-i x1 i k c))
                        (- x x1))
                     (fn*cos-i-prime x i k c)))
   :hints (("Goal"
            :in-theory (disable i-close-plus i-close-times)
            :use ((:instance i-close-times
                             (x (r i))
                             (y1 (/ (- (cos-orthog x i k c)
                                       (cos-orthog x1 i k c))
                                    (- x x1)))
                             (y2 (cos-orthog-prime x i k c)))
                  (:instance i-close-times
                             (x (s i))
                             (y1 (/ (- (sin-cos-orthog x i k c)
                                       (sin-cos-orthog x1 i k c))
                                    (- x x1)))
                             (y2 (sin-cos-orthog-prime x i k c)))
                  (:instance i-close-plus
                             (x1 (* (r i)
                                    (/ (- (cos-orthog x i k c)
                                          (cos-orthog x1 i k c))
                                       (- x x1))))
                             (x2 (* (r i)
                                    (cos-orthog-prime x i k c)))
                             (y1 (* (s i)
                                    (/ (- (sin-cos-orthog x i k c)
                                          (sin-cos-orthog x1 i k c))
                                       (- x x1))))
                             (y2 (* (s i)
                                    (sin-cos-orthog-prime x i k c))))
                  (:instance cos-orthog-derivative
                             (m i)
                             (n k))
                  (:instance sin-cos-orthog-derivative
                             (m i)
                             (n k)))))))

(local (in-theory (disable fn*cos-i fn*cos-i-prime)))

;; ======================================================================

;; Define the Riemann integral of fn*cos-i-prime.

(local
 (defun map-fn*cos-i-prime (p i k c)
   (if (consp p)
       (cons (fn*cos-i-prime (car p) i k c)
             (map-fn*cos-i-prime (cdr p) i k c))
     nil)))

(local
 (defun riemann-fn*cos-i-prime (p i k c)
   (dotprod (deltas p)
            (map-fn*cos-i-prime (cdr p) i k c))))

(local
 (defthm limited-riemann-fn*cos-i-prime-small-partition-lemma
   (implies (and (standardp arg)
                 (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-fn*cos-i-prime
                        (make-small-partition a b)
                        (nth 0 arg)
                        (nth 1 arg)
                        (nth 2 arg))))
   :hints (("Goal"
            :by (:functional-instance
                 limited-riemann-rcfn-2-small-partition
                 (rcfn-2 (lambda (x arg)
                           (fn*cos-i-prime x
                                       (nth 0 arg)
                                       (nth 1 arg)
                                       (nth 2 arg))))
                 (rcfn-2-domain fn-domain)
                 (map-rcfn-2
                  (lambda (p arg)
                    (map-fn*cos-i-prime p
                                    (nth 0 arg)
                                    (nth 1 arg)
                                    (nth 2 arg))))
                 (riemann-rcfn-2
                  (lambda (p arg)
                    (riemann-fn*cos-i-prime p
                                        (nth 0 arg)
                                        (nth 1 arg)
                                        (nth 2 arg)))))))))

(local
 (defthm-std standardp-list
   (implies (and (standardp i)
                 (standardp k)
                 (standardp c))
            (standardp (list i k c)))
   :rule-classes :type-prescription))

(local
 (defthm limited-riemann-fn*cos-i-prime-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (standardp i)
                 (standardp k)
                 (standardp c)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-fn*cos-i-prime
                        (make-small-partition a b)
                        i k c)))
   :hints (("Goal"
            :use (:instance limited-riemann-fn*cos-i-prime-small-partition-lemma
                            (arg (list i k c)))))))

(local
 (encapsulate
  ()

  (local (in-theory (disable riemann-fn*cos-i-prime)))

  (defun-std strict-int-fn*cos-i-prime (a b i k c)
    (if (and (realp a)
             (realp b)
             (inside-interval-p a (fn-domain))
             (inside-interval-p b (fn-domain))
             (< a b))
        (standard-part (riemann-fn*cos-i-prime
                        (make-small-partition a b)
                        i k c))
      0))))

(local
 (defun int-fn*cos-i-prime (a b i k c)
   (if (<= a b)
       (strict-int-fn*cos-i-prime a b i k c)
     (- (strict-int-fn*cos-i-prime b a i k c)))))

;; ======================================================================

;; Prove the ftc-2 that connects fn*cos-i-prime with fn*cos-i.

(local
 (encapsulate
  (((i) => *)
   ((k) => *)
   ((c) => *))

  (local (defun i () 0))
  (local (defun k () 0))
  (local (defun c () 1))

  (defthm natp-i
    (natp (i))
    :rule-classes :type-prescription)

  (defthm natp-k
    (natp (k))
    :rule-classes :type-prescription)

  (defthm realp-c
    (realp (c))
    :rule-classes :type-prescription)

  (defthm nonzero-c
    (not (equal (c) 0)))))

(local
 (defthm-std standardp-i
   (standardp (i))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm-std standardp-k
   (standardp (k))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm-std standardp-c
   (standardp (c))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm fn*cos-i-ftc-2-lemma
   (implies (and (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-fn*cos-i-prime a b (i) (k) (c))
                   (- (fn*cos-i b (i) (k) (c))
                      (fn*cos-i a (i) (k) (c)))))
   :hints (("Goal"
            :by (:functional-instance
                 ftc-2
                 (rcdfn
                  (lambda (x)
                    (fn*cos-i x (i)
                          (k) (c))))
                 (rcdfn-prime
                  (lambda (x)
                    (fn*cos-i-prime x (i)
                                (k) (c))))
                 (rcdfn-domain fn-domain)
                 (map-rcdfn-prime
                  (lambda (p)
                    (map-fn*cos-i-prime p (i)
                                    (k) (c))))
                 (riemann-rcdfn-prime
                  (lambda (p)
                    (riemann-fn*cos-i-prime p (i)
                                        (k) (c))))
                 (strict-int-rcdfn-prime
                  (lambda (a b)
                    (strict-int-fn*cos-i-prime a b (i)
                                           (k) (c))))
                 (int-rcdfn-prime
                  (lambda (a b)
                    (int-fn*cos-i-prime a b (i)
                                    (k) (c))))))
           ("Subgoal 6"
            :use (:instance fn*cos-i-derivative
                            (i (i))
                            (k (k))
                            (c (c)))))))

(local
 (defthm fn*cos-i-ftc-2
   (implies (and (natp i)
                 (natp k)
                 (realp c)
                 (not (equal c 0))
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-fn*cos-i-prime a b i k c)
                   (- (fn*cos-i b i k c)
                      (fn*cos-i a i k c))))
   :hints (("Goal"
            :by (:functional-instance fn*cos-i-ftc-2-lemma
                                      (i (lambda ()
                                           (if (natp i) i 0)))
                                      (k (lambda ()
                                           (if (natp k) k 0)))
                                      (c (lambda ()
                                           (if (and (realp c)
                                                    (not (equal c 0)))
                                               c
                                             1))))))))

(local (in-theory (disable int-fn*cos-i-prime)))

(local
 (defthm int-fn*cos-i-prime-thm
   (implies (and (natp i)
                 (natp k)
                 (realp c)
                 (not (equal c 0))
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-fn*cos-i-prime a b i k c)
                   (+ (* (r i)
                         (int-cos-orthog-prime a b i k c))
                      (* (s i)
                         (int-sin-cos-orthog-prime a b i k c)))))
   :hints (("Goal"
            :use ((:instance cos-orthog-m!=n-ftc-2
                             (m i)
                             (n k))
                  (:instance sin-cos-orthog-m!=n-ftc-2
                             (m i)
                             (n k)))
            :in-theory (enable fn*cos-i cos-orthog sin-cos-orthog)))))

;; ======================================================================

;; Define sum-fn*cos-i-prime.

(local
 (defun sum-fn*cos-i-prime (x i k c)
   (if (zp i)
       (fn*cos-i-prime x 0 k c)
     (+ (fn*cos-i-prime x i k c)
        (sum-fn*cos-i-prime x (1- i) k c)))))

(local
 (defthm realp-sum-fn*cos-i-prime
   (realp (sum-fn*cos-i-prime x i k c))
   :rule-classes :type-prescription))

(local
 (defthm sum-fn*cos-i-prime-continuous
   (implies (and (standardp i)
                 (standardp k)
                 (standardp c)
                 (standardp x)
                 (inside-interval-p x (fn-domain))
                 (inside-interval-p y (fn-domain))
                 (i-close x y))
            (i-close (sum-fn*cos-i-prime x i k c)
                     (sum-fn*cos-i-prime y i k c)))))

;; ======================================================================

;; Define the Riemann integral of sum-fn*cos-i-prime.

(local
 (defun map-sum-fn*cos-i-prime (p i k c)
   (if (consp p)
       (cons (sum-fn*cos-i-prime (car p) i k c)
             (map-sum-fn*cos-i-prime (cdr p) i k c))
     nil)))

(local
 (defun riemann-sum-fn*cos-i-prime (p i k c)
   (dotprod (deltas p)
            (map-sum-fn*cos-i-prime (cdr p) i k c))))

(local
 (defthm limited-riemann-sum-fn*cos-i-prime-small-partition-lemma
   (implies (and (standardp arg)
                 (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-sum-fn*cos-i-prime
                        (make-small-partition a b)
                        (nth 0 arg)
                        (nth 1 arg)
                        (nth 2 arg))))
   :hints (("Goal"
            :by (:functional-instance
                 limited-riemann-rcfn-2-small-partition
                 (rcfn-2 (lambda (x arg)
                           (sum-fn*cos-i-prime x
                                               (nth 0 arg)
                                               (nth 1 arg)
                                               (nth 2 arg))))
                 (rcfn-2-domain fn-domain)
                 (map-rcfn-2
                  (lambda (p arg)
                    (map-sum-fn*cos-i-prime p
                                            (nth 0 arg)
                                            (nth 1 arg)
                                            (nth 2 arg))))
                 (riemann-rcfn-2
                  (lambda (p arg)
                    (riemann-sum-fn*cos-i-prime p
                                                (nth 0 arg)
                                                (nth 1 arg)
                                                (nth 2 arg)))))))))

(local
 (defthm limited-riemann-sum-fn*cos-i-prime-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (standardp i)
                 (standardp k)
                 (standardp c)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-sum-fn*cos-i-prime
                        (make-small-partition a b)
                        i k c)))
   :hints (("Goal"
            :use (:instance limited-riemann-sum-fn*cos-i-prime-small-partition-lemma
                            (arg (list i k c)))))))

(local
 (encapsulate
  ()

  (local (in-theory (disable riemann-sum-fn*cos-i-prime)))

  (defun-std strict-int-sum-fn*cos-i-prime (a b i k c)
    (if (and (realp a)
             (realp b)
             (inside-interval-p a (fn-domain))
             (inside-interval-p b (fn-domain))
             (< a b))
        (standard-part (riemann-sum-fn*cos-i-prime (make-small-partition a b)
                                                   i k c))
      0))))

(local
 (defun int-sum-fn*cos-i-prime (a b i k c)
   (if (<= a b)
       (strict-int-sum-fn*cos-i-prime a b i k c)
     (- (strict-int-sum-fn*cos-i-prime b a i k c)))))

;; ======================================================================

;; Prove the sum rule of the integral of sum-fn*cos-i-prime.

(local
 (defun sum-int-fn*cos-i-prime (a b i k c)
   (if (zp i)
       (int-fn*cos-i-prime a b 0 k c)
     (+ (int-fn*cos-i-prime a b i k c)
        (sum-int-fn*cos-i-prime a b (1- i) k c)))))

(local
 (defthm sum-rule-of-int-sum-fn*cos-i-prime-lemma
   (implies (and (natp i)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-sum-fn*cos-i-prime a b i
                                           (k) (c))
                   (sum-int-fn*cos-i-prime a b i
                                           (k) (c))))
   :hints (("Goal"
            :in-theory (enable int-fn*cos-i-prime)
            :by (:functional-instance
                 sum-rule-of-int-sum-fi-prime
                 (low (lambda () 0))
                 (fi-prime
                  (lambda (x i)
                    (fn*cos-i-prime x i
                                    (k) (c))))
                 (fi-domain fn-domain)
                 (map-fi-prime
                  (lambda (p i)
                    (map-fn*cos-i-prime p i
                                        (k) (c))))
                 (riemann-fi-prime
                  (lambda (p i)
                    (riemann-fn*cos-i-prime p i
                                            (k) (c))))
                 (strict-int-fi-prime
                  (lambda (a b i)
                    (strict-int-fn*cos-i-prime a b i
                                               (k) (c))))
                 (int-fi-prime
                  (lambda (a b i)
                    (int-fn*cos-i-prime a b i
                                        (k) (c))))
                 (sum-fi-prime
                  (lambda (x i)
                    (sum-fn*cos-i-prime x i
                                        (k) (c))))
                 (map-sum-fi-prime
                  (lambda (p i)
                    (map-sum-fn*cos-i-prime p i
                                            (k) (c))))
                 (riemann-sum-fi-prime
                  (lambda (p i)
                    (riemann-sum-fn*cos-i-prime p i
                                                (k) (c))))
                 (strict-int-sum-fi-prime
                  (lambda (a b i)
                    (strict-int-sum-fn*cos-i-prime a b i
                                                   (k) (c))))
                 (int-sum-fi-prime
                  (lambda (a b i)
                    (int-sum-fn*cos-i-prime a b i
                                            (k) (c))))
                 (sum-int-fi-prime
                  (lambda (a b i)
                    (sum-int-fn*cos-i-prime a b i
                                            (k) (c)))))))))

(local
 (defthm sum-rule-of-int-sum-fn*cos-i-prime
   (implies (and (natp i)
                 (natp k)
                 (realp c)
                 (not (equal c 0))
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-sum-fn*cos-i-prime a b i
                                           k c)
                   (sum-int-fn*cos-i-prime a b i
                                           k c)))
   :hints (("Goal"
            :by (:functional-instance sum-rule-of-int-sum-fn*cos-i-prime-lemma
                                      (k (lambda ()
                                           (if (natp k)
                                               k
                                             0)))
                                      (c (lambda ()
                                           (if (and (realp c)
                                                    (not (equal c 0)))
                                               c
                                             1))))))))

(local (in-theory (disable int-sum-fn*cos-i-prime)))

;; Corollaries:

(local
 (defthm int-sum-fn*cos-i-prime-thm-1
   (implies (and (natp i)
                 (natp k)
                 (< i k)
                 (realp L)
                 (not (equal L 0)))
            (equal (* (/ L)
                      (int-sum-fn*cos-i-prime (- L) L
                                              i k (/ (acl2-pi) L)))
                   0))))

(local
 (defthm int-sum-fn*cos-i-prime-thm-2
   (implies (and (natp i)
                 (realp L)
                 (not (equal L 0)))
            (equal (* 1/2 (/ L)
                      (int-sum-fn*cos-i-prime (- L) L
                                              i 0 (/ (acl2-pi) L)))
                   (r 0)))))

(local
 (defthm int-sum-fn*cos-i-prime-thm-3
   (implies (and (natp i)
                 (posp k)
                 (<= k i)
                 (realp L)
                 (not (equal L 0)))
            (equal (* (/ L)
                      (int-sum-fn*cos-i-prime (- L) L
                                              i k (/ (acl2-pi) L)))
                   (r k)))
   :hints (("Subgoal *1/4"
            :in-theory (disable int-sum-fn*cos-i-prime-thm-1)
            :use (:instance int-sum-fn*cos-i-prime-thm-1
                            (i (1- i))
                            (k i))))))

(local (in-theory (disable sum-rule-of-int-sum-fn*cos-i-prime)))

;; ======================================================================

;; Define fn*sin-i and fn*sin-i-prime.

(local
 (defun fn*sin-i (x i k c)
   (+ (* (r i)
         (sin-cos-orthog x k i c))
      (* (s i)
         (sin-orthog x k i c)))))

(local
 (defun fn*sin-i-prime (x i k c)
   (+ (* (r i)
         (sin-cos-orthog-prime x k i c))
      (* (s i)
         (sin-orthog-prime x k i c)))))

(local
 (defthm realp-fn*sin-i
   (realp (fn*sin-i x i k c))
   :rule-classes :type-prescription))

(local
 (defthm realp-fn*sin-i-prime
   (realp (fn*sin-i-prime x i k c))
   :rule-classes :type-prescription))

(local
 (defthm fn*sin-i-prime-continuous
   (implies (and (standardp i)
                 (standardp k)
                 (standardp c)
                 (standardp x)
                 (inside-interval-p x (fn-domain))
                 (inside-interval-p y (fn-domain))
                 (i-close x y))
            (i-close (fn*sin-i-prime x i k c)
                     (fn*sin-i-prime y i k c)))
   :hints (("Goal"
            :use ((:instance i-close-times
                             (x (r i))
                             (y1 (sin-orthog-prime x k i c))
                             (y2 (sin-orthog-prime y k i c)))
                  (:instance i-close-times
                             (x (s i))
                             (y1 (sin-cos-orthog-prime x k i c))
                             (y2 (sin-cos-orthog-prime y k i c))))))))

(local
 (defthm fn*sin-i-derivative
   (implies (and (standardp i)
                 (natp i)
                 (standardp k)
                 (natp k)
                 (standardp c)
                 (realp c)
                 (not (equal c 0))
                 (standardp x)
                 (inside-interval-p x (fn-domain))
                 (inside-interval-p x1 (fn-domain))
                 (i-close x x1)
                 (not (equal x x1)))
            (i-close (/ (- (fn*sin-i x i k c)
                           (fn*sin-i x1 i k c))
                        (- x x1))
                     (fn*sin-i-prime x i k c)))
   :hints (("Goal"
            :in-theory (disable i-close-plus i-close-times)
            :use ((:instance i-close-times
                             (x (r i))
                             (y1 (/ (- (sin-cos-orthog x k i c)
                                       (sin-cos-orthog x1 k i c))
                                    (- x x1)))
                             (y2 (sin-cos-orthog-prime x k i c)))
                  (:instance i-close-times
                             (x (s i))
                             (y1 (/ (- (sin-orthog x k i c)
                                       (sin-orthog x1 k i c))
                                    (- x x1)))
                             (y2 (sin-orthog-prime x k i c)))
                  (:instance i-close-plus
                             (x1 (* (r i)
                                    (/ (- (sin-cos-orthog x k i c)
                                          (sin-cos-orthog x1 k i c))
                                       (- x x1))))
                             (x2 (* (r i)
                                    (sin-cos-orthog-prime x k i c)))
                             (y1 (* (s i)
                                    (/ (- (sin-orthog x k i c)
                                          (sin-orthog x1 k i c))
                                       (- x x1))))
                             (y2 (* (s i)
                                    (sin-orthog-prime x k i c))))
                  (:instance sin-orthog-derivative
                             (m k)
                             (n i))
                  (:instance sin-cos-orthog-derivative
                             (m k)
                             (n i)))))))

(local (in-theory (disable fn*sin-i fn*sin-i-prime)))

;; ======================================================================

;; Define the Riemann integral of fn*sin-i-prime.

(local
 (defun map-fn*sin-i-prime (p i k c)
   (if (consp p)
       (cons (fn*sin-i-prime (car p) i k c)
             (map-fn*sin-i-prime (cdr p) i k c))
     nil)))

(local
 (defun riemann-fn*sin-i-prime (p i k c)
   (dotprod (deltas p)
            (map-fn*sin-i-prime (cdr p) i k c))))

(local
 (defthm limited-riemann-fn*sin-i-prime-small-partition-lemma
   (implies (and (standardp arg)
                 (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-fn*sin-i-prime
                        (make-small-partition a b)
                        (nth 0 arg)
                        (nth 1 arg)
                        (nth 2 arg))))
   :hints (("Goal"
            :by (:functional-instance
                 limited-riemann-rcfn-2-small-partition
                 (rcfn-2 (lambda (x arg)
                           (fn*sin-i-prime x
                                       (nth 0 arg)
                                       (nth 1 arg)
                                       (nth 2 arg))))
                 (rcfn-2-domain fn-domain)
                 (map-rcfn-2
                  (lambda (p arg)
                    (map-fn*sin-i-prime p
                                    (nth 0 arg)
                                    (nth 1 arg)
                                    (nth 2 arg))))
                 (riemann-rcfn-2
                  (lambda (p arg)
                    (riemann-fn*sin-i-prime p
                                        (nth 0 arg)
                                        (nth 1 arg)
                                        (nth 2 arg)))))))))

(local
 (defthm limited-riemann-fn*sin-i-prime-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (standardp i)
                 (standardp k)
                 (standardp c)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-fn*sin-i-prime
                        (make-small-partition a b)
                        i k c)))
   :hints (("Goal"
            :use (:instance limited-riemann-fn*sin-i-prime-small-partition-lemma
                            (arg (list i k c)))))))

(local
 (encapsulate
  ()

  (local (in-theory (disable riemann-fn*sin-i-prime)))

  (defun-std strict-int-fn*sin-i-prime (a b i k c)
    (if (and (realp a)
             (realp b)
             (inside-interval-p a (fn-domain))
             (inside-interval-p b (fn-domain))
             (< a b))
        (standard-part (riemann-fn*sin-i-prime
                        (make-small-partition a b)
                        i k c))
      0))))

(local
 (defun int-fn*sin-i-prime (a b i k c)
   (if (<= a b)
       (strict-int-fn*sin-i-prime a b i k c)
     (- (strict-int-fn*sin-i-prime b a i k c)))))

;; ======================================================================

;; Prove the ftc-2 that connects fn*sin-i-prime with fn*sin-i.

(local
 (defthm fn*sin-i-ftc-2-lemma
   (implies (and (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-fn*sin-i-prime a b (i) (k) (c))
                   (- (fn*sin-i b (i) (k) (c))
                      (fn*sin-i a (i) (k) (c)))))
   :hints (("Goal"
            :by (:functional-instance
                 ftc-2
                 (rcdfn
                  (lambda (x)
                    (fn*sin-i x (i)
                          (k) (c))))
                 (rcdfn-prime
                  (lambda (x)
                    (fn*sin-i-prime x (i)
                                (k) (c))))
                 (rcdfn-domain fn-domain)
                 (map-rcdfn-prime
                  (lambda (p)
                    (map-fn*sin-i-prime p (i)
                                    (k) (c))))
                 (riemann-rcdfn-prime
                  (lambda (p)
                    (riemann-fn*sin-i-prime p (i)
                                        (k) (c))))
                 (strict-int-rcdfn-prime
                  (lambda (a b)
                    (strict-int-fn*sin-i-prime a b (i)
                                           (k) (c))))
                 (int-rcdfn-prime
                  (lambda (a b)
                    (int-fn*sin-i-prime a b (i)
                                    (k) (c))))))
           ("Subgoal 6"
            :use (:instance fn*sin-i-derivative
                            (i (i))
                            (k (k))
                            (c (c)))))))

(local
 (defthm fn*sin-i-ftc-2
   (implies (and (natp i)
                 (natp k)
                 (realp c)
                 (not (equal c 0))
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-fn*sin-i-prime a b i k c)
                   (- (fn*sin-i b i k c)
                      (fn*sin-i a i k c))))
   :hints (("Goal"
            :by (:functional-instance fn*sin-i-ftc-2-lemma
                                      (i (lambda ()
                                           (if (natp i) i 0)))
                                      (k (lambda ()
                                           (if (natp k) k 0)))
                                      (c (lambda ()
                                           (if (and (realp c)
                                                    (not (equal c 0)))
                                               c
                                             1))))))))

(local (in-theory (disable int-fn*sin-i-prime)))

(local
 (defthm int-fn*sin-i-prime-thm
   (implies (and (natp i)
                 (natp k)
                 (realp c)
                 (not (equal c 0))
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-fn*sin-i-prime a b i k c)
                   (+ (* (r i)
                         (int-sin-cos-orthog-prime a b k i c))
                      (* (s i)
                         (int-sin-orthog-prime a b k i c)))))
   :hints (("Goal"
            :use ((:instance sin-orthog-m!=n-ftc-2
                             (m k)
                             (n i))
                  (:instance sin-cos-orthog-m!=n-ftc-2
                             (m k)
                             (n i)))
            :in-theory (enable fn*sin-i sin-orthog sin-cos-orthog)))))

;; ======================================================================

;; Define sum-fn*sin-i-prime.

(local
 (defun sum-fn*sin-i-prime (x i k c)
   (if (zp i)
       (fn*sin-i-prime x 0 k c)
     (+ (fn*sin-i-prime x i k c)
        (sum-fn*sin-i-prime x (1- i) k c)))))

(local
 (defthm realp-sum-fn*sin-i-prime
   (realp (sum-fn*sin-i-prime x i k c))
   :rule-classes :type-prescription))

(local
 (defthm sum-fn*sin-i-prime-continuous
   (implies (and (standardp i)
                 (standardp k)
                 (standardp c)
                 (standardp x)
                 (inside-interval-p x (fn-domain))
                 (inside-interval-p y (fn-domain))
                 (i-close x y))
            (i-close (sum-fn*sin-i-prime x i k c)
                     (sum-fn*sin-i-prime y i k c)))))

;; ======================================================================

;; Define the Riemann integral of sum-fn*sin-i-prime.

(local
 (defun map-sum-fn*sin-i-prime (p i k c)
   (if (consp p)
       (cons (sum-fn*sin-i-prime (car p) i k c)
             (map-sum-fn*sin-i-prime (cdr p) i k c))
     nil)))

(local
 (defun riemann-sum-fn*sin-i-prime (p i k c)
   (dotprod (deltas p)
            (map-sum-fn*sin-i-prime (cdr p) i k c))))

(local
 (defthm limited-riemann-sum-fn*sin-i-prime-small-partition-lemma
   (implies (and (standardp arg)
                 (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-sum-fn*sin-i-prime
                        (make-small-partition a b)
                        (nth 0 arg)
                        (nth 1 arg)
                        (nth 2 arg))))
   :hints (("Goal"
            :by (:functional-instance
                 limited-riemann-rcfn-2-small-partition
                 (rcfn-2 (lambda (x arg)
                           (sum-fn*sin-i-prime x
                                           (nth 0 arg)
                                           (nth 1 arg)
                                           (nth 2 arg))))
                 (rcfn-2-domain fn-domain)
                 (map-rcfn-2
                  (lambda (p arg)
                    (map-sum-fn*sin-i-prime p
                                        (nth 0 arg)
                                        (nth 1 arg)
                                        (nth 2 arg))))
                 (riemann-rcfn-2
                  (lambda (p arg)
                    (riemann-sum-fn*sin-i-prime p
                                            (nth 0 arg)
                                            (nth 1 arg)
                                            (nth 2 arg)))))))))

(local
 (defthm limited-riemann-sum-fn*sin-i-prime-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (standardp i)
                 (standardp k)
                 (standardp c)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-sum-fn*sin-i-prime
                        (make-small-partition a b)
                        i k c)))
   :hints (("Goal"
            :use (:instance limited-riemann-sum-fn*sin-i-prime-small-partition-lemma
                            (arg (list i k c)))))))

(local
 (encapsulate
  ()

  (local (in-theory (disable riemann-sum-fn*sin-i-prime)))

  (defun-std strict-int-sum-fn*sin-i-prime (a b i k c)
    (if (and (realp a)
             (realp b)
             (inside-interval-p a (fn-domain))
             (inside-interval-p b (fn-domain))
             (< a b))
        (standard-part (riemann-sum-fn*sin-i-prime
                        (make-small-partition a b)
                        i k c))
      0))))

(local
 (defun int-sum-fn*sin-i-prime (a b i k c)
   (if (<= a b)
       (strict-int-sum-fn*sin-i-prime a b i k c)
     (- (strict-int-sum-fn*sin-i-prime b a i k c)))))

;; ======================================================================

;; Prove the sum rule of the integral of sum-fn*sin-i-prime.

(local
 (defun sum-int-fn*sin-i-prime (a b i k c)
   (if (zp i)
       (int-fn*sin-i-prime a b 0 k c)
     (+ (int-fn*sin-i-prime a b i k c)
        (sum-int-fn*sin-i-prime a b (1- i) k c)))))

(local
 (defthm sum-rule-of-int-sum-fn*sin-i-prime-lemma
   (implies (and (natp i)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-sum-fn*sin-i-prime a b i
                                           (k) (c))
                   (sum-int-fn*sin-i-prime a b i
                                           (k) (c))))
   :hints (("Goal"
            :in-theory (enable int-fn*sin-i-prime)
            :by (:functional-instance
                 sum-rule-of-int-sum-fi-prime
                 (low (lambda () 0))
                 (fi-prime
                  (lambda (x i)
                    (fn*sin-i-prime x i
                                    (k) (c))))
                 (fi-domain fn-domain)
                 (map-fi-prime
                  (lambda (p i)
                    (map-fn*sin-i-prime p i
                                        (k) (c))))
                 (riemann-fi-prime
                  (lambda (p i)
                    (riemann-fn*sin-i-prime p i
                                            (k) (c))))
                 (strict-int-fi-prime
                  (lambda (a b i)
                    (strict-int-fn*sin-i-prime a b i
                                               (k) (c))))
                 (int-fi-prime
                  (lambda (a b i)
                    (int-fn*sin-i-prime a b i
                                        (k) (c))))
                 (sum-fi-prime
                  (lambda (x i)
                    (sum-fn*sin-i-prime x i
                                        (k) (c))))
                 (map-sum-fi-prime
                  (lambda (p i)
                    (map-sum-fn*sin-i-prime p i
                                            (k) (c))))
                 (riemann-sum-fi-prime
                  (lambda (p i)
                    (riemann-sum-fn*sin-i-prime p i
                                                (k) (c))))
                 (strict-int-sum-fi-prime
                  (lambda (a b i)
                    (strict-int-sum-fn*sin-i-prime a b i
                                                   (k) (c))))
                 (int-sum-fi-prime
                  (lambda (a b i)
                    (int-sum-fn*sin-i-prime a b i
                                            (k) (c))))
                 (sum-int-fi-prime
                  (lambda (a b i)
                    (sum-int-fn*sin-i-prime a b i
                                            (k) (c)))))))))

(local
 (defthm sum-rule-of-int-sum-fn*sin-i-prime
   (implies (and (natp i)
                 (natp k)
                 (realp c)
                 (not (equal c 0))
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-sum-fn*sin-i-prime a b i
                                           k c)
                   (sum-int-fn*sin-i-prime a b i
                                           k c)))
   :hints (("Goal"
            :by (:functional-instance sum-rule-of-int-sum-fn*sin-i-prime-lemma
                                      (k (lambda ()
                                           (if (natp k)
                                               k
                                             0)))
                                      (c (lambda ()
                                           (if (and (realp c)
                                                    (not (equal c 0)))
                                               c
                                             1))))))))

(local (in-theory (disable int-sum-fn*sin-i-prime)))

;; Corollaries:

(local
 (defthm int-sum-fn*sin-i-prime-thm-1
   (implies (and (natp i)
                 (natp k)
                 (< i k)
                 (realp L)
                 (not (equal L 0)))
            (equal (* (/ L)
                      (int-sum-fn*sin-i-prime (- L) L
                                              i k (/ (acl2-pi) L)))
                   0))))

(local
 (defthm int-sum-fn*sin-i-prime-thm-2
   (implies (and (natp i)
                 (realp L)
                 (not (equal L 0)))
            (equal (* (/ L)
                      (int-sum-fn*sin-i-prime (- L) L
                                              i 0 (/ (acl2-pi) L)))
                   0))))

(local
 (defthm int-sum-fn*sin-i-prime-thm-3
   (implies (and (natp i)
                 (posp k)
                 (<= k i)
                 (realp L)
                 (not (equal L 0)))
            (equal (* (/ L)
                      (int-sum-fn*sin-i-prime (- L) L
                                              i k (/ (acl2-pi) L)))
                   (s k)))
   :hints (("Subgoal *1/4"
            :in-theory (disable int-sum-fn*sin-i-prime-thm-1)
            :use (:instance int-sum-fn*sin-i-prime-thm-1
                            (i (1- i))
                            (k i))))))

(local (in-theory (disable sum-rule-of-int-sum-fn*sin-i-prime)))

;; ======================================================================

;; Formalize the Fourier coefficients r_k.

(defun fourier-series-2*fixed-cos (x i k c)
  (* (fourier-series-2 x i c)
     (fixed-cos x k c)))

(defthm realp-fourier-series-2*fixed-cos
  (realp (fourier-series-2*fixed-cos x i k c))
  :rule-classes :type-prescription)

(local
 (defthm fourier-series-2*fixed-cos-rewrite
   (equal (fourier-series-2*fixed-cos x i k c)
          (sum-fn*cos-i-prime x i k c))
   :hints (("Goal" :in-theory (enable fn*cos-i-prime
                                      cos-orthog-prime
                                      sin-cos-orthog-prime)))))

(in-theory (disable fourier-series-2*fixed-cos))

(defun map-fourier-series-2*fixed-cos (p i k c)
  (if (consp p)
      (cons (fourier-series-2*fixed-cos (car p) i k c)
	    (map-fourier-series-2*fixed-cos (cdr p) i k c))
    nil))

(local
 (defthm map-fourier-series-2*fixed-cos-rewrite
   (equal (map-fourier-series-2*fixed-cos p i k c)
          (map-sum-fn*cos-i-prime p i k c))))

(defun riemann-fourier-series-2*fixed-cos (p i k c)
  (dotprod (deltas p)
	   (map-fourier-series-2*fixed-cos (cdr p) i k c)))

(local
 (defthm riemann-fourier-series-2*fixed-cos-rewrite
   (equal (riemann-fourier-series-2*fixed-cos p i k c)
          (riemann-sum-fn*cos-i-prime p i k c))))

(in-theory (disable riemann-fourier-series-2*fixed-cos))

(local (in-theory (disable riemann-sum-fn*cos-i-prime)))

(defun-std strict-fourier-series-2*fixed-cos (a b i k c)
  (if (and (realp a)
           (realp b)
           (inside-interval-p a (fn-domain))
           (inside-interval-p b (fn-domain))
           (< a b))
      (standard-part (riemann-fourier-series-2*fixed-cos
                      (make-small-partition a b)
                      i k c))
    0))

(defun int-fourier-series-2*fixed-cos (a b i k c)
  (if (<= a b)
      (strict-fourier-series-2*fixed-cos a b i k c)
    (- (strict-fourier-series-2*fixed-cos b a i k c))))

(local
 (defthm-std int-fourier-series-2*fixed-cos-rewrite
   (equal (int-fourier-series-2*fixed-cos a b i k c)
          (int-sum-fn*cos-i-prime a b i k c))
   :hints (("Goal" :in-theory (enable int-sum-fn*cos-i-prime)))))

(in-theory (disable int-fourier-series-2*fixed-cos))

(defthm int-fourier-series-2*fixed-cos-thm-1
  (implies (and (natp i)
                (natp k)
                (< i k)
                (realp L)
                (not (equal L 0)))
           (equal (* (/ L)
                     (int-fourier-series-2*fixed-cos
                      (- L) L
                      i k (/ (acl2-pi) L)))
                  0)))

(defthm int-fourier-series-2*fixed-cos-thm-2
  (implies (and (natp i)
                (realp L)
                (not (equal L 0)))
           (equal (* 1/2 (/ L)
                     (int-fourier-series-2*fixed-cos
                      (- L) L
                      i 0 (/ (acl2-pi) L)))
                  (r 0))))

(defthm int-fourier-series-2*fixed-cos-thm-3
  (implies (and (natp i)
                (posp k)
                (<= k i)
                (realp L)
                (not (equal L 0)))
           (equal (* (/ L)
                     (int-fourier-series-2*fixed-cos
                      (- L) L
                      i k (/ (acl2-pi) L)))
                  (r k))))

;; ======================================================================

;; Formalize the Fourier coefficients s_k.

(defun fourier-series-2*fixed-sin (x i k c)
  (* (fourier-series-2 x i c)
     (fixed-sin x k c)))

(defthm realp-fourier-series-2*fixed-sin
  (realp (fourier-series-2*fixed-sin x i k c))
  :rule-classes :type-prescription)

(local
 (defthm fourier-series-2*fixed-sin-rewrite
   (equal (fourier-series-2*fixed-sin x i k c)
          (sum-fn*sin-i-prime x i k c))
   :hints (("Goal" :in-theory (enable fn*sin-i-prime
                                      sin-orthog-prime
                                      sin-cos-orthog-prime)))))

(in-theory (disable fourier-series-2 fourier-series-2*fixed-sin))

(defun map-fourier-series-2*fixed-sin (p i k c)
  (if (consp p)
      (cons (fourier-series-2*fixed-sin (car p) i k c)
	    (map-fourier-series-2*fixed-sin (cdr p) i k c))
    nil))

(local
 (defthm map-fourier-series-2*fixed-sin-rewrite
   (equal (map-fourier-series-2*fixed-sin p i k c)
          (map-sum-fn*sin-i-prime p i k c))))

(defun riemann-fourier-series-2*fixed-sin (p i k c)
  (dotprod (deltas p)
	   (map-fourier-series-2*fixed-sin (cdr p) i k c)))

(local
 (defthm riemann-fourier-series-2*fixed-sin-rewrite
   (equal (riemann-fourier-series-2*fixed-sin p i k c)
          (riemann-sum-fn*sin-i-prime p i k c))))

(in-theory (disable riemann-fourier-series-2*fixed-sin))

(local (in-theory (disable riemann-sum-fn*sin-i-prime)))

(defun-std strict-fourier-series-2*fixed-sin (a b i k c)
  (if (and (realp a)
           (realp b)
           (inside-interval-p a (fn-domain))
           (inside-interval-p b (fn-domain))
           (< a b))
      (standard-part (riemann-fourier-series-2*fixed-sin
                      (make-small-partition a b)
                      i k c))
    0))

(defun int-fourier-series-2*fixed-sin (a b i k c)
  (if (<= a b)
      (strict-fourier-series-2*fixed-sin a b i k c)
    (- (strict-fourier-series-2*fixed-sin b a i k c))))

(local
 (defthm-std int-fourier-series-2*fixed-sin-rewrite
   (equal (int-fourier-series-2*fixed-sin a b i k c)
          (int-sum-fn*sin-i-prime a b i k c))
   :hints (("Goal" :in-theory (enable int-sum-fn*sin-i-prime)))))

(in-theory (disable int-fourier-series-2*fixed-sin))

(defthm int-fourier-series-2*fixed-sin-thm-1
  (implies (and (natp i)
                (natp k)
                (< i k)
                (realp L)
                (not (equal L 0)))
           (equal (* (/ L)
                     (int-fourier-series-2*fixed-sin
                      (- L) L
                      i k (/ (acl2-pi) L)))
                  0)))

(defthm int-fourier-series-2*fixed-sin-thm-2
  (implies (and (natp i)
                (realp L)
                (not (equal L 0)))
           (equal (* (/ L)
                     (int-fourier-series-2*fixed-sin
                      (- L) L
                      i 0 (/ (acl2-pi) L)))
                  0)))

(defthm int-fourier-series-2*fixed-sin-thm-3
  (implies (and (natp i)
                (posp k)
                (<= k i)
                (realp L)
                (not (equal L 0)))
           (equal (* (/ L)
                     (int-fourier-series-2*fixed-sin
                      (- L) L
                      i k (/ (acl2-pi) L)))
                  (s k))))


