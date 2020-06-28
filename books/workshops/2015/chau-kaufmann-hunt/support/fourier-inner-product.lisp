;; Proof of the inner product of two Fourier series.

;; Cuong Chau                             August, 2015

(in-package "ACL2")

(include-book "riemann-integral/continuous-function-2")
(include-book "utils")

(local (include-book "int-sum"))
(local (include-book "sines-orthog"))
(local (include-book "cosines-orthog"))
(local (include-book "sine-cosine-orthog"))
(local
 (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal" :dir :system))
(local (include-book "nonstd/integrals/ftc-2" :dir :system))

;; ======================================================================

;; Define Fourier coefficients a_i, b_i, r_i, and s_i as encapsulated
;; functions.

(encapsulate
 ((a (i) t)
  (b (i) t)
  (r (i) t)
  (s (i) t))

 (local (defun a (i) (declare (ignore i)) 0))
 (local (defun b (i) (declare (ignore i)) 0))
 (local (defun r (i) (declare (ignore i)) 0))
 (local (defun s (i) (declare (ignore i)) 0))

 (defthm realp-a
   (realp (a i))
   :rule-classes :type-prescription)

 (defthm realp-b
   (realp (b i))
   :rule-classes :type-prescription)

 (defthm realp-r
   (realp (r i))
   :rule-classes :type-prescription)

 (defthm realp-s
   (realp (s i))
   :rule-classes :type-prescription))

(defthm-std standardp-a
  (implies (standardp i)
           (standardp (a i)))
  :rule-classes :type-prescription)

(defthm-std standardp-b
  (implies (standardp i)
           (standardp (b i)))
  :rule-classes :type-prescription)

(defthm-std standardp-r
  (implies (standardp i)
           (standardp (r i)))
  :rule-classes :type-prescription)

(defthm-std standardp-s
  (implies (standardp i)
           (standardp (s i)))
  :rule-classes :type-prescription)

;; Define prod-fn-i*k and prod-fn-i*k-prime.

(local
 (defun prod-fn-i*k (x i k c)
   (+ (* (a i) (r k)
         (cos-orthog x i k c))
      (* (a i) (s k)
         (sin-cos-orthog x k i c)) ;; Note the order of i & k.
      (* (b i) (r k)
         (sin-cos-orthog x i k c))
      (* (b i) (s k)
         (sin-orthog x i k c)))))

(local
 (defun prod-fn-i*k-prime (x i k c)
   (+ (* (a i) (r k)
         (cos-orthog-prime x i k c))
      (* (a i) (s k)
         (sin-cos-orthog-prime x k i c)) ;; Note the order of i & k.
      (* (b i) (r k)
         (sin-cos-orthog-prime x i k c))
      (* (b i) (s k)
         (sin-orthog-prime x i k c)))))

(defun fn-domain ()
  (interval nil nil))

(local
 (defthm realp-prod-fn-i*k
   (realp (prod-fn-i*k x i k c))
   :rule-classes :type-prescription))

(local
 (defthm realp-prod-fn-i*k-prime
   (realp (prod-fn-i*k-prime x i k c))
   :rule-classes :type-prescription))

(local
 (defthm prod-fn-i*k-prime-continuous
   (implies (and (standardp i)
                 (standardp k)
                 (standardp c)
                 (standardp x)
                 (inside-interval-p x (fn-domain))
                 (inside-interval-p y (fn-domain))
                 (i-close x y))
            (i-close (prod-fn-i*k-prime x i k c)
                     (prod-fn-i*k-prime y i k c)))
   :hints (("Goal"
            :use ((:instance i-limited-times
                             (x (a i))
                             (y (r k)))
                  (:instance i-limited-times
                             (x (a i))
                             (y (s k)))
                  (:instance i-limited-times
                             (x (b i))
                             (y (r k)))
                  (:instance i-limited-times
                             (x (b i))
                             (y (s k)))
                  (:instance i-close-times
                             (x (* (a i) (r k)))
                             (y1 (cos-orthog-prime x i k c))
                             (y2 (cos-orthog-prime y i k c)))
                  (:instance i-close-times
                             (x (* (a i) (s k)))
                             (y1 (sin-cos-orthog-prime x k i c))
                             (y2 (sin-cos-orthog-prime y k i c)))
                  (:instance i-close-times
                             (x (* (b i) (r k)))
                             (y1 (sin-cos-orthog-prime x i k c))
                             (y2 (sin-cos-orthog-prime y i k c)))
                  (:instance i-close-times
                             (x (* (b i) (s k)))
                             (y1 (sin-orthog-prime x i k c))
                             (y2 (sin-orthog-prime y i k c))))))))

(local
 (defthm prod-fn-i*k-derivative
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
            (i-close (/ (- (prod-fn-i*k x i k c)
                           (prod-fn-i*k x1 i k c))
                        (- x x1))
                     (prod-fn-i*k-prime x i k c)))
   :hints (("Goal"
            :in-theory (disable <-*-LEFT-CANCEL
                                SQUARES-CLOSE
                                <-+-NEGATIVE-0-2
                                NON-STANDARD-BETWEEN-STANDARDS
                                NON-STANDARD-BETWEEN-STANDARDS-2
                                *-PRESERVES->=-FOR-NONNEGATIVES
                                |x < y  =>  0 < y-x|
                                i-close-plus
                                i-close-times
                                i-limited-times
                                cos-orthog-derivative
                                sin-orthog-derivative
                                sin-cos-orthog-derivative)
            :use ((:instance i-limited-times
                             (x (a i))
                             (y (r k)))
                  (:instance i-limited-times
                             (x (a i))
                             (y (s k)))
                  (:instance i-limited-times
                             (x (b i))
                             (y (r k)))
                  (:instance i-limited-times
                             (x (b i))
                             (y (s k)))
                  (:instance i-close-times
                             (x (* (a i) (r k)))
                             (y1 (/ (- (cos-orthog x i k c)
                                       (cos-orthog x1 i k c))
                                    (- x x1)))
                             (y2 (cos-orthog-prime x i k c)))
                  (:instance i-close-times
                             (x (* (a i) (s k)))
                             (y1 (/ (- (sin-cos-orthog x k i c)
                                       (sin-cos-orthog x1 k i c))
                                    (- x x1)))
                             (y2 (sin-cos-orthog-prime x k i c)))
                  (:instance i-close-times
                             (x (* (b i) (r k)))
                             (y1 (/ (- (sin-cos-orthog x i k c)
                                       (sin-cos-orthog x1 i k c))
                                    (- x x1)))
                             (y2 (sin-cos-orthog-prime x i k c)))
                  (:instance i-close-times
                             (x (* (b i) (s k)))
                             (y1 (/ (- (sin-orthog x i k c)
                                       (sin-orthog x1 i k c))
                                    (- x x1)))
                             (y2 (sin-orthog-prime x i k c)))
                  (:instance i-close-plus
                             (x1 (* (* (a i) (r k))
                                    (/ (- (cos-orthog x i k c)
                                          (cos-orthog x1 i k c))
                                       (- x x1))))
                             (x2 (* (* (a i) (r k))
                                    (cos-orthog-prime x i k c)))
                             (y1 (* (* (a i) (s k))
                                    (/ (- (sin-cos-orthog x k i c)
                                          (sin-cos-orthog x1 k i c))
                                       (- x x1))))
                             (y2 (* (* (a i) (s k))
                                    (sin-cos-orthog-prime x k i c))))
                  (:instance i-close-plus
                             (x1 (* (* (b i) (r k))
                                    (/ (- (sin-cos-orthog x i k c)
                                          (sin-cos-orthog x1 i k c))
                                       (- x x1))))
                             (x2 (* (* (b i) (r k))
                                    (sin-cos-orthog-prime x i k c)))
                             (y1 (* (* (b i) (s k))
                                    (/ (- (sin-orthog x i k c)
                                          (sin-orthog x1 i k c))
                                       (- x x1))))
                             (y2 (* (* (b i) (s k))
                                    (sin-orthog-prime x i k c))))
                  (:instance i-close-plus
                             (x1 (+ (* (* (a i) (r k))
                                       (/ (- (cos-orthog x i k c)
                                             (cos-orthog x1 i k c))
                                          (- x x1)))
                                    (* (* (a i) (s k))
                                       (/ (- (sin-cos-orthog x k i c)
                                             (sin-cos-orthog x1 k i c))
                                          (- x x1)))))
                             (x2 (+ (* (* (a i) (r k))
                                       (cos-orthog-prime x i k c))
                                    (* (* (a i) (s k))
                                       (sin-cos-orthog-prime x k i c))))
                             (y1 (+ (* (* (b i) (r k))
                                       (/ (- (sin-cos-orthog x i k c)
                                             (sin-cos-orthog x1 i k c))
                                          (- x x1)))
                                    (* (* (b i) (s k))
                                       (/ (- (sin-orthog x i k c)
                                             (sin-orthog x1 i k c))
                                          (- x x1)))))
                             (y2 (+ (* (* (b i) (r k))
                                       (sin-cos-orthog-prime x i k c))
                                    (* (* (b i) (s k))
                                       (sin-orthog-prime x i k c)))))
                  (:instance cos-orthog-derivative
                             (m i)
                             (n k))
                  (:instance sin-orthog-derivative
                             (m i)
                             (n k))
                  (:instance sin-cos-orthog-derivative
                             (m k)
                             (n i))
                  (:instance sin-cos-orthog-derivative
                             (m i)
                             (n k)))))))

(local (in-theory (disable prod-fn-i*k prod-fn-i*k-prime)))

;; ======================================================================

;; Define the Riemann integral of prod-fn-i*k-prime.

(local
 (defun map-prod-fn-i*k-prime (p i k c)
   (if (consp p)
       (cons (prod-fn-i*k-prime (car p) i k c)
             (map-prod-fn-i*k-prime (cdr p) i k c))
     nil)))

(local
 (defun riemann-prod-fn-i*k-prime (p i k c)
   (dotprod (deltas p)
            (map-prod-fn-i*k-prime (cdr p) i k c))))

(local
 (defthm limited-riemann-prod-fn-i*k-prime-small-partition-lemma
   (implies (and (standardp arg)
                 (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-prod-fn-i*k-prime
                        (make-small-partition a b)
                        (nth 0 arg)
                        (nth 1 arg)
                        (nth 2 arg))))
   :hints (("Goal"
            :by (:functional-instance
                 limited-riemann-rcfn-2-small-partition
                 (rcfn-2 (lambda (x arg)
                           (prod-fn-i*k-prime x
                                       (nth 0 arg)
                                       (nth 1 arg)
                                       (nth 2 arg))))
                 (rcfn-2-domain fn-domain)
                 (map-rcfn-2
                  (lambda (p arg)
                    (map-prod-fn-i*k-prime p
                                    (nth 0 arg)
                                    (nth 1 arg)
                                    (nth 2 arg))))
                 (riemann-rcfn-2
                  (lambda (p arg)
                    (riemann-prod-fn-i*k-prime p
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
 (defthm limited-riemann-prod-fn-i*k-prime-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (standardp i)
                 (standardp k)
                 (standardp c)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-prod-fn-i*k-prime
                        (make-small-partition a b)
                        i k c)))
   :hints (("Goal"
            :use (:instance limited-riemann-prod-fn-i*k-prime-small-partition-lemma
                            (arg (list i k c)))))))

(local
 (encapsulate
  ()

  (local (in-theory (disable riemann-prod-fn-i*k-prime)))

  (defun-std strict-int-prod-fn-i*k-prime (a b i k c)
    (if (and (realp a)
             (realp b)
             (inside-interval-p a (fn-domain))
             (inside-interval-p b (fn-domain))
             (< a b))
        (standard-part (riemann-prod-fn-i*k-prime
                        (make-small-partition a b)
                        i k c))
      0))))

(local
 (defun int-prod-fn-i*k-prime (a b i k c)
   (if (<= a b)
       (strict-int-prod-fn-i*k-prime a b i k c)
     (- (strict-int-prod-fn-i*k-prime b a i k c)))))

;; ======================================================================

;; Prove the ftc-2 that connects prod-fn-i*k-prime with prod-fn-i*k.

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
 (defthm prod-fn-i*k-ftc-2-lemma
   (implies (and (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-prod-fn-i*k-prime a b (i) (k) (c))
                   (- (prod-fn-i*k b (i) (k) (c))
                      (prod-fn-i*k a (i) (k) (c)))))
   :hints (("Goal"
            :by (:functional-instance
                 ftc-2
                 (rcdfn
                  (lambda (x)
                    (prod-fn-i*k x (i)
                          (k) (c))))
                 (rcdfn-prime
                  (lambda (x)
                    (prod-fn-i*k-prime x (i)
                                (k) (c))))
                 (rcdfn-domain fn-domain)
                 (map-rcdfn-prime
                  (lambda (p)
                    (map-prod-fn-i*k-prime p (i)
                                    (k) (c))))
                 (riemann-rcdfn-prime
                  (lambda (p)
                    (riemann-prod-fn-i*k-prime p (i)
                                        (k) (c))))
                 (strict-int-rcdfn-prime
                  (lambda (a b)
                    (strict-int-prod-fn-i*k-prime a b (i)
                                           (k) (c))))
                 (int-rcdfn-prime
                  (lambda (a b)
                    (int-prod-fn-i*k-prime a b (i)
                                    (k) (c))))))
           ("Subgoal 6"
            :use (:instance prod-fn-i*k-derivative
                            (i (i))
                            (k (k))
                            (c (c)))))))

(local
 (defthm prod-fn-i*k-ftc-2
   (implies (and (natp i)
                 (natp k)
                 (realp c)
                 (not (equal c 0))
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-prod-fn-i*k-prime a b i k c)
                   (- (prod-fn-i*k b i k c)
                      (prod-fn-i*k a i k c))))
   :hints (("Goal"
            :by (:functional-instance prod-fn-i*k-ftc-2-lemma
                                      (i (lambda ()
                                           (if (natp i) i 0)))
                                      (k (lambda ()
                                           (if (natp k) k 0)))
                                      (c (lambda ()
                                           (if (and (realp c)
                                                    (not (equal c 0)))
                                               c
                                             1))))))))

(local (in-theory (disable int-prod-fn-i*k-prime)))

(local
 (defthm int-prod-fn-i*k-prime-thm
   (implies (and (natp i)
                 (natp k)
                 (realp c)
                 (not (equal c 0))
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-prod-fn-i*k-prime a b i k c)
                   (+ (* (a i) (r k)
                         (int-cos-orthog-prime a b i k c))
                      (* (a i) (s k)
                         (int-sin-cos-orthog-prime a b k i c))
                      (* (b i) (r k)
                         (int-sin-cos-orthog-prime a b i k c))
                      (* (b i) (s k)
                         (int-sin-orthog-prime a b i k c)))))
   :hints (("Goal"
            :use ((:instance cos-orthog-m!=n-ftc-2
                             (m i)
                             (n k))
                  (:instance sin-orthog-m!=n-ftc-2
                             (m i)
                             (n k))
                  (:instance sin-cos-orthog-m!=n-ftc-2
                             (m k)
                             (n i))
                  (:instance sin-cos-orthog-m!=n-ftc-2
                             (m i)
                             (n k)))
            :in-theory (enable prod-fn-i*k
                               cos-orthog sin-orthog
                               sin-cos-orthog)))))

;; ======================================================================

;; Define sum-prod-fn-i*k-prime-fix-i.

(local
 (defun sum-prod-fn-i*k-prime-fix-i (x i k c)
   (if (zp k)
       (prod-fn-i*k-prime x i 0 c)
     (+ (prod-fn-i*k-prime x i k c)
        (sum-prod-fn-i*k-prime-fix-i x i (1- k) c)))))

(local
 (defthm realp-sum-prod-fn-i*k-prime-fix-i
   (realp (sum-prod-fn-i*k-prime-fix-i x i k c))
   :rule-classes :type-prescription))

(local
 (defthm sum-prod-fn-i*k-prime-fix-i-continuous
   (implies (and (standardp i)
                 (standardp k)
                 (standardp c)
                 (standardp x)
                 (inside-interval-p x (fn-domain))
                 (inside-interval-p y (fn-domain))
                 (i-close x y))
            (i-close (sum-prod-fn-i*k-prime-fix-i x i k c)
                     (sum-prod-fn-i*k-prime-fix-i y i k c)))))

;; ======================================================================

;; Define the Riemann integral of sum-prod-fn-i*k-prime.

(local
 (defun map-sum-prod-fn-i*k-prime-fix-i (p i k c)
   (if (consp p)
       (cons (sum-prod-fn-i*k-prime-fix-i (car p) i k c)
             (map-sum-prod-fn-i*k-prime-fix-i (cdr p) i k c))
     nil)))

(local
 (defun riemann-sum-prod-fn-i*k-prime-fix-i (p i k c)
   (dotprod (deltas p)
            (map-sum-prod-fn-i*k-prime-fix-i (cdr p) i k c))))

(local
 (defthm limited-riemann-sum-prod-fn-i*k-prime-fix-i-small-partition-lemma
   (implies (and (standardp arg)
                 (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-sum-prod-fn-i*k-prime-fix-i
                        (make-small-partition a b)
                        (nth 0 arg)
                        (nth 1 arg)
                        (nth 2 arg))))
   :hints (("Goal"
            :by (:functional-instance
                 limited-riemann-rcfn-2-small-partition
                 (rcfn-2 (lambda (x arg)
                           (sum-prod-fn-i*k-prime-fix-i
                            x
                            (nth 0 arg)
                            (nth 1 arg)
                            (nth 2 arg))))
                 (rcfn-2-domain fn-domain)
                 (map-rcfn-2
                  (lambda (p arg)
                    (map-sum-prod-fn-i*k-prime-fix-i
                     p
                     (nth 0 arg)
                     (nth 1 arg)
                     (nth 2 arg))))
                 (riemann-rcfn-2
                  (lambda (p arg)
                    (riemann-sum-prod-fn-i*k-prime-fix-i
                     p
                     (nth 0 arg)
                     (nth 1 arg)
                     (nth 2 arg)))))))))

(local
 (defthm limited-riemann-sum-prod-fn-i*k-prime-fix-i-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (standardp i)
                 (standardp k)
                 (standardp c)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-sum-prod-fn-i*k-prime-fix-i
                        (make-small-partition a b)
                        i k c)))
   :hints (("Goal"
            :use (:instance limited-riemann-sum-prod-fn-i*k-prime-fix-i-small-partition-lemma
                            (arg (list i k c)))))))

(local
 (encapsulate
  ()

  (local (in-theory (disable riemann-sum-prod-fn-i*k-prime-fix-i)))

  (defun-std strict-int-sum-prod-fn-i*k-prime-fix-i (a b i k c)
    (if (and (realp a)
             (realp b)
             (inside-interval-p a (fn-domain))
             (inside-interval-p b (fn-domain))
             (< a b))
        (standard-part (riemann-sum-prod-fn-i*k-prime-fix-i
                        (make-small-partition a b)
                        i k c))
      0))))

(local
 (defun int-sum-prod-fn-i*k-prime-fix-i (a b i k c)
   (if (<= a b)
       (strict-int-sum-prod-fn-i*k-prime-fix-i a b i k c)
     (- (strict-int-sum-prod-fn-i*k-prime-fix-i b a i k c)))))

;; ======================================================================

;; Prove the sum rule of the integral of sum-prod-fn-i*k-prime-fix-i.

(local
 (defun sum-int-prod-fn-i*k-prime-fix-i (a b i k c)
   (if (zp k)
       (int-prod-fn-i*k-prime a b i 0 c)
     (+ (int-prod-fn-i*k-prime a b i k c)
        (sum-int-prod-fn-i*k-prime-fix-i a b i (1- k) c)))))

(local
 (defthm sum-rule-of-int-sum-prod-fn-i*k-prime-fix-i-lemma
   (implies (and (natp k)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-sum-prod-fn-i*k-prime-fix-i a b (i)
                                                    k (c))
                   (sum-int-prod-fn-i*k-prime-fix-i a b (i)
                                                    k (c))))
   :hints (("Goal"
            :in-theory (enable int-prod-fn-i*k-prime)
            :by (:functional-instance
                 sum-rule-of-int-sum-fi-prime
                 (low (lambda () 0))
                 (fi-prime
                  (lambda (x k)
                    (prod-fn-i*k-prime x (i)
                                       k (c))))
                 (fi-domain fn-domain)
                 (map-fi-prime
                  (lambda (p k)
                    (map-prod-fn-i*k-prime p (i)
                                           k (c))))
                 (riemann-fi-prime
                  (lambda (p k)
                    (riemann-prod-fn-i*k-prime p (i)
                                               k (c))))
                 (strict-int-fi-prime
                  (lambda (a b k)
                    (strict-int-prod-fn-i*k-prime a b (i)
                                                  k (c))))
                 (int-fi-prime
                  (lambda (a b k)
                    (int-prod-fn-i*k-prime a b (i)
                                           k (c))))
                 (sum-fi-prime
                  (lambda (x k)
                    (sum-prod-fn-i*k-prime-fix-i x (i)
                                                 k (c))))
                 (map-sum-fi-prime
                  (lambda (p k)
                    (map-sum-prod-fn-i*k-prime-fix-i p (i)
                                                     k (c))))
                 (riemann-sum-fi-prime
                  (lambda (p k)
                    (riemann-sum-prod-fn-i*k-prime-fix-i p (i)
                                                         k (c))))
                 (strict-int-sum-fi-prime
                  (lambda (a b k)
                    (strict-int-sum-prod-fn-i*k-prime-fix-i a b (i)
                                                            k (c))))
                 (int-sum-fi-prime
                  (lambda (a b k)
                    (int-sum-prod-fn-i*k-prime-fix-i a b (i)
                                                     k (c))))
                 (sum-int-fi-prime
                  (lambda (a b k)
                    (sum-int-prod-fn-i*k-prime-fix-i a b (i)
                                                     k (c)))))))))

(local
 (defthm sum-rule-of-int-sum-prod-fn-i*k-prime-fix-i
   (implies (and (natp i)
                 (natp k)
                 (realp c)
                 (not (equal c 0))
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-sum-prod-fn-i*k-prime-fix-i a b i
                                                    k c)
                   (sum-int-prod-fn-i*k-prime-fix-i a b i
                                                    k c)))
   :hints (("Goal"
            :by (:functional-instance sum-rule-of-int-sum-prod-fn-i*k-prime-fix-i-lemma
                                      (i (lambda ()
                                           (if (natp i)
                                               i
                                             0)))
                                      (c (lambda ()
                                           (if (and (realp c)
                                                    (not (equal c 0)))
                                               c
                                             1))))))))

(local (in-theory (disable int-sum-prod-fn-i*k-prime-fix-i)))

;; Corollaries:

(local
 (defthm int-sum-prod-fn-i*k-prime-fix-i-thm-1
   (implies (and (natp i)
                 (natp k)
                 (< k i)
                 (realp L)
                 (not (equal L 0)))
            (equal (int-sum-prod-fn-i*k-prime-fix-i (- L) L
                                                    i k (/ (acl2-pi) L))
                   0))))

(local
 (defthm int-sum-prod-fn-i*k-prime-fix-i-thm-2
   (implies (and (natp k)
                 (realp L)
                 (not (equal L 0)))
            (equal (int-sum-prod-fn-i*k-prime-fix-i
                    (- L) L
                    0 k (/ (acl2-pi) L))
                   (* 2 (a 0) (r 0) L)))))

(local
 (defthm int-sum-prod-fn-i*k-prime-fix-i-thm-3
   (implies (and (posp i)
                 (natp k)
                 (<= i k)
                 (realp L)
                 (not (equal L 0)))
            (equal (int-sum-prod-fn-i*k-prime-fix-i
                    (- L) L
                    i k (/ (acl2-pi) L))
                   (+ (* (a i) (r i) L)
                      (* (b i) (s i) L))))
   :hints (("Subgoal *1/4"
            :in-theory (disable int-sum-prod-fn-i*k-prime-fix-i-thm-1)
            :use (:instance int-sum-prod-fn-i*k-prime-fix-i-thm-1
                            (k (1- i)))))))

(local (in-theory (disable sum-rule-of-int-sum-prod-fn-i*k-prime-fix-i)))

;; ======================================================================

;; Define sum-prod-fn-i*k-prime.

(local
 (defun sum-prod-fn-i*k-prime (x i k c)
   (if (zp i)
       (sum-prod-fn-i*k-prime-fix-i x 0 k c)
     (+ (sum-prod-fn-i*k-prime-fix-i x i k c)
        (sum-prod-fn-i*k-prime x (1- i) k c)))))

(local
 (defthm realp-sum-prod-fn-i*k-prime
   (realp (sum-prod-fn-i*k-prime x i k c))
   :rule-classes :type-prescription))

(local
 (defthm sum-prod-fn-i*k-prime-continuous
   (implies (and (standardp i)
                 (standardp k)
                 (standardp c)
                 (standardp x)
                 (inside-interval-p x (fn-domain))
                 (inside-interval-p y (fn-domain))
                 (i-close x y))
            (i-close (sum-prod-fn-i*k-prime x i k c)
                     (sum-prod-fn-i*k-prime y i k c)))))

;; ======================================================================

;; Define the Riemann integral of sum-prod-fn-i*k-prime.

(local
 (defun map-sum-prod-fn-i*k-prime (p i k c)
   (if (consp p)
       (cons (sum-prod-fn-i*k-prime (car p) i k c)
             (map-sum-prod-fn-i*k-prime (cdr p) i k c))
     nil)))

(local
 (defun riemann-sum-prod-fn-i*k-prime (p i k c)
   (dotprod (deltas p)
            (map-sum-prod-fn-i*k-prime (cdr p) i k c))))

(local
 (defthm limited-riemann-sum-prod-fn-i*k-prime-small-partition-lemma
   (implies (and (standardp arg)
                 (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-sum-prod-fn-i*k-prime
                        (make-small-partition a b)
                        (nth 0 arg)
                        (nth 1 arg)
                        (nth 2 arg))))
   :hints (("Goal"
            :by (:functional-instance
                 limited-riemann-rcfn-2-small-partition
                 (rcfn-2 (lambda (x arg)
                           (sum-prod-fn-i*k-prime
                            x
                            (nth 0 arg)
                            (nth 1 arg)
                            (nth 2 arg))))
                 (rcfn-2-domain fn-domain)
                 (map-rcfn-2
                  (lambda (p arg)
                    (map-sum-prod-fn-i*k-prime
                     p
                     (nth 0 arg)
                     (nth 1 arg)
                     (nth 2 arg))))
                 (riemann-rcfn-2
                  (lambda (p arg)
                    (riemann-sum-prod-fn-i*k-prime
                     p
                     (nth 0 arg)
                     (nth 1 arg)
                     (nth 2 arg)))))))))

(local
 (defthm limited-riemann-sum-prod-fn-i*k-prime-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (standardp i)
                 (standardp k)
                 (standardp c)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain))
                 (< a b))
            (i-limited (riemann-sum-prod-fn-i*k-prime
                        (make-small-partition a b)
                        i k c)))
   :hints (("Goal"
            :use (:instance limited-riemann-sum-prod-fn-i*k-prime-small-partition-lemma
                            (arg (list i k c)))))))

(local
 (encapsulate
  ()

  (local (in-theory (disable riemann-sum-prod-fn-i*k-prime)))

  (defun-std strict-int-sum-prod-fn-i*k-prime (a b i k c)
    (if (and (realp a)
             (realp b)
             (inside-interval-p a (fn-domain))
             (inside-interval-p b (fn-domain))
             (< a b))
        (standard-part (riemann-sum-prod-fn-i*k-prime
                        (make-small-partition a b)
                        i k c))
      0))))

(local
 (defun int-sum-prod-fn-i*k-prime (a b i k c)
   (if (<= a b)
       (strict-int-sum-prod-fn-i*k-prime a b i k c)
     (- (strict-int-sum-prod-fn-i*k-prime b a i k c)))))

;; ======================================================================

;; Prove the sum rule of the integral of sum-prod-fn-i*k-prime.

(local
 (defun sum-int-prod-fn-i*k-prime (a b i k c)
   (if (zp i)
       (int-sum-prod-fn-i*k-prime-fix-i a b 0 k c)
     (+ (int-sum-prod-fn-i*k-prime-fix-i a b i k c)
        (sum-int-prod-fn-i*k-prime a b (1- i) k c)))))

(local
 (defthm sum-rule-of-int-sum-prod-fn-i*k-prime-lemma
   (implies (and (natp i)
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-sum-prod-fn-i*k-prime a b i
                                              (k) (c))
                   (sum-int-prod-fn-i*k-prime a b i
                                              (k) (c))))
   :hints (("Goal"
            :in-theory (enable int-sum-prod-fn-i*k-prime-fix-i)
            :by (:functional-instance
                 sum-rule-of-int-sum-fi-prime
                 (low (lambda () 0))
                 (fi-prime
                  (lambda (x i)
                    (sum-prod-fn-i*k-prime-fix-i x i
                                                 (k) (c))))
                 (fi-domain fn-domain)
                 (map-fi-prime
                  (lambda (p i)
                    (map-sum-prod-fn-i*k-prime-fix-i p i
                                                     (k) (c))))
                 (riemann-fi-prime
                  (lambda (p i)
                    (riemann-sum-prod-fn-i*k-prime-fix-i p i
                                                         (k) (c))))
                 (strict-int-fi-prime
                  (lambda (a b i)
                    (strict-int-sum-prod-fn-i*k-prime-fix-i a b i
                                                            (k) (c))))
                 (int-fi-prime
                  (lambda (a b i)
                    (int-sum-prod-fn-i*k-prime-fix-i a b i
                                                     (k) (c))))
                 (sum-fi-prime
                  (lambda (x i)
                    (sum-prod-fn-i*k-prime x i
                                           (k) (c))))
                 (map-sum-fi-prime
                  (lambda (p i)
                    (map-sum-prod-fn-i*k-prime p i
                                               (k) (c))))
                 (riemann-sum-fi-prime
                  (lambda (p i)
                    (riemann-sum-prod-fn-i*k-prime p i
                                                   (k) (c))))
                 (strict-int-sum-fi-prime
                  (lambda (a b i)
                    (strict-int-sum-prod-fn-i*k-prime a b i
                                                      (k) (c))))
                 (int-sum-fi-prime
                  (lambda (a b i)
                    (int-sum-prod-fn-i*k-prime a b i
                                               (k) (c))))
                 (sum-int-fi-prime
                  (lambda (a b i)
                    (sum-int-prod-fn-i*k-prime a b i
                                               (k) (c)))))))))

(local
 (defthm sum-rule-of-int-sum-prod-fn-i*k-prime
   (implies (and (natp i)
                 (natp k)
                 (realp c)
                 (not (equal c 0))
                 (inside-interval-p a (fn-domain))
                 (inside-interval-p b (fn-domain)))
            (equal (int-sum-prod-fn-i*k-prime a b i
                                              k c)
                   (sum-int-prod-fn-i*k-prime a b i
                                              k c)))
   :hints (("Goal"
            :by (:functional-instance sum-rule-of-int-sum-prod-fn-i*k-prime-lemma
                                      (k (lambda ()
                                           (if (natp k)
                                               k
                                             0)))
                                      (c (lambda ()
                                           (if (and (realp c)
                                                    (not (equal c 0)))
                                               c
                                             1))))))))

(local (in-theory (disable int-sum-prod-fn-i*k-prime)))

;; Corollaries:

(defun sum-coefficients (i)
  (if (zp i)
      (* 2 (a 0) (r 0))
    (+ (+ (* (a i) (r i))
          (* (b i) (s i)))
       (sum-coefficients (1- i)))))

(local
 (defthm int-sum-prod-fn-i*k-prime-lemma-1
   (implies (and (natp i)
                 (natp k)
                 (<= i k)
                 (realp L)
                 (not (equal L 0)))
            (equal (* (/ L)
                      (int-sum-prod-fn-i*k-prime (- L) L
                                                 i k (/ (acl2-pi) L)))
                   (sum-coefficients i)))
   :hints (("Subgoal *1/1"
; Matt K. mod after ACL2 8.3 for use of COMMENT with HIDE:
            :expand ((:free (v) (hide v)))))))

(local
 (defthm int-sum-prod-fn-i*k-prime-lemma-2
   (implies (and (natp i)
                 (natp k)
                 (< k i)
                 (realp L)
                 (not (equal L 0)))
            (equal (* (/ L)
                      (int-sum-prod-fn-i*k-prime (- L) L
                                                 i k (/ (acl2-pi) L)))
                   (sum-coefficients k)))
   :hints (("Subgoal *1/3"
            :in-theory (disable int-sum-prod-fn-i*k-prime-lemma-1)
            :use (:instance int-sum-prod-fn-i*k-prime-lemma-1
                            (i (1- i))
                            (k (1- i)))))))

(local (in-theory (disable sum-rule-of-int-sum-prod-fn-i*k-prime)))

(local
 (defthm int-sum-prod-fn-i*k-prime-thm
   (implies (and (natp i)
                 (natp k)
                 (realp L)
                 (not (equal L 0)))
            (equal (* (/ L)
                      (int-sum-prod-fn-i*k-prime (- L) L
                                                 i k (/ (acl2-pi) L)))
                   (sum-coefficients (min i k))))
   :hints (("Goal"
            :cases ((<= i k) (< k i))))))

;; ======================================================================

;; Formalize and prove the inner product of two Fourier series.

(defun fourier-series-1 (x i c)
  (if (zp i)
      (a 0)
    (+ (* (a i)
          (fixed-cos x i c))
       (* (b i)
          (fixed-sin x i c))
       (fourier-series-1 x (1- i) c))))

(defthm realp-fourier-series-1
  (realp (fourier-series-1 x i c))
  :rule-classes :type-prescription)

(defun fourier-series-2 (x i c)
  (if (zp i)
      (r 0)
    (+ (* (r i)
          (fixed-cos x i c))
       (* (s i)
          (fixed-sin x i c))
       (fourier-series-2 x (1- i) c))))

(defthm realp-fourier-series-2
  (realp (fourier-series-2 x i c))
  :rule-classes :type-prescription)

(defun prod-fourier-series (x i k c)
  (* (fourier-series-1 x i c)
     (fourier-series-2 x k c)))

(defthm realp-prod-fourier-series
  (realp (prod-fourier-series x i k c))
  :rule-classes :type-prescription)

(local
 (defthm prod-fourier-series-fix-i-rewrite
   (equal (* (+ (* (a i)
                   (fixed-cos x i c))
                (* (b i)
                   (fixed-sin x i c)))
             (fourier-series-2 x k c))
          (sum-prod-fn-i*k-prime-fix-i x i k c))
   :hints (("Goal" :in-theory (enable prod-fn-i*k-prime
                                      cos-orthog-prime
                                      sin-orthog-prime
                                      sin-cos-orthog-prime)))))

(local
 (defthm prod-fourier-series-i=0-rewrite
   (equal (* (a 0)
             (fourier-series-2 x k c))
          (sum-prod-fn-i*k-prime-fix-i x 0 k c))
   :hints (("Goal" :in-theory (enable prod-fn-i*k-prime
                                      cos-orthog-prime
                                      sin-orthog-prime
                                      sin-cos-orthog-prime)))))

(local
 (defthm prod-fourier-series-rewrite
   (equal (prod-fourier-series x i k c)
          (sum-prod-fn-i*k-prime x i k c))
   :hints (("Subgoal *1/2"
            :in-theory (disable prod-fourier-series-fix-i-rewrite)
            :use prod-fourier-series-fix-i-rewrite))))

(in-theory (disable prod-fourier-series))

(defun map-prod-fourier-series (p i k c)
  (if (consp p)
      (cons (prod-fourier-series (car p) i k c)
	    (map-prod-fourier-series (cdr p) i k c))
    nil))

(local
 (defthm map-prod-fourier-series-rewrite
   (equal (map-prod-fourier-series p i k c)
          (map-sum-prod-fn-i*k-prime p i k c))))

(defun riemann-prod-fourier-series (p i k c)
  (dotprod (deltas p)
	   (map-prod-fourier-series (cdr p) i k c)))

(local
 (defthm riemann-prod-fourier-series-rewrite
   (equal (riemann-prod-fourier-series p i k c)
          (riemann-sum-prod-fn-i*k-prime p i k c))))

(in-theory (disable riemann-prod-fourier-series))

(local (in-theory (disable riemann-sum-prod-fn-i*k-prime)))

(defun-std strict-prod-fourier-series (a b i k c)
  (if (and (realp a)
           (realp b)
           (inside-interval-p a (fn-domain))
           (inside-interval-p b (fn-domain))
           (< a b))
      (standard-part (riemann-prod-fourier-series
                      (make-small-partition a b)
                      i k c))
    0))

(defun int-prod-fourier-series (a b i k c)
  (if (<= a b)
      (strict-prod-fourier-series a b i k c)
    (- (strict-prod-fourier-series b a i k c))))

(local
 (defthm-std int-prod-fourier-series-rewrite
   (equal (int-prod-fourier-series a b i k c)
          (int-sum-prod-fn-i*k-prime a b i k c))
   :hints (("Goal" :in-theory (enable int-sum-prod-fn-i*k-prime)))))

(in-theory (disable int-prod-fourier-series))

(defthm int-prod-fourier-series-thm
  (implies (and (natp i)
                (natp k)
                (realp L)
                (not (equal L 0)))
           (equal (* (/ L)
                     (int-prod-fourier-series (- L) L
                                              i k (/ (acl2-pi) L)))
                  (sum-coefficients (min i k)))))

