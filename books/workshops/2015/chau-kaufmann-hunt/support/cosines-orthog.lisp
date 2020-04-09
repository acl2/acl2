;; Proof of the orthogonality relation between two cosines.

;; Cuong Chau                             March, 2015

;; === OVERVIEW ===

;; The orthogonality relation between two cosines is the definite
;; integral formula of the function f-prime(x, m, n, c) =
;; cos(m*c*x)*cos(n*c*x) w.r.t. real variable x on [-pi/c, pi/c] s.t. this
;; integral equals
;;      0, if m != n,
;;      pi/c, if m = n != 0,
;;      2*pi/c, if m = n = 0.
;; where m and n are fixed integers, c is a fixed nonzero real.

;; The proof procedure:

;; 1. Proving that f-prime returns real values on [a, b].
;; 2. Proving that f-prime is continuous on [a, b].
;; 3. Specifying and proving the correctness of a real-valued antiderivative f
;; of f-prime on [a, b].
;; 4. Defining the Riemann integral of f-prime on [a, b].
;; 5. Evaluating the integral of f-prime on [a, b] in terms of f by applying
;; the Second Fundamental Theorem of Calculus (FTC-2).

;; ================

(in-package "ACL2")

(include-book "riemann-integral/continuous-function-2")
(include-book "utils")

(local
 (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal" :dir :system))
(local (include-book "nonstd/integrals/ftc-2" :dir :system))

;; ======================================================================

;; Define the function f-prime named as cos-orthog-prime.

(defun cos-orthog-prime (x m n c)
  (let ((x (realfix x))
        (m (ifix m))
        (n (ifix n))
        (c (realfix c)))
    (* (acl2-cosine (* m c x))
       (acl2-cosine (* n c x)))))

(defun cos-orthog-domain ()
  (interval nil nil))

(defthm realp-cos-orthog-prime
  (realp (cos-orthog-prime x m n c))
  :rule-classes :type-prescription)

;; We'll show that cos-orthog-prime can be rewritten as follows based on the
;; relation between m and n:

;; cos-orthog-prime(x, m, n, c)
;; = cos-orthog-m!=n-prime(x, m, n, c), if m != n
;; = cos-orthog-m=n-prime(x, m, c),     if m = n != 0
;; = 1,                                 if m = n = 0

;; where cos-orthog-m!=n-prime(x, m, n, c)
;;       = 1/2*[cos((m - n)*c*x) + cos((m + n)*c*x)],
;; and
;; cos-orthog-m=n-prime(x, m, c) = 1/2*[1 + cos(2*m*c*x)]

;; ======================================================================

;; Define the functions
;; cos-orthog-aux-1-prime(x, m, n, c) = cos((m + n)*c*x)
;; and cos-orthog-aux-2-prime(x, m, n, c) = cos((m - n)*c*x), and
;; their corresponding antiderivatives cos-orthog-aux-1 and cos-orthog-aux-2,
;; respectively. These functions will be used to define the function
;; cos-orthog-m!=n-prime and its antiderivative cos-orthog-m!=n.

(defun cos-orthog-aux-1 (x m n c)
  (/ (acl2-sine (* (+ m n) c x))
     (* (+ m n) c)))

(defun cos-orthog-aux-1-prime (x m n c)
  (acl2-cosine (* (+ m n) c x)))

(defun cos-orthog-aux-2 (x m n c)
  (cos-orthog-aux-1 x m (- n) c))

(defun cos-orthog-aux-2-prime (x m n c)
  (cos-orthog-aux-1-prime x m (- n) c))

;; Define cos-orthog-m!=n and cos-orthog-m!=n-prime for the case m != n.

(defun cos-orthog-m!=n-primitive (x m n c)
  (* 1/2 (+ (cos-orthog-aux-2 x m n c)
            (cos-orthog-aux-1 x m n c))))

(defun cos-orthog-m!=n-primitive-prime (x m n c)
  (* 1/2 (+ (cos-orthog-aux-2-prime x m n c)
            (cos-orthog-aux-1-prime x m n c))))

(defun cos-orthog-m!=n (x m n c)
  (let ((x (realfix x))
        (m (ifix m))
        (n (ifix n))
        (c (realfix c)))
    (cos-orthog-m!=n-primitive x m n c)))

(defun cos-orthog-m!=n-prime (x m n c)
  (let ((x (realfix x))
        (m (ifix m))
        (n (ifix n))
        (c (realfix c)))
    (cos-orthog-m!=n-primitive-prime x m n c)))

; Added by Matt K. after v8-2 for (HIDE (COMMENT ...)) change:
(defattach-system ; generates (local (defattach ...))
  hide-with-comment-p
  constant-nil-function-arity-0)

(defthm realp-cos-orthog-m!=n
  (realp (cos-orthog-m!=n x m n c))
  :hints (("Goal"
           :expand (hide (cos-orthog-m!=n-primitive 0 0 0 0))))
  :rule-classes :type-prescription)

(defthm realp-cos-orthog-m!=n-prime
  (realp (cos-orthog-m!=n-prime x m n c))
  :hints (("Goal"
           :expand (hide (cos-orthog-m!=n-primitive-prime 0 0 0 0))))
  :rule-classes :type-prescription)

;; cos-orthog-m!=n-prime is continuous on cos-orthog-domain.

(defthm cos-orthog-m!=n-prime-continuous
  (implies (and (standardp m)
                (standardp n)
                (standardp c)
                (standardp x)
                (inside-interval-p x (cos-orthog-domain))
                (inside-interval-p y (cos-orthog-domain))
                (i-close x y))
           (i-close (cos-orthog-m!=n-prime x m n c)
                    (cos-orthog-m!=n-prime y m n c)))
  :hints (("Goal" :in-theory (disable COSINE-OF-SUMS)
                  :use ((:instance STANDARDS-ARE-LIMITED-FORWARD
                                   (x (* (+ m n) c)))
                        (:instance i-close-times
                                   (x (* (+ m n) c))
                                   (y1 x)
                                   (y2 y))
                        (:instance STANDARDS-ARE-LIMITED-FORWARD
                                   (x (* (- m n) c)))
                        (:instance i-close-times
                                   (x (* (- m n) c))
                                   (y1 x)
                                   (y2 y))))))

;; cos-orthog-m!=n-prime is the derivative of cos-orthog-m!=n on
;; cos-orthog-domain.

(encapsulate
 ()

 (local
  (defderivative cos-orthog-m!=n-primitive-deriv
    (cos-orthog-m!=n-primitive x m n c)))

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp x)
                  (acl2-numberp y)
                  (not (equal x 0)))
             (equal (* x (/ x) y)
                    y))))

 (defthm cos-orthog-m!=n-derivative
   (implies (and (standardp m)
                 (integerp m)
                 (standardp n)
                 (integerp n)
                 (not (equal m n))
                 (not (equal m (- n)))
                 (standardp c)
                 (realp c)
                 (not (equal c 0))
                 (standardp x)
                 (inside-interval-p x (cos-orthog-domain))
                 (inside-interval-p x1 (cos-orthog-domain))
                 (i-close x x1)
                 (not (equal x x1)))
            (i-close (/ (- (cos-orthog-m!=n x m n c)
                           (cos-orthog-m!=n x1 m n c))
                        (- x x1))
                     (cos-orthog-m!=n-prime x m n c)))
   :hints (("Goal"
            :in-theory (disable DISTRIBUTIVITY)
            :use ((:instance cos-orthog-m!=n-primitive-deriv
                             (y x1))
                  (:instance lemma-1
                             (x (+ m n))
                             (y (acl2-cosine (* (+ m n) c x)))))))))

(in-theory (disable cos-orthog-m!=n cos-orthog-m!=n-prime))

;; ======================================================================

;; Define the Riemann integral of cos-orthog-m!=n-prime.

(defun map-cos-orthog-m!=n-prime (p m n c)
  (if (consp p)
      (cons (cos-orthog-m!=n-prime (car p) m n c)
	    (map-cos-orthog-m!=n-prime (cdr p) m n c))
    nil))

(defun riemann-cos-orthog-m!=n-prime (p m n c)
  (dotprod (deltas p)
	   (map-cos-orthog-m!=n-prime (cdr p) m n c)))

(local
 (encapsulate
  ()

  (local
   (defthm limited-riemann-cos-orthog-m!=n-prime-small-partition-lemma
     (implies (and (standardp arg)
                   (realp a) (standardp a)
                   (realp b) (standardp b)
                   (inside-interval-p a (cos-orthog-domain))
                   (inside-interval-p b (cos-orthog-domain))
                   (< a b))
              (i-limited (riemann-cos-orthog-m!=n-prime
                          (make-small-partition a b)
                          (nth 0 arg)
                          (nth 1 arg)
                          (nth 2 arg))))
     :hints (("Goal"
              :expand (hide (cos-orthog-m!=n-primitive-prime 0 0 0 0))
              :by (:functional-instance
                   limited-riemann-rcfn-2-small-partition
                   (rcfn-2 (lambda (x arg)
                             (cos-orthog-m!=n-prime x
                                                    (nth 0 arg)
                                                    (nth 1 arg)
                                                    (nth 2 arg))))
                   (rcfn-2-domain cos-orthog-domain)
                   (map-rcfn-2
                    (lambda (p arg)
                      (map-cos-orthog-m!=n-prime p
                                                 (nth 0 arg)
                                                 (nth 1 arg)
                                                 (nth 2 arg))))
                   (riemann-rcfn-2
                    (lambda (p arg)
                      (riemann-cos-orthog-m!=n-prime p
                                                     (nth 0 arg)
                                                     (nth 1 arg)
                                                     (nth 2 arg))))))
             ("Subgoal 3"
              :use (:instance cos-orthog-m!=n-prime-continuous
                              (m (nth 0 arg))
                              (n (nth 1 arg))
                              (c (nth 2 arg)))))))

  (local
   (defthm-std standardp-list-1
     (implies (and (standardp m)
                   (standardp n)
                   (standardp c))
              (standardp (list m n c)))
     :rule-classes :type-prescription))

  (defthm limited-riemann-cos-orthog-m!=n-prime-small-partition
    (implies (and (realp a) (standardp a)
                  (realp b) (standardp b)
                  (standardp m)
                  (standardp n)
                  (standardp c)
                  (inside-interval-p a (cos-orthog-domain))
                  (inside-interval-p b (cos-orthog-domain))
                  (< a b))
             (i-limited (riemann-cos-orthog-m!=n-prime
                         (make-small-partition a b)
                         m n c)))
    :hints (("Goal"
             :in-theory (disable riemann-cos-orthog-m!=n-prime)
             :use (:instance limited-riemann-cos-orthog-m!=n-prime-small-partition-lemma
                             (arg (list m n c))))))))

(encapsulate
 ()

 (local (in-theory (disable riemann-cos-orthog-m!=n-prime)))

 (defun-std strict-int-cos-orthog-m!=n-prime (a b m n c)
   (if (and (realp a)
            (realp b)
            (inside-interval-p a (cos-orthog-domain))
            (inside-interval-p b (cos-orthog-domain))
            (< a b))
       (standard-part (riemann-cos-orthog-m!=n-prime
                       (make-small-partition a b)
                       m n c))
     0)))

(defun int-cos-orthog-m!=n-prime (a b m n c)
  (if (<= a b)
      (strict-int-cos-orthog-m!=n-prime a b m n c)
    (- (strict-int-cos-orthog-m!=n-prime b a m n c))))

;; ======================================================================

;; Prove the ftc-2 that connects cos-orthog-m!=n-prime with cos-orthog-m!=n.

;; Below is the trick we use to prove a classical theorem using
;; functional instantiation with the present of free variables.

;;; First, define an encapsulate event that introduces zero-arity classical
;;; functions representing the free variables.

(local
 (encapsulate
  (((m) => *)
   ((n) => *)
   ((c) => *))

  (local (defun m () 0))
  (local (defun n () 1))
  (local (defun c () 2))

  (defthm integerp-m
    (integerp (m))
    :rule-classes :type-prescription)

  (defthm integerp-n
    (integerp (n))
    :rule-classes :type-prescription)

  (defthm not-equal-m-n
    (not (equal (m) (n))))

  (defthm not-equal-m-minus-n
    (not (equal (m) (- (n)))))

  (defthm realp-c
    (realp (c))
    :rule-classes :type-prescription)

  (defthm nonzero-c
    (not (equal (c) 0)))))

;;; Second, prove that the zero-arity functions return standard values (use
;;; defthm-std).

(local
 (defthm-std standardp-m
   (standardp (m))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm-std standardp-n
   (standardp (n))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm-std standardp-c
   (standardp (c))
   :rule-classes (:rewrite :type-prescription)))

;;; Third, prove the main theorem but replacing the free variables with the
;;; zero-arity functions introduced above. Without free variables, the
;;; functional instantiation can be applied straightforwardly.

(local
 (defthm cos-orthog-m!=n-ftc-2-lemma
   (implies (and (inside-interval-p a (cos-orthog-domain))
                 (inside-interval-p b (cos-orthog-domain)))
            (equal (int-cos-orthog-m!=n-prime a b (m) (n) (c))
                   (- (cos-orthog-m!=n b (m) (n) (c))
                      (cos-orthog-m!=n a (m) (n) (c)))))
   :hints (("Goal"
            :by (:functional-instance
                 ftc-2
                 (rcdfn
                  (lambda (x)
                    (cos-orthog-m!=n x (m) (n) (c))))
                 (rcdfn-prime
                  (lambda (x)
                    (cos-orthog-m!=n-prime x (m) (n) (c))))
                 (rcdfn-domain cos-orthog-domain)
                 (map-rcdfn-prime
                  (lambda (p)
                    (map-cos-orthog-m!=n-prime p (m) (n) (c))))
                 (riemann-rcdfn-prime
                  (lambda (p)
                    (riemann-cos-orthog-m!=n-prime p (m) (n) (c))))
                 (strict-int-rcdfn-prime
                  (lambda (a b)
                    (strict-int-cos-orthog-m!=n-prime a b (m) (n) (c))))
                 (int-rcdfn-prime
                  (lambda (a b)
                    (int-cos-orthog-m!=n-prime a b (m) (n) (c))))))
           ("Subgoal 6"
            :use (:instance cos-orthog-m!=n-derivative
                            (m (m))
                            (n (n))
                            (c (c)))))))

;;; Finally, prove the main theorem by functionally instantiating the
;;; zero-arity functions in the lemma above with free variables.

(defthm cos-orthog-m!=n-ftc-2
  (implies (and (integerp m)
                (integerp n)
                (not (equal m n))
                (not (equal m (- n)))
                (realp c)
                (not (equal c 0))
                (inside-interval-p a (cos-orthog-domain))
		(inside-interval-p b (cos-orthog-domain)))
	   (equal (int-cos-orthog-m!=n-prime a b m n c)
		  (- (cos-orthog-m!=n b m n c)
		     (cos-orthog-m!=n a m n c))))
  :hints (("Goal"
           :by (:functional-instance cos-orthog-m!=n-ftc-2-lemma
                                     (m (lambda ()
                                          (if (and (integerp m)
                                                   (integerp n)
                                                   (not (equal m n))
                                                   (not (equal m (- n)))
                                                   (realp c)
                                                   (not (equal c 0)))
                                              m
                                            0)))
                                     (n (lambda ()
                                          (if (and (integerp m)
                                                   (integerp n)
                                                   (not (equal m n))
                                                   (not (equal m (- n)))
                                                   (realp c)
                                                   (not (equal c 0)))
                                              n
                                            1)))
                                     (c (lambda ()
                                          (if (and (integerp m)
                                                   (integerp n)
                                                   (not (equal m n))
                                                   (not (equal m (- n)))
                                                   (realp c)
                                                   (not (equal c 0)))
                                              c
                                            2)))))))

(defthm int-cos-orthog-m!=n-prime-thm
  (implies (and (integerp m)
                (integerp n)
                (not (equal m n))
                (not (equal m (- n)))
                (realp L)
                (not (equal L 0)))
           (equal (int-cos-orthog-m!=n-prime (- L) L
                                             m n (/ (acl2-pi) L))
                  0))
  :hints (("Goal"
           :in-theory (enable cos-orthog-m!=n))))

;; ======================================================================

;; Define cos-orthog-m=n and cos-orthog-m=n-prime for the case m = n.

(defun cos-orthog-m=n-primitive (x m c)
  (* 1/2 (+ x (/ (acl2-sine (* 2 m c x))
                 (* 2 m c)))))

(defun cos-orthog-m=n-primitive-prime (x m c)
  (* 1/2 (+ 1 (acl2-cosine (* 2 m c x)))))

(defun cos-orthog-m=n (x m c)
  (let ((x (realfix x))
        (m (ifix m))
        (c (realfix c)))
    (cos-orthog-m=n-primitive x m c)))

(defun cos-orthog-m=n-prime (x m c)
  (let ((x (realfix x))
        (m (ifix m))
        (c (realfix c)))
    (cos-orthog-m=n-primitive-prime x m c)))

(defthm realp-cos-orthog-m=n
  (realp (cos-orthog-m=n x m c))
  :hints (("Goal" :expand (hide (cos-orthog-m=n-primitive 0 0 0))))
  :rule-classes :type-prescription)

(defthm realp-cos-orthog-m=n-prime
  (realp (cos-orthog-m=n-prime x m c))
  :rule-classes :type-prescription)

;; cos-orthog-m=n-prime is continous on cos-orthog-domain.

(defthm cos-orthog-m=n-prime-continous
  (implies (and (standardp m)
                (standardp c)
                (standardp x)
                (inside-interval-p x (cos-orthog-domain))
                (inside-interval-p y (cos-orthog-domain))
                (i-close x y))
           (i-close (cos-orthog-m=n-prime x m c)
                    (cos-orthog-m=n-prime y m c)))
  :hints (("Goal"
           :in-theory (disable COSINE-2X))))

;; cos-orthog-m=n-prime is the derivative of cos-orthog-m=n on
;; cos-orthog-domain.

(encapsulate
 ()

 (local
  (defderivative cos-orthog-m=n-primitive-deriv
    (cos-orthog-m=n-primitive x m c)))

 (defthm cos-orthog-m=n-derivative
   (implies (and (standardp m)
                 (integerp m)
                 (not (equal m 0))
                 (standardp c)
                 (realp c)
                 (not (equal c 0))
                 (standardp x)
                 (inside-interval-p x (cos-orthog-domain))
                 (inside-interval-p x1 (cos-orthog-domain))
                 (i-close x x1)
                 (not (equal x x1)))
            (i-close (/ (- (cos-orthog-m=n x m c)
                           (cos-orthog-m=n x1 m c))
                        (- x x1))
                     (cos-orthog-m=n-prime x m c)))
   :hints (("Goal" :use (:instance cos-orthog-m=n-primitive-deriv
                                   (y x1))))))

(in-theory (disable cos-orthog-m=n cos-orthog-m=n-prime))

;; ======================================================================

;; Define the Riemann integral of cos-orthog-m=n-prime.

(defun map-cos-orthog-m=n-prime (p m c)
  (if (consp p)
      (cons (cos-orthog-m=n-prime (car p) m c)
	    (map-cos-orthog-m=n-prime (cdr p) m c))
    nil))

(defun riemann-cos-orthog-m=n-prime (p m c)
  (dotprod (deltas p)
	   (map-cos-orthog-m=n-prime (cdr p) m c)))

(local
 (encapsulate
  ()

  (local
   (defthm limited-riemann-cos-orthog-m=n-prime-small-partition-lemma
     (implies (and (standardp arg)
                   (realp a) (standardp a)
                   (realp b) (standardp b)
                   (inside-interval-p a (cos-orthog-domain))
                   (inside-interval-p b (cos-orthog-domain))
                   (< a b))
              (i-limited (riemann-cos-orthog-m=n-prime
                          (make-small-partition a b)
                          (nth 0 arg)
                          (nth 1 arg))))
     :hints (("Goal"
              :by (:functional-instance
                   limited-riemann-rcfn-2-small-partition
                   (rcfn-2 (lambda (x arg)
                             (cos-orthog-m=n-prime x
                                                   (nth 0 arg)
                                                   (nth 1 arg))))
                   (rcfn-2-domain cos-orthog-domain)
                   (map-rcfn-2
                    (lambda (p arg)
                      (map-cos-orthog-m=n-prime p
                                                (nth 0 arg)
                                                (nth 1 arg))))
                   (riemann-rcfn-2
                    (lambda (p arg)
                      (riemann-cos-orthog-m=n-prime p
                                                    (nth 0 arg)
                                                    (nth 1 arg)))))))))

  (local
   (defthm-std standardp-list-2
     (implies (and (standardp m)
                   (standardp c))
              (standardp (list m c)))
     :rule-classes :type-prescription))

  (defthm limited-riemann-cos-orthog-m=n-prime-small-partition
    (implies (and (realp a) (standardp a)
                  (realp b) (standardp b)
                  (standardp m)
                  (standardp c)
                  (inside-interval-p a (cos-orthog-domain))
                  (inside-interval-p b (cos-orthog-domain))
                  (< a b))
             (i-limited (riemann-cos-orthog-m=n-prime
                         (make-small-partition a b)
                         m c)))
    :hints (("Goal"
             :in-theory (disable riemann-cos-orthog-m=n-prime)
             :use (:instance limited-riemann-cos-orthog-m=n-prime-small-partition-lemma
                             (arg (list m c))))))))

(encapsulate
 ()

 (local (in-theory (disable riemann-cos-orthog-m=n-prime)))

 (defun-std strict-int-cos-orthog-m=n-prime (a b m c)
   (if (and (realp a)
            (realp b)
            (inside-interval-p a (cos-orthog-domain))
            (inside-interval-p b (cos-orthog-domain))
            (< a b))
       (standard-part (riemann-cos-orthog-m=n-prime
                       (make-small-partition a b)
                       m c))
     0)))

(defun int-cos-orthog-m=n-prime (a b m c)
  (if (<= a b)
      (strict-int-cos-orthog-m=n-prime a b m c)
    (- (strict-int-cos-orthog-m=n-prime b a m c))))

;; ======================================================================

;; Prove the ftc-2 that connects cos-orthog-m=n-prime with cos-orthog-m=n.

;; Below is the trick we use to prove a classical theorem using
;; functional instantiation with the present of free variables.

;;; First, define an encapsulate event that introduces zero-arity classical
;;; functions representing the free variables.

(local
 (encapsulate
  (((new-m) => *)
   ((new-c) => *))

  (local (defun new-m () 1))
  (local (defun new-c () 2))

  (defthm integerp-new-m
    (integerp (new-m))
    :rule-classes :type-prescription)

  (defthm nonzero-new-m
    (not (equal (new-m) 0)))

  (defthm realp-new-c
    (realp (new-c))
    :rule-classes :type-prescription)

  (defthm nonzero-new-c
    (not (equal (new-c) 0)))))

;;; Second, prove that the zero-arity functions return standard values (use
;;; defthm-std).

(local
 (defthm-std standardp-new-m
   (standardp (new-m))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm-std standardp-new-c
   (standardp (new-c))
   :rule-classes (:rewrite :type-prescription)))

;;; Third, prove the main theorem but replacing the free variables with the
;;; zero-arity functions introduced above. Without free variables, the
;;; functional instantiation can be applied straightforwardly.

(local
 (defthm cos-orthog-m=n-ftc-2-lemma
   (implies (and (inside-interval-p a (cos-orthog-domain))
                 (inside-interval-p b (cos-orthog-domain)))
            (equal (int-cos-orthog-m=n-prime a b (new-m) (new-c))
                   (- (cos-orthog-m=n b (new-m) (new-c))
                      (cos-orthog-m=n a (new-m) (new-c)))))
   :hints (("Goal"
            :by (:functional-instance
                 ftc-2
                 (rcdfn
                  (lambda (x)
                    (cos-orthog-m=n x (new-m) (new-c))))
                 (rcdfn-prime
                  (lambda (x)
                    (cos-orthog-m=n-prime x (new-m) (new-c))))
                 (rcdfn-domain cos-orthog-domain)
                 (map-rcdfn-prime
                  (lambda (p)
                    (map-cos-orthog-m=n-prime p (new-m) (new-c))))
                 (riemann-rcdfn-prime
                  (lambda (p)
                    (riemann-cos-orthog-m=n-prime p (new-m) (new-c))))
                 (strict-int-rcdfn-prime
                  (lambda (a b)
                    (strict-int-cos-orthog-m=n-prime a b (new-m) (new-c))))
                 (int-rcdfn-prime
                  (lambda (a b)
                    (int-cos-orthog-m=n-prime a b (new-m) (new-c))))))
           ("Subgoal 6"
            :use (:instance cos-orthog-m=n-derivative
                            (m (new-m))
                            (c (new-c)))))))

;;; Finally, prove the main theorem by functionally instantiating the
;;; zero-arity functions in the lemma above with free variables.

(defthm cos-orthog-m=n-ftc-2
  (implies (and (integerp m)
                (not (equal m 0))
                (realp c)
                (not (equal c 0))
                (inside-interval-p a (cos-orthog-domain))
		(inside-interval-p b (cos-orthog-domain)))
	   (equal (int-cos-orthog-m=n-prime a b m c)
		  (- (cos-orthog-m=n b m c)
		     (cos-orthog-m=n a m c))))
  :hints (("Goal"
           :by (:functional-instance cos-orthog-m=n-ftc-2-lemma
                                     (new-m (lambda ()
                                              (if (and (integerp m)
                                                       (not (equal m 0))
                                                       (realp c)
                                                       (not (equal c 0)))
                                                  m
                                                1)))
                                     (new-c (lambda ()
                                              (if (and (integerp m)
                                                       (not (equal m 0))
                                                       (realp c)
                                                       (not (equal c 0)))
                                                  c
                                                2)))))))

(defthm int-cos-orthog-m=n-prime-thm
  (implies (and (integerp m)
                (not (equal m 0))
                (realp L)
                (not (equal L 0)))
           (equal (int-cos-orthog-m=n-prime (- L) L
                                            m (/ (acl2-pi) L))
                  L))
  :hints (("Goal" :in-theory (enable cos-orthog-m=n))))

;; ======================================================================

;; Finally, compute the definite integral of cos-orthog-prime on [-L, L],
;; where L = pi/c.

(defthm cos-orthog-prime-rewrite
  (equal (cos-orthog-prime x m n c)
         (if (equal m n)
             (if (equal m 0)
                 1
               (cos-orthog-m=n-prime x m c))
           (cos-orthog-m!=n-prime x m n c)))
  :hints (("Goal"
           :expand (hide (cos-orthog-m!=n-primitive-prime 0 0 0 0))
           :use (:instance COS**2->1-SIN**2
                           (x (* m c x)))
           :in-theory (enable cos-orthog-m=n-prime
                              cos-orthog-m!=n-prime))))

(in-theory (disable cos-orthog-prime))

(defthm cos-orthog-prime-continuous
  (implies (and (standardp m)
                (standardp n)
                (standardp c)
                (standardp x)
                (inside-interval-p x (cos-orthog-domain))
                (inside-interval-p y (cos-orthog-domain))
                (i-close x y))
           (i-close (cos-orthog-prime x m n c)
                    (cos-orthog-prime y m n c))))

(defun cos-orthog (x m n c)
  (if (equal m n)
      (if (equal m 0)
          (realfix x)
        (cos-orthog-m=n x m c))
    (cos-orthog-m!=n x m n c)))

(defthm realp-cos-orthog
  (realp (cos-orthog x m n c))
  :rule-classes :type-prescription)

(defthm cos-orthog-derivative
  (implies (and (standardp m)
                (natp m)
                (standardp n)
                (natp n)
                (standardp c)
                (realp c)
                (not (equal c 0))
                (standardp x)
                (inside-interval-p x (cos-orthog-domain))
                (inside-interval-p x1 (cos-orthog-domain))
                (i-close x x1)
                (not (equal x x1)))
           (i-close (/ (- (cos-orthog x m n c)
                          (cos-orthog x1 m n c))
                       (- x x1))
                    (cos-orthog-prime x m n c)))
  :hints (("Goal"
           :in-theory (disable distributivity)
           :use ((:instance cos-orthog-m!=n-derivative)
                 (:instance cos-orthog-m=n-derivative)))))

(defun map-cos-orthog-prime (p m n c)
  (if (consp p)
      (cons (cos-orthog-prime (car p) m n c)
	    (map-cos-orthog-prime (cdr p) m n c))
    nil))

(defthm map-cos-orthog-prime-rewrite
  (equal (map-cos-orthog-prime p m n c)
         (if (equal m n)
             (if (equal m 0)
                 (map-const p 1)
               (map-cos-orthog-m=n-prime p m c))
           (map-cos-orthog-m!=n-prime p m n c))))

(in-theory (disable cos-orthog cos-orthog-prime-rewrite))

(defun riemann-cos-orthog-prime (p m n c)
  (dotprod (deltas p)
	   (map-cos-orthog-prime (cdr p) m n c)))

(defthm riemann-cos-orthog-prime-rewrite
  (equal (riemann-cos-orthog-prime p m n c)
         (if (equal m n)
             (if (equal m 0)
                 (- (car (last p))
                    (car p))
               (riemann-cos-orthog-m=n-prime p m c))
           (riemann-cos-orthog-m!=n-prime p m n c)))
  :hints (("Goal" :use (:instance dotprod-map-const
                                  (y 1)))))

(in-theory (disable riemann-cos-orthog-prime
                    riemann-cos-orthog-m=n-prime
                    riemann-cos-orthog-m!=n-prime))

(local
 (defthm limited-riemann-cos-orthog-prime-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (standardp m)
                 (standardp n)
                 (standardp c)
                 (inside-interval-p a (cos-orthog-domain))
                 (inside-interval-p b (cos-orthog-domain))
                 (< a b))
            (i-limited (riemann-cos-orthog-prime
                        (make-small-partition a b)
                        m n c)))))

(defun-std strict-int-cos-orthog-prime (a b m n c)
  (if (and (realp a)
           (realp b)
           (inside-interval-p a (cos-orthog-domain))
           (inside-interval-p b (cos-orthog-domain))
           (< a b))
      (standard-part (riemann-cos-orthog-prime
                      (make-small-partition a b)
                      m n c))
    0))

(defun int-cos-orthog-prime (a b m n c)
  (if (<= a b)
      (strict-int-cos-orthog-prime a b m n c)
    (- (strict-int-cos-orthog-prime b a m n c))))

(defthm-std int-cos-orthog-prime-rewrite
  (implies (and (inside-interval-p a (cos-orthog-domain))
                (inside-interval-p b (cos-orthog-domain)))
           (equal (int-cos-orthog-prime a b m n c)
                  (if (equal m n)
                      (if (equal m 0)
                          (- b a)
                        (int-cos-orthog-m=n-prime a b m c))
                    (int-cos-orthog-m!=n-prime a b m n c)))))

(in-theory (disable int-cos-orthog-prime
                    int-cos-orthog-m=n-prime
                    int-cos-orthog-m!=n-prime))

;; The orthogonality relation on [-L, L] for any nonzero real number L.

(defthm int-cos-orthog-prime-thm
  (implies (and (integerp m)
                (integerp n)
                (not (equal m (- n)))
                (realp L)
                (not (equal L 0)))
           (equal (int-cos-orthog-prime (- L) L
                                        m n (/ (acl2-pi) L))
                  (if (equal m n)
                      (if (equal m 0) (* 2 L) L)
                    0))))

;; The orthogonality relation on [-pi, pi], i.e., L = pi.

(defthm int-cos-orthog-prime-thm-instance
  (implies (and (integerp m)
                (integerp n)
                (not (equal m (- n))))
           (equal (int-cos-orthog-prime (- (acl2-pi)) (acl2-pi)
                                        m n 1)
                  (if (equal m n)
                      (if (equal m 0)
                          (* 2 (acl2-pi))
                        (acl2-pi))
                    0)))
  :hints (("Goal" :use (:instance int-cos-orthog-prime-thm
                                  (L (acl2-pi))))))


