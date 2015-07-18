;; Cuong Chau                             February, 2015

(in-package "ACL2")

(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)

(local (include-book "nonstd/nsa/nsa" :dir :system))

;; ======================================================================

(defun fixed-sin (x k c)
  (let ((x (realfix x))
        (k (ifix k))
        (c (realfix c)))
    (acl2-sine (* k c x))))

(defun fixed-cos (x k c)
  (let ((x (realfix x))
        (k (ifix k))
        (c (realfix c)))
    (acl2-cosine (* k c x))))

(defthm inside-interval-p-uminus-real
  (implies (realp L)
           (inside-interval-p (- L) '(nil)))
  :hints (("goal" :in-theory (enable inside-interval-p))))

(defthm inside-interval-p-real
  (implies (realp L)
           (inside-interval-p L '(nil)))
  :hints (("goal" :in-theory (enable inside-interval-p))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (local
  (defthmd small-squeeze
    (implies (and (realp x)
                  (realp y)
                  (realp z)
                  (<= x y)
                  (<= y z)
                  (i-small x)
                  (i-small z))
             (i-small y))
    :hints (("Goal"
             :use ((:instance standard-part-squeeze))
             :in-theory (enable i-small)))))

 (defthmd close-squeeze
   (implies (and (realp x)
		 (realp y)
		 (realp z)
		 (<= x y)
		 (<= y z)
		 (i-close x z))
	    (and (i-close y x)
		 (i-close y z)))
   :hints (("Goal"
	    :use ((:instance small-squeeze
			     (x 0)
			     (y (- y x))
			     (z (- z x))))
	    :in-theory (enable i-close)))))

(local (include-book "arithmetic/top" :dir :system))

(defthm i-close-plus
  (implies (and (i-close x1 x2)
                (i-close y1 y2))
           (i-close (+ x1 y1) (+ x2 y2)))
  :hints (("Goal" :in-theory (enable i-close))))

(defthm i-close-times
  (implies (and (i-close y1 y2)
                (i-limited x))
           (i-close (* x y1) (* x y2)))
  :hints (("Goal"
           :use ((:instance limited*small->small
                            (x x)
                            (y (- y1 y2))))
           :in-theory (e/d (i-close)
                           (limited*small->small)))))

(encapsulate
 ()

 (local
  (defthm lemma-2
    (implies (and (realp s)
                  (< s -1))
             (< 1 (* s s)))
    :hints (("Goal"
             :use ((:instance (:theorem
                               (implies (and (realp s)
                                             (< 1 s))
                                        (< 1 (* s s))))
                              (s (- s))))))
    :rule-classes (:rewrite :linear)))

 ;; -1 <= sin(x) <= 1.

 (defthm sine-lower-bound
   (implies (realp x)
            (<= -1 (acl2-sine x)))
   :hints (("Goal" :use (:instance sin**2+cos**2)
            :cases ((< (acl2-sine x) -1))
            :in-theory (disable sin**2+cos**2)))
   :rule-classes :linear)

 (defthm sine-upper-bound
   (implies (realp x)
            (<= (acl2-sine x) 1))
   :hints (("Goal"
            :use (:instance sin**2+cos**2)
            :in-theory (disable sin**2+cos**2)))
   :rule-classes :linear)

 ;; -1 <= cos(x) <= 1.

 (defthm cosine-lower-bound
   (implies (realp x)
            (<= -1 (acl2-cosine x)))
   :hints (("Goal" :use (:instance sin**2+cos**2)
            :cases ((< (acl2-cosine x) -1))
            :in-theory (disable sin**2+cos**2)))
   :rule-classes :linear)

 (defthm cosine-upper-bound
   (implies (realp x)
            (<= (acl2-cosine x) 1))
   :hints (("Goal"
            :use (:instance sin**2+cos**2)
            :in-theory (disable sin**2+cos**2)))
   :rule-classes :linear))

;; Auxiliary functions and lemmas for proving the Riemann sum is bounded.

(defun map-const (p y)
  (if (consp p)
      (cons y
            (map-const (cdr p) y))
    nil))

(defun point-wise-<= (xs ys)
  (if (consp xs)
      (and (realp (car xs))
           (realp (car ys))
           (<= (car xs)
               (car ys))
           (point-wise-<= (cdr xs) (cdr ys)))
    (not (consp ys))))

(defun nonneg-listp (l)
  (if (atom l)
      (eq l nil)
    (and (realp (car l))
         (<= 0 (car l))
         (nonneg-listp (cdr l)))))

(defthm sumlist-point-wise-<=
  (implies (point-wise-<= xs ys)
           (<= (sumlist xs)
               (sumlist ys))))

(defthm point-wise-<=-transitive
  (implies (and (point-wise-<= xs ys)
                (point-wise-<= ys zs))
           (point-wise-<= xs zs)))

(defthm point-wise-<=-map-const
  (implies (and (realp y1)
                (realp y2)
                (<= y1 y2))
           (point-wise-<= (map-const p y1)
                          (map-const p y2))))

(defthm maptimes-point-wise-<=
  (implies (and (nonneg-listp xs)
                (point-wise-<= ys zs))
           (point-wise-<= (map-times xs ys)
                          (map-times xs zs))))

(defthm point-wise-<=-implies-dotprod-bounded-2
  (implies (and (point-wise-<= ys zs)
                (nonneg-listp xs))
           (<= (dotprod xs ys)
               (dotprod xs zs))))

(defthm nonneg-listp-deltas
  (implies (partitionp p)
           (nonneg-listp (deltas p))))

(defthmd simplify-riemann-map-const-lemma
  (implies (partitionp p)
           (equal (dotprod (deltas p)
                           (map-const (cdr p) k))
                  (* k
                     (- (car (last p))
                        (car p))))))

(defthmd dotprod-map-const
  (equal (dotprod (deltas p) (map-const (cdr p) y))
         (* (sumlist (deltas p)) y)))

;; sin(n*pi) = 0 for all integer n.

(local
 (encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm lemma-3
    (implies (and (integerp n)
                  (not (integerp (* 1/2 n))))
             (integerp (* 1/2 (1- n))))
    :rule-classes :type-prescription)))

(defthm sin-n*pi
  (implies (integerp n)
           (equal (acl2-sine (* (acl2-pi) n)) 0))
  :hints (("Goal"
           :cases ((integerp (* 1/2 n))
                   (not (integerp (* 1/2 n)))))
          ("Subgoal 1"
           :use ((:instance lemma-3)
                 (:instance sin-2npi
                            (n (* 1/2 (1- n))))))
          ("Subgoal 2"
           :use (:instance sin-2npi
                           (n (* 1/2 n))))))
