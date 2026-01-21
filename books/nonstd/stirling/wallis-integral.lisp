(in-package "ACL2")

(local (include-book "nonstd/integrals/by-parts" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(local (include-book "nonstd/nsa/intervals" :dir :system))
(local (include-book "nonstd/nsa/chain-rule" :dir :system))
(local (include-book "nonstd/nsa/derivative-raise" :dir :system))
(local (include-book "nonstd/integrals/make-partition" :dir :system))
(local (include-book "nonstd/integrals/integrable-functions" :dir :system))


(include-book "nonstd/nsa/trig" :dir :system)

(ENCAPSULATE
    NIL

    (local (include-book
            "nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal"
            :dir :system))

  (defthm acl2-sine-derivative
      (implies (and (acl2-numberp x)
                    (acl2-numberp y)
                    (standardp x)
                    (i-close x y)
                    (not (equal x y)))
               (i-close (/ (- (acl2-sine x) (acl2-sine y))
                           (- x y))
                        (acl2-cosine x))))

  )

(encapsulate
    nil

    (local (include-book "nonstd/nsa/derivative-raise" :dir :system))

  (defun derivative-expt (x n)
    (* (ifix n) (expt x (1- n))))

  (defthm derivative-expt-is-derivative-for-natural-n
    (implies (and (standardp x)
                  (standardp n)
                  (natp n)
                  (inside-interval-p x (real-domain))
                  (i-close x x1)
                  (inside-interval-p x1 (real-domain))
                  (not (equal x1 x)))
             (i-close (/ (- (expt x n) (expt x1 n))
                         (- x x1))
                      (derivative-expt x n))))

  (defthm derivative-expt-is-derivative-for-natural-n-alternative
    (implies (and (standardp x)
                  (standardp n)
                  (natp n)
                  (inside-interval-p x (real-domain))
                  (i-close x x1)
                  (inside-interval-p x1 (real-domain))
                  (not (equal x1 x)))
             (equal (standard-part (/ (- (expt x n) (expt x1 n))
                                      (- x x1)))
                    (derivative-expt x n)))
    :hints (("Goal"
             :use ((:instance derivative-expt-is-derivative-for-natural-n)
                   (:instance close-x-y->same-standard-part
                              (x (derivative-expt x n))
                              (y (/ (- (expt x n) (expt x1 n))
                                    (- x x1)))))
             :in-theory (disable derivative-expt-is-derivative-for-natural-n
                                 close-x-y->same-standard-part))))
  )





(defun expt-sine (x n)
  (let ((x (realfix x))
        (n (nfix n)))
    (expt (acl2-sine x) n)))

(defthmd expt-sine-recursive
    (implies (and (realp x)
                  (posp n))
             (equal (expt-sine x n)
                    (* (expt-sine x (1- n)) (acl2-sine x)))))

(defun expt-sine-prime (x n)
  (let ((x (realfix x))
        (n (nfix n)))
    (* n (expt-sine x (1- n)) (acl2-cosine x))))

(local
 (defthm inside-real-domain
     (implies (realp x)
              (inside-interval-p x (interval nil nil)))
   :hints (("Goal"
            :in-theory (enable interval-definition-theory)))))

(local
 (defthmd close-if-same-standard-part
     (implies (and (acl2-numberp x)
		   (acl2-numberp y)
		   (i-limited x)
		   (i-limited y)
		   (equal (standard-part x) (standard-part y)))
	      (i-close x y))
   :hints (("Goal"
	    :use ((:instance i-close-transitive
			     (x x)
			     (y (standard-part x))
			     (z y)))
	    :in-theory (disable i-close-transitive)))))

(local
 (defthm small-diff-if-close
     (implies (i-close x y)
              (i-small (- x y)))
   :hints (("Goal"
            :in-theory (enable i-close)))
   ))

#|
 TODO:
                 (I-LARGE (+ (* (/ (+ X (- X1)))
                             (EXPT (ACL2-SINE X) N))
                          (- (* (/ (+ X (- X1)))
                                (EXPT (ACL2-SINE X1) N)))))
|#

(LOCAL
 (defthm-std standard-sine
     (implies (standardp x)
              (standardp (acl2-sine x)))))

(LOCAL
 (defthm-std standard-cosine
     (implies (standardp x)
              (standardp (acl2-cosine x)))))


(local
 (defthmd sine-differentiable
     (implies (and (acl2-numberp x)
                   (acl2-numberp y1)
                   (acl2-numberp y2)
                   (standardp x)
                   (i-close x y1)
                   (not (equal x y1))
                   (i-close x y2)
                   (not (equal x y2))
                   )
              (and (and (acl2-numberp (* (+ (acl2-sine x) (- (acl2-sine y1)))
                                         (/ (+ x (- y1)))))
                        (not (i-large (* (+ (acl2-sine x) (- (acl2-sine y1)))
                                    (/ (+ x (- y1)))))))
                   (i-close (* (+ (acl2-sine x) (- (acl2-sine y1)))
                               (/ (+ x (- y1))))
                            (* (+ (acl2-sine x) (- (acl2-sine y2)))
                               (/ (+ x (- y2)))))))
   :hints (("Goal"
            :use ((:instance acl2-sine-derivative (y y1))
                  (:instance acl2-sine-derivative (y y2))
                  (:instance i-close-transitive
                             (x (* (+ (acl2-sine x) (- (acl2-sine y1)))
                                   (/ (+ x (- y1)))))
                             (y (acl2-cosine x))
                             (z (* (+ (acl2-sine x) (- (acl2-sine y2)))
                                   (/ (+ x (- y2))))))
                  (:instance i-close-limited
                             (x (acl2-cosine x))
                             (y (* (+ (acl2-sine x) (- (acl2-sine y1)))
                                   (/ (+ x (- y1))))))
                  (:instance standards-are-limited
                             (x (acl2-cosine x)))
                  )
            :in-theory (disable acl2-sine-derivative
                                i-close-transitive
                                i-close-limited)
            )
           )
   ))



(local
 (defthm limited-expt-sine-differential
     (implies (and (standardp x)
                   (standardp n)
                   (realp x)
                   (natp n)
                   (realp x1)
                   (i-close x x1))
              (i-limited (/ (- (expt-sine x n)
                               (expt-sine x1 n))
                            (- x x1))))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance
                    cr-fn1-o-fn2-differentiable-part1
                    (cr-fn1 (lambda (n x) (expt (realfix x) (nfix n))))
                    (cr-fn2 (lambda (context x) (acl2-sine (realfix x))))
                    (cr-fn1-o-fn2 (lambda (n x) (expt-sine (realfix x) n)))
                    (cr-fn2-domain (lambda () (interval nil nil)))
                    (cr-fn2-range (lambda () (interval nil nil)))
                    (cr-car-context (lambda (n) n))
                    (differential-cr-fn1
                     (lambda (n x eps)
                       (/ (- (expt (+ x eps) (nfix n))
                             (expt x (nfix n)))
                          eps)))
                    (differential-cr-fn2
                     (lambda (context x eps)
                       (/ (- (acl2-sine (+ (realfix x) eps))
                             (acl2-sine (realfix x)))
                          eps)))
                    (derivative-cr-fn1-o-fn2
                     (lambda (n x)
                       (expt-sine-prime (realfix x) n)))
                    )
                   (context n)
                   (y1 x1)
                   )
                  )
            )
           ("Subgoal 6"
            :use ((:instance sine-differentiable)))
           ("Subgoal 5"
            :use ((:instance expt-differentiable-using-nonstd-criterion-for-natural-n
                             (n context))
                  )
            )
           )))

(local
 (defthm-std standard-expt-sine-prime-body
     (implies (and (standardp x)
                   (standardp n))
              (standardp (* N (ACL2-COSINE X)
                            (EXPT (ACL2-SINE X) (+ -1 N)))))))


(local
 (defthm-std standard-expt-sine-deriv-expression
     (implies (and (standardp x)
                   (standardp n)
                   )
              (standardp (* N (ACL2-COSINE X)
                            (EXPT (ACL2-SINE X) (+ -1 N)))))))

(local
 (defthm limited-cosine
     (implies (standardp x)
              (NOT (I-LARGE (ACL2-COSINE X))))
   :hints (("Goal"
            :use ((:instance standards-are-limited
                             (x (acl2-cosine x))))))))


(local
 (defthm-std standard-expt-sine-prime
     (implies (and (standardp x)
                   (standardp n))
              (standardp (expt-sine-prime x n)))))


(local
 (defthm limited-expt-sine-prime
     (implies (and (standardp x)
                   (standardp n))
              (not (i-large (expt-sine-prime x n))))
   :hints (("Goal"
            :use ((:instance standards-are-limited
                             (x (expt-sine-prime x n))))))))



(local
 (defthm-std standard-expt-sine-expression
     (implies (and (standardp x)
                   (standardp n))
              (standardp (* N (ACL2-COSINE X)
                            (EXPT (ACL2-SINE X) (+ -1 N)))))))

(local
 (defthm limited-expt-sine-expression
     (implies (and (standardp x)
                   (standardp n))
              (i-limited (* N (ACL2-COSINE X)
                            (EXPT (ACL2-SINE X) (+ -1 N)))))
   :hints (("Goal"
            :use ((:instance standards-are-limited
                             (x (* N (ACL2-COSINE X)
                                   (EXPT (ACL2-SINE X) (+ -1 N))))))))
   ))

(local
 (defthm inside-interval-nil-nil
     (equal (inside-interval-p x (interval nil nil))
            (realp x))
   :hints (("Goal"
            :in-theory (enable interval-definition-theory)))))

(local
 (defthm inside-interval-nil-nil-2
     (equal (inside-interval-p x '(nil))
            (realp x))
   :hints (("Goal"
            :in-theory (enable interval-definition-theory)))))

(local
 (defthm-std standard-differential-expt-expression
     (implies (and (standardp x)
                   (standardp context))
              (standardp (* CONTEXT (EXPT X (+ -1 CONTEXT)))))))

(local
 (defthm limited-differential-expt-expression
     (implies (and (standardp x)
                   (standardp context))
              (not (i-large (* CONTEXT (EXPT X (+ -1 CONTEXT))))))
   :hints (("Goal"
            :use ((:instance standards-are-limited
                             (x (* CONTEXT (EXPT X (+ -1 CONTEXT))))))))))

(defun differential-sine (x eps)
  (let ((x (realfix x)))
    (/ (- (acl2-sine (+ x eps)) (acl2-sine x))
       eps)))

(defun differential-expt (x n eps)
  (let ((x (realfix x))
        (n (nfix n)))
    (/ (- (expt (+ x eps) n) (expt x n))
       eps)))


(defun differential-expt-sine (x n eps)
  (let ((n (nfix n))
        (x (realfix x)))
    (if (equal (acl2-sine (+ x eps)) (acl2-sine x))
        0
        (* (differential-expt (acl2-sine x)
                              n
                              (- (acl2-sine (+ x eps))
                                 (acl2-sine x)))
           (differential-sine x eps)))))


(local
 (defthm close-minus-2
     (implies (i-close x x1)
              (i-small (+ (- x) x1)))
   :hints (("Goal"
            :in-theory (enable i-close i-small)))))

(defthmd expand-differential-expt-sine
    (implies (and (realp x)
                  (realp eps)
                  ;(natp n)
                  )
             (equal (differential-expt-sine x n eps)
                    (/ (- (expt-sine (+ x eps) n)
                          (expt-sine x n))
                       eps)))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance
                   expand-differential-cr-fn1-o-fn2
                   (cr-fn1 (lambda (n x) (expt (realfix x) (nfix n))))
                   (cr-fn2 (lambda (context x) (acl2-sine (realfix x))))
                   (cr-fn1-o-fn2 (lambda (n x) (expt-sine (realfix x) (nfix n))))
                   (cr-fn2-domain (lambda () (interval nil nil)))
                   (cr-fn2-range (lambda () (interval nil nil)))
                   (cr-car-context (lambda (n) n))
                   (cr-cdr-context (lambda (n) 0))
                   (differential-cr-fn1-o-fn2
                    (lambda (n x eps)
                      (differential-expt-sine x n eps)))
                   (differential-cr-fn1
                    (lambda (n x eps)
                      (differential-expt x n eps)))
                   (derivative-cr-fn1
                    (lambda (n x)
                      (let ((n (nfix n)))
                        (* n (expt (realfix x) (1-  n))))
                      ))
                   (differential-cr-fn2
                    (lambda (context x eps)
                      (differential-sine x eps)))
                   (derivative-cr-fn2
                    (lambda (context x)
                      (acl2-cosine (realfix x))))
                   (derivative-cr-fn1-o-fn2
                    (lambda (n x)
                      (expt-sine-prime (realfix x) (NFIX n))))
                   )
                  (context n)
                  ))
           :in-theory (disable binomial-theorem
                               SINE-OF-SUMS
                               )
           )
          ))




(defthmd expt-sine-prime-is-limited-for-positive-n
    (implies (and (standardp x)
                  (standardp n)
                  (realp x)
                  (realp x1)
                  (posp n)
		  (i-close x x1) (not (= x x1)))
	     (i-limited (/ (- (expt-sine x n)
                              (expt-sine x1 n))
                           (- x x1))))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance
                   cr-fn1-o-fn2-differentiable-part1
                   (cr-fn1 (lambda (n x) (expt (realfix x) (nfix n))))
                   (cr-fn2 (lambda (context x) (acl2-sine (realfix x))))
                   (cr-fn1-o-fn2 (lambda (n x) (expt-sine (realfix x) (nfix n))))
                   (cr-fn2-domain (lambda () (interval nil nil)))
                   (cr-fn2-range (lambda () (interval nil nil)))
                   (cr-car-context (lambda (n) n))
                   (cr-cdr-context (lambda (n) 0))
                   (differential-cr-fn1-o-fn2
                    (lambda (n x eps)
                      (differential-expt-sine x n eps)))
                   (differential-cr-fn1
                    (lambda (n x eps)
                      (differential-expt x n eps)))
                   (derivative-cr-fn1
                    (lambda (n x)
                      (let ((n (nfix n)))
                        (* n (expt (realfix x) (1-  n))))
                      ))
                   (differential-cr-fn2
                    (lambda (context x eps)
                      (differential-sine x eps)))
                   (derivative-cr-fn2
                    (lambda (context x)
                      (acl2-cosine (realfix x))))
                   (derivative-cr-fn1-o-fn2
                    (lambda (n x)
                      (expt-sine-prime (realfix x) (NFIX n))))
                   )
                  (context n)
                  (y1 x1)
                  )
                 )
           :in-theory (disable expt-sine
                               expt-sine-recursive)
           )
          )
  )


(local
 (defthmd differential-swap-lemma
     (implies (and (realp x)
                   (realp x1))
              (equal (* (+ (EXPT-SINE (+ X X1 (- X)) N)
                           (- (EXPT-SINE X N)))
                        (/ (+ X1 (- X))))
                     (* (+ (EXPT-SINE X N)
                           (- (EXPT-SINE (+ X X1 (- X)) N)))
                        (/ (+ X (- X1))))
                     ))
   :hints (("Goal"
            :use ((:instance
                   (:theorem
                    (implies (and (realp x) (realp y))
                             (equal (/ (- x) (- y))
                                    (/ x y))))
                   (x (+ (EXPT-SINE (+ X X1 (- X)) N)
                         (- (EXPT-SINE X N))))
                   (y (+ X1 (- X)))))
            :in-theory (disable expt-sine
                                expt-sine-recursive)))
   )
 )

(defthm expt-sine-prime-is-derivative-for-positive-n
    (implies (and (standardp x)
                  (standardp n)
                  (realp x)
                  (realp x1)
                  (posp n)
		  (i-close x x1) (not (= x x1)))
	     (i-close (/ (- (expt-sine x n)
                            (expt-sine x1 n))
                         (- x x1))
		      (expt-sine-prime x n)))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance
                   differential-cr-fn1-o-fn2-close
                   (cr-fn1 (lambda (n x) (expt (realfix x) (nfix n))))
                   (cr-fn2 (lambda (context x) (acl2-sine (realfix x))))
                   (cr-fn1-o-fn2 (lambda (n x) (expt-sine (realfix x) (nfix n))))
                   (cr-fn2-domain (lambda () (interval nil nil)))
                   (cr-fn2-range (lambda () (interval nil nil)))
                   (cr-car-context (lambda (n) n))
                   (cr-cdr-context (lambda (n) 0))
                   (differential-cr-fn1-o-fn2
                    (lambda (n x eps)
                      (differential-expt-sine x n eps)))
                   (differential-cr-fn1
                    (lambda (n x eps)
                      (differential-expt x n eps)))
                   (derivative-cr-fn1
                    (lambda (n x)
                      (let ((n (nfix n)))
                        (* n (expt (realfix x) (1-  n))))
                      ))
                   (differential-cr-fn2
                    (lambda (context x eps)
                      (differential-sine x eps)))
                   (derivative-cr-fn2
                    (lambda (context x)
                      (acl2-cosine (realfix x))))
                   (derivative-cr-fn1-o-fn2
                    (lambda (n x)
                      (expt-sine-prime (realfix x) (NFIX n))))
                   )
                  (context n)
                  (eps (- x1 x))
                  )
                 (:instance close-if-same-standard-part
                            (x (/ (- (expt-sine x n)
                                     (expt-sine x1 n))
                                  (- x x1)))
                            (y (EXPT-SINE-PRIME X N)))
                 (:instance expand-differential-expt-sine
                            (eps (- x1 x)))
                 (:instance expt-sine-prime-is-limited-for-positive-n)
                 (:instance close-if-same-standard-part
                            (x (+ (* (EXPT-SINE X N) (/ (+ X (- X1))))
                                  (- (* (EXPT-SINE X1 N) (/ (+ X (- X1)))))))
                            (y (EXPT-SINE-PRIME X N)))
                 (:instance differential-swap-lemma)
                 )
           :in-theory (disable cosine-of-sums
                               sine-of-sums
                               STANDARD-PART-OF-PLUS
                               STANDARD-PART-OF-UMINUS
                               close-if-same-standard-part
                               differential-expt-sine
                               expt-sine
                               expt-sine-recursive
                               expt-sine-prime
                               )
           )
          ("Subgoal 3"
           :in-theory (enable expt-sine expt-sine-prime))
          ("Subgoal 2"
           :use ((:instance acl2-sine-derivative
                            (y (+ x (/ (i-large-integer)))))
                 (:instance i-close-to-small-sum
                            (eps (/ (i-large-integer))))
                 (:instance close-x-y->same-standard-part
                            (x (acl2-cosine x))
                            (y (+ (- (* (I-LARGE-INTEGER) (ACL2-SINE X)))
                                  (* (I-LARGE-INTEGER)
                                     (ACL2-SINE (+ (/ (I-LARGE-INTEGER))
                                                   X)))))))
           :in-theory (disable acl2-sine-derivative
                               close-x-y->same-standard-part
                               i-close-to-small-sum)
           )
          ("Subgoal 1"
           :use ((:instance
                  derivative-expt-is-derivative-for-natural-n-alternative
                  (n (nfix context))
                  (x1 (+ x (/ (i-large-integer))))
                  )
                 (:instance i-close-to-small-sum
                            (eps (/ (i-large-integer))))
                 )
           :in-theory (disable
                       derivative-expt-is-derivative-for-natural-n-alternative
                       i-close-to-small-sum))
          )
  )

(i-am-here)

(local
 (defun u-plain*v-prime (x n)
   (* (expt-sine x (1- n))
      (acl2-sine x))))

(defthmd expt-sine-recursive-alternative
    (implies (and (realp x)
                  (posp n))
             (equal (expt-sine x n)
                    (u-plain*v-prime x n))))

(local
 (defun map-u-plain*v-prime (n p)
   (if (consp p)
       (cond (u-plain*v-prime (car p) n)
             (map-u-plain*v-prime n (cdr p)))
       nil)))

(defun riemann-bpfn-u*v-prime (context p)
  (dotprod (deltas p)
           (map-bpfn-u*v-prime context (cdr p))))
