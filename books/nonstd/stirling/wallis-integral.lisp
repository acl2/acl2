(in-package "ACL2")

;;; This book is meant to be included locally from walis-product.lisp.
;;; So there's no need to stress about polluting the namespace by making
;;; everything local.


(include-book "nonstd/integrals/by-parts" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

(include-book "nonstd/nsa/intervals" :dir :system)
(include-book "nonstd/nsa/chain-rule" :dir :system)
(include-book "nonstd/nsa/derivative-raise" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/ftc-2" :dir :system)
(include-book "nonstd/nsa/derivatives-composition" :dir :system)



(include-book "nonstd/nsa/trig" :dir :system)

(encapsulate
    nil

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

  (defthm acl2-cosine-derivative
      (implies (and (acl2-numberp x)
                    (acl2-numberp y)
                    (standardp x)
                    (i-close x y)
                    (not (equal x y)))
               (i-close (/ (- (acl2-cosine x) (acl2-cosine y))
                           (- x y))
                        (- (acl2-sine x)))))

)

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


(LOCAL
 (defthm-std standard-sine
     (implies (standardp x)
              (standardp (acl2-sine x)))))

(LOCAL
 (defthm limited-sine
     (implies (standardp x)
              (i-limited (acl2-sine x)))
   :hints (("Goal"
            :use ((:instance standards-are-limited
                             (x (acl2-sine x))))))))

(LOCAL
 (defthm-std standard-cosine
     (implies (standardp x)
              (standardp (acl2-cosine x)))))

(LOCAL
 (defthm limited-cosine
     (implies (standardp x)
              (i-limited (acl2-cosine x)))
   :hints (("Goal"
            :use ((:instance standards-are-limited
                             (x (acl2-cosine x))))))))

(defthm acl2-sine-differentiable
    (implies (and (acl2-numberp x)
                  (acl2-numberp y1)
                  (acl2-numberp y2)
                  (standardp x)
                  (i-close x y1)
                  (not (equal x y1))
                  (i-close x y2)
                  (not (equal x y2)))
             (and (i-limited (/ (- (acl2-sine x) (acl2-sine y1))
                                (- x y1)))
                  (i-close (/ (- (acl2-sine x) (acl2-sine y1))
                              (- x y1))
                           (/ (- (acl2-sine x) (acl2-sine y2))
                              (- x y2)))))
  :hints (("Goal"
           :use ((:instance close-if-same-standard-part
                            (x (/ (- (acl2-sine x) (acl2-sine y1))
                                  (- x y1)))
                            (y (/ (- (acl2-sine x) (acl2-sine y2))
                                  (- x y2))))
                 (:instance I-CLOSE-LIMITED-2
                            (x (/ (- (acl2-sine x) (acl2-sine y1))
                                  (- x y1)))
                            (y (acl2-cosine x)))
                 (:instance acl2-sine-derivative
                            (x x)
                            (y y1))
                 (:instance acl2-sine-derivative
                            (x x)
                            (y y2))
                 )
           )))

(defthm acl2-cosine-differentiable
    (implies (and (acl2-numberp x)
                  (acl2-numberp y1)
                  (acl2-numberp y2)
                  (standardp x)
                  (i-close x y1)
                  (not (equal x y1))
                  (i-close x y2)
                  (not (equal x y2)))
             (and (i-limited (/ (- (acl2-cosine x) (acl2-cosine y1))
                                (- x y1)))
                  (i-close (/ (- (acl2-cosine x) (acl2-cosine y1))
                              (- x y1))
                           (/ (- (acl2-cosine x) (acl2-cosine y2))
                              (- x y2)))))
  :hints (("Goal"
           :use ((:instance close-if-same-standard-part
                            (x (/ (- (acl2-cosine x) (acl2-cosine y1))
                                  (- x y1)))
                            (y (/ (- (acl2-cosine x) (acl2-cosine y2))
                                  (- x y2))))
                 (:instance I-CLOSE-LIMITED-2
                            (x (/ (- (acl2-cosine x) (acl2-cosine y1))
                                  (- x y1)))
                            (y (- (acl2-sine x))))
                 (:instance acl2-cosine-derivative
                            (x x)
                            (y y1))
                 (:instance acl2-cosine-derivative
                            (x x)
                            (y y2))
                 )
           )))



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

  (local
   (defthm-std lemma-1
       (implies (and (standardp x)
                     (standardp n))
                (standardp (* N (EXPT X (+ -1 N)))))
     :rule-classes nil))

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
                                    (- x x1))))
                   (:instance lemma-1)
                   (:instance STANDARDS-ARE-LIMITED
                              (x (* N (EXPT X (+ -1 N))))))
             :in-theory (disable derivative-expt-is-derivative-for-natural-n
                                 close-x-y->same-standard-part
                                 standards-are-limited))))
  )



(defun expt-sine (x n)
  (if (zp n)
      1
      (if (realp x)
          (expt (acl2-sine x) n)
          0)))

(defthmd expt-sine-recursive
    (implies (and (realp x)
                  (posp n))
             (equal (expt-sine x n)
                    (* (expt-sine x (1- n)) (acl2-sine x)))))

(defun expt-sine-prime (x n)
  (if (zp n)
      0
      (if (realp x)
          (* n (expt-sine x (1- n)) (acl2-cosine x))
          0)))

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
  (if (realp x)
      (/ (- (acl2-sine (+ x eps)) (acl2-sine x))
         eps)
      1))

(defun differential-expt (x n eps)
  (if (zp n)
      0
      (if (realp x)
          (/ (- (expt (+ x eps) n) (expt x n))
             eps)
          (if (= n 1) 1 0)
          )))


(defun differential-expt-sine (x n eps)
  (if (zp n)
      0
      (if (realp x)
          (if (equal (acl2-sine (+ x eps)) (acl2-sine x))
              0
              (* (differential-expt (acl2-sine x)
                                    n
                                    (- (acl2-sine (+ x eps))
                                       (acl2-sine x)))
                 (differential-sine x eps)))
          0)))


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

(defthm expt-sine-prime-is-close-for-positive-n
    (implies (and (standardp x)
                  (standardp n)
                  (realp x)
                  (realp x1)
                  (realp x2)
                  (posp n)
		  (i-close x x1) (not (= x x1))
		  (i-close x x2) (not (= x x2)))
	     (i-close (/ (- (expt-sine x n)
                            (expt-sine x1 n))
                         (- x x1))
                      (/ (- (expt-sine x n)
                            (expt-sine x2 n))
                         (- x x2))))
  :hints (("Goal"
           :use ((:instance expt-sine-prime-is-derivative-for-positive-n)
                 (:instance expt-sine-prime-is-derivative-for-positive-n (x1 x2))
                 (:instance i-close-transitive
                            (y (expt-sine-prime x n))
                            (x (/ (- (expt-sine x n)
                                     (expt-sine x1 n))
                                  (- x x1)))
                            (z (/ (- (expt-sine x n)
                                     (expt-sine x2 n))
                                  (- x x2e))
		      ))))))

(defthm expt-sine-continuous
    (implies (and (realp x)
                  (standardp x)
		  (realp x1)
                  (standardp n)
                  (natp n)
                  (i-close x x1))
             (I-CLOSE (expt-sine x n)
                      (expt-sine x1 n)))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance rdfn-continuous
                                        (rdfn (lambda (context x)
                                                (expt-sine x context)))
                                        (rdfn-domain real-domain))
                  (y x1)
                  (context n)
                  )))
          ("Subgoal 1"
           :use ((:instance expt-sine-prime-is-close-for-positive-n
                            (x1 y1)
                            (x2 y2)
                            (n context))
                 (:INSTANCE expt-sine-prime-is-limited-for-positive-n
                            (x1 y1)
                            (N CONTEXT))))
          ))


(defthm acl2-cosine-continuous
    (implies (and (realp x)
                  (standardp x)
		  (realp x1)
                  (i-close x x1))
             (I-CLOSE (acl2-cosine x)
                      (acl2-cosine x1)))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance rdfn-continuous
                                        (rdfn (lambda (context x) (acl2-cosine (realfix x))))
                                        (rdfn-domain real-domain))
                  (y x1)
                  )))
          ("Subgoal 2"
           :use ((:instance acl2-cosine-derivative ; elem-cosine-close
                            (y y1))
                 (:instance acl2-cosine-derivative ; elem-cosine-close
                            (y y2))
                 (:instance i-close-limited-2
                            (x (/ (- (acl2-cosine x) (acl2-cosine y1))
                                  (- x y1)))
                            (y (- (acl2-sine x))))
                 (:instance standards-are-limited
                            (x (acl2-sine x)))
                 ))
          ("Subgoal 1"
           :use ((:instance acl2-cosine-derivative ; elem-cosine-close
                            (y y1))
                 (:instance acl2-cosine-derivative ; elem-cosine-close
                            (y y2))
                 (:instance i-close-limited-2
                            (x (/ (- (acl2-cosine x) (acl2-cosine y1))
                                  (- x y1)))
                            (y (- (acl2-sine x))))
                 (:instance standards-are-limited
                            (x (acl2-sine x)))
                 ))
          ))


(defun u-plain (n x)
  (if (zp n)
      1
      (if (realp x)
          (expt-sine x (1- n))
          0)))

(defun u-prime (n x)
  (if (zp n)
      0
      (if (realp x)
          (* (1- n) (expt-sine x (- n 2)) (acl2-cosine x))
          0)))

(defun v-plain (n x)
  (if (zp n)
      1
      (- (acl2-cosine (REALFIX x)))))

(defun v-prime (n x)
  (if (zp n)
      0
      (if (realp x)
          (acl2-sine x)
          0)))


(defun u-plain*v-prime (n x)
  (* (u-plain n x)
     (v-prime n x)))

(defthmd expt-sine-recursive-alternative
    (implies (and (realp x)
                  (posp n))
             (equal (expt-sine x n)
                    (u-plain*v-prime n x))))

(defun uv-prime (n x)
  (+ (* (U-PLAIN (NFIX n) X)
        (V-PRIME (NFIX n) X))
     (* (V-PLAIN (NFIX n) X)
        (U-PRIME (NFIX n) X))))

(defun map-u-plain*v-prime (n p)
  (if (consp p)
      (cons (u-plain*v-prime n (car p))
            (map-u-plain*v-prime n (cdr p)))
      nil))

(defun riemann-u-plain*v-prime (context p)
  (dotprod (deltas p)
           (map-u-plain*v-prime context (cdr p))))


(defun map-uv-prime (n p)
  (if (consp p)
      (cons (uv-prime n (car p))
            (map-uv-prime n (cdr p)))
      nil))

(defun riemann-uv-prime (context p)
  (dotprod (deltas p)
           (map-uv-prime context (cdr p))))


(defun repeat-n-times (n x)
  (if (zp n)
      nil
      (cons x (repeat-n-times (1- n) x))))

(encapsulate nil

    (local
     (defthm lemma-1
         (implies (not (posp n))
                  (equal (expt-sine x n)
                         1))))

  (local
   (defthm lemma-2
       (implies (not (posp n))
                (equal (UV-PRIME n x)
                       0))))


  (local
   (defthm lemma-3
       (implies (not (posp n))
                (equal (MAP-UV-PRIME n p)
                       (repeat-n-times (len p) 0)))
     ))

  (LOCAL
   (DEFTHM LEMMA-5
       (IMPLIES (Posp N)
                (MAKE-PARTITION-REC A DELTA N))))

  (LOCAL
   (DEFTHM LEMMA-6
       (IMPLIES (POSP N)
                (MAKE-PARTITION A B N))))

  (LOCAL
   (DEFTHM LEMMA-7
       (MAKE-SMALL-PARTITION A B)))

  (local
   (defthm lemma-8
       (implies (posp (1- n))
                (cdr (make-partition-rec a delta n)))
     :hints (("Goal"
              :expand (make-partition-rec a delta n)))
     ))

  (LOCAL
   (DEFTHM LEMMA-9
       (CDR (MAKE-SMALL-PARTITION A B))
     :HINTS (("GOAL"
              :expand (MAKE-SMALL-PARTITION A B)))))


  (local
   (defthmd close-plus-2
       (implies (and (i-close x1 x2)
                     (i-close y1 y2))
                (i-close (+ x1 y1)
                         (+ x2 y2)))
     :hints (("Goal"
              :in-theory (enable i-close)))
     ))


  (local
   (defthmd expt-sine-x-0
       (equal (expt-sine x 0) 1)))

  (local
   (defthm-std standard-expt-sine
       (implies (and (standardp x)
                     (standardp n))
                (standardp (expt-sine x n)))))

  (local
   (defthm limited-expt-sine
       (implies (and (standardp x)
                     (standardp n))
                (i-limited (expt-sine x n)))
     :hints (("Goal"
              :use ((:instance standards-are-limited
                               (x (expt-sine x n))))))
     ))

  (local
   (defthmd subgoal-5
       (IMPLIES (AND (STANDARDP X)
                     (STANDARDP CONTEXTU)
                     (REALP X)
                     (I-CLOSE X X1)
                     (REALP X1))
                (I-CLOSE (U-PRIME CONTEXTU X)
                         (U-PRIME CONTEXTU X1)))
     :hints (("Goal"
              :use ((:instance expt-sine-continuous
                               (n (nfix (- contextu 2))))
                    (:instance acl2-cosine-continuous)
                    (:instance close-times-2
                               (x1 (acl2-cosine x))
                               (x2 (acl2-cosine x1))
                               (y1 (expt-sine x (- contextu 2)))
                               (y2 (expt-sine x1 (- (nfix contextu) 2)))
                               )
                    (:instance close-times
                               (x1 (* (acl2-cosine x) (expt-sine x (- contextu 2))))
                               (x2 (* (acl2-cosine x1) (expt-sine x1 (- contextu 2))))
                               (y contextu))
                    (:instance close-uminus
                               (x (* (ACL2-COSINE X)
                                     (EXPT-SINE X (+ -2 CONTEXTU))))
                               (y (* (ACL2-COSINE X1)
                                     (EXPT-SINE X1 (+ -2 CONTEXTU))))
                               )
                    (:instance close-plus-2
                               (x1 (- (* (acl2-cosine x)
                                         (expt-sine x (+ -2 contextu)))))
                               (x2 (- (* (acl2-cosine x1)
                                         (expt-sine x1 (+ -2 contextu)))))
                               (y1 (* contextu (acl2-cosine x)
                                      (expt-sine x (+ -2 contextu))))
                               (y2 (* contextu (acl2-cosine x1)
                                      (expt-sine x1
                                                 (+ -2 contextu))))))
              :in-theory (disable expt-sine
                                  close-plus-2
                                  close-uminus
                                  close-times
                                  close-times-2
                                  acl2-cosine-continuous
                                  expt-sine-continuous)))))

  (local
   (defthm limited-riemann-uv-prime-small-partition-posp-context
       (implies (and (realp a) (standardp a)
		     (realp b) (standardp b)
                     (standardp context)
                     (posp context)
		     (inside-interval-p a (real-domain))
		     (inside-interval-p b (real-domain))
		     (< a b))
	        (i-limited (riemann-uv-prime context
                                             (make-small-partition a b))))
     :otf-flg t
     :hints (("Goal"
	      :use ((:functional-instance limited-riemann-bpfn-u*v-prime-small-partition
				          (bpfn-domain real-domain)
                                          (BPFN-CAR-CONTEXT (lambda (context) (nfix context)))
                                          (BPFN-CdR-CONTEXT (lambda (context) (nfix context)))
				          (bpfn-u*v-prime uv-prime)
                                          (bpfn-u-prime u-prime)
                                          (bpfn-v-prime v-prime)
                                          (bpfn-u u-plain)
                                          (bpfn-v v-plain)
                                          (bpfn-u*v (lambda (context x)
                                                      (* (u-plain context x)
                                                         (v-plain context x))))
				          (map-bpfn-u*v-prime map-uv-prime)
				          (riemann-bpfn-u*v-prime riemann-uv-prime))))
             ("Subgoal 5"
              :by (:instance subgoal-5))
             ("Subgoal 4"
              :use  ((:instance acl2-cosine-derivative
                                (Y X1))
                     (:instance CLOSE-UMINUS
                                (x (+ (* (ACL2-COSINE X) (/ (+ X (- X1))))
                                      (- (* (ACL2-COSINE X1) (/ (+ X (- X1)))))))
                                (y (- (ACL2-SINE X))))
                     )
              )
             ("Subgoal 3"
              :use ((:instance expt-sine-prime-is-derivative-for-positive-n
                               (n (1- contextu)))))
             )))


  (local
   (defthm map-uv-prime-not-posp-context
       (implies (not (posp context))
                (equal (map-uv-prime context p)
                       (repeat-n-times (len p) 0)
                       ))))

  (LOCAL
   (DEFTHM MAP-TIMES-ZEROS
       (EQUAL (MAP-TIMES (DELTAS P) (cdr (REPEAT-N-TIMES (LEN P) 0)))
              (cdr (REPEAT-N-TIMES (LEN P) 0)))))

  (LOCAL
   (DEFTHM MAP-TIMES-ZEROS-2
       (EQUAL (MAP-TIMES (DELTAS P) (REPEAT-N-TIMES (+ -1 (LEN P)) 0))
              (cdr (REPEAT-N-TIMES (LEN P) 0)))))

  (local
   (defthm cdr-repeat-n-times
       (equal (cdr (repeat-n-times n a))
              (if (zp n)
                  nil
                  (repeat-n-times (1- n) a)))
     :HINTS (("GOAL"
              :DO-NOT-INDUCT T
              :EXPAND ((repeat-n-times n a))))
     ))

  (LOCAL
   (DEFTHM sumlist-ZEROS
       (EQUAL (sumlist (cdr (REPEAT-N-TIMES n 0)))
              0)
     :hints (("Goal"
              :cases ((cdr (REPEAT-N-TIMES n 0)))))
     ))

  (local
   (defthm riemann-uv-prime-not-posp-context
       (implies (not (posp context))
                (equal (riemann-uv-prime context p)
                       0))
     :hints (("Goal" :do-not-induct t))
     ))

  (local (in-theory (disable riemann-uv-prime)))

  (local
   (defthm limited-riemann-uv-prime-small-partition-not-posp-context
       (implies (and (realp a) (standardp a)
		     (realp b) (standardp b)
                     (standardp context)
                     (not (posp context))
		     (inside-interval-p a (real-domain))
		     (inside-interval-p b (real-domain))
		     (< a b))
	        (i-limited (riemann-uv-prime context
                                             (make-small-partition a b))))
     :otf-flg t)
   )

  (local
   (defthm limited-riemann-uv-prime-small-partition
       (implies (and (realp a) (standardp a)
		     (realp b) (standardp b)
                     (standardp context)
		     (inside-interval-p a (real-domain))
		     (inside-interval-p b (real-domain))
		     (< a b))
	        (i-limited (riemann-uv-prime context
                                             (make-small-partition a b))))
     :otf-flg t
     :hints (("Goal"
              :use ((:instance limited-riemann-uv-prime-small-partition-posp-context)
                    (:instance limited-riemann-uv-prime-small-partition-not-posp-context)))))
   )


  (defun-std strict-int-uv-prime (context a b)
    (if (and (realp a)
	     (realp b)
	     (inside-interval-p a (bpfn-domain))
	     (inside-interval-p b (bpfn-domain))
	     (< a b))
        (standard-part (riemann-uv-prime context (make-small-partition a b)))
        0))
  )

(defun int-uv-prime (context a b)
  (if (<= a b)
      (strict-int-uv-prime context a b)
      (- (strict-int-uv-prime context b a))))

(encapsulate
    nil

    (defthm limited-riemann-u-plain*v-prime-small-partition-posp-context
     (implies (and (realp a) (standardp a)
		   (realp b) (standardp b)
                   (standardp context)
                   (posp context)
		   (inside-interval-p a (real-domain))
                   (inside-interval-p b (real-domain))
		   (< a b))
	      (i-limited (riemann-u-plain*v-prime context (make-small-partition a b))))
     :hints (("Goal"
	      :by (:functional-instance limited-riemann-bpfn-u-plain*v-prime-small-partition
				        (bpfn-domain real-domain)
                                        (BPFN-CAR-CONTEXT (lambda (context) (nfix context)))
                                        (BPFN-CdR-CONTEXT (lambda (context) (nfix context)))
				        (bpfn-u*v-prime uv-prime)
                                        (bpfn-u-prime u-prime)
                                        (bpfn-v-prime v-prime)
                                        (bpfn-u u-plain)
                                        (bpfn-v v-plain)
                                        (bpfn-u-plain*v-prime u-plain*v-prime)
				        (map-bpfn-u-plain*v-prime map-u-plain*v-prime)
				        (riemann-bpfn-u-plain*v-prime riemann-u-plain*v-prime))))
     )

  (local
   (defthm map-u-plain*v-prime-not-posp-context
       (implies (not (posp context))
                (equal (map-u-plain*v-prime context p)
                       (repeat-n-times (len p) 0)
                       ))))

  (LOCAL
   (DEFTHM MAP-TIMES-ZEROS
       (EQUAL (MAP-TIMES (DELTAS P) (cdr (REPEAT-N-TIMES (LEN P) 0)))
              (cdr (REPEAT-N-TIMES (LEN P) 0)))))

  (LOCAL
   (DEFTHM MAP-TIMES-ZEROS-2
       (EQUAL (MAP-TIMES (DELTAS P) (REPEAT-N-TIMES (+ -1 (LEN P)) 0))
              (cdr (REPEAT-N-TIMES (LEN P) 0)))))

  (local
   (defthm cdr-repeat-n-times
       (equal (cdr (repeat-n-times n a))
              (if (zp n)
                  nil
                  (repeat-n-times (1- n) a)))
     :HINTS (("GOAL"
              :DO-NOT-INDUCT T
              :EXPAND ((repeat-n-times n a))))
     ))

  (LOCAL
   (DEFTHM sumlist-ZEROS
       (EQUAL (sumlist (cdr (REPEAT-N-TIMES n 0)))
              0)
     :hints (("Goal"
              :cases ((cdr (REPEAT-N-TIMES n 0)))))
     ))

  (local
   (defthm riemann-u-PLAIN*v-prime-not-posp-context
       (implies (not (posp context))
                (equal (riemann-u-PLAIN*v-prime context p)
                       0))
     :hints (("Goal" :do-not-induct t))
     ))

  (local
   (in-theory (disable riemann-u-plain*v-prime)))

  (local
   (defthm limited-riemann-u-PLAIN*v-prime-small-partition-not-posp-context
       (implies (and (realp a) (standardp a)
		     (realp b) (standardp b)
                     (standardp context)
                     (not (posp context))
		     (inside-interval-p a (real-domain))
		     (inside-interval-p b (real-domain))
		     (< a b))
	        (i-limited (riemann-u-PLAIN*v-prime context
                                             (make-small-partition a b))))
     :otf-flg t)
   )

  (defthm limited-riemann-u-PLAIN*v-prime-small-partition
      (implies (and (realp a) (standardp a)
		    (realp b) (standardp b)
                    (standardp context)
		    (inside-interval-p a (real-domain))
		    (inside-interval-p b (real-domain))
		    (< a b))
	       (i-limited (riemann-u-PLAIN*v-prime context
                                                   (make-small-partition a b))))
    :otf-flg t
    :hints (("Goal"
             :use ((:instance limited-riemann-u-PLAIN*v-prime-small-partition-posp-context)
                   (:instance limited-riemann-u-PLAIN*v-prime-small-partition-not-posp-context)))))

  (defun-std strict-int-u-plain*v-prime (context a b)
    (if (and (realp a)
	     (realp b)
	     (inside-interval-p a (real-domain))
	     (inside-interval-p b (real-domain))
	     (< a b))
        (standard-part (riemann-u-plain*v-prime context (make-small-partition a b)))
        0))
  )


(defun int-u-plain*v-prime (context a b)
  (if (<= a b)
      (strict-int-u-plain*v-prime context a b)
      (- (strict-int-u-plain*v-prime context b a))))

(defun u-prime*v-plain (n x)
  (* (u-prime n x)
     (v-plain n x)))

(defun map-u-prime*v-plain (context p)
  (if (consp p)
      (cons (u-prime*v-plain context (car p))
            (map-u-prime*v-plain context (cdr p)))
      nil))

(defun riemann-u-prime*v-plain (context p)
  (dotprod (deltas p)
           (map-u-prime*v-plain context (cdr p))))

(encapsulate
    nil

    (local
     (defthm limited-riemann-u-prime*v-plain-small-partition-posp-context
         (implies (and (realp a) (standardp a)
		       (realp b) (standardp b)
                       (standardp context)
                       (posp context)
		       (inside-interval-p a (real-domain))
                       (inside-interval-p b (real-domain))
		       (< a b))
	          (i-limited (riemann-u-prime*v-plain context (make-small-partition a b))))
       :hints (("Goal"
	        :by (:functional-instance limited-riemann-bpfn-u-prime*v-plain-small-partition
				          (bpfn-domain real-domain)
                                          (BPFN-CAR-CONTEXT (lambda (context) (nfix context)))
                                          (BPFN-CdR-CONTEXT (lambda (context) (nfix context)))
				          (bpfn-u*v-prime uv-prime)
                                          (bpfn-u-prime u-prime)
                                          (bpfn-v-prime v-prime)
                                          (bpfn-u u-plain)
                                          (bpfn-v v-plain)
                                          (bpfn-u-prime*v-plain u-prime*v-plain)
				          (map-bpfn-u-prime*v-plain map-u-prime*v-plain)
				          (riemann-bpfn-u-prime*v-plain riemann-u-prime*v-plain))))
       ))

  (local
   (defthm map-u-prime*v-plain-not-posp-context
       (implies (not (posp context))
                (equal (map-u-prime*v-plain context p)
                       (repeat-n-times (len p) 0)
                       ))))

  (LOCAL
   (DEFTHM MAP-TIMES-ZEROS
       (EQUAL (MAP-TIMES (DELTAS P) (cdr (REPEAT-N-TIMES (LEN P) 0)))
              (cdr (REPEAT-N-TIMES (LEN P) 0)))))

  (LOCAL
   (DEFTHM MAP-TIMES-ZEROS-2
       (EQUAL (MAP-TIMES (DELTAS P) (REPEAT-N-TIMES (+ -1 (LEN P)) 0))
              (cdr (REPEAT-N-TIMES (LEN P) 0)))))

  (local
   (defthm cdr-repeat-n-times
       (equal (cdr (repeat-n-times n a))
              (if (zp n)
                  nil
                  (repeat-n-times (1- n) a)))
     :HINTS (("GOAL"
              :DO-NOT-INDUCT T
              :EXPAND ((repeat-n-times n a))))
     ))

  (LOCAL
   (DEFTHM sumlist-ZEROS
       (EQUAL (sumlist (cdr (REPEAT-N-TIMES n 0)))
              0)
     :hints (("Goal"
              :cases ((cdr (REPEAT-N-TIMES n 0)))))
     ))

  (local
   (defthm riemann-u-prime*v-plain-not-posp-context
       (implies (not (posp context))
                (equal (riemann-u-prime*v-plain context p)
                       0))
     :hints (("Goal" :do-not-induct t))
     ))

  (local
   (in-theory (disable riemann-u-prime*v-plain)))

  (local
   (defthm limited-riemann-u-prime*v-plain-small-partition-not-posp-context
       (implies (and (realp a) (standardp a)
		     (realp b) (standardp b)
                     (standardp context)
                     (not (posp context))
		     (inside-interval-p a (real-domain))
		     (inside-interval-p b (real-domain))
		     (< a b))
	        (i-limited (riemann-u-prime*v-plain context
                                             (make-small-partition a b))))
     :otf-flg t)
   )

  (local
   (defthm limited-riemann-u-prime*v-plain-small-partition
       (implies (and (realp a) (standardp a)
		     (realp b) (standardp b)
                     (standardp context)
		     (inside-interval-p a (real-domain))
		     (inside-interval-p b (real-domain))
		     (< a b))
	        (i-limited (riemann-u-prime*v-plain context
                                             (make-small-partition a b))))
     :otf-flg t
     :hints (("Goal"
              :use ((:instance limited-riemann-u-prime*v-plain-small-partition-posp-context)
                    (:instance limited-riemann-u-prime*v-plain-small-partition-not-posp-context)))))
   )

  (defun-std strict-int-u-prime*v-plain (context a b)
    (if (and (realp a)
	     (realp b)
	     (inside-interval-p a (real-domain))
	     (inside-interval-p b (real-domain))
	     (< a b))
        (standard-part (riemann-u-prime*v-plain context (make-small-partition a b)))
        0))
  )

(defun int-u-prime*v-plain (context a b)
  (if (<= a b)
      (strict-int-u-prime*v-plain context a b)
      (- (strict-int-u-prime*v-plain context b a))))

(defun uv (context x)
  (* (u-plain context x)
     (v-plain context x)))

(defthm integration-by-parts-wallis-integral
    (implies (and (inside-interval-p a (real-domain))
		  (inside-interval-p b (real-domain)))
	     (equal (int-u-plain*v-prime context a b)
                    (- (- (uv context b)
		          (uv context a))
                       (int-u-prime*v-plain context a b))))
  :hints (("Goal"
           :use ((:functional-instance integration-by-parts
				       (bpfn-domain real-domain)
                                       (BPFN-CAR-CONTEXT (lambda (context) (nfix context)))
                                       (BPFN-CdR-CONTEXT (lambda (context) (nfix context)))
				       (bpfn-u*v uv)
				       (bpfn-u*v-prime uv-prime)
                                       (bpfn-u-prime u-prime)
                                       (bpfn-v-prime v-prime)
                                       (bpfn-u u-plain)
                                       (bpfn-v v-plain)
                                       (bpfn-u-prime*v-plain u-prime*v-plain)
				       (map-bpfn-u-prime*v-plain map-u-prime*v-plain)
				       (riemann-bpfn-u-prime*v-plain
                                        riemann-u-prime*v-plain)
                                       (int-bpfn-u-plain*v-prime int-u-plain*v-prime)
                                       (int-bpfn-u-prime*v-plain
                                        int-u-prime*v-plain)
                                       (MAP-BPFN-U-PLAIN*V-PRIME MAP-U-PLAIN*V-PRIME)
				       (riemann-bpfn-u-plain*v-prime
                                        riemann-u-plain*v-prime)
                                       (BPFN-U-PLAIN*V-PRIME u-plain*v-prime)
                                       (strict-int-bpfn-u-plain*v-prime strict-int-u-plain*v-prime)
                                       (strict-int-bpfn-u-prime*v-plain strict-int-u-prime*v-plain)

                                       )))
          ))



(local
 (defthmd u-prime*v-plain-rewrite
     (implies (and (realp x)
                   (integerp n)
                   (<= 1 n))
              (equal (u-prime*v-plain n x)
                     (- (* (1- n) (expt-sine x (- n 2)) (expt (acl2-cosine x)
                                                              2)))))))

(local
 (defthmd u-prime*v-plain-rewrite-2
     (implies (and (realp x)
                   (integerp n)
                   (<= 1 n))
              (equal (u-prime*v-plain n x)
                     (- (* (1- n) (expt-sine x (- n 2))
                           (- 1 (expt (acl2-sine x) 2))))))
   :hints (("Goal"
            :INSTRUCTIONS ((:USE (:INSTANCE U-PRIME*V-PLAIN-REWRITE))
                           (:USE (:INSTANCE COS**2->1-SIN**2))
                           :PRO (:FORWARDCHAIN 2)
                           (:DV 1)
                           := :TOP
                           (:CLAIM (EQUAL (EXPT (ACL2-COSINE X) 2)
                                          (- 1 (EXPT (ACL2-SINE X) 2))))
                           (:DV 1)
                           (:DV 1)
                           (:DV 3)
                           :=
                           :TOP :S)))
   ))

(local
 (defthmd u-prime*v-plain-rewrite-3
     (implies (and (realp x)
                   (integerp n)
                   (<= 1 n))
              (equal (u-prime*v-plain n x)
                     (- (* (1- n) (expt-sine x n))
                        (* (1- n) (expt-sine x (- n 2))))))
   :hints (("Goal"
            :INSTRUCTIONS (:PRO (:USE (:INSTANCE U-PRIME*V-PLAIN-REWRITE-2))
                                :PRO (:FORWARDCHAIN 1)
                                (:DV 1)
                                := :TOP (:DROP 4)
                                :BASH)
            )
           )
   ))

(local
 (defthmd u-prime*v-plain-rewrite-4
     (implies (and (realp x)
                   (integerp n)
                   (< 2 n))
              (equal (u-prime*v-plain n x)
                     (- (* (1- n) (u-plain*v-prime n x))
                        (* (1- n) (u-plain*v-prime (- n 2) x)))))
   :hints (("Goal"
            :use ((:instance u-prime*v-plain-rewrite-3)
                  (:instance expt-sine-recursive-alternative (n n))
                  (:instance expt-sine-recursive-alternative (n (- n 2))))
            :in-theory (disable u-plain*v-prime
                                u-prime*v-plain
                                expt-sine)
            )
           )
   ))

;; (local
;;  (defthmd map-u-prime*v-plain-rewrite
;;      (implies (and (real-listp p)
;;                    (integerp n)
;;                    (< 2 n))
;;               (equal (map-u-prime*v-plain n p)
;;                      (- (* (1- n) (sumlist (map-u-plain*v-prime n p)))
;;                         (* (1- n) (sumlist (map-u-plain*v-prime (- n 2) p))))))o
;;      :instructions ((:in-theory (disable u-prime*v-plain u-plain*v-prime))
;;                  :induct :bash :pro (:forwardchain 2)
;;                  (:dv 1)

;;                  (:dv 1)
;;                  :x :up :x (:dv 2)
;;                  := (:drop 5)
;;                  :up :up (:dv 2)
;;                  (:dv 1)
;;                  (:dv 2)
;;                  (:dv 1)
;;                  :x :up :s :up
;;                  (:= (+ (* (+ -1 n) (u-plain*v-prime n (car p)))
;;                         (* (+ -1 n)
;;                            (sumlist (map-u-plain*v-prime n (cdr p))))))
;;                  :nx :up (:dv 2)
;;                  (:dv 1)
;;                  (:dv 2)
;;                  (:dv 1)
;;                  :x :up :x :up
;;                  (:= (+ (* (+ -1 n)
;;                            (u-plain*v-prime (+ -2 n) (car p)))
;;                         (* (+ -1 n)
;;                            (sumlist (map-u-plain*v-prime (+ -2 n)
;;                                                          (cdr p))))))
;;                  :up :up
;;                  (:= (+ (- (* (+ -1 n) (u-plain*v-prime n (car p)))
;;                            (* (+ -1 n)
;;                               (u-plain*v-prime (+ -2 n) (car p))))
;;                         (- (* (+ -1 n)
;;                               (sumlist (map-u-plain*v-prime n (cdr p))))
;;                            (* (+ -1 n)
;;                               (sumlist (map-u-plain*v-prime (+ -2 n)
;;                                                             (cdr p)))))))
;;                  :top
;;                  (:= (equal (u-prime*v-plain n (car p))
;;                             (+ (* (+ -1 n) (u-plain*v-prime n (car p)))
;;                                (- (* (+ -1 n)
;;                                      (u-plain*v-prime (+ -2 n) (car p)))))))
;;                  (:dv 1)
;;                  (:rewrite u-prime*v-plain-rewrite-4)
;;                  :top
;;                  :s :bash)))

(local
 (defthmd riemann-u-prime*v-plain-alternative
     (implies (real-listp p)
              (equal (riemann-u-prime*v-plain n p)
                     (if (and (consp p) (consp (cdr p)))
                         (+ (* (- (CADR P) (CAR P)) (u-prime*v-plain n (cadr p)))
                            (riemann-u-prime*v-plain n (cdr p)))
                         0)))))

(local
 (defthmd riemann-u-plain*v-prime-alternative
     (implies (real-listp p)
              (equal (riemann-u-plain*v-prime n p)
                     (if (and (consp p) (consp (cdr p)))
                         (+ (* (- (CADR P) (CAR P)) (u-plain*v-prime n (cadr p)))
                            (riemann-u-plain*v-prime n (cdr p)))
                         0)))))

(local
 (defthmd riemann-map-u-prime*v-plain-rewrite
     (implies (and (real-listp p)
                   (integerp n)
                   (< 2 n))
              (equal (riemann-u-prime*v-plain n p)
                     (- (* (1- n) (riemann-u-plain*v-prime n p))
                        (* (1- n) (riemann-u-plain*v-prime (- n 2) p)))))
   :instructions ((:induct (deltas p))
                  :bash :pro (:forwardchain 2)
                  (:dv 1)
                  (:rewrite riemann-u-prime*v-plain-alternative)
                  (:= (+ (* (+ (cadr p) (- (car p)))
                            (u-prime*v-plain n (cadr p)))
                         (riemann-u-prime*v-plain n (cdr p))))
                  :nx (:dv 1)
                  (:dv 2)
                  (:rewrite riemann-u-plain*v-prime-alternative)
                  (:= (+ (* (+ (cadr p) (- (car p)))
                            (u-plain*v-prime n (cadr p)))
                         (riemann-u-plain*v-prime n (cdr p))))
                  :up :nx (:dv 1)
                  (:dv 2)
                  (:rewrite riemann-u-plain*v-prime-alternative)
                  (:= (+ (* (+ (cadr p) (- (car p)))
                            (u-plain*v-prime (+ -2 n) (cadr p)))
                         (riemann-u-plain*v-prime (+ -2 n)
                                                  (cdr p))))
                  :top
                  (:in-theory (disable riemann-u-plain*v-prime
                                       riemann-u-prime*v-plain
                                       u-prime*v-plain u-plain*v-prime))
                  (:dv 1)
                  (:dv 1)
                  (:dv 2)
                  (:rewrite u-prime*v-plain-rewrite-4)
                  :top
                  :bash (:= t))))


(local
 (encapsulate
     nil

     (local
      (defthmd lemma-1
          (IMPLIES
           (IMPLIES
            (AND (REAL-LISTP (MAKE-SMALL-PARTITION A B))
                 (INTEGERP N)
                 (< 2 N))
            (EQUAL (RIEMANN-U-PRIME*V-PLAIN N (MAKE-SMALL-PARTITION A B))
                   (+ (* (+ -1 N)
                         (RIEMANN-U-PLAIN*V-PRIME N (MAKE-SMALL-PARTITION A B)))
                      (- (* (+ -1 N)
                            (RIEMANN-U-PLAIN*V-PRIME (+ -2 N)
                                                     (MAKE-SMALL-PARTITION A B)))))))
           (IMPLIES (AND (STANDARDP 2)
                         (STANDARDP N)
                         (STANDARDP B)
                         (STANDARDP A)
                         (REALP A)
                         (REALP B)
                         (< A B)
                         (INTEGERP N)
                         (< 2 N))
                    (EQUAL (STRICT-INT-U-PRIME*V-PLAIN N A B)
                           (+ (* (+ -1 N)
                                 (STRICT-INT-U-PLAIN*V-PRIME N A B))
                              (- (* (+ -1 N)
                                    (STRICT-INT-U-PLAIN*V-PRIME (+ -2 N)
                                                                A B)))))))
        :INSTRUCTIONS
        (:PRO
         (:FORWARDCHAIN 1)
         (:DV 1)
         (:IN-THEORY (DISABLE RIEMANN-U-PRIME*V-PLAIN))
         (:REWRITE STRICT-INT-U-PRIME*V-PLAIN)
         :S (:DV 1)
         (:REWRITE RIEMANN-MAP-U-PRIME*V-PLAIN-REWRITE)
         :UP (:REWRITE STANDARD-PART-OF-PLUS)
         (:DV 1)
         (:DV 1)
         (:= (* (+ -1 N)
                (RIEMANN-U-PLAIN*V-PRIME N (MAKE-SMALL-PARTITION A B))))
         :UP (:REWRITE STANDARD-PART-OF-TIMES)
         (:DV 1)
         (:= (+ -1 N))
         :NX :UP :NX (:DV 1)
         (:= (- (* (+ -1 N)
                   (RIEMANN-U-PLAIN*V-PRIME (+ -2 N)
                                            (MAKE-SMALL-PARTITION A B)))))
         :UP (:REWRITE STANDARD-PART-OF-UMINUS)
         (:DV 1)
         (:DV 1)
         (:= (* (+ -1 N)
                (RIEMANN-U-PLAIN*V-PRIME (+ -2 N)
                                         (MAKE-SMALL-PARTITION A B))))
         :UP (:REWRITE STANDARD-PART-OF-TIMES)
         (:DV 1)
         (:= (+ -1 N))
         :UP :TOP :BASH :BASH
         (:USE
          (:INSTANCE LIMITED-RIEMANN-U-PLAIN*V-PRIME-SMALL-PARTITION-POSP-CONTEXT
                     (CONTEXT (+ -2 N))))
         :BASH
         :BASH
         (:USE
          (:INSTANCE LIMITED-RIEMANN-U-PLAIN*V-PRIME-SMALL-PARTITION-POSP-CONTEXT
                     (CONTEXT N)))
         :BASH :BASH)))

   (defthm-std strict-int-prime*v-plain-rewrite
       (implies (and (realp a)
                     (realp b)
                     (< a b)
                     (integerp n)
                     (< 2 n))
                (equal (strict-int-u-prime*v-plain n a b)
                       (- (* (1- n) (strict-int-u-plain*v-prime n a b))
                          (* (1- n) (strict-int-u-plain*v-prime (- n 2) a b)))))
     :hints (("goal'"
              :use ((:instance lemma-1)
                    (:instance riemann-map-u-prime*v-plain-rewrite
                               (p (make-small-partition a b))))
              :in-theory (disable strict-int-u-prime*v-plain strict-int-u-plain*v-prime)))))
 )

(local
 (defthm-std STRICT-INT-U-PLAIN*V-PRIME-a-a
     (implies (and (realp a)
                   (natp n))
              (equal (strict-int-u-plain*v-prime n a a) 0))
   ))

(local
 (defthm-std STRICT-INT-U-prime*V-plain-a-a
     (implies (and (realp a)
                   (natp n))
              (equal (strict-int-u-prime*v-plain n a a) 0))
   ))

(local
 (defthm int-map-u-prime*v-plain-rewrite
     (implies (and (realp a)
                   (realp b)
                   (integerp n)
                   (< 2 n))
              (equal (int-u-prime*v-plain n a b)
                     (- (* (1- n) (int-u-plain*v-prime n a b))
                        (* (1- n) (int-u-plain*v-prime (- n 2) a b)))))
   :hints (("Goal"
            :use ((:instance strict-int-prime*v-plain-rewrite (a b) (b a))
                  (:instance strict-int-prime*v-plain-rewrite (a a) (b b)))
            :in-theory (disable strict-int-u-prime*v-plain
                                strict-int-u-plain*v-prime
                                STRICT-INT-PRIME*V-PLAIN-REWRITE
                                INTEGRATION-BY-PARTS-WALLIS-INTEGRAL)))))



(local
 (defthmd integration-by-parts-wallis-integral-2
     (implies (and (realp a)
                   (realp b)
                   (integerp n)
                   (< 2 n))
	      (equal (int-u-plain*v-prime n a b)
                     (- (- (uv n b)
		           (uv n a))
                        (- (* (1- n) (int-u-plain*v-prime n a b))
                           (* (1- n) (int-u-plain*v-prime (- n 2) a b))))))
   :hints (("Goal"
            :use ((:instance integration-by-parts-wallis-integral (context n))
                  (:instance int-map-u-prime*v-plain-rewrite))
            :in-theory (disable integration-by-parts-wallis-integral
                                int-map-u-prime*v-plain-rewrite
                                int-u-plain*v-prime
                                int-u-prime*v-plain
                                uv)))))

(defun map-expt-sine (n p)
  (if (consp p)
      (cons (expt-sine (car p) n)
            (map-expt-sine n (cdr p)))
      nil)
  )

(defun riemann-expt-sine (context p)
  (dotprod (deltas p)
           (map-expt-sine context (cdr p))))

(local
 (defthm rewrite-map-expt-sine-posp-n
     (implIes (and (real-listp p)
                   (posp n))
              (equal (map-expt-sine n p)
                     (map-u-plain*v-prime n p)))
   :hints (("Goal"
            :in-theory (disable expt-sine u-plain*v-prime))
           ("Subgoal *1/2"
            :use ((:instance expt-sine-recursive-alternative (x (car p))))))
   ))

(local
 (defthm rewrite-riemann-expt-sine-posp-n-lemma
     (implIes (and (real-listp p)
                   (posp n))
              (equal (riemann-expt-sine n p)
                     (riemann-u-plain*v-prime n p)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (disable map-expt-sine
                                map-u-plain*v-prime)))
   ))

(local
 (defthm rewrite-riemann-expt-sine-posp-n
     (implies (and (posp n)
                   (realp a)
                   (realp b)
                   (< a b)
                   )
              (equal (riemann-expt-sine n (make-small-partition a b))
                     (riemann-u-plain*v-prime n (make-small-partition a b))))
   ))


(local
 (encapsulate
     nil

  (local
   (defthm lemma-1
       (implies (not (posp n))
                (equal (UV-PRIME n x)
                       0))))

  (local
   (defthm lemma-2
       (implies (not (posp n))
                (equal (map-expt-sine n p)
                       (repeat-n-times (len p) 1)))))

  (local
   (defthm lemma-3
       (implies (and (not (posp n))
                     (consp p)
                     )
                (equal (riemann-expt-sine n p)
                       (- (car (last p)) (car p))))
     :hints (("Goal"
              :induct (deltas p)))
     ))

  (defthm rewrite-riemann-expt-sine-not-posp-n
       (implies (and (not (posp n))
                     (realp a)
                     (realp b)
                     (< a b)
                     )
                (equal (riemann-expt-sine n (make-small-partition a b))
                       (- b a)))
    )
  )

 )


(defthm limited-riemann-expt-sine-small-partition
    (implies (and (realp a)
                  (standardp a)
                  (realp b)
                  (standardp b)
                  (standardp n)
                  (< a b))
             (i-limited (riemann-expt-sine n (make-small-partition a b))))
  :hints (("Goal"
           :use ((:instance rewrite-riemann-expt-sine-not-posp-n)
                 (:instance rewrite-riemann-expt-sine-posp-n)
                 (:instance limited-riemann-u-plain*v-prime-small-partition-posp-context
                            (context n)))
           :in-theory (disable RIEMANN-EXPT-SINE
                               RIEMANN-U-PLAIN*V-PRIME))

          ))

(local (in-theory (disable riemann-expt-sine)))

(defun-std strict-int-expt-sine (n a b)
  (if (and (realp a)
	   (realp b)
	   (inside-interval-p a (real-domain))
	   (inside-interval-p b (real-domain))
	   (< a b))
      (standard-part (riemann-expt-sine n (make-small-partition a b)))
      0))

(defun int-expt-sine (n a b)
  (if (<= a b)
      (strict-int-expt-sine n a b)
      (- (strict-int-expt-sine n b a))))

(defthm-std rewrite-int-expt-sine-posp-n
     (implies (and (posp n)
                   (realp a)
                   (realp b)
                   )
              (equal (int-expt-sine n a b)
                     (int-u-plain*v-prime n a b)))
  :hints (("Goal"
           :in-theory (disable riemann-expt-sine
                               riemann-u-plain*v-prime
                               STRICT-INT-U-PRIME*V-PLAIN
                               INTEGRATION-BY-PARTS-WALLIS-INTEGRAL))))

(defthmd integration-by-parts-wallis-integral-3
    (implies (and (realp a)
                  (realp b)
                  (integerp n)
                  (< 2 n))
	     (equal (int-expt-sine n a b)
                    (- (- (uv n b)
		          (uv n a))
                       (- (* (1- n) (int-expt-sine n a b))
                          (* (1- n) (int-expt-sine (- n 2) a b))))))
  :hints (("Goal"
           :use ((:instance integration-by-parts-wallis-integral-2)
                 (:instance rewrite-int-expt-sine-posp-n (n n))
                 (:instance rewrite-int-expt-sine-posp-n (n (- n 2))))
           :in-theory (disable integration-by-parts-wallis-integral
                               int-expt-sine
                               uv
                               int-u-plain*v-prime))))

(defun wallis-integral (n)
  (int-expt-sine n 0 (acl2-pi)))

(local
 (defthm uv-0
     (implies (and (integerp n)
                   (<= 2 n))
              (equal (uv n 0) 0))))

(local
 (defthm uv-pi
     (implies (and (integerp n)
                   (<= 2 n))
              (equal (uv n (acl2-pi)) 0))))


(local
 (defthmd wallis-integral-recursion-lemma
     (implies (and (integerp n)
                   (< 2 n))
	      (equal (wallis-integral n)
                     (- (* (1- n) (wallis-integral (- n 2)))
                        (* (1- n) (wallis-integral n)))))
   :hints (("Goal"
            :use ((:instance integration-by-parts-wallis-integral-3
                             (a 0)
                             (b (acl2-pi))))
            :in-theory (disable integration-by-parts-wallis-integral-3
                                int-expt-sine
                                uv
                                REWRITE-INT-EXPT-SINE-POSP-N)))))

(local
 (defthmd wallis-integral-recursion-lemma-2
     (implies (and (integerp n)
                   (< 2 n))
	      (equal (+ (wallis-integral n)
                        (* (1- n) (wallis-integral n)))
                     (* (1- n) (wallis-integral (- n 2)))))
   :hints (("Goal"
            :use ((:instance wallis-integral-recursion-lemma))
            :in-theory (disable wallis-integral
                                )))))

(local
 (defthmd wallis-integral-recursion-lemma-3
     (implies (and (integerp n)
                   (< 2 n))
	      (equal (* n (wallis-integral n))
                     (* (1- n) (wallis-integral (- n 2)))))
   :hints (("Goal"
            :use ((:instance wallis-integral-recursion-lemma-2))
            :in-theory (disable wallis-integral
                                )))))

(local
 (encapsulate
     nil

     (local
      (defthm lemma-1
          (implies (and (acl2-numberp x)
                        (acl2-numberp y)
                        (acl2-numberp z)
                        (not (equal x 0))
                        (equal (* x y) z))
                   (equal y (* z (/ x))))
        :rule-classes nil))

   (defthmd wallis-integral-recursion-for-2<n
       (implies (and (integerp n)
                     (< 2 n))
	        (equal (wallis-integral n)
                       (* (1- n) (/ n) (wallis-integral (- n 2)))))
     :hints (("Goal"
              :use ((:instance wallis-integral-recursion-lemma-3)
                    (:instance lemma-1
                               (x n)
                               (y (wallis-integral n))
                               (z (* (1- n) (wallis-integral (- n 2))))))
              :in-theory (disable wallis-integral
                                  ))))

   ))

(local
 (defthm-std standard-pi
     (standardp (acl2-pi))))

(defthmd wallis-integral-0
    (equal (wallis-integral 0) (acl2-pi)))

(local
 (defun expt-sine-1-antiderivative (x)
   (if (realp x)
       (- (acl2-cosine x))
       0)))

(local
 (defthm expt-sine-1-antiderivative-works
      (implies (and (acl2-numberp x)
                    (acl2-numberp y)
                    (standardp x)
                    (realp x)
                    (realp y)
                    (i-close x y)
                    (not (equal x y)))
               (i-close (/ (- (expt-sine-1-antiderivative x)
                              (expt-sine-1-antiderivative y))
                           (- x y))
                        (expt-sine x 1)))
   :hints (("Goal"
            :use ((:instance acl2-cosine-derivative)
                  (:instance close-uminus
                             (x (+ (* (ACL2-COSINE X) (/ (+ X (- Y))))
                                   (- (* (ACL2-COSINE Y) (/ (+ X (- Y)))))))
                             (y (- (ACL2-SINE X))))
                  )
            ))
   )
 )

(defthmd wallis-integral-1
    (equal (wallis-integral 1) 2)
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance ftc-2
                                        (rcdfn (lambda (context x)
                                                 (expt-sine-1-antiderivative x)))
                                        (rcdfn-prime (lambda (context x)
                                                       (expt-sine x 1)))
                                        (rcdfn-domain real-domain)
                                        (map-rcdfn-prime (lambda (context p)
                                                           (map-expt-sine 1 p)))
                                        (riemann-rcdfn-prime (lambda (context p)
                                                               (riemann-expt-sine 1 p)))
                                        (strict-int-rcdfn-prime
                                         (lambda (context a b)
                                           (strict-int-expt-sine 1 a b)))
                                        (int-rcdfn-prime
                                         (lambda (context a b)
                                           (int-expt-sine 1 a b)))
                                        )
                  (a 0)
                  (b (acl2-pi))
                  ))
           :in-theory (disable ftc-2
                               expt-sine))
          ("Subgoal 5"
           :use ((:instance expt-sine-1-antiderivative-works (y x1))))
          ("Subgoal 2"
           :expand ((RIEMANN-EXPT-SINE 1 P)))
          ))

(local
 (defun expt-sine-2-antiderivative (x)
   (if (realp x)
       (* 1/2 (- x (* (acl2-sine x) (acl2-cosine x))))
       0)))


(local
 (defthmd expt-sine-2-antiderivative-works-part1
     (implies (and (realp x)
                   (realp x1)
                   (not (equal x x1)))
              (equal (- (/ x 2) (/ x1 2))
                     (* 1/2 (- x x1))))
   ))

(local
 (defthm expt-sine-2-antiderivative-works-part2
     (implies (and (realp x)
                   (standardp x)
                   (realp x1)
                   (i-close x x1)
                   (not (equal x x1)))
              (i-close (/ (- (/ x 2) (/ x1 2)) (- x x1))
                       1/2))
   :instructions ((:use (:instance expt-sine-2-antiderivative-works-part1))
                  :pro (:forwardchain 1)
                  (:dv 1)
                  (:dv 1)
                  (:= (* 1/2 (+ x (- x1))))
                  (:drop 6)
                  :up (:= 1/2)
                  :up :s)))




(local
 (defthm rewrite-/-eps
     (implies (and (realp x)
                   (realp x1)
                   (not (equal x x1)))
              (= (/ (+ (- x) x1))
                 (- (/ (+ x (- x1))))))
   :INSTRUCTIONS (:PRO (:DV 1)
                       (:DV 1)
                       (:= (- (- X X1)))
                       :UP (:REWRITE |(/ (- x))| NIL T)
                       :UP :S)
   ))

(local
 (defthm close-x-x+/-i-large-integer
     (implies (realp x)
              (i-close x (+ (/ (i-large-integer)) x)))
   :hints (("Goal"
            :in-theory (enable i-close)))))


(local
 (defthm expt-sine-2-antiderivative-works-part3
     (implies (and (realp x)
                   (standardp x)
                   (realp x1)
                   (i-close x x1)
                   (not (equal x x1)))
              (i-limited (+ (* (ACL2-COSINE X)
                               (ACL2-SINE X)
                               (/ (+ X (- X1))))
                            (- (* (ACL2-COSINE X1)
                                  (ACL2-SINE X1)
                                  (/ (+ X (- X1))))))))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance differential-dc-fn1*fn2-limited
                                         (dc-fn-domain real-domain)
                                         (dc-fn1 (lambda (context x)
                                                   (acl2-sine (REALFIX x))))
                                         (dc-fn2 (lambda (context x)
                                                   (acl2-cosine (REALFIX x))))
                                         (differential-dc-fn1
                                          (lambda (context x eps)
                                            (/ (- (acl2-sine (+ x eps))
                                                  (acl2-sine x))
                                               eps)))
                                         (differential-dc-fn2
                                          (lambda (context x eps)
                                            (/ (- (acl2-cosine (+ x eps))
                                                  (acl2-cosine x))
                                               eps)))
                                         (derivative-dc-fn1
                                          (lambda (context x)
                                            (acl2-cosine x)))
                                         (derivative-dc-fn2
                                          (lambda (context x)
                                            (- (acl2-sine x))))
                                         (dc-fn1*fn2
                                          (lambda (context x)
                                            (* (acl2-sine x) (acl2-cosine x))))
                                         (differential-dc-fn1*fn2
                                          (lambda (context x eps)
                                            (/ (- (* (acl2-sine (+ x eps))
                                                     (acl2-cosine (+ x eps)))
                                                  (* (acl2-sine x)
                                                     (acl2-cosine x)))
                                               eps)))
                                         (derivative-dc-fn1*fn2
                                          (lambda (context x)
                                            (- (* (acl2-cosine x) (acl2-cosine x))
                                               (* (acl2-sine x) (acl2-sine x)))))
                                         ;;;
                                         (dc-fnz (lambda (context x) 1))
                                         (differential-dc-fnz (lambda (context x eps) 0))
                                         (derivative-dc-fnz (lambda (context x) 0))
                                         )
                   (context 0)
                   (eps (- x1 x))
                   )))
           ("Subgoal 8"
            :use ((:instance acl2-sine-derivative
                             (y (+ x (/ (i-large-integer)))))
                  )
            :in-theory (e/d (i-close i-small)
                            ())
            )
           ("Subgoal 6"
            :use ((:instance acl2-cosine-differentiable))
            :in-theory (disable acl2-cosine-differentiable))
           ("Subgoal 5"
            :use ((:instance acl2-sine-differentiable))
            :in-theory (disable acl2-sine-differentiable))
           ("Subgoal 4"
            :use ((:instance acl2-cosine-derivative
                             (y (+ x (/ (i-large-integer))))))
            :in-theory (e/d (i-close i-small)
                            ())
            )
           )))


(local
 (defthm expt-sine-2-antiderivative-works-part4
     (implies (and (realp x)
                   (standardp x)
                   (realp x1)
                   (i-close x x1)
                   (not (equal x x1)))
              (i-close (/ (- (* (acl2-sine x) (acl2-cosine x))
                             (* (acl2-sine x1) (acl2-cosine x1)))
                          (- x x1))
                       (- (* (acl2-cosine x) (acl2-cosine x))
                          (* (acl2-sine x) (acl2-sine x)))))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance differential-dc-fn1*fn2-close
                                         (dc-fn-domain real-domain)
                                         (dc-fn1 (lambda (context x)
                                                   (acl2-sine (REALFIX x))))
                                         (dc-fn2 (lambda (context x)
                                                   (acl2-cosine (REALFIX x))))
                                         (differential-dc-fn1
                                          (lambda (context x eps)
                                            (/ (- (acl2-sine (+ x eps))
                                                  (acl2-sine x))
                                               eps)))
                                         (differential-dc-fn2
                                          (lambda (context x eps)
                                            (/ (- (acl2-cosine (+ x eps))
                                                  (acl2-cosine x))
                                               eps)))
                                         (derivative-dc-fn1
                                          (lambda (context x)
                                            (acl2-cosine x)))
                                         (derivative-dc-fn2
                                          (lambda (context x)
                                            (- (acl2-sine x))))
                                         (dc-fn1*fn2
                                          (lambda (context x)
                                            (* (acl2-sine x) (acl2-cosine x))))
                                         (differential-dc-fn1*fn2
                                          (lambda (context x eps)
                                            (/ (- (* (acl2-sine (+ x eps))
                                                     (acl2-cosine (+ x eps)))
                                                  (* (acl2-sine x)
                                                     (acl2-cosine x)))
                                               eps)))
                                         (derivative-dc-fn1*fn2
                                          (lambda (context x)
                                            (- (* (acl2-cosine x) (acl2-cosine x))
                                               (* (acl2-sine x) (acl2-sine x)))))
                                         ;;;
                                         (dc-fnz (lambda (context x) 1))
                                         (differential-dc-fnz (lambda (context x eps) 0))
                                         (derivative-dc-fnz (lambda (context x) 0))
                                         )
                   (context 0)
                   (eps (- x1 x))
                   ))
            :in-theory (disable standard-part-of-plus))
           ("Subgoal 1100"
            :use ((:instance CLOSE-IF-SAME-STANDARD-PART
                             (x (+ (* (ACL2-COSINE X)
                                      (ACL2-SINE X)
                                      (/ (+ X (- X1))))
                                   (- (* (ACL2-COSINE X1)
                                         (ACL2-SINE X1)
                                         (/ (+ X (- X1)))))))
                             (y (+ (EXPT (ACL2-COSINE X) 2)
                                   (- (EXPT (ACL2-SINE X) 2))))
                             )
                  (:instance standard-part-of-uminus
                             (x (* (ACL2-COSINE X)
                                   (ACL2-SINE X)
                                   (/ (+ X (- X1))))))
                             )
            :in-theory (disable CLOSE-IF-SAME-STANDARD-PART)
            )
           ("Subgoal 1000"
            :use ((:instance close-if-same-standard-part
                              (x (acl2-cosine x))
                              (y (* (+ (ACL2-SINE (+ X (/ (I-LARGE-INTEGER))))
                                       (- (ACL2-SINE X)))
                                    (/ (/ (I-LARGE-INTEGER))))))
                   ))

           )
      ))

(local
 (defthm expt-sine-2-antiderivative-works-part5
     (implies (and (realp x)
                   (standardp x)
                   (realp x1)
                   (i-close x x1)
                   (not (equal x x1)))
              (i-close (/ (- (* (acl2-sine x) (acl2-cosine x))
                             (* (acl2-sine x1) (acl2-cosine x1)))
                          (- x x1))
                       (- 1
                          (* 2 (acl2-sine x) (acl2-sine x)))))
   :INSTRUCTIONS ((:USE (:INSTANCE EXPT-SINE-2-ANTIDERIVATIVE-WORKS-PART4))
                  (:USE (:INSTANCE COS**2->1-SIN**2))
                  :PRO (:FORWARDCHAIN 2)
                  (:CONTRAPOSE 7)
                  (:DV 1)
                  (:DV 2)
                  (:DV 1)
                  :=
                  :UP (:= (+ 1
                             (- (* 2 (ACL2-SINE X) (ACL2-SINE X)))))
                  :TOP :S)))

(local
 (defthm close-plus
   (implies (and (i-close x1 x2)
		 (i-close y1 y2))
	    (i-close (+ x1 y1) (+ x2 y2)))
   :hints (("Goal"
	    :use ((:instance i-small-plus
			     (x (+ x1 (- x2)))
			     (y (+ y1 (- y2)))))
	    :in-theory '(i-close
			 associativity-of-+
			 commutativity-of-+
			 commutativity-2-of-+
			 distributivity-of-minus-over-+
			 )))))

(local
 (defthm expt-sine-2-antiderivative-works
     (implies (and (realp x)
                   (standardp x)
                   (realp x1)
                   (i-close x x1)
                   (not (equal x x1)))
              (i-close (/ (- (expt-sine-2-antiderivative x)
                             (expt-sine-2-antiderivative x1))
                          (- x x1))
                       (* (acl2-sine x) (acl2-sine x))))
   :INSTRUCTIONS
   ((:USE (:INSTANCE EXPT-SINE-2-ANTIDERIVATIVE-WORKS-PART2))
    (:USE (:INSTANCE EXPT-SINE-2-ANTIDERIVATIVE-WORKS-PART5))
    (:USE (:INSTANCE CLOSE-PLUS
                     (X1 (/ (- (/ X 2) (/ X1 2)) (- X X1)))
                     (X2 1/2)
                     (Y1 (* -1/2
                            (- (* (ACL2-SINE X) (ACL2-COSINE X))
                               (* (ACL2-SINE X1) (ACL2-COSINE X1)))
                            (/ (- X X1))))
                     (Y2 (+ -1/2 (* (ACL2-SINE X) (ACL2-SINE X))))))
    :PRO (:FORWARDCHAIN 2)
    (:FORWARDCHAIN 2)
    (:USE EXPT-SINE-2-ANTIDERIVATIVE-WORKS-PART3)
    :PRO (:FORWARDCHAIN 1)
    (:DEMOTE 1)
    (:DV 1)
    (:DV 1)
    (:= (I-CLOSE (* -1/2
                    (+ (* (ACL2-SINE X) (ACL2-COSINE X))
                       (- (* (ACL2-SINE X1) (ACL2-COSINE X1))))
                    (/ (+ X (- X1))))
                 (+ -1/2 (* (ACL2-SINE X) (ACL2-SINE X)))))
    (:DV 2)
    (:= (* -1/2
           (- 1 (* 2 (ACL2-SINE X) (ACL2-SINE X)))))
    :UP (:REWRITE CLOSE-TIMES-2)
    (:CHANGE-GOAL NIL T)
    :BASH :BASH :BASH :UP
    (:= (I-CLOSE (+ (* (+ (* X (/ 2)) (- (* X1 (/ 2))))
                       (/ (+ X (- X1))))
                    (* -1/2
                       (+ (* (ACL2-SINE X) (ACL2-COSINE X))
                          (- (* (ACL2-SINE X1) (ACL2-COSINE X1))))
                       (/ (+ X (- X1)))))
                 (+ 1/2
                    -1/2 (* (ACL2-SINE X) (ACL2-SINE X)))))
    (:DV 2)
    (:= (* (ACL2-SINE X) (ACL2-SINE X)))
    :TOP :PRO (:DV 1)
    (:= (+ (* (+ (* X (/ 2)) (- (* X1 (/ 2))))
              (/ (+ X (- X1))))
           (* -1/2
              (+ (* (ACL2-SINE X) (ACL2-COSINE X))
                 (- (* (ACL2-SINE X1) (ACL2-COSINE X1))))
              (/ (+ X (- X1))))))
    :TOP (:= T))))


(defthmd wallis-integral-2
    (equal (wallis-integral 2) (/ (acl2-pi) 2))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance ftc-2
                                        (rcdfn (lambda (context x)
                                                 (expt-sine-2-antiderivative x)))
                                        (rcdfn-prime (lambda (context x)
                                                       (expt-sine x 2)))
                                        (rcdfn-domain real-domain)
                                        (map-rcdfn-prime (lambda (context p)
                                                           (map-expt-sine 2 p)))
                                        (riemann-rcdfn-prime (lambda (context p)
                                                               (riemann-expt-sine 2 p)))
                                        (strict-int-rcdfn-prime
                                         (lambda (context a b)
                                           (strict-int-expt-sine 2 a b)))
                                        (int-rcdfn-prime
                                         (lambda (context a b)
                                           (int-expt-sine 2 a b)))
                                        )
                  (a 0)
                  (b (acl2-pi))
                  ))
           :in-theory (disable ftc-2
                               expt-sine))
          ("Subgoal 5"
           :use ((:instance expt-sine-2-antiderivative-works))
           :in-theory (enable expt-sine))
          ("Subgoal 2"
           :expand ((RIEMANN-EXPT-SINE 2 P)))
          ))

(defthmd wallis-integral-recursion
       (implies (and (integerp n)
                     (<= 2 n))
	        (equal (wallis-integral n)
                       (* (1- n) (/ n) (wallis-integral (- n 2)))))
  :hints (("Goal"
           :use ((:instance wallis-integral-recursion-for-2<n)
                 (:instance wallis-integral-2)
                 (:instance wallis-integral-0))
           :in-theory (disable wallis-integral-recursion-for-2<n
                               wallis-integral-2
                               wallis-integral-0))))




(local
 (defthm sine-bound
   (implies (realp x)
	    (and (<= -1 (acl2-sine x))
		 (<= (acl2-sine x) 1)))
   :hints (("Goal"
	    :use ((:instance sine-<-1-if-cosine-non-0)
		  (:instance sin**2+cos**2))
	    :in-theory (disable sine-<-1-if-cosine-non-0 sin**2+cos**2)))))

(local
 (defthm sine-bound-0-pi
     (implies (and (realp x)
                   (<= 0 x)
                   (<= x (acl2-pi)))
	      (and (<= 0 (acl2-sine x))
		   (<= (acl2-sine x) 1)))
   :hints (("Goal"
	    :use ((:instance sine-bound)
                  (:instance sine-positive-in-0-pi/2)
                  (:instance sine-positive-in-pi/2-pi))
	    :in-theory (disable sine-bound
                                sine-positive-in-0-pi/2
                                sine-positive-in-pi/2-pi)))))

(local
 (defthm sine-bound-0-pi
     (implies (and (realp x)
                   (<= 0 x)
                   (<= x (acl2-pi)))
	      (and (<= 0 (acl2-sine x))
		   (<= (acl2-sine x) 1)))
   :hints (("Goal"
	    :use ((:instance sine-bound)
                  (:instance sine-positive-in-0-pi/2)
                  (:instance sine-positive-in-pi/2-pi))
	    :in-theory (disable sine-bound
                                sine-positive-in-0-pi/2
                                sine-positive-in-pi/2-pi)))))

(local
 (defthm expt-sine-decreasing
     (implies (and (natp n)
                   (realp x)
                   (<= 0 x)
                   (<= x (acl2-pi)))
              (<= (expt-sine x (1+ n))
                  (expt-sine x n)))))

(local
 (defthm expt-sine-bound
     (implies (and (natp n)
                   (realp x)
                   (<= 0 x)
                   (<= x (acl2-pi)))
              (and (<= 0 (expt-sine x n))
                   (<= (expt-sine x n) 1)))))

(local
 (defun all-in-range (a b p)
   (if (consp p)
       (and (realp (car p))
            (<= a (car p))
            (<= (car p) b)
            (all-in-range a b (cdr p)))
       t)))

(local
 (defthm car-make-partition-rec
     (implies (not (zp n))
              (equal (car (make-partition-rec a b n))
                     a))))

(local
 (defthm in-range-for-bigger-interval
     (implies (and (all-in-range a1 b1 xs)
                   (<= a a1)
                   (<= b1 b))
              (all-in-range a b xs))))

(local
 (defthm make-partition-rec-in-range
     (implies (and (realp a)
                   (realp eps)
                   (<= 0 eps)
                   (natp n))
              (all-in-range a (+ a (* n eps)) (make-partition-rec a eps n)))))

(local
 (defthm make-partition-in-range
     (implies (and (realp a)
                   (realp b)
                   (<= a b)
                   (natp n))
              (all-in-range a b (make-partition a b n)))
   :hints (("Goal"
            :use ((:instance make-partition-rec-in-range
                             (eps (/ (- b a) n))))
            :in-theory (disable make-partition-rec-in-range)))
   ))

(local
 (defthm make-small-partition-in-range
     (implies (and (realp a)
                   (realp b)
                   (<= a b))
              (all-in-range a b (make-small-partition a b)))
   :hints (("Goal"
            :use ((:instance make-partition-in-range
                             (n (i-large-integer))))
            :in-theory (e/d (make-small-partition)
                            (make-partition-in-range
                             make-partition))))
   ))

(local
 (defun pairwise-<= (xs ys)
   (if (consp xs)
       (and (<= (car xs) (car ys))
            (pairwise-<= (cdr xs) (cdr ys)))
       t)))

(local
 (defthm acl2-number-car-all-in-range
     (implies (and (all-in-range a b p)
                   (realp a)
                   (realp b))
              (equal (acl2-numberp (car p))
                     (consp p)))))

(local
 (defthm pairwise-<=-map-expt-prime
     (implies (and (all-in-range 0 (acl2-pi) p)
                   (natp n))
              (pairwise-<= (map-expt-sine (1+ n) p)
                           (map-expt-sine n p)))
   :hints (("Goal"
            :in-theory (disable expt-sine)))
   ))

(local
 (defun all-non-negative (xs)
   (if (consp xs)
       (and (realp (car xs))
            (<= 0 (car xs))
            (all-non-negative (cdr xs)))
       t)))

(local
 (defun non-decreasing-list (xs)
   (if (consp xs)
       (if (consp (cdr xs))
           (and (realp (car xs))
                (realp (cadr xs))
                (<= (car xs) (cadr xs))
                (non-decreasing-list (cdr xs)))
           t)
       t)))

(local
 (defthm non-negative-deltas
     (implies (non-decreasing-list xs)
              (all-non-negative (deltas xs)))))

(local
 (defthm map-times-pairwise-<=
     (implies (and (pairwise-<= xs ys)
                   (all-non-negative deltas)
                   (<= (len deltas) (len xs))
                   )
              (pairwise-<= (map-times deltas xs)
                           (map-times deltas ys)))))

(local
 (defthm sumlist-pairwise-<=
     (implies (and (pairwise-<= xs ys)
                   (equal (len xs) (len ys)))
              (<= (sumlist xs) (sumlist ys)))))

(local
 (defthm map-times-pairwise-<=
     (implies (and (pairwise-<= xs ys)
                   (all-non-negative deltas)
                   (<= (len deltas) (len xs))
                   )
              (pairwise-<= (map-times deltas xs)
                           (map-times deltas ys)))))


(local
 (defthm len-map-times
     (equal (len (map-times xs ys))
            (len xs))))

(local
 (defthm len-deltas
     (equal (len (deltas xs))
            (if (consp xs)
                (1- (len xs))
                0))))

(local
 (defthm dotproduct-pairwise-<=
     (implies (and (non-decreasing-list p)
                   (pairwise-<= xs ys)
                   (<= (len (deltas p)) (len xs))
                   (equal (len xs) (len ys)))
              (<= (dotprod (deltas p) xs)
                  (dotprod (deltas p) ys)))
   :hints (("Goal"
            :use ((:instance sumlist-pairwise-<=
                             (xs (map-times (deltas p) xs))
                             (ys (map-times (deltas p) ys)))
                  (:instance map-times-pairwise-<=
                             (deltas (deltas p)))
                  )
            :in-theory (disable sumlist-pairwise-<=
                                map-times-pairwise-<=
                                expt-sine)
            )
           )
   ))

(local
 (defthm len-map-expt-sine
     (equal (len (map-expt-sine n p))
            (len p))))

(local
 (defthm riemann-expt-sine-decreasing
     (implies (and (all-in-range 0 (acl2-pi) p)
                   (non-decreasing-list p)
                   (natp n))
              (<= (riemann-expt-sine (1+ n) p)
                  (riemann-expt-sine n p)))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance dotproduct-pairwise-<=
                             (xs (map-expt-sine (1+ n) (cdr p)))
                             (ys (map-expt-sine n (cdr p))))
                  )
            :in-theory (e/d (riemann-expt-sine)
                            (dotprod deltas))
            )
           )
   ))

(local
 (defthm make-partition-rec-non-decreasing
     (implies (and (realp a)
                   (realp eps)
                   (<= 0 eps))
              (non-decreasing-list (make-partition-rec a eps n)))
   :instructions (:induct (:change-goal nil t)
                          :bash :pro (:forwardchain 2)
                          (:casesplit (zp (1- n)))
                          :bash :bash)))

(local
 (defthm make-partition-non-decreasing
     (implies (and (realp a)
                   (realp b)
                   (<= a b)
                   (natp n))
              (non-decreasing-list (make-partition a b n)))
   :hints (("Goal"
            :use ((:instance make-partition-rec-non-decreasing
                             (eps (/ (- b a) n))))
            :in-theory (disable make-partition-rec-non-decreasing)))))

(local
 (defthm make-small-partition-non-decreasing
     (implies (and (realp a)
                   (realp b)
                   (<= a b))
              (non-decreasing-list (make-small-partition a b)))
   :hints (("Goal"
            :use ((:instance make-partition-non-decreasing
                             (n (i-large-integer))))
            :in-theory (e/d (make-small-partition)
                            (make-partition-non-decreasing))))))


(local
 (defthm strict-int-expt-sine-decreasing-lemma
     (implies (natp n)
              (<= (riemann-expt-sine (1+ n) (make-small-partition 0 (acl2-pi)))
                  (riemann-expt-sine n (make-small-partition 0 (acl2-pi)))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance riemann-expt-sine-decreasing
                             (p (make-small-partition 0 (acl2-pi))))
                  )
            :in-theory (disable riemann-expt-sine-decreasing)
            )
           )
   ))

(local
 (defthm realp-riemann-expt-sine
     (implies (non-decreasing-list p)
              (realp (riemann-expt-sine n p)))
   :hints (("Goal"
            :in-theory (enable riemann-expt-sine)))
   ))

(local
 (defthm-std strict-int-expt-sine-decreasing
     (implies (natp n)
              (<= (strict-int-expt-sine (1+ n) 0 (acl2-pi))
                  (strict-int-expt-sine n 0 (acl2-pi))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance strict-int-expt-sine-decreasing-lemma)
                  (:instance standard-part-<=
                             (x (RIEMANN-EXPT-SINE (+ 1 N)
                                                   (MAKE-SMALL-PARTITION 0
                                                                         (ACL2-PI))))
                             (y (RIEMANN-EXPT-SINE N
                                                   (MAKE-SMALL-PARTITION 0
                                                                         (ACL2-PI)))))

                  )
            :in-theory (e/d (strict-int-expt-sine)
                            (strict-int-expt-sine-decreasing-lemma
                             REWRITE-RIEMANN-EXPT-SINE-POSP-N
                             REWRITE-RIEMANN-EXPT-SINE-POSP-N-LEMMA))
            )
           )
   ))

(local
 (defthm int-expt-sine-decreasing
     (implies (natp n)
              (<= (int-expt-sine (1+ n) 0 (acl2-pi))
                  (int-expt-sine n 0 (acl2-pi))))
   :hints (("Goal"
            :use ((:instance strict-int-expt-sine-decreasing))
            :in-theory (e/d (int-expt-sine)
                            (strict-int-expt-sine-decreasing
                             STRICT-INT-EXPT-SINE
                             INTEGRATION-BY-PARTS-WALLIS-INTEGRAL
                             REWRITE-INT-EXPT-SINE-POSP-N
                             ))))
   ))

(defthm wallis-integral-decreasing
    (implies (natp n)
             (<= (wallis-integral (+ n 1))
                 (wallis-integral n)))
  :hints (("Goal"
           :use ((:instance int-expt-sine-decreasing))
           :in-theory (disable strict-int-expt-sine-decreasing
                               STRICT-INT-EXPT-SINE
                               INTEGRATION-BY-PARTS-WALLIS-INTEGRAL
                               REWRITE-INT-EXPT-SINE-POSP-N
                               ))))

(local
 (defthm-std int-expt-sine-realp
     (realp (int-expt-sine n 0 (acl2-pi)))))

(defthm wallis-integral-real
    (realp (wallis-integral n)))

(in-theory (disable wallis-integral))
