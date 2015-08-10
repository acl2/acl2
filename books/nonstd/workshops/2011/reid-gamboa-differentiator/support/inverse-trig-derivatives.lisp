(in-package "ACL2")

(include-book "inverse-trig-ex")
(include-book "inverse-derivative")
(include-book "sin-cos-minimal")
(include-book "sqrt-derivative")


(defthm-std acl2-acos-standard
  (implies (standardp x)
           (standardp (acl2-acos x))))

(local
 (defthm sine-acos-nonnegative
   (implies (and (realp x)
                 (<= -1 x)
                 (<= x 1))
            (<= 0 (acl2-sine (acl2-acos x))))
   :hints (("Goal"
            :use ((:instance sine-positive-in-0-pi/2
                             (x (acl2-acos x)))
                  (:instance sine-positive-in-pi/2-pi
                             (x (acl2-acos x)))
                  (:instance acl2-acos-exists (y x)))
            :in-theory (enable-disable
                        (interval-definition-theory)
                        (sine-positive-in-0-pi/2
                         sine-positive-in-pi/2-pi
                         interval-definition-theory
                         sine-2x
                         sine-3x
                         cosine-2x
                         EQUAL-*-/-1))))))

(local
 (defthm 1-cos*cos
   (implies (acl2-numberp x)
            (equal (- 1 (* (acl2-cosine x) (acl2-cosine x)))
                   (* (acl2-sine x) (acl2-sine x))))
   :hints (("Goal" :in-theory (disable sin**2+cos**2)
            :use (:instance sin**2+cos**2)))))

(local
 (defthm sine-acos-lemma
   (implies (and (realp x)
                 (<= 0 (acl2-sine (acl2-acos x))))
            (equal (acl2-sine (acl2-acos x))
                   (acl2-sqrt (- 1 (* (acl2-cosine (acl2-acos x)) (acl2-cosine (acl2-acos x)))))))
   :hints (("Goal"
            :use (:instance sqrt-*-x-x
                            (x (acl2-sine (acl2-acos x))))
            :in-theory (enable abs)))))

(defthm sqrt-positive
  (implies (and (realp x)
                (< 0 x))
           (< 0 (acl2-sqrt x))))

(defthm x*x<1
  (implies (and (realp x)
                (< -1 x)
                (realp y)
                (< x 1))
           (< (* x x) 1))
  :hints (("Goal"
           :cases ((< 0 x) (< x 0) (= x 0)))
          ("Subgoal 3"
           :use (:instance x*y>1-positive-lemma (i x) (j x) (x 1) (y 1)))
           ("subgoal 2"
           :use (:instance x*y>1-positive-lemma (i (- x)) (j (- x)) (x 1) (y 1)))))

(defthm sine-acos-positive
  (implies (and (realp x)
                (< -1 x)
                (< x 1))
           (< 0 (acl2-sine (acl2-acos x))))
  :hints (("Goal" :use (:instance sqrt-positive
                                  (x (- 1 (* x x)))))))

(defthm acl2-acos-derivative
  (implies (and (realp x) (< -1 x) (< x 1)
                (realp y) (< -1 y) (< y 1)
                (standardp x)
                (i-close x y)
                (not (equal x y)))
           (i-close (/ (- (acl2-acos x) (acl2-acos y))
                       (- x y))
                    (- (/ (acl2-sqrt (- 1 (* x x)))))))
  :hints (("Goal"
           :use ((:functional-instance
                  inverse-g-close
                  (inverse-f acl2-cosine)
                  (inverse-f-prime (lambda (x) (- (acl2-sine x))))
                  (inverse-f-domain-p (lambda (x) (and (realp x) (<= 0 x) (<= x (acl2-pi)))))
                  (inverse-g acl2-acos)
                  (inverse-g-domain-p (lambda (x) (and (realp x) (<= -1 x) (<=  x 1))))) ;acl2-acos-domain))
                 (:instance sine-acos-positive)
                 (:instance reciprocal-minus
                            (x (acl2-sqrt (- 1 (* x x)))))))
          ("Subgoal 8"
; changed after v4-3 from "Subgoal 10", and then 12/13/12 from "Subgoal 7", and
; then again 2/16/13 from "Subgoal 6", probably all for tau-system, by Matt K.
           :use (:instance acl2-acos-continuous)
           :in-theory (enable interval-definition-theory))
          ("Subgoal 4"
           :use (:instance acl2-cosine-derivative))
          ("Subgoal 3"
           :use (:instance acl2-acos-exists (y x))
           :in-theory (enable interval-definition-theory))
	  ("Subgoal 1"
           :use (:instance acl2-acos-inverse-exists)
           :in-theory (enable interval-definition-theory))
	  ))

#|
(encapsulate
 nil

 (local
  (defthmd lemma-1
    (equal (acl2-sine (- (/ (acl2-pi) 2) (acl2-acos x)))
	   (acl2-cosine (acl2-acos x)))
    :hints (("Goal"
	     :use ((:instance sine-of-sums
			      (x (/ (acl2-pi) 2))
			      (y (acl2-acos x))))
	     :in-theory (disable sine-of-sums)))))

 (local
  (defthmd lemma-2
    (implies (and (realp x)
		  (<= -1 x)
		  (<= x 1))
	     (equal (acl2-sine (- (/ (acl2-pi) 2) (acl2-acos x)))
		    x))
    :hints (("Goal"
	     :use ((:instance lemma-1)
		   (:instance acl2-acos-exists (y x)))
	     :in-theory (disable sine-of-sums acl2-acos-exists)))))

 (local
  (defthmd lemma-3
    (implies (and (realp x)
		  (<= -1 x)
		  (<= x 1))
	     (equal (acl2-asin (acl2-sine (- (/ (acl2-pi) 2) (acl2-acos x))))
		    (acl2-asin x)))
    :hints (("Goal"
	     :use ((:instance lemma-2))))))

 (local
  (defthmd lemma-4
    (implies (and (realp x)
		  (<= -1 x)
		  (<= x 1))
	     (inside-interval-p (+ (* 1/2 (acl2-pi)) (- (acl2-acos x)))
				(interval (- (* 1/2 (acl2-pi)))
					  (* 1/2 (acl2-pi)))))
    :hints (("Goal"
	     :use ((:instance acl2-acos-exists (y x)))
	     :in-theory (enable-disable (interval-definition-theory) (acl2-acos-exists sine-acos-lemma))))
    ))

 (defthmd pi/2-acos-=-asin
   (implies (and (realp x)
		 (<= -1 x)
		 (<= x 1))
	    (equal (- (/ (acl2-pi) 2) (acl2-acos x))
		   (acl2-asin x)))
   :hints (("Goal"
	    :use ((:instance lemma-3)
		  (:instance lemma-4)
		  (:instance acl2-asin-inverse-exists (x (- (/ (acl2-pi) 2) (acl2-acos x)))))
	    :in-theory (disable acl2-asin-inverse-exists)
	    )))

  )
|#

(encapsulate
 nil

 (local
  (defthm asin-to-acos
    (implies (and (realp x) (< -1 x) (< x 1))
             (equal (acl2-asin x)
                    (- (/ (acl2-pi) 2) (acl2-acos x))))
    :hints (("Goal" :use (:instance pi/2-acos-=-asin
                                    (x x))
             :in-theory (enable-disable (interval-definition-theory) (pi/2-acos-=-asin))))
    ))

 (local
  (defthm asin-differential-close-lemma
    (implies (and (realp x)
                  (realp y)
                  (realp z))
             (equal (* z (+ (- x) y))
                    (- (* z (+ x (- y))))))))

 (defthm acl2-asin-derivative
   (implies (and (realp x) (< -1 x) (< x 1)
                 (realp y) (< -1 y) (< y 1)
                 (standardp x)
                 (i-close x y)
                 (not (equal x y)))
            (i-close (/ (- (acl2-asin x) (acl2-asin y))
                        (- x y))
                     (/ (acl2-sqrt (- 1 (* x x))))))
   :hints (("Goal"
            :in-theory (disable pi/2-acos-=-asin)
            :use ((:instance acl2-acos-derivative (x x) (y y))
                  (:instance close-uminus
                             (x (* (/ (+ x (- y)))
                                   (+ (acl2-acos x) (- (acl2-acos y)) )))
                             (y (- (/ (acl2-sqrt (+ 1 (- (* x x)))))))))))))



; Adding asin, acos into the differentiator.


(defthm-std acl2-asin-standard
  (implies (standardp x)
           (standardp (acl2-asin x))))

(differentiable-criteria-expr
 elem-acl2-asin
 (acl2-asin x)
 (and (realp x) (< -1 x) (< x 1))
 :continuous-hints
 (("Goal" :use (:instance acl2-asin-continuous)
   :in-theory (enable interval-definition-theory))))

(defthm sqrt-term-positive
  (implies (and (realp x)
                (< -1 x)
                (< x 1))
           (< 0 (acl2-sqrt (- 1 (* x x)))))
  :hints (("Goal"
           :use (:instance sine-acos-positive (x x))))) ;sine-acos rewrites to sqrt(1-x*x)

(defthm close-to-standard-not-small
  (implies (and (realp x) (standardp x)
                (< 0 x)
                (i-close x y))
           (not (i-small y)))
  :hints (("Goal" :in-theory (enable i-close i-small))))


(defthm 1-x*x-continuous
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (standardp x)
                (i-close x y))
           (i-close (- 1 (* x x))
                    (- 1 (* y y))))
  :hints (("Goal" :in-theory (enable i-close i-small)
           :use (:instance i-close-limited (x x) (y y)))))

(defthm expr-continuous
  (implies (and (realp x) (< -1 x) (< x 1)
                (realp y) (< -1 y) (< y 1)
                (standardp x)
                (i-close x y))
           (i-close (/ (acl2-sqrt (- 1 (* x x))))
                    (/ (acl2-sqrt (- 1 (* y y))))))
  :hints (("Goal" :use (:instance close-/
                                  (x (ACL2-SQRT (+ 1 (- (* X X)))))
                                  (y (ACL2-SQRT (+ 1 (- (* y y)))))))
          ("Subgoal 2"
           :use (:instance close-to-standard-not-small
                           (x (acl2-sqrt (- 1 (* x x))))
                           (y (acl2-sqrt (- 1 (* x x))))))
          ("Subgoal 1"
           :in-theory (disable x*x<1)
           :use ((:instance  x*x<1 (x x))
                 (:instance  x*x<1 (x y))
                 (:instance sqrt-continuous
                            (x (- 1 (* x x)))
                            (y (- 1 (* y y))))))))



(differentiable-criteria-expr
 elem-acl2-asin-prime
 (/ (acl2-sqrt (- 1 (* x x))))
 (and (realp x) (< -1 x) (< x 1)))


(defthmd elem-acl2-asin-close
  (implies (and (realp x) (< -1 x) (< x 1)
                (realp y) (< -1 y) (< y 1)
                (standardp x)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (acl2-asin x) (acl2-asin y))
                       (- x y))
                    (/ (acl2-sqrt (- 1 (* x x))))))
  :hints (("Goal" :use (:instance acl2-asin-derivative))))

(def-elem-derivative acl2-asin
  elem-acl2-asin
  (and (realp x) (< -1 x) (< x 1))
  (/ (acl2-sqrt (- 1 (* x x)))))

; Now for acos
(differentiable-criteria-expr
 elem-acl2-acos
 (acl2-acos x)
 (and (realp x) (< -1 x) (< x 1))
 :continuous-hints
 (("Goal" :use (:instance acl2-acos-continuous)
   :in-theory (enable interval-definition-theory))))

(differentiable-criteria-expr
 elem-acl2-acos-prime
 (- (/ (acl2-sqrt (- 1 (* x x)))))
 (and (realp x) (< -1 x) (< x 1)))

(defthmd elem-acl2-acos-close
  (implies (and (realp x) (< -1 x) (< x 1)
                (realp y) (< -1 y) (< y 1)
                (standardp x)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (acl2-acos x) (acl2-acos y))
                       (- x y))
                    (- (/ (acl2-sqrt (- 1 (* x x)))))))
  :hints (("Goal" :use (:instance acl2-acos-derivative))))


(def-elem-derivative acl2-acos
  elem-acl2-acos
  (and (realp x) (< -1 x) (< x 1))
  (- (/ (acl2-sqrt (- 1 (* x x))))))

;(i-am-here)
(local
 (defthm i-close-product
   (implies (and (i-limited a)
                 (i-close a b)
                 (i-limited c)
                 (i-close c d))
            (i-close (* a c) (* b d)))
   :hints (("Goal" :in-theory (enable i-close i-small)
            :use ((:instance STANDARD-PART-OF-TIMES (x a) (y c))
                  (:instance STANDARD-PART-OF-TIMES (x b) (y d)))))))

(defthm acl2-tangent-continuous
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (standardp x)
                (not (equal (acl2-cosine x) 0))
                (i-close x y))
           (i-close (acl2-tangent x)
                    (acl2-tangent y)))
  :hints (("Goal"
           :use ((:instance i-close-product
                           (a (/ (acl2-cosine x)))
                           (b (/ (acl2-cosine y)))
                           (c (acl2-sine x))
                           (d (acl2-sine y)))
                 (:instance standards-are-limited
                            (x (/ (acl2-cosine x))))
                 (:instance standards-are-limited
                            (x (acl2-sine x)))))))

(defthm condense-sqrt-/
  (implies (and (realp x)
                (< 0 x))
           (equal (* (/ (acl2-sqrt x))
                     (/ (acl2-sqrt x)))
                  (/ x)))
  :hints (("Goal"
           :use (:instance sqrt-sqrt (x (/ x)))
           :in-theory (disable sqrt-sqrt ))))

(defthm acl2-atan-derivative
  (implies (and (realp x)
                (standardp x)
                (i-close x y)
                (not (equal x y))
                (realp y))
           (i-close (/ (- (acl2-atan x) (acl2-atan y))
                       (- x y))
                    (/ (+ 1 (* x x)))))
  :hints (("Goal"
           :use (:functional-instance
                 inverse-g-close
                 (inverse-f (lambda (x) (acl2-tangent x)))
                 (inverse-f-domain-p (lambda (x)
                                     (and (realp x)
                                          (< (- (/ (acl2-pi) 2)) x)
                                          (< x (/ (acl2-pi) 2)))))
                 (inverse-f-prime (lambda (x)
                                         (/ (* (acl2-cosine x)
                                               (acl2-cosine x)))))
                 (inverse-g acl2-atan)
                 (inverse-g-domain-p (lambda (x) (realp x)))

                 ))

          ("Subgoal 6"
; changed 12/13/12 from "Subgoal 7" and then 2/16/13 from "Subgoal 5", both
; probably for tau-system,by Matt K
           :use ((:instance acl2-tangent-continuous (x x) (y y))
                 (:instance cos-positive--pi/2-to-pi/2)))
          ("Subgoal 4"
           :use ((:instance tangent-derivative (x x) (y y))
                 (:instance cos-positive--pi/2-to-pi/2 (x x))
                 (:instance cos-positive--pi/2-to-pi/2 (x y))))
          ("Subgoal 3"
           :use (:instance atan-bounds))
          ("Subgoal 2"
           :use (:instance tangent-atan))
          ("Subgoal 1"
           :use (:instance atan-tangent))))

(defthmd elem-acl2-atan-close
  (implies (and (realp x)
                (standardp x)
                (i-close x y)
                (not (equal x y))
                (realp y))
           (i-close (/ (- (acl2-atan x) (acl2-atan y))
                       (- x y))
                    (/ (+ 1 (* x x)))))
  :hints (("Goal" :use (:instance acl2-atan-derivative))))

(differentiable-criteria-expr
 elem-acl2-atan
 (acl2-atan x)
 (realp x))

(defthm 1+x*x-continuous
  (implies (and (realp x)
                (standardp x)
                (realp y)
                (i-close x y))
           (i-close (+ 1 (* x x))
                    (+ 1 (* y y))))
  :hints (("Goal"
           :in-theory (enable i-close i-small)
           :use (:instance i-close-limited (x x) (y y)))))

(differentiable-criteria-expr
 elem-acl2-atan-prime
 (/ (+ 1 (* x x)))
 (realp x)
 :continuous-hints
 (("Goal"
   :use (:instance close-/
                   (x (+ 1 (* x x)))
                   (y (+ 1 (* y y)))))))


(def-elem-derivative acl2-atan
  elem-acl2-atan
  (realp x)
  (/ (+ 1 (* x x))))
