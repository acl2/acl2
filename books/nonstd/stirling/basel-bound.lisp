(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/derivative-raise" :dir :system))
(local (include-book "nonstd/integrals/ftc-2" :dir :system))
(include-book "nonstd/nsa/intervals" :dir :system)

(local (include-book "standard-close-utils"))

(defun basel-series (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
      (+ (expt i -2)
         (basel-series (1+ i) n))))

(local
 (defun positive-domain ()
   (interval '(0) nil)))

(local
 (defun realposfix (x)
   (if (and (realp x) (< 0 x))
       x
       1)))

(local
 (encapsulate nil
     (local (include-book "nonstd/nsa/derivative-raise" :dir :system))

   (defthmd expt-continuous
       (implies (and (realp x)
                     (< 0 x)
                     (standardp x)
		     (realp x1)
                     (< 0 x1)
                     (standardp n)
                     (i-close x x1))
                (I-CLOSE (expt x n)
                         (expt x1 n)))
     :hints (("Goal"
              :use ((:instance
                     (:functional-instance rdfn-continuous
                                           (rdfn (lambda (context x)
                                                   (expt (realposfix x) context)))
                                           (rdfn-domain positive-domain))
                     (y x1)
                     (context n)
                     )
                    )
              :in-theory (enable interval-definition-theory)
              )
             ("Subgoal 1"
              :use ((:instance
                     expt-differentiable-using-nonstd-criterion
                     (x (realposfix x))
                     (n context))))
             ))
   ))

(local
 (defun map-expt-2 (p)
   (if (consp p)
       (cons (expt (realposfix (car p)) -2)
             (map-expt-2 (cdr p)))
       nil)))

(local
 (defun riemann-expt-2 (p)
   (dotprod (deltas p)
            (map-expt-2 (cdr p)))))

(local
 (encapsulate nil

     (defthm limited-riemann-expt-2
      (implies (and (realp a) (standardp a)
		    (realp b) (standardp b)
		    (inside-interval-p a (positive-domain))
		    (inside-interval-p b (positive-domain))
		    (< a b))
	       (i-limited (riemann-expt-2 (make-small-partition a b))))
      :otf-flg t
      :hints (("Goal"
	       :use ((:instance
                      (:functional-instance limited-riemann-rcdfn-prime-small-partition
				            (rcdfn-domain positive-domain)
				            (rcdfn
                                             (lambda (context x)
                                               (- (expt (realposfix x) -1))))
                                            (rcdfn-prime
                                             (lambda (context x)
                                               (expt
                                                (realposfix x)
                                                -2)))
				            (map-rcdfn-prime
                                             (lambda (context p)
                                               (map-expt-2 p)))
				            (riemann-rcdfn-prime
                                             (lambda (context p)
                                               (riemann-expt-2 p))))
                      (context -2)
                      ))
               :in-theory (e/d (interval-definition-theory)
                               (standard-part-is-standard-implies-close-to-standard-part))
               )
              ("Subgoal 2"
               :use ((:instance EXPT-CONTINUOUS (N -2))
                     )
               :IN-THEORY (DISABLE EXPT-CONTINUOUS)
               )
              ("Subgoal 1"
               :use ((:instance derivative-expt-is-derivative
                                (x x)
                                (x1 x1)
                                (n -1))
                     (:instance close-uminus
                                (x (+ (* (/ X) (/ (+ X (- X1))))
                                      (- (* (/ X1) (/ (+ X (- X1)))))))
                                (y (- (EXPT X -2)))
                                )
                     )
               :in-theory (e/d (inside-interval-p)
                               (derivative-expt-is-derivative
                                close-uminus))
               )
              ))

   (local (in-theory (disable riemann-expt-2)))

   (defun-std strict-int-expt-2 (a b)
     (if (and (realp a)
	      (realp b)
	      (inside-interval-p a (positive-domain))
	      (inside-interval-p b (positive-domain))
	      (< a b))
         (standard-part (riemann-expt-2 (make-small-partition a b)))
         0))
   ))

(local
 (defun int-expt-2 (a b)
   (if (<= a b)
       (strict-int-expt-2 a b)
       (- (strict-int-expt-2 b a)))))

(local
 (defthmd int-expt-2-computation
     (implies (and (inside-interval-p a (positive-domain))
                   (inside-interval-p b (positive-domain)))
              (equal (int-expt-2 a b)
                     (- (/ a) (/ b))))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance ftc-2
                                         (rcdfn-domain positive-domain)
                                         (rcdfn
                                          (lambda (context x)
                                            (- (expt (realposfix x) -1))))
                                         (rcdfn-prime
                                          (lambda (context x)
                                               (expt
                                                (realposfix x)
                                                -2)))
                                         (map-rcdfn-prime
                                          (lambda (context p)
                                               (map-expt-2 p)))
                                         (riemann-rcdfn-prime
                                          (lambda (context p)
                                               (riemann-expt-2 p)))
                                         (strict-int-rcdfn-prime
                                          (lambda (context a b)
                                            (strict-int-expt-2 a b)))
                                         (int-rcdfn-prime
                                          (lambda (context a b)
                                            (int-expt-2 a b)))
                                         )
                   ))
            :in-theory (e/d (interval-definition-theory)
                            (ftc-2)))
           )))


(local
 (defthmd int-expt-2-unit-lower-bound
     (implies (and (posp i))
              (<= (int-expt-2 i (1+ i))
                  (expt i -2)))
   :instructions
   ((:use (:instance int-expt-2-computation (a i)
                     (b (1+ i))))
    :pro
    (:in-theory (enable inside-interval-p))
    (:forwardchain 1)
    (:dv 1)
    := :top (:drop 2)
    (:dv 2)
    (:= (* (/ i) (/ i)))
    :up :top
    (:use (:instance (:theorem (implies (and (realp a)
                                             (realp b)
                                             (not (= a 0))
                                             (not (= b 0)))
                                        (equal (- (/ a) (/ b))
                                               (/ (- b a) (* a b)))))
                     (a i)
                     (b (1+ i))))
    (:change-goal nil t)
    :bash :pro (:forwardchain 1)
    (:dv 1)
    := (:dv 1)
    :s :top (:drop 2)
    (:dv 1)
    (:= (* (/ i) (/ (1+ i))))
    :top :bash)))


(local
 (defthmd int-expt-2-i-i+1
     (implies (posp i)
              (equal (int-expt-2 i (1+ i))
                     (* (/ i) (/ (1+ i)))))
  :instructions
  ((:use (:instance int-expt-2-computation (a i)
                    (b (1+ i))))
   :pro
   (:in-theory (enable inside-interval-p))
   (:forwardchain 1)
   (:dv 1)
   := (:drop 2)
   :top
   (:use (:instance (:theorem (implies (and (realp a)
                                            (realp b)
                                            (not (= a 0))
                                            (not (= b 0)))
                                       (equal (- (/ a) (/ b))
                                              (/ (- b a) (* a b)))))
                    (a i)
                    (b (1+ i))))
   :pro (:forwardchain 1)
   (:dv 1)
   := (:dv 1)
   :s :up
   :top (:drop 2)
   :bash :bash)))

(local
 (defthmd expt-2-unit-upper-bound
     (implies (posp i)
              (<= (expt (1+ i) -2)
                  (int-expt-2 i (1+ i))))
   :hints (("Goal"
            :use ((:instance int-expt-2-i-i+1))))))
(local
 (defthmd expt-2-unit-lower-bound
     (implies (posp i)
              (<= (int-expt-2 i (1+ i))
                  (expt i -2)))
   :hints (("Goal"
            :use ((:instance int-expt-2-i-i+1))))))

(local
 (defun sum-int-expt-2 (i n)
   (declare (xargs :measure (nfix (- n i))))
   (if (zp (- n i))
       0
       (+ (int-expt-2 i (1+ i))
          (sum-int-expt-2 (1+ i) n)))))

(local
    (defthm-std int-expt-a-a
        (implies (and (realp a)
                      (< 0 a))
                 (equal (int-expt-2 a a) 0))))

(local
 (defthmd sum-int-expt-2-=-int-expt-2-lemma
     (implies (and (posp a)
                   (posp b)
                   (<= a b))
              (equal (sum-int-expt-2 a b)
                     (int-expt-2 a b)))
   :otf-flg nil
   :hints (("Goal"
            :do-not-induct t
            :induct (sum-int-expt-2 a b)
            :in-theory (e/d (inside-interval-p)
                            ())
            )
           ("Subgoal *1/2"
            :use ((:instance
                   (:functional-instance split-rcfn-integral-by-subintervals
                                         (rcfn-domain positive-domain)
                                         (rcfn
                                          (lambda (context x)
                                            (expt
                                             (realposfix x)
                                             -2)))
                                         (map-rcfn
                                          (lambda (context p)
                                            (map-expt-2 p)))
                                         (riemann-rcfn
                                          (lambda (context p)
                                            (riemann-expt-2 p)))
                                         (strict-int-rcfn
                                          (lambda (context a b)
                                            (strict-int-expt-2 a b)))
                                         (int-rcfn
                                          (lambda (context a b)
                                            (int-expt-2 a b))))
                   (a a)
                   (b b)
                   (c (1+ a)))))
           ("Subgoal *1/2.1"
            :use ((:instance expt-continuous
                             (x x)
                             (x1 y)
                             (n -2))))
           ("Subgoal *1/1"
            :use ((:instance int-expt-a-a))
            :in-theory (disable int-expt-a-a))
           )
   ))

(local
 (defthmd basel-series-lower-bound-sum-int-expt-2
     (implies (and (posp i)
                   (posp n)
                   (<= i n))
              (<= (sum-int-expt-2 i n)
                  (basel-series i n)))
   :hints (("Goal"
            :induct (sum-int-expt-2 i n))
           ("Subgoal *1/2"
            :use ((:instance expt-2-unit-lower-bound))))))

(local
 (defthmd basel-series-upper-bound-sum-int-expt-2-lemma
     (implies (and (posp i)
                   (posp n)
                   (<= i n))
              (<= (basel-series  (1+ i) (1+ n))
                  (sum-int-expt-2 i n)))
   :hints (("Goal"
            :induct (sum-int-expt-2 i n))
           ("Subgoal *1/2"
            :use ((:instance expt-2-unit-upper-bound))))))

(local
 (defthmd basel-series-upper-bound-sum-int-expt-2
     (implies (and (posp i)
                   (not (= i 1))
                   (posp n)
                   (<= i n))
              (<= (basel-series i n)
                  (sum-int-expt-2 (1- i) (1- n))))
   :hints (("Goal"
            :use ((:instance basel-series-upper-bound-sum-int-expt-2-lemma
                             (i (1- i))
                             (n (1- n))))))))


(local
 (defthmd basel-series-lower-bound-int-expt-2
     (implies (and (posp i)
                   (posp n)
                   (<= i n))
              (<= (int-expt-2 i n)
                  (basel-series i n)))
   :hints (("Goal"
            :use ((:instance basel-series-lower-bound-sum-int-expt-2)
                  (:instance sum-int-expt-2-=-int-expt-2-lemma
                             (a i)
                             (b n)))))))

(local
 (defthmd basel-series-upper-bound-int-expt-2-lemma
     (implies (and (posp i)
                   (not (= i 1))
                   (posp n)
                   (<= i n))
              (<= (basel-series i n)
                  (int-expt-2 (1- i) (1- n))))
   :hints (("Goal"
            :use ((:instance basel-series-upper-bound-sum-int-expt-2)
                  (:instance sum-int-expt-2-=-int-expt-2-lemma
                             (a (1- i))
                             (b (1- n))))))))

(local
 (defthmd basel-series-lower-bound
     (implies (and (posp i)
                   (posp n)
                   (<= i n))
              (<= (- (/ i) (/ n))
                  (basel-series i n)))
   :hints (("Goal"
            :use ((:instance basel-series-lower-bound-int-expt-2)
                  (:instance int-expt-2-computation
                             (a i)
                             (b n)))
            :in-theory (e/d (inside-interval-p)
                            (basel-series
                             int-expt-2))
            ))))

(local
 (defthmd basel-series-upper-bound
     (implies (and (posp i)
                   (not (= i 1))
                   (posp n)
                   (<= i n))
              (<= (basel-series i n)
                  (- (/ (1- i)) (/ (1- n)))))
   :hints (("Goal"
            :use ((:instance basel-series-upper-bound-int-expt-2-lemma)
                  (:instance int-expt-2-computation
                             (a (1- i))
                             (b (1- n))))
            :in-theory (e/d (inside-interval-p)
                            (basel-series
                             int-expt-2))))))

(local
 (defthmd basel-series-upper-bound-i=1
     (implies (and (posp i)
                   (= i 1)
                   (posp n)
                   (<= i n))
              (<= (basel-series i n)
                  (+ 1 (/ i) (- (/ (1- n))))))
   :instructions (:pro (:use (:instance basel-series-upper-bound (i 2)))
                       :pro (:dv 1)
                       :x (:casesplit (= i n))
                       (:= 0)
                       :up
                       :top :bash (:= (+ 1 (basel-series 2 n)))
                       (:forwardchain 1)
                       :top :bash)))

(local
 (defthmd basel-series-non-negative
     (implies (and (posp i)
                   (posp n)
                   (<= i n))
              (<= 0 (basel-series i n)))))

(local
 (defthmd basel-series-upper-bound-corollary
     (implies (and (posp i)
                   (not (= i 1))
                   (posp n)
                   (<= i n))
              (<= (basel-series i n) 1))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance basel-series-upper-bound)
                  (:instance
                   (:theorem (implies (posp i)
                                      (<= (/ i) 1)))
                   (i (1- i)))
                  (:instance
                   (:theorem (implies (and (realp x)
                                           (realp y)
                                           (<= 0 y)
                                           (<= x 1))
                                      (<= (+ x (- y)) 1)))
                   (x (/ (1- i)))
                   (y (/ (1- n))))
                  )))))


(defthmd basel-series-gross-bounds
    (implies (and (posp i)
                  (posp n)
                  (<= i n))
             (and (<= 0 (basel-series i n))
                  (<= (basel-series i n) 2)))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance basel-series-upper-bound-corollary)
                 (:instance basel-series-upper-bound-corollary
                            (i (1+ i)))
                 (:instance basel-series-upper-bound-i=1)
                 (:instance basel-series-non-negative))
           :in-theory (disable basel-series))))

(defthm real-basel-series
    (implies (and (realp i)
                  (realp n))
             (realp (basel-series i n)))
  :rule-classes (:rewrite :type-prescription))

(defthmd limited-basel-series
    (implies (and (posp i)
                  (posp n)
                  (<= i n))
             (i-limited (basel-series i n)))
  :hints (("Goal"
           :use ((:instance large-if->-large
                            (x (basel-series i n))
                            (y 2)))
           :in-theory (disable basel-series
                               large-if->-large))))

(defthmd basel-series-split
    (implies (and (posp m)
                  (posp n)
                  (posp i)
                  (<= i m)
                  (<= m n))
             (equal (- (basel-series i n)
                       (basel-series i m))
                    (basel-series m n))))

(local
 (defthmd basel-series-close-for-large-values-lemma
     (implies (and (posp m)
                   (posp n)
                   (posp i)
                   (<= i m)
                   (<= m n)
                   (i-large m)
                   (i-large n))
              (i-close (basel-series i m)
                       (basel-series i n)))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance basel-series-split)
                  (:instance small-if-<-small
                             (x (+ (/ (1- m)) (- (/ (1- n)))))
                             (y (basel-series m n)))
                  (:instance basel-series-upper-bound
                             (i m)
                             (n n)))
            :in-theory (enable i-close))
           )))

(defthmd basel-series-close-for-large-values
     (implies (and (posp m)
                   (posp n)
                   (posp i)
                   (<= i m)
                   (<= i n)
                   (i-large m)
                   (i-large n))
              (i-close (basel-series i m)
                       (basel-series i n)))
  :hints (("Goal"
           :do-not-induct t
           :cases ((<= m n)))
          ("Subgoal 1"
           :use ((:instance basel-series-close-for-large-values-lemma))
           )
          ("Subgoal 2"
           :use ((:instance basel-series-close-for-large-values-lemma
                            (m n)
                            (n m)))
           )
          ))

(in-theory (disable basel-series))
