(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "nonstd/nsa/ln" :dir :system)

(include-book "nonstd/integrals/ftc-2" :dir :system)
(local (include-book "nonstd/nsa/derivatives-composition" :dir :system))

(encapsulate
    NIL

    (local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/ln-derivative-real" :dir :system))

  (local (include-book
          "nonstd/workshops/2011/reid-gamboa-differentiator/support/ln-derivative-real"
          :dir :system))

  (defthm acl2-ln-real-derivative
      (implies (and (realp x) (< 0 x)
                    (realp y) (< 0 y)
                    (standardp x)
                    (i-close x y) (not (equal x y)))
               (i-close (/ (- (acl2-ln x) (acl2-ln y))
                           (- x y))
                        (/ x))))

  (defthm acl2-ln-real-continuous
      (implies (and (realp x) (< 0 x)
                    (realp y) (< 0 y)
                    (standardp x)
                    (i-close x y))
               (i-close (acl2-ln x)
                        (acl2-ln y))))

  (defthm standard-nonzero-not-small
                 (implies (and (standardp x) (not (equal x 0)))
                          (not (i-small x))))
)

(LOCAL
 (defun ln-antiderivative (x)
   (- (* x (acl2-ln x)) x)))

(local
 (defun f (x)
   (* x (acl2-ln x))))

(local
 (defun f-prime (x)
   (+ (acl2-ln x) 1)))

(defun positive-domain ()
  (interval '(0) nil))

(local
 (defthm /-x-not-large
   (implies (and (acl2-numberp x)
                 (not (i-small x)))
            (not (i-large (/ x))))
   :hints (("Goal" :in-theory (enable i-small i-large)))))

(local
 (defthmd ln-differentiable-part1
  (implies (and (realp x) (< 0 x)
                (realp y) (< 0 y)
                (standardp x)
                (i-close x y) (not (equal x y)))
           (i-limited (/ (- (acl2-ln x) (acl2-ln y))
                         (- x y))))
   :hints (("Goal"
            :use ((:instance i-close-limited-2
                             (x (/ (- (acl2-ln x) (acl2-ln y))
                                   (- x y)))
                             (y (/ x)))
                  (:instance /-x-not-large)
                  )
            :in-theory (disable i-close-limited-2
                                /-x-not-large)))))

(local
 (defthmd ln-differentiable-part2
  (implies (and (realp x) (< 0 x)
                (realp y1) (< 0 y1)
                (realp y2) (< 0 y2)
                (standardp x)
                (i-close x y1) (not (equal x y1))
                (i-close x y2) (not (equal x y2))
                )
           (i-close (/ (- (acl2-ln x) (acl2-ln y1))
                       (- x y1))
                    (/ (- (acl2-ln x) (acl2-ln y2))
                       (- x y2))))
   :hints (("Goal"
            :use ((:instance I-CLOSE-TRANSITIVE
                             (x (/ (- (acl2-ln x) (acl2-ln y1))
                                   (- x y1)))
                             (y (/ x))
                             (z (/ (- (acl2-ln x) (acl2-ln y2))
                                   (- x y2))))
                  (:instance acl2-ln-real-derivative
                             (x x)
                             (y y1))
                  (:instance acl2-ln-real-derivative
                             (x x)
                             (y y2))
                  )
            :in-theory (disable I-CLOSE-TRANSITIVE
                                acl2-ln-real-derivative)))))


(DEFUN realposfix (x)
  (if (and (realp x) (< 0 x))
      x
      1))

(local
 (defthm f-differentiable-part1
     (implies (and (standardp x)
		   (inside-interval-p x (positive-domain))
		   (inside-interval-p y1 (positive-domain))
		   (i-close x y1) (not (= x y1)))
	      (i-limited  (/ (- (f x) (f y1)) (- x y1))))
  :hints (("Goal"
	   :use ((:instance
                  (:functional-instance
                   dc-fn1*fn2-differentiable-part1
                   (dc-fn-domain positive-domain)
                   (dc-fn1 (lambda (context x)
                             (acl2-ln (REALPOSFIX x))))
                   (dc-fn2 (lambda (context x)
                             (realposfix x)))
                   (differential-dc-fn1
                    (lambda (context x eps)
                      (/ (- (acl2-ln (+ x eps))
                            (acl2-ln x))
                         eps)))
                   (differential-dc-fn2
                    (lambda (context x eps)
                      1))
                   (derivative-dc-fn1
                    (lambda (context x)
                      (/ x)))
                   (derivative-dc-fn2
                    (lambda (context x)
                      1))
                   (dc-fn1*fn2
                    (lambda (context x)
                      (f (realposfix x))))
                   (differential-dc-fn1*fn2
                    (lambda (context x eps)
                      (/ (- (f (realposfix (+ x eps)))
                            (f (realposfix x)))
                         eps)))
                   (derivative-dc-fn1*fn2
                    (lambda (context x)
                      (f-prime (realposfix x))))
                  ;;;
                   (dc-fnz (lambda (context x) 1))
                   (differential-dc-fnz (lambda (context x eps) 0))
                   (derivative-dc-fnz (lambda (context x) 0))
                   )
                  (context 0)
                  )
                 )
           )
          ("Subgoal 5"
           :in-theory (enable interval-definition-theory))
          ("Subgoal 3"
           :use ((:instance ln-differentiable-part1
                            (x x)
                            (y y1))
                 (:instance ln-differentiable-part2)
                 )
           :in-theory (enable interval-definition-theory)
           )
          ("Subgoal 2"
           :use ((:instance ln-differentiable-part1
                            (x x)
                            (y y1))
                 (:instance ln-differentiable-part2)
                 )
           :in-theory (enable interval-definition-theory)
           )
          )
  ))

(local
 (defthm f-differentiable-part2
     (implies (and (standardp x)
		   (inside-interval-p x (positive-domain))
		   (inside-interval-p y1 (positive-domain))
		   (inside-interval-p y2 (positive-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2)))
	      (i-close (/ (- (f x) (f y1)) (- x y1))
                       (/ (- (f x) (f y2)) (- x y2))
                       ))
  :hints (("Goal"
	   :use ((:instance
                  (:functional-instance
                   dc-fn1*fn2-differentiable-part2
                   (dc-fn-domain positive-domain)
                   (dc-fn1 (lambda (context x)
                             (acl2-ln (REALPOSFIX x))))
                   (dc-fn2 (lambda (context x)
                             (realposfix x)))
                   (differential-dc-fn1
                    (lambda (context x eps)
                      (/ (- (acl2-ln (+ x eps))
                            (acl2-ln x))
                         eps)))
                   (differential-dc-fn2
                    (lambda (context x eps)
                      1))
                   (derivative-dc-fn1
                    (lambda (context x)
                      (/ x)))
                   (derivative-dc-fn2
                    (lambda (context x)
                      1))
                   (dc-fn1*fn2
                    (lambda (context x)
                      (f (realposfix x))))
                   (differential-dc-fn1*fn2
                    (lambda (context x eps)
                      (/ (- (f (realposfix (+ x eps)))
                            (f (realposfix x)))
                         eps)))
                   (derivative-dc-fn1*fn2
                    (lambda (context x)
                      (f-prime (realposfix x))))
                  ;;;
                   (dc-fnz (lambda (context x) 1))
                   (differential-dc-fnz (lambda (context x eps) 0))
                   (derivative-dc-fnz (lambda (context x) 0))
                   )
                  (context 0)
                  )
                 )
           :in-theory (enable interval-definition-theory)
           )
          )
  ))

(local
 (defthm f-differentiable
     (implies (and (standardp x)
		   (inside-interval-p x (positive-domain))
		   (inside-interval-p y1 (positive-domain))
		   (inside-interval-p y2 (positive-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2)))
              (and (i-limited (/ (- (f x) (f y1)) (- x y1)))
	           (i-close (/ (- (f x) (f y1)) (- x y1))
                            (/ (- (f x) (f y2)) (- x y2))
                            )))
  :hints (("Goal"
	   :use ((:instance f-differentiable-part1)
                 (:instance f-differentiable-part2))))))

(local
 (defthmd close-to-standard-in-positive-domain
     (implies (and (standardp x)
                   (inside-interval-p x (positive-domain))
                   (realp y)
                   (i-close x y))
              (inside-interval-p y (positive-domain)))
  :otf-flg t
   :hints (("Goal"
            :use ((:instance close-x-y->same-standard-part)
                  )
            :in-theory (enable interval-definition-theory)))))



(local
 (encapsulate
     NIL

     (local
      (defthmd lemma-1
          (implies
           (and (inside-interval-p x '((0)))
                (standardp x)
                (standardp context1))
           (equal
            (/ x)
            (cond ((inside-interval-p (+ x (/ (i-large-integer)))
                                      '((0)))
                   (standard-part (* (+ (acl2-ln (+ x (/ (i-large-integer))))
                                        (- (acl2-ln x)))
                                     (/ (/ (i-large-integer))))))
                  ((inside-interval-p (+ x (- (/ (i-large-integer))))
                                      '((0)))
                   (standard-part (* (+ (acl2-ln (+ x (- (/ (i-large-integer)))))
                                        (- (acl2-ln x)))
                                     (/ (- (/ (i-large-integer)))))))
                  (t 'error))))
        :instructions
        (:pro (:in-theory (enable interval-definition-theory))
              (:dv 2)
              (:= (standard-part (* (+ (acl2-ln (+ x (/ (i-large-integer))))
                                       (- (acl2-ln x)))
                                    (/ (/ (i-large-integer))))))
              (:claim (standardp (/ x)))
              :top
              (:use (:instance close-x-y->same-standard-part
                               (y (* (+ (acl2-ln (+ x (/ (i-large-integer))))
                                        (- (acl2-ln x)))
                                     (/ (/ (i-large-integer)))))
                               (x (/ x))))
              :pro
              (:use (:instance acl2-ln-real-derivative (x x)
                               (y (+ x (/ (i-large-integer))))))
              :bash (:in-theory (enable i-close))
              :bash)))

   (defthm f-prime-is-derivative
       (implies (and (standardp x)
		     (inside-interval-p x (positive-domain))
                     (realp eps) (i-small eps) (not (= eps 0))
                     )
                (equal (standard-part (/ (- (f (+ x eps)) (f x)) eps))
                       (f-prime x)))
     :otf-flg t
     :hints (("Goal"
	      :use ((:instance
                     (:functional-instance differential-dc-fn1*fn2-close
                                           (dc-fn-domain positive-domain)
                                           (dc-fn1 (lambda (context x)
                                                     (acl2-ln (REALPOSFIX x))))
                                           (dc-fn2 (lambda (context x)
                                                     (realposfix x)))
                                           (differential-dc-fn1
                                            (lambda (context x eps)
                                              (/ (- (acl2-ln (+ x eps))
                                                    (acl2-ln x))
                                                 eps)))
                                           (differential-dc-fn2
                                            (lambda (context x eps)
                                              (if (= (fix eps) 0)
                                                  0
                                                  1)))
                                           (derivative-dc-fn1
                                            (lambda (context x)
                                              (/ x)))
                                           (derivative-dc-fn2
                                            (lambda (context x)
                                              1))
                                           (dc-fn1*fn2
                                            (lambda (context x)
                                              (f (realposfix x))))
                                           (differential-dc-fn1*fn2
                                            (lambda (context x eps)
                                              (if (= (fix eps) 0)
                                                  0
                                                  (/ (- (f (realposfix (+ x eps)))
                                                        (f (realposfix x)))
                                                     eps))))
                                           (derivative-dc-fn1*fn2
                                            (lambda (context x)
                                              (f-prime (realposfix x))))
                  ;;;
                                           (dc-fnz (lambda (context x) 1))
                                           (differential-dc-fnz (lambda (context x eps) 0))
                                           (derivative-dc-fnz (lambda (context x) 0))
                                           )
                     (context 0)
                     )
                    )
              :in-theory (disable standard-part-of-plus)
              )
             ("Subgoal 7"
              :use ((:instance close-to-standard-in-positive-domain
                               (x x)
                               (y (+ x eps)))
                    )
              :in-theory (e/d (i-close
                               interval-definition-theory)
                              (standard-part-of-plus
                               f
                               f-prime))
              )
             ("Subgoal 6"
              :use ((:instance lemma-1))
              :in-theory (enable interval-definition-theory))
             ("Subgoal 5"
              :in-theory (enable interval-definition-theory))
             ("Subgoal 4"
              :in-theory (enable interval-definition-theory))
             ("Subgoal 3"
              :in-theory (enable interval-definition-theory))
             ("Subgoal 2"
              :in-theory (enable interval-definition-theory))
             ("Subgoal 1"
              :in-theory (enable interval-definition-theory))
             )))
 )



(LOCAL
  (encapsulate
     nil

     (local
      (defthm lemma-1
          (implies (and (realp x)
                        (realp y)
                        (not (= x y)))
                   (equal (* (/ (+ x (- y)))
                             (+ (- x) y))
                          -1))
        :hints (("Goal"
                 :use ((:instance
                        (:theorem (implies (and (realp x) (not (equal x 0)))
                                           (equal (* (/ x) (- x)) -1)))
                        (x (+ x (- y)))))))
        ))

 (defthm ln-antiderivative-differentiable-part1
     (implies (and (standardp x)
		   (inside-interval-p x (positive-domain))
		   (inside-interval-p y1 (positive-domain))
		   (i-close x y1) (not (= x y1)))
	      (i-limited  (/ (- (ln-antiderivative x)
                                (ln-antiderivative y1))
                             (- x y1))))
  :hints (("Goal"
	   :use ((:instance
                  (:functional-instance
                   dc-fn1+fn2-differentiable-part1
                   (dc-fn-domain positive-domain)
                   (dc-fn1 (lambda (context x)
                             (f (REALPOSFIX x))))
                   (dc-fn2 (lambda (context x)
                             (- (realposfix x))))
                   (differential-dc-fn1
                    (lambda (context x eps)
                      (/ (- (f (+ x eps))
                            (f x))
                         eps)))
                   (differential-dc-fn2
                    (lambda (context x eps)
                      -1))
                   (derivative-dc-fn1
                    (lambda (context x)
                      (1+ (acl2-ln x))))
                   (derivative-dc-fn2
                    (lambda (context x)
                      -1))
                   (dc-fn1+fn2
                    (lambda (context x)
                      (ln-antiderivative (realposfix x))))
                   (differential-dc-fn1+fn2
                    (lambda (context x eps)
                      (/ (- (ln-antiderivative (realposfix (+ x eps)))
                            (ln-antiderivative (realposfix x)))
                         eps)))
                   (derivative-dc-fn1+fn2
                    (lambda (context x)
                      (acl2-ln (realposfix x))))
                  ;;;
                   (dc-fnz (lambda (context x) 1))
                   (differential-dc-fnz (lambda (context x eps) 0))
                   (derivative-dc-fnz (lambda (context x) 0))
                   )
                  (context 0)
                  )
                 )
           )
          ("Subgoal 6"
           :in-theory (e/d (interval-definition-theory)
                           (ln-antiderivative))
           )
          ("Subgoal 4"
           :in-theory (e/d (interval-definition-theory)
                           (|(* x (+ y z))|))
           )
          ("Subgoal 3"
           :use ((:instance f-differentiable-part1)
                 (:instance f-differentiable-part2)
                 )
           :in-theory (enable interval-definition-theory)
           )
          )
  )

 (defthm ln-antiderivative-differentiable-part2
     (implies (and (standardp x)
		   (inside-interval-p x (positive-domain))
		   (inside-interval-p y1 (positive-domain))
		   (inside-interval-p y2 (positive-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2))
                   )
	      (i-close (/ (- (ln-antiderivative x)
                             (ln-antiderivative y1))
                          (- x y1))
                       (/ (- (ln-antiderivative x)
                             (ln-antiderivative y2))
                           (- x y2))))
  :hints (("Goal"
	   :use ((:instance
                  (:functional-instance
                   dc-fn1+fn2-differentiable-part2
                   (dc-fn-domain positive-domain)
                   (dc-fn1 (lambda (context x)
                             (f (REALPOSFIX x))))
                   (dc-fn2 (lambda (context x)
                             (- (realposfix x))))
                   (differential-dc-fn1
                    (lambda (context x eps)
                      (/ (- (f (+ x eps))
                            (f x))
                         eps)))
                   (differential-dc-fn2
                    (lambda (context x eps)
                      -1))
                   (derivative-dc-fn1
                    (lambda (context x)
                      (1+ (acl2-ln x))))
                   (derivative-dc-fn2
                    (lambda (context x)
                      -1))
                   (dc-fn1+fn2
                    (lambda (context x)
                      (ln-antiderivative (realposfix x))))
                   (differential-dc-fn1+fn2
                    (lambda (context x eps)
                      (/ (- (ln-antiderivative (realposfix (+ x eps)))
                            (ln-antiderivative (realposfix x)))
                         eps)))
                   (derivative-dc-fn1+fn2
                    (lambda (context x)
                      (acl2-ln (realposfix x))))
                  ;;;
                   (dc-fnz (lambda (context x) 1))
                   (differential-dc-fnz (lambda (context x eps) 0))
                   (derivative-dc-fnz (lambda (context x) 0))
                   )
                  (context 0)
                  )
                 )
           :in-theory (e/d (interval-definition-theory)
                           (ln-antiderivative))
           )
          )
  )
 ))


(local
 (defthm ln-antiderivative-differentiable
     (implies (and (standardp x)
		   (inside-interval-p x (positive-domain))
		   (inside-interval-p y1 (positive-domain))
		   (inside-interval-p y2 (positive-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2)))
              (and (i-limited (/ (- (ln-antiderivative x)
                                    (ln-antiderivative y1))
                                 (- x y1)))
	           (i-close (/ (- (ln-antiderivative x)
                                  (ln-antiderivative y1))
                               (- x y1))
                            (/ (- (ln-antiderivative x)
                                  (ln-antiderivative y2))
                               (- x y2))
                            )))
  :hints (("Goal"
	   :use ((:instance ln-antiderivative-differentiable-part1)
                 (:instance ln-antiderivative-differentiable-part2))))))


(local
 (defthm ln-antiderivative-works
     (implies (and (standardp x)
		   (inside-interval-p x (positive-domain))
                   (realp eps) (i-small eps) (not (= eps 0))
                   )
              (equal (standard-part (/ (- (ln-antiderivative (+ x eps))
                                          (ln-antiderivative x))
                                       eps))
                     (acl2-ln x)))
   :hints (("Goal"
	    :use ((:instance
                   (:functional-instance differential-dc-fn1+fn2-close
                                         (dc-fn-domain positive-domain)
                                         (dc-fn1 (lambda (context x)
                                                   (f (REALPOSFIX x))))
                                         (dc-fn2 (lambda (context x)
                                                   (- (realposfix x))))
                                         (differential-dc-fn1
                                          (lambda (context x eps)
                                            (/ (- (f (+ x eps))
                                                  (f x))
                                               eps)))
                                         (differential-dc-fn2
                                          (lambda (context x eps)
                                            (if (and (realp eps) (not (= 0 eps)))
                                                -1
                                                0)))
                                         (derivative-dc-fn1
                                          (lambda (context x)
                                            (1+ (acl2-ln x))))
                                         (derivative-dc-fn2
                                          (lambda (context x)
                                            -1))
                                         (dc-fn1+fn2
                                          (lambda (context x)
                                            (ln-antiderivative (realposfix x))))
                                         (differential-dc-fn1+fn2
                                          (lambda (context x eps)
                                            (/ (- (ln-antiderivative (realposfix (+ x eps)))
                                                  (ln-antiderivative (realposfix x)))
                                               eps)))
                                         (derivative-dc-fn1+fn2
                                          (lambda (context x)
                                            (acl2-ln (realposfix x))))
                  ;;;
                                         (dc-fnz (lambda (context x) 1))
                                         (differential-dc-fnz (lambda (context x eps) 0))
                                         (derivative-dc-fnz (lambda (context x) 0))
                                         )
                   (context 0)
                   )
                  )
            :in-theory (disable standard-part-of-plus)
            )
           ("Subgoal 7"
            :use ((:instance close-to-standard-in-positive-domain
                             (x x)
                             (y (+ x eps)))
                  )
            :in-theory (e/d (i-close
                             interval-definition-theory)
                            (standard-part-of-plus
                             f
                             f-prime))
            )
           ("Subgoal 6"
            :in-theory (enable interval-definition-theory))
           ("Subgoal 5"
            :in-theory (enable interval-definition-theory))
           ("Subgoal 4"
            :USE ((:INSTANCE f-prime-is-derivative (eps (/ (i-large-integer)))))
            :in-theory (E/D (interval-definition-theory)
                            (|(* (+ x y) z)|
                             |(* x (+ y z))|
                             STANDARD-PART-OF-PLUS
                             f-prime-is-derivative)))
           ("Subgoal 3"
            :in-theory (enable interval-definition-theory))
           ("Subgoal 2"
            :in-theory (enable interval-definition-theory))
           ("Subgoal 1"
            :in-theory (enable interval-definition-theory))
           ))
 )


;;; At this point, we know that ln-antiderivative truly is the
;;; antiderivative of ln. So we can now invoke the FTC-2 to
;;; compute the integral of ln. We proceed by doing the boilerplate
;;; necessary to define an integral.

(defun map-ln (p)
  (if (consp p)
      (cons (acl2-ln (realposfix (car p)))
            (map-ln (cdr p)))
      nil))

(defun riemann-ln (p)
  (dotprod (deltas p)
           (map-ln (cdr p))))

(defthm-std standard-ln
    (implies (standardp x)
             (standardp (acl2-ln x))))

(defthm limited-ln
    (implies (standardp x)
             (i-limited (acl2-ln x)))
  :hints (("Goal"
           :use ((:instance standards-are-limited
                            (x (acl2-ln x))))))
  )

(encapsulate
    nil

    (local
     (defthmd lemma-1
         (implies (and (realp x)
                       (realp y))
                  (equal (/ (+ x (- y)))
                         (- (/ (+ (- x) y)))))
       :INSTRUCTIONS (:PRO (:DV 2)
                           (:DV 1)
                           (:DV 1)
                           (:= (- (- X Y)))
                           :UP (:REWRITE |(/ (- x))|)
                           :TOP :S)))

    (local
     (defthm lemma-2
         (implies (and (realp x)
                       (realp x1))
                  (equal (* (+ (LN-ANTIDERIVATIVE (+ X X1 (- X)))
                               (- (LN-ANTIDERIVATIVE X)))
                            (/ (+ X1 (- X))))
                         (* (+ (- (LN-ANTIDERIVATIVE (+ X X1 (- X))))
                               (LN-ANTIDERIVATIVE X))
                            (/ (+ X (- X1))))))
       :hints (("Goal"
                :use ((:instance
                       (:theorem
                        (implies (and (realp x)
                                      (realp y))
                                 (equal (/ (- x) (- y))
                                        (/ x y))))
                       (x (+ (- (LN-ANTIDERIVATIVE (+ X X1 (- X))))
                             (LN-ANTIDERIVATIVE X)))
                       (y (/ (+ X (- X1))))))
                :in-theory (e/d (lemma-1)
                                (ln-ANTIderivative)))
               )))

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
			         (z y))
                      (:instance i-close-limited))
	        :in-theory (disable i-close-transitive
                                    i-close-limited)))))

    (local
     (DEFTHMd lemma-3
         (IMPLIES (AND (STANDARDP X)
                       (STANDARDP CONTEXT)
                       (INSIDE-INTERVAL-P X '((0)))
                       (INSIDE-INTERVAL-P X1 '((0)))
                       (I-CLOSE X X1)
                       (NOT (EQUAL X X1)))
                  (I-CLOSE (* (+ (LN-ANTIDERIVATIVE X)
                                 (- (LN-ANTIDERIVATIVE X1)))
                              (/ (+ X (- X1))))
                           (ACL2-LN X)))
       :INSTRUCTIONS
       (:PRO (:USE (:INSTANCE LN-ANTIDERIVATIVE-WORKS (EPS (- X1 X))))
             :PRO (:CLAIM (I-CLOSE X1 X))
             (:DEMOTE 8)
             (:DV 1)
             :X :TOP :PRO (:FORWARDCHAIN 1)
             (:DEMOTE 8)
             (:DV 1)
             (:DV 1)
             (:DV 1)
             (:DV 1)
             (:DV 1)
             (:DV 1)
             :S :UP :UP
             (:= (- (+ (- (LN-ANTIDERIVATIVE X1))
                       (LN-ANTIDERIVATIVE X))))
             :UP (:DV 2)
             (:DV 1)
             (:= (- (+ X (- X1))))
             :UP (:REWRITE |(/ (- x))|)
             :UP
             (:= (* (+ (- (LN-ANTIDERIVATIVE X1))
                       (LN-ANTIDERIVATIVE X))
                    (/ (+ X (- X1)))))
             :TOP :PRO
             (:USE (:INSTANCE CLOSE-IF-SAME-STANDARD-PART
                              (Y (* (+ (LN-ANTIDERIVATIVE X)
                                       (- (LN-ANTIDERIVATIVE X1)))
                                    (/ (+ X (- X1)))))
                              (X (ACL2-LN X))))
             :PRO
             (:USE (:INSTANCE (:INSTANCE LN-ANTIDERIVATIVE-DIFFERENTIABLE-PART1
                                         (Y1 X1))))
             :PRO (:FORWARDCHAIN 1)
             (:FORWARDCHAIN 1)
             :BASH)))

    (defthm limited-riemann-ln
        (implies (and (realp a) (standardp a)
		      (realp b) (standardp b)
		      (inside-interval-p a (positive-domain))
		      (inside-interval-p b (positive-domain))
		      (< a b))
	         (i-limited (riemann-ln (make-small-partition a b))))
      :otf-flg t
      :hints (("Goal"
	       :use ((:instance
                      (:functional-instance limited-riemann-rcdfn-prime-small-partition
				            (rcdfn-domain positive-domain)
				            (rcdfn
                                             (lambda (context x)
                                               (ln-antiderivative (realposfix x))))
                                            (rcdfn-prime
                                             (lambda (context x)
                                               (acl2-ln (realposfix x))))
				            (map-rcdfn-prime
                                             (lambda (context p)
                                               (map-ln p)))
				            (riemann-rcdfn-prime
                                             (lambda (context p)
                                               (riemann-ln p))))
                      (context 0)))
               )
              ("Subgoal 4"
               :use ((:instance acl2-ln-real-continuous (x x) (y x1)))
               :in-theory (e/d (interval-definition-theory)
                               (acl2-ln-real-continuous))
               )
              ("Subgoal 3"
               :use ((:instance lemma-3))
               :in-theory (enable interval-definition-theory)
               )
              ("Subgoal 2"
               :use ((:instance realp-ln (y x)))
               :in-theory (enable interval-definition-theory)
               )
              )
      )

    (local (in-theory (disable riemann-ln)))

    (defun-std strict-int-ln (a b)
      (if (and (realp a)
	       (realp b)
	       (inside-interval-p a (positive-domain))
	       (inside-interval-p b (positive-domain))
	       (< a b))
          (standard-part (riemann-ln (make-small-partition a b)))
          0))
)

(defun int-ln (a b)
  (if (<= a b)
      (strict-int-ln a b)
      (- (strict-int-ln b a))))

(LOCAL
 (defthmd int-ln-computation-lemma
     (implies (and (inside-interval-p a (positive-domain))
                   (inside-interval-p b (positive-domain)))
              (equal (int-ln a b)
                     (- (ln-antiderivative b)
                        (ln-antiderivative a))))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance ftc-2
                                         (rcdfn (lambda (context x)
                                                  (ln-antiderivative (realposfix x))))
                                         (rcdfn-prime (lambda (context x)
                                                        (acl2-ln (realposfix x))))
                                         (rcdfn-domain positive-domain)
                                         (map-rcdfn-prime (lambda (context p)
                                                            (map-ln p)))
                                         (riemann-rcdfn-prime (lambda (context p)
                                                                (riemann-ln p)))
                                         (strict-int-rcdfn-prime
                                          (lambda (context a b)
                                            (strict-int-ln a b)))
                                         (int-rcdfn-prime
                                          (lambda (context a b)
                                            (int-ln a b)))
                                         )
                   ))
            :in-theory (e/d (interval-definition-theory)
                            (ftc-2
                             ln-antiderivative)))
           )))

(defthmd int-ln-computation
    (implies (and (inside-interval-p a (positive-domain))
                  (inside-interval-p b (positive-domain)))
             (equal (int-ln a b)
                    (+ (- (* b (acl2-ln b))
                          (* a (acl2-ln a)))
                       (- a b))))
  :hints (("Goal"
           :use ((:instance int-ln-computation-lemma)))))

(defthmd int-ln-from-1-computation
    (implies (and (realp b)
                  (<= 1 b))
             (equal (int-ln 1 b)
                    (+ (* b (acl2-ln b))
                       (- b)
                       1)))
  :hints (("Goal"
           :use ((:instance int-ln-computation (a 1)))
           :in-theory (enable inside-interval-p))))
