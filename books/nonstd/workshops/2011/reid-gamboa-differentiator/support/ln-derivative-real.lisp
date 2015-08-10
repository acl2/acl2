(in-package "ACL2")

(include-book "exp-minimal")
(include-book "nonstd/nsa/ln" :dir :system)
(include-book "inverse-derivative")
(include-book "exp-properties")

(local
 (defun ln-domain-p (x)
  (and (realp x)
       (< 0 x))))

(local
 (defun exp-domain-p (x)
  (realp x)))


(local
 (defthm acl2-exp-standard-part-out
   (implies (and (acl2-numberp x) (i-limited x))
            (equal (acl2-exp (standard-part x))
                   (standard-part (acl2-exp x))))
   :hints
   (("goal" :in-theory (enable-disable (i-close i-small)
                                       (exp-continuous-for-limited
                                        exp-continuous-2
                                        exp-continuous))
     :use (:instance exp-continuous-for-limited
                     (x (standard-part x))
                     (Y X))))))

(defthm-std acl2-ln-for-positive-standard
   (implies (standardp x)
            (standardp (acl2-ln-for-positive x))))

; In order to prove that acl2-ln is limited for any non-small x, I
; use the fact that acl2-exp is large for large, positive x. I prove that by
; establishing x as a (loose) lower bound for acl2-exp. The first two terms
; in acl2-exp's Taylor series expansions are 1+x and all subsequent terms
; are positive, which proves the power bound.
(local
 (defthm taylor-exp-term-positive
  (implies (and (realp x)
                (< 0 x)
                (integerp counter)
                (< 0 counter))
           (< 0 (taylor-exp-term x counter)))))

(local
 (defthm taylor-exp-list-positive
  (implies (and (realp x)
                (< 0 x)
                (< 0 counter)
                (integerp counter)
                (< 0 nterms) (integerp nterms))
           (< 0 (sumlist (taylor-exp-list nterms counter x))))
  :hints (("Subgoal *1/4"
           :expand (taylor-exp-list 1 counter x)))))

(local
 (defthm first-taylor-exp-list
   (implies (and (integerp nterms)
                 (acl2-numberp x)
                 (< 2 nterms))
            (equal (cadr (taylor-exp-list nterms 0 x))
                   x))
   :hints (("Goal"
            :expand (taylor-exp-list nterms 0 x))
           ("Goal'"
            :expand (TAYLOR-EXP-LIST (+ -1 NTERMS) 1 X)))))

(local
 (defthm expand-out-exp-list-lemma
   (implies (and (acl2-numberp x)
                 (integerp nterms)
                 (< 2 nterms))
            (equal (SUMLIST (TAYLOR-EXP-LIST nterms 0 x))
                   (+ 1
                      x
                      (sumlist (taylor-exp-list (- nterms 2) 2 x)))))))

(local
 (defthm expand-out-exp-list-less
  (implies (and (acl2-numberp x)
                (realp x)
                (< 0 x)
                (integerp nterms)
                (< 3 nterms))
           (< x (SUMLIST (TAYLOR-EXP-LIST nterms 0 x))))
  :hints (("Goal" :in-theory (disable taylor-exp-list-positive)
           :use ((:instance  taylor-exp-list-positive
                             (nterms (- nterms 2))
                             (counter 2)
                             (x x)))))))


(local
 (defthm i-large-integer->-3
  (< 3 (I-LARGE-INTEGER))
  :hints (("Goal"
           :use (:instance large->-non-large (x (i-large-integer))
                           (y 3))))))

(defthm-std x-<=-exp
  (implies (and (realp x)
                (< 0 x))
           (<= x (acl2-exp x)))
  :hints (("Goal"
           :use ((:instance expand-out-exp-list-less
                           (nterms (i-large-integer))
                           (x x))
                 (:instance standard-part-<=
                            (y (SUMLIST (TAYLOR-EXP-LIST (I-LARGE-INTEGER)
                                           0 X)))
                            (x x)))
           :in-theory (enable-disable (acl2-exp)
                                      (EXPAND-OUT-EXP-LIST-LESS
                                       STANDARD-PART-<=)))))


(defthm exp-large-for-positive-large
  (implies (and (i-large x)
                (< 0 x)
                (realp x))
           (i-large (acl2-exp x)))
  :hints (("Goal" :use (:instance large-if->-large
                                  (x x) (y (acl2-exp x))))))

(defthm acl2-exp-nondecreasing
  (implies (and (realp x)
                (realp y)
                (<= x y))
           (<= (acl2-exp x) (acl2-exp y)))
  :hints (("Goal" :cases ((< x y) (= x y))))
  :rule-classes (:linear :rewrite))

(defthm acl2-ln-for-positive-increasing
  (implies (and (realp x)
                (realp y)
                (< x y)
                (< 0 x) )
           (< (acl2-ln-for-positive x)
              (acl2-ln-for-positive y)))
  :hints (("Goal" :use (:instance acl2-exp-nondecreasing
                                  (y (acl2-ln-for-positive x))
                                  (x (acl2-ln-for-positive y)))))
  :rule-classes (:linear :rewrite))

(defthm acl-ln-positive-1
  (equal (acl2-ln-for-positive 1)
         0)
  :hints (("Goal" :use (:instance uniqueness-of-ln-for-positive
                                  (x 0) (y 1)))))

(defthm acl2-ln-positive->-1
  (implies (and (realp x)
                (< 1 x))
           (< 0 (acl2-ln-for-positive x)))
  :hints (("Goal" :use (:instance acl2-ln-for-positive-increasing
                                  (x 1) (y x)))))

(defthm ln-for-positive-limited->-1
  (implies (and (i-limited x)
                (realp x)
                (< 1 x))
           (i-limited (acl2-ln-for-positive x)))
  :hints (("Goal"
           :in-theory (disable exp-large-for-positive-large)
           :use (:instance exp-large-for-positive-large
                           (x (acl2-ln-for-positive x))))))

(local
 (defthm /-x-not-large
   (implies (and (acl2-numberp x)
                 (not (i-small x)))
            (not (i-large (/ x))))
   :hints (("Goal" :in-theory (enable i-small i-large)))))

(local
 (defthm ln-for-positive-limited-<-1
   (implies (and (not (i-small x))
                 (realp x)
                 (< 0 x)
                 (< x 1))
            (i-limited (acl2-ln-for-positive x)))
   :hints (("Goal"
            :in-theory (enable-disable (acl2-ln-for-positive)
                                       (ln-for-positive-limited->-1))
            :use ((:instance ln-for-positive-limited->-1 (x (/ x))))))))

(defthm ln-for-positive-limited
  (implies (and (realp x)
                (i-limited x)
                (< 0 x)
                (not (i-small x)))
           (i-limited (acl2-ln-for-positive x)))
  :hints (("Goal" :cases ((< 1 x) (= 1 x) (> 1 x)))))

(defthm-std pi-standard
  (standardp (acl2-pi))
  :rule-classes (:rewrite :type-prescription))
(local
 (defthm pi-limited
   (i-limited (acl2-pi))
   :rule-classes (:rewrite :type-prescription)))

(defthm anglepart-limited
  (i-limited (anglepart x))
  :hints (("Goal" :in-theory (disable anglepart LARGE-IF->-LARGE anglepart-between-0-and-2pi)
          :use ((:instance anglepart-between-0-and-2pi)
                (:instance limited-squeeze
                           (a 0)
                           (b (* 2 (acl2-pi)))
                           (x (anglepart x))) ))))


(local
 (defthm add-square-to-nonsmall
   (implies (and (realp x) (< 0 x) (not (i-small x))
                 (realp y))
            (not (i-small (+ x (* y y)))))))


(defthm i-small-sqrt
  (implies (and (realp x)
                (<= 0 x))
           (equal (i-small (acl2-sqrt x))
                  (i-small x)))
  :hints (("Goal" :use (:instance i-small-* (x (acl2-sqrt x))))))



(defthm radiuspart-not-small
  (implies (acl2-numberp x)
           (equal (i-small (radiuspart x))
                  (i-small x)))
  :hints (("Goal"
           :cases ((and (i-small (realpart x)) (i-small (imagpart x)))
                   (not (i-small (imagpart x)))
                   (not (i-small (realpart x)))))
          ("Subgoal 3" :use (:instance complex-small (x x)))
          ("Subgoal 2" :use ((:instance complex-small (x x))
                             (:instance add-square-to-nonsmall
                                        (x (* (imagpart x) (imagpart x)))
                                        (y (realpart x)))))
          ("Subgoal 1" :use ((:instance complex-small (x x))
                             (:instance add-square-to-nonsmall
                                        (x (* (realpart x) (realpart x)))
                                        (y (imagpart x)))))))

(local
 (defthmd number-limited
  (implies (and (acl2-numberp x)
                (i-limited (realpart x))
                (i-limited (imagpart x)))
	   (i-limited x))
  :hints (("Goal" :in-theory (enable )
           :use (:instance complex-limited-1)))))

(defthm i-large-*
  (implies (acl2-numberp x)
           (equal (i-large (* x x)) (i-large x)))
  :hints (("Goal"
           :cases ((i-limited x)))))


(defthm large-sqrt
  (implies (and (realp x)
                (<= 0 x))
           (equal (i-large (acl2-sqrt x))
                  (i-large x)))
  :hints (("Goal" :use (:instance i-large-* (x (acl2-sqrt x))))))

(local
 (defthm large-*-+
  (implies (and (realp x)
                (i-large x)
                (realp y)
                )
           (i-large (+ (* y y) (* x x))))
  :hints (("Goal"
           :use (:instance large-if->-large
                           (x (* x x))
                           (y (+ (* y y) (* x x))))))))

(local
 (defthm number-large-1
   (implies (complexp x)
	    (implies (or (i-large (realpart x))
			 (i-large (imagpart x)))
		     (i-large x)))
   :hints (("Goal"
	    :in-theory (enable i-small i-large)))))

(defthm radiuspart-limited
  (implies (acl2-numberp x)
           (equal (i-large (radiuspart x))
                  (i-large x)))
  :hints (("Goal"
           :cases ((i-large (realpart x))
                   (i-large (imagpart x))))
          ("Subgoal 3"
           :use (:instance number-limited))
          ("Subgoal 2"
           :in-theory (enable abs)
           :use ((:instance number-limited)
                 (:instance large-*-+
                            (x (realpart x))
                            (y (imagpart x)))
                 (:instance number-large-1)))
          ("Subgoal 1"
           :in-theory (enable abs)
           :use ((:instance number-limited)
                 (:instance large-*-+
                            (x (realpart x))
                            (y (imagpart x)))
                 (:instance number-large-1)))))

(local
 (defthmd zero-is-small
   (implies (equal x 0)
            (i-small x))))

(defthm acl2-ln-limited
  (implies (and (i-limited x)
                (not (i-small x)))
           (i-limited (acl2-ln x)))
  :hints (("Goal"
           :in-theory (enable-disable (acl2-ln)
                                      (radiuspart anglepart))
           :use ((:instance zero-is-small (x (radiuspart x)))
                 (:instance number-limited (x (acl2-ln x)))
                 (:instance ln-for-positive-limited (x (radiuspart x)))))))

(defthm-std acl2-ln-standard
  (implies (standardp x)
           (standardp (acl2-ln x)))
  :hints (("Goal" :in-theory (enable acl2-ln))))


(local
 (defthm acl2-ln-continuous-lemma-1
   (implies (and (realp x) (< 0 x)
                 (realp y) (< 0 y)
                 (i-limited x)
                 (i-limited y)
                 (i-close x y))

            (i-close (acl2-exp (acl2-ln x)) (acl2-exp (acl2-ln y))))))

(local
 (defthm acl2-ln-continuous-lemma-2
   (implies (and (realp x) (< 0 x)
                 (realp y) (< 0 y)
                 (standardp x)
                 (i-close x y))
            (equal (acl2-exp (standard-part (acl2-ln x)))
                   (acl2-exp (standard-part (acl2-ln y)))))
   :hints (("Goal" :use ((:instance acl2-ln-continuous-lemma-1)
                         (:instance acl2-exp-standard-part-out
                                    (x (acl2-ln x)))
                         (:instance acl2-exp-standard-part-out
                                    (x (acl2-ln y)))
                         (:instance i-close-limited (x x) (y y)))
            :in-theory (enable-disable (i-close i-small)
                                       (exp-ln acl2-ln-continuous-lemma-1
                                               acl2-exp-standard-part-out
                                               i-close-limited
                                               i-close-limited-2
                                               LIMITED+LARGE->LARGE
                                               ))))))

(defthm acl2-ln-real-continuous
  (implies (and (realp x) (< 0 x)
                (realp y) (< 0 y)
                (standardp x)
                (i-close x y))
           (i-close (acl2-ln x)
                    (acl2-ln y)))
  :hints (("Goal"
           :in-theory (enable i-close i-small)
           :use ((:instance acl2-exp-is-1-1
                           (x (standard-part (acl2-ln x)))
                           (y (standard-part (acl2-ln y))))
                 (:instance acl2-ln-continuous-lemma-2)))))


(defthm acl2-ln-real-derivative
  (implies (and (realp x) (< 0 x)
                (realp y) (< 0 y)
                (standardp x)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (acl2-ln x) (acl2-ln y))
                       (- x y))
                    (/ x)))
  :hints (("Goal"
           :use (:functional-instance
                 inverse-g-close
                 (inverse-f acl2-exp)
                 (inverse-f-domain-p exp-domain-p)
                 (inverse-f-prime acl2-exp)
                 (inverse-g acl2-ln)
                 (inverse-g-domain-p ln-domain-p)))
          ("Subgoal 3"
; changed from "Subgoal 4" by Matt K. 12/13/12, probably because of tau-system
           :use (:instance acl2-exp-derivative))))


(defthmd elem-acl2-ln-close
  (implies (and (realp x) (< 0 x)
                (realp y) (< 0 y)
                (standardp x)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (acl2-ln x) (acl2-ln y))
                       (- x y))
                    (/ x)))
  :hints (("Goal" :use (:instance acl2-ln-real-derivative))))

(differentiable-criteria-expr
 elem-acl2-ln
 (acl2-ln x)
 (and (realp x) (< 0 x)))

(differentiable-criteria-expr
 elem-acl2-ln-prime
 (/ x)
 (and (realp x) (< 0 x)))


(def-elem-derivative acl2-ln
  elem-acl2-ln
  (and (realp x) (< 0 x))
  (/ x))
