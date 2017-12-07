; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "arith-nsa4")
(include-book "abs")
(include-book "eexp")
(include-book "phi-exists")
(include-book "computed-hints")
(include-book "tm-floor")

(in-theory (disable i-large))
(in-theory (disable standard-part-<=))

;; Cuong Chau: Some proofs failed when I left the following lemmas enable.

(local
 (in-theory (disable EPS-N-FUN-RW-1-THM
                     EPS-N-FUN-RW-2-THM
                     EPS-N-FUN-RW-3-THM
                     EPS-N-FUN-RW-4-THM)))

(defun f-sum (x n eps)
  (cond
   ((zp n) 0)
   (t (+ (* eps (f (run x (- n 1) eps)))
         (f-sum x (- n 1) eps)))))

(defthm run-f-sum-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps))
   (equal (run x n eps)
          (+ x (f-sum x n eps))))
  :rule-classes nil
  :hints (("Goal" :do-not '(generalize))
          ("Subgoal *1/2" :in-theory (disable step-run-thm)
           :use ((:instance
                  step-run-thm (n (- n 1)))))))

(defun resid (x n eps)
  (- (f-sum x n eps) (* n eps (f x))))

(defthm f-sum-type
  (implies
   (and
    (realp x)
    (realp eps))
   (realp (f-sum x n eps)))
  :rule-classes :type-prescription)

(defthm run-type
  (implies
   (and
    (realp x)
    (realp eps))
   (realp (run x n eps)))
  :rule-classes :type-prescription)

(defthm run-limited-thm
  (implies
   (and
    (realp x)
    (i-limited x)
    (realp eps)
    (integerp n)
    (< 0 eps)
    (<= 0 n)
    (i-limited (* eps n)))
   (i-limited (run x n eps)))
  :rule-classes ((:type-prescription) (:rewrite))
  :hints (("Goal" :in-theory (disable abs
                                      run
                                      run-n-limit
                                      i-large
                                      plus-limited
                                      times-limited
                                      divide-limited)
           :use ((:instance run-limit-eexpt-thm)
                 (:instance run-n-limit-limited-thm)
                 (:instance limited-bound-x-implies-limited-x-thm
                            (y (run-n-limit x n eps))
                            (x (run x n eps)))))))

(defthm resid-limited-thm
  (implies
   (and
    (realp x)
    (i-limited x)
    (integerp n)
    (<= 0 n)
    (realp eps)
    (< 0 eps)
    (i-limited (* eps n)))
   (i-limited (resid x n eps)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable i-large)
           :use ((:instance run-f-sum-thm)
                 (:instance run-limited-thm)))
          ("Goal'''" :use ((:instance times-limited
                                      (x (* eps n))
                                      (y (f x)))
                           (:instance plus-limited
                                      (x (+ X (F-SUM X N EPS)))
                                      (y (- x)))))))

(defthm resid-standard-thm
  (implies
   (and
    (realp x)
    (i-limited x)
    (integerp n)
    (<= 0 n)
    (realp eps)
    (< 0 eps)
    (i-limited (* eps n)))
   (standard-numberp (standard-part (resid x n eps))))
  :hints (("Goal" :in-theory (disable i-large resid)
           :use ((:instance resid-limited-thm)))))

(defthm resid-std-thm
  (IMPLIES
   (AND (STANDARD-NUMBERP X)
        (STANDARD-NUMBERP TM)
        (REALP X)
        (REALP TM)
        (<= 0 TM))
   (STANDARD-NUMBERP (STANDARD-PART
                      (resid X
                             (FLOOR1 (* (I-LARGE-INTEGER) TM))
                             (/ (I-LARGE-INTEGER))))))
  :hints (("Goal" :in-theory (disable i-large)
           :use ((:instance resid-standard-thm
                            (n (floor1 (* tm (i-large-integer))))
                            (eps (/ (i-large-integer))))))))

(in-theory (disable resid))

(defun-std resid-tm (x tm)
  (cond
   ((not (and (realp x)
              (realp tm)
              (<= 0 tm))) 0)
   (t (standard-part (resid x
                            (floor1 (* tm (i-large-integer)))
                            (/ (i-large-integer)))))))

(in-theory (enable resid))

(defthm f-run-bound-hint-1
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps))
   (equal (f (step1 x eps))
          (+ (f x) (- (f (step1 x eps)) (f x)))))
  :rule-classes nil)

(defthm f-run-bound-hint-2
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps))
   (<= (abs (f (step1 x eps)))
       (* (+ 1 (* eps (L))) (abs (f x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs)
           :use ((:instance f-run-bound-hint-1)
                 (:instance abs-triangular-inequality-thm
                            (x (f x))
                            (y (- (f (step1 x eps)) (f x))))
                 (:instance f-lim-thm
                            (x1 (step1 x eps))
                            (x2 x))))))

(defthm f-run-bound-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n))
   (<= (abs (f (run x n eps)))
       (* (eexp (* n eps (L))) (abs (f x)))))
  :hints (("Goal" :in-theory (disable abs step1)
           :do-not '(generalize))
          ("Subgoal *1/5" :use ((:instance pos-factor-<=-thm
                                           (x (abs (f (step1 x eps))))
                                           (y (* (+ 1 (* eps (L))) (abs (f x))))
                                           (a (EEXP (+ (* -1 (L) EPS)
                                                       (* (L) EPS N)))))
                                (:instance pos-factor-<=-thm
                                           (x (+ 1 (* eps (L))))
                                           (y (eexp (* eps (L))))
                                           (a (* (EEXP (+ (* -1 (L) EPS)
                                                          (* (L) EPS N)))
                                                 (abs (f x)))))
                                (:instance  f-run-bound-hint-2)
                                (:instance  1+x-<=eexp-thm
                                            (x (* eps (L))))))))

(defthm f-sum-exp-bound-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n))
   (<= (abs (f-sum x n eps))
       (* n eps (eexp (* eps n (L))) (abs (f x)))))
  :rule-classes nil
  :hints (("Goal" :induct (f-sum x n eps)
           :do-not-induct t
           :in-theory (disable abs <-*-LEFT-CANCEL)
           :do-not '(generalize))
          ("Subgoal *1/2" :use ((:instance f-run-bound-thm (n (- n 1)))
                                (:instance pos-factor-<=-thm
                                           (x  (abs (f (run x (- n 1) eps))))
                                           (y (* (eexp (* (- n 1) eps (L)))
                                                 (abs (f x))))
                                           (a eps))
                                (:instance abs-triangular-inequality-thm
                                           (x (F-SUM X (+ -1 N) EPS))
                                           (y (* EPS (F (RUN X (+ -1 N) EPS)))))
                                (:instance pos-factor-<=-thm
                                           (x 1)
                                           (y (EEXP (* (L) EPS)))
                                           (a (* EPS N (ABS (F X))
                                                 (EEXP (+ (* -1 (L) EPS)
                                                          (* (L) EPS N)))))
                                           )))))

(defthm f-sum-diff-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (integerp m)
    (<= 0 n)
    (<= n m))
   (equal (- (f-sum x m eps)
             (f-sum x n eps))
          (f-sum (run x n eps) (- m n) eps))))

(defthm f-run-diff-eq-f-sum-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (integerp m)
    (<= 0 n)
    (<= n m))
   (equal (- (run x m eps)
             (run x n eps))
          (f-sum (run x n eps) (- m n) eps)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance run-f-sum-thm (n m))
                 (:instance run-f-sum-thm)
                 (:instance f-sum-diff-thm)))))

(defthm pos-*-<=-thm
  (implies
   (and
    (realp a)
    (realp b)
    (realp x)
    (realp y)
    (<= 0 a)
    (<= 0 b)
    (<= a x)
    (<= b y))
   (<= (* a b) (* x y)))
  :hints (("Goal" :use ((:instance pos-factor-<=-thm
                                   (x a)
                                   (y x)
                                   (a b))
                        (:instance pos-factor-<=-thm
                                   (x b)
                                   (y y)
                                   (a x))))))

(defthm  f-run-diff-tm-thm-hint
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (integerp m)
    (integerp n)
    (<= n m))
   (<= 0 (* (- m n) eps (eexp (* (- m n) (L) eps)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable distributivity
                                      distributivity-left)
           :use ((:instance pos-factor-<=-thm
                            (x 0)
                            (y (- m n))
                            (a (* eps
                                  (eexp (* (- m n)
                                           (L)
                                           eps))))
                            )))))

(defthm f-run-diff-tm-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (integerp m)
    (<= 0 n)
    (<= n m))
   (<= (abs (- (run x m eps)
               (run x n eps)))
       (* (- m n) eps (eexp (* eps m (L))) (abs (f x)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable abs)
           :use ((:instance f-run-diff-tm-thm-hint)
                 (:instance f-run-diff-eq-f-sum-thm)
                 (:instance f-sum-exp-bound-thm
                            (x (run x n eps))
                            (n (- m n)))
                 (:instance f-run-bound-thm)
                 (:instance pos-factor-<=-thm
                            (x (abs (f (run x n eps))))
                            (y (* (eexp (* n eps (L))) (abs (f x))))
                            (a (* (- m n)
                                  eps
                                  (eexp (* eps
                                           (- m n)
                                           (L))))))))))

;; Cuong Chau: I need this lemma to prove some theorems in this book.

(defthm standard-number-is-limited
  (implies (standard-numberp r)
           (i-limited r)))

(defthm run-diff-tm-standard-part-thm
  (implies
   (and
    (realp x)
    (standard-numberp x)
    (integerp n)
    (integerp m)
    (realp eps)
    (< 0 eps)
    (<= 0 n)
    (<= 0 m)
    (i-limited (* eps n))
    (i-limited (* eps m))
    (equal (standard-part (* m eps))
           (standard-part (* n eps))))
   (equal (- (standard-part (run x m eps))
             (standard-part (run x n eps)))
          0))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (e/d (EPS-N-FUN-RW-1-THM
                                   EPS-N-FUN-RW-3-THM)
                                  (abs))
           :cases ((<= n m) (< m n))
           :do-not-induct t)
          ("Subgoal 2" :use ((:instance f-run-diff-tm-thm)))
          ("Subgoal 1" :use ((:instance f-run-diff-tm-thm
                                        (m n)
                                        (n m))))))

(defthm floor1-large-1<=
  (implies
   (and
    (realp x)
    (< 0 x)
    (standard-numberp x))
   (i-large (* (i-large-integer) x)))
  :hints (("Goal" :in-theory (enable i-large))))

(defthm large-gt-1
  (implies
   (and
    (realp x)
    (< 0 x)
    (i-large x))
   (< 1 x))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (enable i-large)
           :use ((:instance standard-part-<=
                            (x 1)
                            (y (/ x)))))))

(defthm standard-diff-*-large-thm
  (implies
   (and
    (realp x)
    (realp y)
    (standard-numberp x)
    (standard-numberp y)
    (< x y))
   (<= (+ (* (i-large-integer) x) 1)
       (* (i-large-integer) y)))
  :hints (("Goal" :use ((:instance floor1-large-1<= (x (- y x)))
                        (:instance large-gt-1
                                   (x (+ (* -1 (I-LARGE-INTEGER) X)
                                         (* (I-LARGE-INTEGER) Y))))
                        (:instance pos-factor-<-thm
                                   (x 0)
                                   (y (- y x))
                                   (a (i-large-integer)))))))

(defthm abs-standard-numberp
  (implies
   (and
    (realp x)
    (standard-numberp x))
   (standard-numberp (abs x))))

(defthm-std phi-diff-tm-thm
  (implies
   (and
    (realp x)
    (realp tm1)
    (realp tm2)
    (<= 0 tm1)
    (<= tm1 tm2))
   (<= (abs (- (phi x tm2)
               (phi x tm1)))
       (* (- tm2 tm1) (eexp (* tm2 (L))) (abs (f x)))))
  :rule-classes nil
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs <-CANCEL-DIVISORS)
           :use ((:instance f-run-diff-tm-thm
                            (eps (/ (i-large-integer)))
                            (n (floor1 (* tm1 (i-large-integer))))
                            (m (floor1 (* tm2 (i-large-integer)))))
                 (:instance L-STANDARD-THM)
                 (:instance F-STANDARD-THM)
                 (:instance standard-diff-*-large-thm
                            (x TM1)
                            (y TM2))))))

;; ----------------------------------------------
;; The following is the theorem which states
;; that phi is continuous with respect to time
;; ----------------------------------------------

(defthm phi-tm-continuous-thm
  (implies
   (and
    (realp x)
    (standard-numberp x)
    (realp tm1)
    (<= 0 tm1)
    (i-limited tm1))
   (equal (standard-part (phi x tm1))
          (phi x (standard-part tm1))))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs)
           :cases ((<= tm1 (standard-part tm1))
                   (< (standard-part tm1) tm1)))
          ("Subgoal 2" :use ((:instance phi-diff-tm-thm
                                        (tm1 tm1)
                                        (tm2 (standard-part tm1)))))
          ("Subgoal 1" :use ((:instance phi-diff-tm-thm
                                        (tm2 tm1)
                                        (tm1 (standard-part tm1)))))))

(defthm run-plus-thm
  (implies
   (and
    (integerp m)
    (integerp n)
    (<= 0 m)
    (<= 0 n))
   (equal (run (run x n eps) m eps)
          (run x (+ m n) eps))))

(defthm phi-diff-hint-1
  (implies
   (and
    (standard-numberp x1)
    (standard-numberp x2)
    (standard-numberp tm)
    (realp x1)
    (realp x2)
    (realp tm)
    (<= 0 tm))
   (equal (STANDARD-PART (* (EEXP (* (L) (/ (I-LARGE-INTEGER))
                                     (FLOOR1 (* (I-LARGE-INTEGER) TM))))
                            (ABS (+ X1 (* -1 X2)))))
          (* (EEXP (* (L) TM))
             (ABS (+ X1 (* -1 X2))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable *-commut-3way)
           :use (:instance L-STANDARD-THM))))

(defthm-std phi-x-diff-thm
  (implies
   (and
    (realp x1)
    (realp x2)
    (realp tm)
    (<= 0 tm))
   (<= (abs (- (phi x1 tm) (phi x2 tm)))
       (* (abs (- x1 x2)) (eexp (* tm (L))))))
  :rule-classes nil
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs i-large )
           :use ((:instance run-diff-limit-eexp-thm
                            (n (floor1 (* tm (i-large-integer))))
                            (eps (/ (i-large-integer))))
                 (:instance phi-diff-hint-1)))))

(defthm run-x-continuous-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (realp x)
    (i-limited x)
    (integerp n)
    (i-limited (* eps n))
    (<= 0 n))
   (equal (standard-part (run (standard-part x) n eps))
          (standard-part (run x n eps))))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs)
           :do-not-induct t
           :use ((:instance run-diff-limit-eexp-thm
                            (x1 x)
                            (x2 (standard-part x)))))))

;; -------------------------------------------
;; The following is the theorem which states
;; that phi is continuous with respect to x
;; -------------------------------------------

(defthm phi-x-continuous-thm
  (implies
   (and
    (realp x)
    (i-limited x)
    (realp tm)
    (standard-numberp tm)
    (<= 0 tm))
   (equal (standard-part (phi x tm))
          (phi (standard-part x) tm)))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs)
           :use ((:instance phi-x-diff-thm
                            (x1 x)
                            (x2 (standard-part x)))))))

(defthm phi-plus-hint1
  (implies
   (and
    (realp tm1)
    (realp tm2))
   (equal (standard-part (* (+ (FLOOR1 (* (I-LARGE-INTEGER) TM1))
                               (FLOOR1 (* (I-LARGE-INTEGER) TM2)))
                            (/ (I-LARGE-INTEGER))))
          (standard-part (* (floor1 (* (i-large-integer) (+ tm1 tm2)))
                            (/ (i-large-integer))))))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable <-CANCEL-DIVISORS)
           :use ((:instance pos-factor-<-thm
                            (x (+ (* (I-LARGE-INTEGER) TM1)
                                  (* (I-LARGE-INTEGER) TM2)
                                  -2))
                            (y (+ (FLOOR1 (* (I-LARGE-INTEGER) TM1))
                                  (FLOOR1 (* (I-LARGE-INTEGER) TM2))))
                            (a (/ (i-large-integer))))
                 (:instance pos-factor-<=-thm
                            (x (+ (FLOOR1 (* (I-LARGE-INTEGER) TM1))
                                  (FLOOR1 (* (I-LARGE-INTEGER) TM2))))
                            (y (+ (* (I-LARGE-INTEGER) TM1)
                                  (* (I-LARGE-INTEGER) TM2)))
                            (a (/ (i-large-integer))))
                 (:instance pos-factor-<-thm
                            (x (+ (* (i-large-integer) (+ tm1 tm2)) -1))
                            (y (floor1 (* (i-large-integer) (+ tm1 tm2))))
                            (a (/ (i-large-integer))))
                 (:instance pos-factor-<=-thm
                            (x (floor1 (* (i-large-integer) (+ tm1 tm2))))
                            (y (* (i-large-integer) (+ tm1 tm2)))
                            (a (/ (i-large-integer))))))))

(defthm tm1+tm2-limited-thm
  (implies
   (and
    (standard-numberp tm1)
    (standard-numberp tm2)
    (realp tm1)
    (realp tm2))
   (i-limited (* (/ (i-large-integer))
                 (floor1 (* (i-large-integer) (+ tm1 tm2))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance phi-plus-hint1)
                        (:instance standard+small->i-limited
                                   (x (standard-part
                                       (* (/ (i-large-integer))
                                          (floor1 (* (i-large-integer)
                                                     (+ tm1 tm2))))))
                                   (eps (- (* (/ (i-large-integer))
                                              (floor1 (* (i-large-integer)
                                                         (+ tm1 tm2))))
                                           (standard-part
                                            (* (/ (i-large-integer))
                                               (floor1 (* (i-large-integer)
                                                          (+ tm1 tm2)))))))
                                   )))))

;; -------------------------------------------
;; The following is the theorem which states
;; that phi is time invariant
;; -------------------------------------------

(defthm-std phi-plus-thm
  (implies
   (and
    (realp x)
    (realp tm1)
    (realp tm2)
    (<= 0 tm1)
    (<= 0 tm2))
   (equal (phi (phi x tm1) tm2)
          (phi x (+ tm1 tm2))))
  :hints (("Goal" :in-theory (disable i-large run-plus-thm)
           :use ((:instance phi-plus-hint1)
                 (:instance  tm1+tm2-limited-thm)
                 (:instance run-plus-thm (n (floor1 (* tm1
                                                       (i-large-integer))))
                            (m (floor1 (* tm2
                                          (i-large-integer))))
                            (eps (/ (i-large-integer))))
                 (:instance run-diff-tm-standard-part-thm
                            (eps (/ (i-large-integer)))
                            (m (+ (floor1 (* (i-large-integer) tm1))
                                  (floor1 (* (i-large-integer) tm2))))
                            (n (floor1 (* (i-large-integer) (+ tm1 tm2)))))
                 (:instance phi-x-continuous-thm
                            (x (RUN X
                                    (FLOOR1 (* (I-LARGE-INTEGER) TM1))
                                    (/ (I-LARGE-INTEGER))))
                            (tm tm2))))))

;; For some reason, enabling the following rule as a
;; linear lemma may cause ACL2 to stall during simplification

(defthm floor1-1-thm
  (implies
   (and (realp x)
        (<= 1 x))
   (< 0 (floor1 x)))
  :rule-classes nil)

;; For some reason, enabling the following rewrite rule
;; may cause ACL2 to stall during simplification

(defthm floor1-0-thm
  (implies
   (and (realp x)
        (<= 0 x)
        (< x 1))
   (equal (floor1 x) 0))
  :rule-classes nil)

(defun tm-m (tm eps)
  (cond
   ((not (and
          (realp eps)
          (< 0 eps)
          (realp tm)
          (<= eps tm))) 0)
   (t (floor1 (/ tm eps)))))

(defun phi-run (x tm eps)
  (declare (xargs :measure (tm-m tm eps)
                  :hints (("Subgoal 1.2"
                           :use ((:instance floor1-1-thm
                                            (x (* (/ eps) tm))))))))
  (cond
   ((not (and (realp eps)
              (< 0 eps)
              (<= eps tm)
              (realp tm))) (phi x tm))
   (t (phi-run (phi x eps) (- tm eps) eps))))

(defthm phi-run-eq-phi-thm
  (implies
   (and
    (realp x)
    (realp tm)
    (<= 0 tm)
    (< 0 eps)
    (realp eps))
   (equal (phi-run x tm eps)
          (phi x tm)))
  :rule-classes nil)

(defthm run-equal-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n))
   (equal (+ x (* eps n (f x)) (- (f-sum x n eps) (* n eps (f x))))
          (run x n eps)))
  :hints (("Goal" :use ((:instance run-f-sum-thm)))))

(defthm-std phi-equal-thm
  (implies
   (and
    (realp x)
    (realp tm)
    (<= 0 tm))
   (equal (+ x (* tm (f x)) (resid-tm x tm))
          (phi x tm)))
  :hints (("Goal" :use ((:instance F-STANDARD-THM)
                        (:instance run-f-sum-thm
                                   (eps (/ (i-large-integer)))
                                   (n (floor1 (* tm (i-large-integer))))
                                   )))))

(defthm step-resid-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n))
   (equal (+ (resid x n eps)
             (- (* eps (f (run x n eps)))
                (* eps (f x))))
          (resid x (+ n 1) eps))))

(defthm resid-type
  (implies
   (and
    (realp x)
    (realp eps)
    (integerp n))
   (realp (resid x n eps)))
  :rule-classes :type-prescription)

(defthm-std resid-tm-type
  (implies
   (and
    (realp x)
    (realp tm))
   (realp (resid-tm x tm)))
  :rule-classes :type-prescription)

(defthm step-resid-bound-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (< 0 n))
   (<= (abs (resid x n eps))
       (+ (abs (resid x (- n 1) eps))
          (* eps eps (L) (- n 1)
             (eexp (* eps (- n 1) (L)))
             (abs (f x))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs step-resid-thm resid)
           :use ((:instance f-sum-exp-bound-thm (n (- n 1)))
                 (:instance abs-triangular-inequality-thm
                            (x (RESID X (+ -1 N) EPS))
                            (y (- (* eps (f (run x (- n 1) eps)))
                                  (* eps (f x)))))
                 (:instance abs-pos-*-left-thm
                            (x eps)
                            (y (+ (* -1 (F X))
                                  (* (F (RUN X (+ -1 N) EPS))))))
                 (:instance f-lim-thm (x1 (run x (- n 1) eps))
                            (x2 x))
                 (:instance pos-factor-<=-thm
                            (x (ABS (+ (* -1 (F X))
                                       (* (F (RUN X (+ -1 N) EPS))))))
                            (y (* (L)
                                  (ABS (+ (* -1 X)
                                          (RUN X (+ -1 N) EPS)))))
                            (a eps))
                 (:instance run-f-sum-thm (n (- n 1)))
                 (:instance step-resid-thm (n (- n 1)))
                 (:instance pos-factor-<=-thm
                            (x (abs (f-sum x (- n 1) eps)))
                            (y (* (- n 1)
                                  eps
                                  (eexp (* eps (- n 1) (L)))
                                  (abs (f x))))
                            (a (* eps (L))))))))

(defthm resid-bound-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n))
   (<= (abs (resid x n eps))
       (* n n eps eps (L) (eexp (* n eps (L))) (abs (f x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs)
           :do-not '(generalize)
           :do-not-induct t
           :induct (f-sum x n eps))
          ("Subgoal *1/2" :in-theory (disable abs resid
                                              <-*-LEFT-CANCEL)
           :use ((:instance step-resid-bound-thm)
                 (:instance pos-factor-<=-thm
                            (x 0)
                            (y (- n 1))
                            (a (* (L) eps)))
                 (:instance pos-factor-<=-thm
                            (x 1)
                            (y (eexp (* eps (L))))
                            (a (* (L) EPS EPS N N
                                  (ABS (F X))
                                  (EEXP (+ (* -1 (L) EPS)
                                           (* (L) EPS N)))))
                            )))))

(defthm tm-fun-rw-5-thm
  (implies
   (and
    (realp a)
    (realp b)
    (realp c)
    (realp tm)
    (standard-numberp tm))
   (equal (* (/ (I-LARGE-INTEGER)) a b
             (FLOOR1 (* (I-LARGE-INTEGER) TM)) c)
          (* (tm-fun tm) a b c)))
  :hints (("Goal" :in-theory (e/d (tm-fun) (tm-fun-rw-1-thm
                                            tm-fun-rw-2-thm
                                            tm-fun-rw-3-thm
                                            tm-fun-rw-4-thm)))))

(defthm tm-fun-rw-6-thm
  (implies
   (and
    (realp a)
    (realp b)
    (realp c)
    (realp d)
    (realp tm)
    (standard-numberp tm))
   (equal (* (/ (I-LARGE-INTEGER)) a b c
             (FLOOR1 (* (I-LARGE-INTEGER) TM)) d)
          (* (tm-fun tm) a b c d)))
  :hints (("Goal" :in-theory (e/d (tm-fun) (tm-fun-rw-1-thm
                                            tm-fun-rw-2-thm
                                            tm-fun-rw-3-thm
                                            tm-fun-rw-4-thm
                                            tm-fun-rw-5-thm)))))

(defthm-std resid-tm-bound-thm
  (implies
   (and
    (realp x)
    (realp tm)
    (<= 0 tm))
   (<= (abs (resid-tm x tm))
       (* tm tm (L) (eexp (* tm (L))) (abs (f x)))))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs <-CANCEL-DIVISORS)
           :use ((:instance F-STANDARD-THM)
                 (:instance L-STANDARD-THM)
                 (:instance resid-bound-thm
                            (eps (/ (i-large-integer)))
                            (n (floor1 (* tm (i-large-integer)))))))))

(defthm tm-floor-0-thm
  (implies
   (and
    (realp tm)
    (realp eps)
    (<= 0 tm)
    (< 0 eps)
    (< tm eps))
   (equal (FLOOR1 (* (/ EPS) TM))  0))
  :hints (("Goal" :use ((:instance floor1-0-thm (x (/ tm eps)))))))

(defthm-std phi-0-thm
  (implies
   (realp x)
   (equal (phi x 0)
          x)))

(defun tm-induct (tm eps)
  (declare (xargs :measure (tm-m tm eps)
                  :hints (("Subgoal 1.2"
                           :use ((:instance floor1-1-thm
                                            (x (* (/ eps) tm))))))))
  (cond
   ((not (and
          (realp eps)
          (< 0 eps)
          (realp tm)
          (<= eps tm))) tm)
   (t (tm-induct (- tm eps)
                 eps))))

(defthm phi-eps-step-thm
  (implies
   (and
    (realp x1)
    (realp x2)
    (realp eps)
    (< 0 eps))
   (<= (abs (- (phi x1 eps) (step1 x2 eps)))
       (+ (* (abs (- x1 x2)) (+ 1 (* eps (L))))
          (* eps eps (L) (eexp (* eps (L))) (abs (f x1))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs)
           :do-not '(generalize)
           :do-not-induct t
           :use ((:instance phi-equal-thm (x x1) (tm eps))
                 (:instance abs-triangular-inequality-thm
                            (x (+ X1 (* -1 X2)))
                            (y (+(RESID-TM X1 EPS)
                                 (* EPS (F X1))
                                 (* -1 EPS (F X2)))))
                 (:instance abs-triangular-inequality-thm
                            (x (RESID-TM X1 EPS))
                            (y (+ (* EPS (F X1))
                                  (* -1 EPS (F X2)))))
                 (:instance resid-tm-bound-thm
                            (tm eps)
                            (x x1))
                 (:instance abs-pos-*-left-thm
                            (x eps)
                            (y (- (F X1)
                                  (F X2))))
                 (:instance f-lim-thm)
                 (:instance pos-factor-<=-thm
                            (x (abs (- (f x1) (f x2))))
                            (y (* (L) (abs (- x1 x2))))
                            (a eps))))))

(defthm phi-phi-run-thm
  (implies
   (and
    (realp eps)
    (realp x)
    (realp tm)
    (<= 0 tm)
    (<= eps tm)
    (< 0 eps))
   (equal (phi (phi-run x
                        (+ (* -1 EPS)
                           (* EPS
                              (FLOOR1 (* (/ EPS) TM))))
                        eps) eps)
          (phi-run x (* eps (floor1 (/ tm eps))) eps)))
  :hints (("Goal" :induct (phi-run x tm eps)
           :do-not '(generalize))
          ("Subgoal *1/4" :use ((:instance floor1-1-thm
                                           (x (/ tm eps)))
                                (:instance pos-factor-<=-thm
                                           (x 1)
                                           (y (floor1 (/ tm eps)))
                                           (a eps))))
          ("Subgoal *1/2" :use ((:instance floor1-1-thm (x (/ tm eps)))
                                (:instance pos-factor-<=-thm
                                           (x 1)
                                           (y (floor1 (/ tm eps)))
                                           (a eps))))
          ("Subgoal *1/1" :use ((:instance tm-floor-0-thm
                                           (tm (- tm eps)))
                                (:instance distributivity
                                           (y (FLOOR1 (* (/ EPS) TM)))
                                           (z -1)
                                           (x eps))))))

(defthm f-standard-part-thm
  (implies
   (and
    (realp x)
    (i-limited x))
   (equal (standard-part (f x))
          (f (standard-part x))))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs STANDARDP-STANDARD-PART)
           :use ((:instance F-STANDARD-THM
                            (x (standard-part x)))
                 (:instance f-lim-thm
                            (x1 (standard-part x))
                            (x2 x))
                 (:instance standardp-standard-part)))))

(defthm-std f-phi-bound-thm
  (implies
   (and
    (realp x)
    (realp tm)
    (<= 0 tm))
   (<= (abs (f (phi x tm)))
       (* (eexp (* tm (L))) (abs (f x)))))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs)
           :use ((:instance L-STANDARD-THM)
                 (:instance f-run-bound-thm
                            (eps (/ (i-large-integer)))
                            (n (floor1 (* tm (i-large-integer))))
                            )))))

(defthm phi-eps-arith-hint
  (implies
   (and
    (realp tm)
    (< 0 eps)
    (realp eps))
   (equal
    (* (EEXP (* (L) EPS))
       (FLOOR1 (* (/ EPS) TM))
       (EEXP (+ (* -1 (L) EPS)
                (* (L) EPS (FLOOR1 (* (/ EPS) TM))))))
    (* (FLOOR1 (* (/ EPS) TM))
       (EEXP (* (L) EPS (FLOOR1 (* (/ EPS) TM)))))))
  :hints (("Goal" :in-theory (disable *-commut-3way)
           :use ((:instance *-commut-3way
                            (x (EEXP (* (L) EPS)))
                            (y (FLOOR1 (* (/ EPS) TM)))
                            (z (EEXP (+ (* -1 (L) EPS)
                                        (* (L) EPS
                                           (FLOOR1 (* (/ EPS) TM))))))
                            )))))

(defthm phi-eps-thm
  (implies
   (and
    (realp x)
    (realp tm)
    (realp eps)
    (<= 0 tm)
    (< 0 eps))
   (<= (abs (- (phi-run x
                        (* eps (floor1 (/ tm eps)))
                        eps)
               (run x
                    (floor1 (/ tm eps))
                    eps)))
       (* eps eps
          (floor1 (/ tm eps))
          (L)
          (abs (f x))
          (eexp (* eps (floor1 (/ tm eps)) (L))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs)
           :induct (tm-induct tm eps)
           :do-not '(generalize))
          ("Subgoal *1/2" :in-theory (disable abs run step1)
           :use ((:instance floor1-1-thm (x (/ tm eps)))
                 (:instance pos-factor-<=-thm
                            (x 1)
                            (y (floor1 (/ tm eps)))
                            (a eps))))
          ("Subgoal *1/2.1" :in-theory (disable abs run step1
                                                <-*-left-cancel
                                                <-cancel-divisors)
           :use ((:instance phi-run-eq-phi-thm
                            (tm (+ (* -1 EPS)
                                   (* EPS (FLOOR1 (* (/ EPS) TM))))))
                 (:instance phi-run-eq-phi-thm
                            (tm (* EPS (FLOOR1 (* (/ EPS) TM)))))
                 (:instance 1+x-<=eexp-thm (x (* eps (L))))
                 (:instance phi-eps-arith-hint)
                 (:instance pos-factor-<=-thm
                            (x (+ 1 (* eps (L))))
                            (y (eexp (* eps (L))))
                            (a (ABS (+ (* -1
                                          (RUN X
                                               (+ -1
                                                  (FLOOR1
                                                   (* (/ EPS) TM)))
                                               EPS))
                                       (PHI-RUN X
                                                (+ (* -1 EPS)
                                                   (* EPS
                                                      (FLOOR1
                                                       (* (/ EPS) TM))))
                                                EPS)))))
                 (:instance pos-factor-<=-thm
                            (x (ABS (+ (* -1
                                          (RUN X
                                               (+ -1 (FLOOR1
                                                      (* (/ EPS) TM)))
                                               EPS))
                                       (PHI-RUN X
                                                (+ (* -1 EPS)
                                                   (* EPS
                                                      (FLOOR1
                                                       (* (/ EPS) TM))))
                                                EPS))))
                            (y (+ (* -1 (L)
                                     EPS EPS (ABS (F X))
                                     (EEXP (+ (* -1 (L) EPS)
                                              (* (L) EPS
                                                 (FLOOR1
                                                  (* (/ EPS) TM))))))
                                  (* (L)
                                     EPS EPS (ABS (F X))
                                     (FLOOR1 (* (/ EPS) TM))
                                     (EEXP (+ (* -1 (L) EPS)
                                              (* (L) EPS
                                                 (FLOOR1
                                                  (* (/ EPS) TM)))))
                                     )))
                            (a (EEXP (* (L) EPS))))
                 (:instance pos-factor-<=-thm
                            (x (ABS (F (PHI X
                                            (+ (* -1 EPS)
                                               (* EPS
                                                  (FLOOR1
                                                   (* (/ EPS) TM))))
                                            ))))
                            (y (* (ABS (F X))
                                  (EEXP (+ (* -1 (L) EPS)
                                           (* (L) EPS
                                              (FLOOR1
                                               (* (/ EPS) TM))
                                              )))))
                            (a (* (L) EPS EPS (EEXP (* (L) EPS)))))
                 (:instance phi-eps-step-thm
                            (x1 (phi-run x
                                         (* eps
                                            (- (floor1 (/ tm eps)) 1))
                                         eps))
                            (x2 (run x (- (floor1
                                           (/ tm eps)) 1) eps)))
                 (:instance f-phi-bound-thm
                            (tm (+ (* -1 EPS)
                                   (* EPS (FLOOR1 (* (/ EPS) TM)))))
                            )))))

(defthm phi-any-small-eps-thm
  (implies
   (and
    (realp x)
    (realp tm)
    (standard-numberp x)
    (standard-numberp tm)
    (realp eps)
    (<= 0 tm)
    (< 0 eps)
    (i-small eps))
   (equal (standard-part (phi x tm))
          (standard-part (run x (floor1 (/ tm eps)) eps))))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs phi)
           :use ((:instance small-are-limited (x eps))
                 (:instance phi-eps-thm)
                 (:instance phi-run-eq-phi-thm
                            (tm (* EPS (FLOOR1 (* (/ EPS) TM)))))))))

;; ----------------------------------------------
;; The following is the theorem which states
;; that run, hence phi, is independent of the
;; choice of eps.
;; ----------------------------------------------

(defthm run-any-small-eps-thm
  (implies
   (and
    (realp x)
    (realp tm)
    (standard-numberp x)
    (standard-numberp tm)
    (realp eps)
    (<= 0 tm)
    (< 0 eps)
    (i-small eps))
   (equal (standard-part (run x
                              (floor1 (* tm (i-large-integer)))
                              (/ (i-large-integer))))
          (standard-part (run x
                              (floor1 (/ tm eps))
                              eps))))
  :hints (("Goal" :use ((:instance  phi-any-small-eps-thm)))))
