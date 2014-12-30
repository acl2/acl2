; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "arith-nsa4")
(include-book "nsa")
(include-book "eexp")

(defstub f (x) t)
(defstub L () t)
(defstub h (x1 x2 eps) t)

(defaxiom L-type
  (and
   (realp (L))
   (< 0 (L)))
  :rule-classes :type-prescription)

(defaxiom L-standard-thm
  (standard-numberp (L))
  :rule-classes :type-prescription)

(defaxiom L-i-limited-thm
  (i-limited (L))
  :rule-classes  ((:type-prescription) (:rewrite)))

(defaxiom f-type
  (realp (f x))
  :rule-classes :type-prescription)

(defaxiom f-standard-thm
  (implies
   (and
    (realp x)
    (standard-numberp x))
   (standard-numberp (f x)))
  :rule-classes :type-prescription)

(defaxiom f-i-limited-thm
  (implies
   (and
    (realp x)
    (i-limited x))
   (i-limited (f x)))
  :rule-classes  ((:type-prescription) (:rewrite)))

(defaxiom f-lim-thm
  (implies
   (and
    (realp x1)
    (realp x2))
   (and
    (<= (abs (- (f x1) (f x2)))
        (* (L) (abs (- x1 x2)))))))

(defun step1 (x eps)
  (+ x (* (f x) eps)))

(defun run (x n eps)
  (cond
   ((zp n) x)
   (t (run (step1 x eps) (- n 1) eps))))

(defun run-limit (delta n eps)
  (cond
   ((zp n) delta)
   (t (* (+ 1 (* eps (L))) (run-limit delta (- n 1) eps)))))

(defthm run-limit-realp
  (implies
   (and
    (realp delta)
    (realp eps))
   (realp (run-limit delta n eps)))
  :rule-classes :type-prescription)

(defthm run-limit-n+1-thm
  (implies
   (and
    (realp eps)
    (realp delta)
    (<= 0 delta)
    (< 0 eps)
    (integerp n)
    (<= 0 n))
   (<= (run-limit delta n eps)
       (run-limit delta (+ n 1) eps)))
  :hints (("Goal" :in-theory (disable distributivity-left))))

; Added by Matt K.: Avoids rewriter loop in abs-step-thm.
(local (in-theory (disable commutativity-2-of-+)))

(defthm abs-step-thm
  (implies
   (and
    (realp x1)
    (realp x2)
    (realp eps)
    (< 0 eps))
   (<= (abs (- (step1 x1 eps)
               (step1 x2 eps)))
       (+ (abs (- x1 x2))
          (abs (* eps (- (f x1) (f x2)))))))
  :rule-classes :linear)

(defthm step-1+leps-thm-1
  (implies
   (and
    (realp x1)
    (realp x2)
    (realp eps)
    (< 0 eps))
   (<= (abs (- (step1 x1 (/ eps))
               (step1 x2 (/ eps))))
       (* (+ 1 (* (L) (/ eps))) (abs (- x1 x2)))))
  :hints (("Goal"
           :use ((:instance f-lim-thm)
                 (:instance abs-step-thm (eps (/ eps))))))
  :rule-classes nil)

(defthm step-1+leps-thm
  (implies
   (and
    (realp x1)
    (realp x2)
    (realp eps)
    (< 0 eps))
   (<= (abs (- (step1 x1 eps)
               (step1 x2 eps)))
       (* (+ 1 (* (L) eps)) (abs (- x1 x2)))))
  :hints (("Goal"
           :use ((:instance step-1+leps-thm-1 (eps (/ eps)))))))

(defthm run-realp
  (implies
   (and
    (realp x)
    (realp eps))
   (realp (run x n eps)))
  :rule-classes :type-prescription)

(defun n-scheme (n)
  (cond
   ((zp n) 0)
   (t (n-scheme (- n 1)))))

(defthm step-run-thm
  (implies
   (and
    (integerp n)
    (<= 0 n)
    (realp x)
    (realp eps))
   (equal (step1 (run x n eps) eps)
          (run x (+ n 1) eps))))

(defthm run-limit-thm
  (implies
   (and
    (realp x1)
    (realp x2)
    (realp eps)
    (< 0 eps))
   (<= (abs (- (run x1 n eps) (run x2 n eps)))
       (run-limit (abs (- x1 x2)) n eps)))
  :hints (("Goal" :do-not '(generalize)
           :induct (n-scheme n)
           :in-theory (disable abs)
           :nonlinearp t)
          ("Subgoal *1/2" :in-theory (disable abs <-*-LEFT-CANCEL)
           :use ((:instance run-limit-n+1-thm
                            (n (- n 1))
                            (delta (abs (- (step1 x1 eps)
                                           (step1 x2 eps)))))
                 (:instance step-1+leps-thm
                            (x1 (run x1 (- n 1) eps))
                            (x2 (run x2 (- n 1) eps)))
                 (:instance pos-factor-<=-thm
                            (x (ABS (+ (RUN X1 (+ -1 N) eps)
                                       (* -1 (RUN X2
                                                  (+ -1 N)
                                                  eps)))))
                            (y (RUN-LIMIT (ABS (+ X1 (* -1 X2)))
                                          (+ -1 N) eps))
                            (a (+ 1 (* (L) EPS))))))))

(defthm eexp-1+epsl-thm
  (implies
   (and
    (realp eps)
    (integerp n)
    (< 0 eps)
    (realp delta)
    (<= 0 delta)
    (<= 0 n))
   (<= (* delta (eexp (* (- n 1) eps (L)))
          (+ 1 (* eps (L))))
       (* delta (eexp (* n eps (L))))))
  :hints (("Goal" :in-theory (disable 1+x-<=eexp-thm)
           :use ((:instance 1+x-<=eexp-thm (x (* eps (L))))
                 (:instance pos-factor-<=-thm
                            (x (+ 1 (* eps (L))))
                            (y (eexp (* eps (L))))
                            (a (* delta
                                  (eexp (+ (* n eps (L))
                                           (* -1 eps (L))))))))))
  :rule-classes nil)

(defthm run-limit-eexp-thm-1
  (implies
   (and
    (realp eps)
    (realp delta)
    (<= 0 delta)
    (< 0 eps)
    (integerp n)
    (<= 0 n))
   (<= (run-limit delta n eps)
       (* delta (eexp (* eps (L) n)))))
  :hints (("Goal" :do-not '(generalize))
          ("Subgoal *1/4" :use ((:instance pos-factor-<=-thm
                                           (x (RUN-LIMIT DELTA (+ -1 N) eps))
                                           (y (* DELTA
                                                 (EEXP (+ (* -1 (L) EPS)
                                                          (* (L) EPS N)))))
                                           (a (+ 1 (* eps (L)))))
                                (:instance eexp-1+epsl-thm))))
  :rule-classes nil)

(defthm run-diff-limit-eexp-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (realp x1)
    (realp x2)
    (integerp n)
    (<= 0 n))
   (<= (abs (- (run x1 n eps) (run x2 n eps)))
       (* (abs (- x1 x2)) (eexp (* eps (L) n)))))
  :hints (("Goal" :do-not '(generalize))
          ("Subgoal *1/2" :in-theory (disable abs)
           :use ((:instance run-limit-thm)
                 (:instance run-limit-eexp-thm-1
                            (delta (abs (- x1 x2)))))))
  :rule-classes nil)

(defthm run-plus-thm
  (implies
   (and
    (integerp m)
    (integerp n)
    (<= 0 m)
    (<= 0 n))
   (equal (run (run x n eps) m eps)
          (run x (+ m n) eps))))

(defun run-n-limit (x n eps)
  (+ (abs x)
     (* (eexp (* (L) n eps)) (abs (f x))  n eps)))

(defthm f-step-thm-hint1
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (realp x))
   (<= (abs (f (step1 x eps)))
       (+ (abs (f x)) (abs (- (f (step1 x eps)) (f x))))))
  :rule-classes nil)

(defthm f-step-thm-hint2
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (realp x))
   (<= (abs (f (step1 x eps)))
       (* (eexp (* (L) eps)) (abs (f x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs)
           :use ((:instance f-step-thm-hint1)
                 (:instance f-lim-thm (x1 (+ x (* (f x) eps)))
                            (x2 x))
                 (:instance 1+x-<=eexp-thm (x (* (L) eps)))
                 (:instance pos-factor-<=-thm (x (+ 1 (* eps (L))))
                            (y (eexp (* eps (L) )))
                            (a (abs (f x))))))))

(defthm arith-3
  (implies
   (and
    (integerp n)
    (< 0 n))
   (<= 0 (- n 1)))
  :rule-classes :type-prescription)

(defthm f-step-thm-hint3
  (implies
   (and
    (integerp n)
    (< 0 n)
    (realp x)
    (realp eps)
    (< 0 eps))
   (<= 0
       (* (EEXP (* -1 EPS (L)))
          (EEXP (* EPS (L) N))
          (+ -1 N)
          EPS)))
  :rule-classes nil)

(defthm step1-type-thm
  (implies
   (and
    (realp x)
    (realp eps))
   (realp (step1 x eps)))
  :rule-classes :type-prescription)

(defthm abs-step1-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (realp x))
   (<= (abs (step1 x eps))
       (+ (abs x)
          (* (abs (f x)) eps))))
  :rule-classes nil)

(defthm run-limit-eexp-step-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (integerp n)
    (< 0 n)
    (realp x))
   (<= (run-n-limit (step1 x eps)
                    (- n 1)
                    eps)
       (run-n-limit x n eps)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable abs <-*-LEFT-CANCEL)
           :use ((:instance abs-step1-thm)
                 (:instance f-step-thm-hint3)
                 (:instance f-step-thm-hint2)
                 (:instance pos-factor-<=-thm (x 1)
                            (y (eexp (* eps (L) n)))
                            (a (* (abs (f x)) eps)))
                 (:instance pos-factor-<=-thm
                            (x (abs (f (step1 x eps))))
                            (y (* (eexp (* (L) eps)) (abs (f x))))
                            (a (* (eexp (* -1 eps (L)))
                                  (eexp (* eps (L) n))
                                  (- n 1) eps)))))))

(defthm run-limit-eexpt-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (realp x)
    (integerp n)
    (<= 0 n))
   (<= (abs (run x n eps))
       (run-n-limit x n eps)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable step1 run-n-limit abs))
          ("Subgoal *1/1" :in-theory (e/d (step1 run-n-limit) (abs)))))

(defun run-tm-limit (x tm)
  (+ (abs x)
     (* (eexp (* (L) tm)) (abs (f x))  tm)))

;; Cuong Chau: Add the :use hint to the following theorem.

(defthm run-tm-limit-standard-thm
  (implies
   (and
    (realp tm)
    (standard-numberp tm)
    (realp x)
    (standard-numberp x))
   (standard-numberp (run-tm-limit x tm)))
  :hints (("Goal" :use ((:instance EEXP-STANDARD-THM
                                   (x (* (L) tm)))
                        (:instance L-STANDARD-THM)
                        (:instance F-STANDARD-THM))))
  :rule-classes nil)

(defthm run-n-limit-standard-thm
  (implies
   (and
    (realp eps)
    (integerp n)
    (standard-numberp (* eps n))
    (realp x)
    (standard-numberp x))
   (standard-numberp (run-n-limit x n eps)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance run-tm-limit-standard-thm
                                   (tm (* eps n)))))))

(defthm run-tm-limit-limited-thm
  (implies
   (and
    (realp tm)
    (i-limited tm)
    (realp x)
    (i-limited x))
   (i-limited (run-tm-limit x tm)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable i-large)
           :use ((:instance standards-are-limited)))))

(defthm run-n-limit-limited-thm
  (implies
   (and
    (realp eps)
    (integerp n)
    (i-limited (* eps n))
    (realp x)
    (i-limited x))
   (i-limited (run-n-limit x n eps)))
  :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance run-tm-limit-limited-thm
                                   (tm (* eps n)))))))

(defthm run-n-limit-type-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (integerp n))
   (realp (run-n-limit x n eps)))
  :rule-classes :type-prescription)

(defthm run-standard-thm
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n)
    (i-limited (* eps n))
    (standard-numberp x))
   (standard-numberp (standard-part (run x n eps))))
  :hints (("Goal" :in-theory (disable run
                                      run-n-limit
                                      plus-limited
                                      times-limited
                                      divide-limited)
           :use ((:instance run-limit-eexpt-thm)
                 (:instance run-n-limit-limited-thm)
                 (:instance limited-bound-x-implies-limited-x-thm
                            (y (run-n-limit x n eps))
                            (x (run x n eps)))
                 (:instance standardp-standard-part
                            (x (run x n eps)))))))

(defthm floor-limited-thm-hint-1
  (implies (and (i-small (/ (i-large-integer)))
                (realp tm)
                (i-limited tm))
           (i-limited (+ (* -1 (/ (i-large-integer))) tm)))
  :rule-classes nil
  :hints (("goal" :in-theory (disable i-large
                                      i-small
                                      /-large-integer-is-ismall-thm))))

(defthm floor-limited-thm
  (implies
   (and
    (realp tm)
    (i-limited tm))
   (i-limited (* (/ (i-large-integer)) (floor1 (* (i-large-integer) tm)) )))
  :hints (("goal" :in-theory (disable i-large)
           :use ((:instance sandwich-limited-thm
                            (u (/ (- (* tm (i-large-integer)) 1)
                                  (i-large-integer)))
                            (v (/ (* tm (i-large-integer))
                                  (i-large-integer)))
                            (x (* (/ (i-large-integer))
                                  (floor1 (* (i-large-integer) tm)) )))))
          ("subgoal 2"
           :use ((:instance /-large-integer-is-ismall-thm)
                 (:instance floor-limited-thm-hint-1)))))

(defthm phi-thm
  (implies
   (and (standard-numberp x)
        (standard-numberp tm)
        (realp x)
        (realp tm))
   (standard-numberp (standard-part (run x (floor1 (* (i-large-integer) tm))
                                         (/ (i-large-integer))))))
  :hints (("goal" :in-theory (disable i-large)
           :use ((:instance run-standard-thm
                            (n (floor1 (* tm (i-large-integer))))
                            (eps (/ (i-large-integer))))
                 (:instance floor-limited-thm)))))

; The following is the definition of the
; standard function

(defun-std phi (x tm)
  (cond
   ((not (and
          (realp x)
          (realp tm))) 0)
   (t (standard-part (run x
                          (floor1 (* tm (i-large-integer)))
                          (/ (i-large-integer)))))))
