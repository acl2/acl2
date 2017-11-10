; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "arith-nsa4")
(include-book "abs")
(include-book "eexp")
(include-book "phi-exists")
(include-book "phi-properties")
(include-book "computed-hints")
(include-book "tm-floor")

(in-theory (disable i-large))
(in-theory (disable standard-part-<=))

(defstub phi2 (tm) t)

(defaxiom phi2-type
  (implies
   (and
    (realp tm))
   (realp (phi2 tm)))
  :rule-classes :type-prescription)

(defaxiom phi2-standard-thm
  (implies
   (and
    (realp tm)
    (standard-numberp tm))
   (standard-numberp (phi2 tm)))
  :rule-classes ((:type-prescription) (:rewrite)))

(defun resid2-tm (tm eps)
  (+ (phi2 (+ tm eps))
     (- (phi2 tm))
     (- (* eps (f (phi2 tm))))))

(defthm resid2-tm-type
  (implies
   (and
    (realp tm)
    (realp eps))
   (realp (resid2-tm tm eps)))
  :rule-classes :type-prescription)

(defaxiom phi2-deriv
  (implies
   (and
    (realp tm)
    (i-limited tm)
    (realp eps)
    (not (equal eps 0))
    (i-small eps))
   (equal (standard-part (/ (- (phi2 (+ tm eps)) (phi2 tm)) eps))
          (standard-part (f (phi2 tm))))))

(defthm phi2-equal-thm
  (implies
   (and
    (realp tm)
    (realp eps))
   (equal (+ (phi2 tm)
             (* eps (f (phi2 tm)))
             (resid2-tm tm eps))
          (phi2 (+ tm eps)))))

(defthm resid2/eps-small-thm
  (implies
   (and
    (realp tm)
    (i-limited tm)
    (realp eps)
    (not (equal eps 0))
    (i-small eps))
   (equal (standard-part (/ (resid2-tm tm eps) eps))
          0))
  :hints (("Goal" :use ((:instance phi2-deriv)))))

(defthm /eps-gt-1-thm
  (implies
   (and
    (realp eps)
    (not (equal eps 0))
    (equal (standard-part eps) 0))
   (< 1 (abs (/ eps))))
  :hints (("Goal" :use ((:instance standard-part-<= (y 1) (x (/ (abs eps))))
                        (:instance i-large (x (abs (/ eps))))))))

(defthm resid2-small-thm
  (implies
   (and
    (realp tm)
    (i-limited tm)
    (realp eps)
    (not (equal eps 0))
    (i-small eps))
   (equal (standard-part (resid2-tm tm eps))
          0))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs resid2-tm abs-*-thm)
           :use ((:instance resid2/eps-small-thm)
                 (:instance pos-factor-<-thm
                            (x 1)
                            (y (abs (/ eps)))
                            (a (abs (resid2-tm tm eps))))
                 (:instance abs-*-thm
                            (x (/ eps))
                            (y (resid2-tm tm eps)))))))

(defthm phi2-tm-continuous-thm
  (implies
   (and
    (realp tm)
    (i-limited tm))
   (equal (standard-part (phi2 tm))
          (phi2 (standard-part tm))))
  :hints (("Goal" :in-theory (disable resid2-tm standardp-standard-part)
           :cases ((equal tm (standard-part tm))
                   (not (equal tm (standard-part tm)))))
          ("Subgoal 1" :use ((:instance phi2-equal-thm
                                        (eps (- tm (standard-part tm)))
                                        (tm (standard-part tm)))
                             (:instance resid2-small-thm
                                        (eps (- tm (standard-part tm)))
                                        (tm (standard-part tm)))
                             (:instance standardp-standard-part
                                        (x tm))
                             (:instance standards-are-limited
                                        (x (phi2 (standard-part tm))))))
          ("Subgoal 2" :use ((:instance standardp-standard-part
                                        (x tm))))))

(defthm standardp-standard-part-limited
  (implies
   (and
    (acl2-numberp x)
    (standard-numberp (standard-part x)))
   (i-limited x))
  :hints (("Goal" :use ((:instance standard+small->i-limited
                                   (x (standard-part x))
                                   (eps (- x (standard-part x))))))))

(defthm phi2-limited-thm
  (implies
   (and
    (realp tm)
    (i-limited tm))
   (i-limited (phi2 tm)))
  :rule-classes ((:type-prescription) (:rewrite))
  :hints (("Goal" :use ((:instance standardp-standard-part-limited
                                   (x (phi2 tm)))))))

(defthm resid2-tm-limited
  (implies
   (and
    (realp eps)
    (realp tm)
    (i-limited tm)
    (i-small eps))
   (i-limited (resid2-tm tm eps)))
  :rule-classes ((:type-prescription) (:rewrite)))

(defun max-abs-resid2-tm (n eps)
  (cond
   ((zp n) (abs (resid2-tm 0 eps)))
   (t (max (abs (resid2-tm (* n eps) eps))
           (max-abs-resid2-tm (- n 1) eps)))))

(defthm max-abs-resid2-is-bound
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (integerp n)
    (integerp m)
    (<= 0 m)
    (<= m n))
   (<= (abs (resid2-tm (* eps m) eps))
       (max-abs-resid2-tm n eps)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs))))

(defun find-n (n eps)
  (cond
   ((zp n) 0)
   ((equal (abs (resid2-tm (* n eps) eps))
           (max-abs-resid2-tm n eps)) n)
   (t (find-n (- n 1) eps))))

(defthm find-n-is-max
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n))
   (equal (abs (resid2-tm (* eps (find-n n eps)) eps))
          (max-abs-resid2-tm n eps)))
  :rule-classes nil)

(defthm find-n-range
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n))
   (and
    (<= 0 (find-n n eps))
    (<= (find-n n eps) n)))
  :rule-classes :linear)

(defthm find-n-limited
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n)
    (i-limited (* eps n)))
   (i-limited (* eps (find-n n eps))))
  :hints (("Goal" :in-theory (disable abs)
           :do-not-induct t
           :use ((:instance sandwich-limited-thm
                            (u 0)
                            (v (* eps n))
                            (x (* eps (find-n n eps))))
                 (:instance pos-factor-<=-thm
                            (x 0)
                            (y (find-n n eps))
                            (a eps))
                 (:instance pos-factor-<=-thm
                            (x (find-n n eps))
                            (y n)
                            (a eps))
                 (:instance find-n-range)))))

(defthm max-abs-resid2-tm-small
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n)
    (i-small eps)
    (i-limited (* eps n)))
   (equal (standard-part (* (/ eps) (max-abs-resid2-tm n eps)))
          0))
  :hints (("Goal" :in-theory (disable abs
                                      resid2-tm
                                      abs-*-thm
                                      ABS-POS-*-LEFT-THM
                                      <-CANCEL-DIVISORS
                                      EQUAL-CANCEL-DIVISORS)
           :do-not-induct t
           :use ((:instance find-n-is-max)
                 (:instance abs-pos-*-left-thm
                            (x (/ eps))
                            (y (RESID2-TM
                                (EPS-N-FUN EPS (FIND-N N EPS))
                                EPS)))
                 (:instance resid2/eps-small-thm
                            (tm (* eps (find-n n eps)))
                            )))))

(defthm max-abs-resid2-tm-limited
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n)
    (i-small eps)
    (i-limited (* eps n)))
   (i-limited (* (/ eps) (max-abs-resid2-tm n eps))))
  :rule-classes ((:rewrite) (:type-prescription)))

(defthm max-abs-resid2-tm-type
  (implies
   (and
    (realp eps)
    (integerp n))
   (and
    (realp (max-abs-resid2-tm n eps))
    (<= 0 (max-abs-resid2-tm n eps))))
  :rule-classes :type-prescription)

(defthm max-abs-resid2-tm-floor-small-hint
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (integerp n)
    (<= 0 n)
    (i-limited tm)
    (i-small eps)
    (i-limited (* eps n)))
   (equal (standard-part (* tm (/ eps)
                            (max-abs-resid2-tm n eps)))
          0))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs *-commut-3way)
           :do-not-induct t
           :use ((:instance max-abs-resid2-tm-small)))))

(defthm max-abs-resid2-tm-floor-small
  (implies
   (and
    (realp tm)
    (<= 0 tm)
    (i-limited tm))
   (equal (standard-part (* (floor1 (* tm (i-large-integer)))
                            (max-abs-resid2-tm
                             (floor1 (* tm (i-large-integer)))
                             (/ (i-large-integer)))))
          0))
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs resid2-tm
                                      ;; Cuong Chau: Proof failed if not
                                      ;; disable EPS-N-FUN-RW-3-THM.
                                      EPS-N-FUN-RW-3-THM)
           :do-not-induct t
           :use ((:instance max-abs-resid2-tm-small
                            (eps (/ (i-large-integer)))
                            (n (floor1 (* tm (i-large-integer)))))
                 (:instance pos-factor-<-thm
                            (x (- (* tm (i-large-integer)) 1))
                            (y (floor1 (* tm (i-large-integer))))
                            (a (max-abs-resid2-tm
                                (floor1 (* tm (i-large-integer)))
                                (/ (i-large-integer)))))
                 (:instance pos-factor-<=-thm
                            (x (floor1 (* tm (i-large-integer))))
                            (y (* tm (i-large-integer)))
                            (a (max-abs-resid2-tm
                                (floor1 (* tm (i-large-integer)))
                                (/ (i-large-integer)))))))
          ("Subgoal 1" :in-theory (disable abs resid2-tm)
           :use ((:instance max-abs-resid2-tm-floor-small-hint
                            (n (floor1 (* tm (i-large-integer))))
                            (eps (/ (i-large-integer))))))))

(defun n-induct-scheme (n)
  (cond
   ((zp n) 0)
   (t (n-induct-scheme (- n 1)))))

(defthm phi-run-step-diff
  (implies
   (and
    (realp x)
    (realp eps)
    (< 0 eps)
    (integerp n)
    (< 0 n)
    (integerp m)
    (<= n m))
   (<= (abs (- (step1 x eps)
               (phi2 (* n eps))))
       (+ (* (+ 1 (* eps (L))) (abs (- x (phi2 (* (- n 1) eps)))))
          (max-abs-resid2-tm m eps))))
  :hints (("Goal" :in-theory (disable abs resid2-tm)
           :do-not '(generalize)
           :do-not-induct t
           :use ((:instance f-lim-thm
                            (x1 x)
                            (x2 (phi2 (* (- n 1) eps))))
                 (:instance max-abs-resid2-is-bound
                            (m (- n 1))
                            (n m))
                 (:instance pos-factor-<=-thm
                            (x (abs (- (f x) (f (phi2 (* (- n 1) eps))))))
                            (y (* (L) (abs (- x (phi2 (* (- n 1) eps))))))
                            (a eps))
                 (:instance phi2-equal-thm
                            (tm (* (- n 1) eps)))
                 (:instance abs-pos-*-left-thm
                            (x eps)
                            (y (+ (F X)
                                  (* -1
                                     (f (PHI2 (+ (* -1 EPS) (* EPS N))))))))
                 (:instance abs-triangular-inequality-3way-thm
                            (x (- x (phi2 (* (- n 1) eps))))
                            (y (- (* eps (f x))
                                  (* eps (f (phi2 (* (- n 1) eps))))))
                            (z (- (resid2-tm (* (- n 1) eps) eps))))))))

(defthm eexp-unite-exponents-thm
  (implies
   (and
    (realp x)
    (realp y)
    (realp z))
   (equal (* (eexp x) y (eexp z))
          (* y (eexp (+ x z))))))

(defthm phi2-run-eq-thm
  (implies
   (and
    (integerp m)
    (integerp n)
    (<= 0 n)
    (<= n m)
    (< 0 eps)
    (realp eps))
   (<= (abs (- (run (phi2 0) n eps)
               (phi2 (* eps n))))
       (* (eexp (* eps n (L)))
          n
          (max-abs-resid2-tm m eps))))
  :rule-classes nil
  :hints (("Goal" :do-not '(generalize)
           :induct (n-induct-scheme n)
           :do-not-induct t
           :in-theory (disable abs step1 resid2-tm MAX-ABS-RESID2-TM))
          ("Subgoal *1/2" :use ((:instance phi-run-step-diff
                                           (x (run (phi2 0) (- n 1) eps)))
                                (:instance pos-factor-<=-thm
                                           (x (ABS (+ (RUN (PHI2 0) (+ -1 N) EPS)
                                                      (* -1 (PHI2 (+ (* -1 EPS)
                                                                     (* EPS N)))))))
                                           (y (+ (* -1 (MAX-ABS-RESID2-TM M EPS)
                                                    (EEXP (+ (* -1 (L) EPS)
                                                             (* (L) EPS N))))
                                                 (* N (MAX-ABS-RESID2-TM M EPS)
                                                    (EEXP (+ (* -1 (L) EPS)
                                                             (* (L) EPS N))))))
                                           (a (eexp (* (L) eps))))
                                (:instance pos-factor-<=-thm
                                           (x 1)
                                           (y (EEXP (* (L) EPS N)))
                                           (a (MAX-ABS-RESID2-TM M EPS)))
                                (:instance 1+x-<=eexp-thm
                                           (x (* eps (L))))
                                (:instance pos-factor-<=-thm
                                           (x (+ 1 (* eps (L))))
                                           (y (eexp (* eps (L))))
                                           (a (ABS (+ (RUN (PHI2 0) (+ -1 N) EPS)
                                                      (* -1 (PHI2 (+ (* -1 EPS)
                                                                     (* EPS N)))))))))))
  :otf-flg t)

(defthm phi2-st-run-eq-hint
  (implies
   (and
    (realp tm)
    (i-limited y)
    (<= 0 tm)
    (i-limited tm))
   (equal (standard-part (* y
                            (floor1 (* tm (i-large-integer)))
                            (max-abs-resid2-tm
                             (floor1 (* tm (i-large-integer)))
                             (/ (i-large-integer)))))
          0))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs resid2-tm)
           :do-not-induct t
           :use ((:instance max-abs-resid2-tm-floor-small)))))

(defthm phi2-st-run-eq-thm
  (implies
   (and
    (realp tm)
    (standard-numberp tm)
    (<= 0 tm))
   (equal (standard-part (phi2 tm))
          (standard-part (phi (phi2 0) tm))))
  :rule-classes nil
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable abs
                                      ;; Cuong Chau: Proof failed if not
                                      ;; disable the following two lemmas.
                                      EPS-N-FUN-RW-1-THM
                                      EPS-N-FUN-RW-2-THM)
           :use ((:instance phi2-run-eq-thm
                            (eps (/ (i-large-integer)))
                            (n (floor1 (* tm (i-large-integer))))
                            (m (floor1 (* tm (i-large-integer)))))
                 (:instance phi2-st-run-eq-hint
                            (y (EEXP (* (L) (TM-FUN TM)))))))))

;; --------------------------------------------
;; The following is the theorem which states
;; that, for any phi2 satisfying the
;; differential equation, phi2 is equal to
;; phi evaluated at initial condition phi2(0).
;; --------------------------------------------

(defthm-std phi2-st-run-eq-std-thm
  (implies
   (and
    (realp tm)
    (<= 0 tm))
   (equal (phi2 tm)
          (phi (phi2 0) tm)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs)
           :use ((:instance phi2-st-run-eq-thm)))))
