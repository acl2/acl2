; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "RTL")

(local (include-book "../../arithmetic/top"))
(local (include-book "float"))
(local (include-book "away"))
(local (include-book "trunc"))

;; Necessary functions:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defun expo-measure (x)
;  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((not (rationalp x)) 0)
	((< x 0) '(2 . 0))
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defnd expo (x)
  (declare (xargs :measure (expo-measure x)
                  :verify-guards nil))
  (mbe
   :logic
   (cond ((or (not (rationalp x)) (equal x 0)) 0)
         ((< x 0) (expo (- x)))
         ((< x 1) (1- (expo (* 2 x))))
         ((< x 2) 0)
         (t (1+ (expo (/ x 2)))))
   :exec
   (if (rationalp x)
       (let* ((n (abs (numerator x)))
              (d (denominator x))
              (ln (integer-length n))
              (ld (integer-length d))
              (l (- ln ld)))
         (if (>= ln ld)
             (if (>= (ash n (- l)) d) l (1- l))
           (if (> ln 1)
               (if (> n (ash d l)) l (1- l))
             (- (integer-length (1- d))))))
     0)))

;could redefine to divide by the power of 2 (instead of making it a negative power of 2)...
(defund sig (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

;make defund?
(defun sgn (x)
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0)
        -1
      1)))

(defund exactp (x n)
;  (declare (xargs :guard (and (real/rationalp x) (integerp n))))
  (integerp (* (sig x) (expt 2 (1- n)))))

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defund trunc (x n)
  (declare (xargs :guard (integerp n)
                  :verify-guards nil))
  (* (sgn x) (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

(defund away (x n)
  (* (sgn x) (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))


;;
;; New stuff:
;;


(defund re (x)
  (- x (fl x)))

(defund near (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(trunc x n)
      (if (> f 1/2)
	  (away x n)
	(if (evenp z)
	    (trunc x n)
	  (away x n))))))

(defthm near-minus
  (equal (near (* -1 x) n)
         (* -1 (near x n)))
  :hints (("goal" :in-theory (enable near sig-minus))))

(defthm near-of-non-rationalp-is-0
  (implies (not (rationalp x))
           (equal (near x n)
                  0))
  :hints (("goal" :in-theory (enable near sig))))

(defthm near-choice
  (or (= (near x n) (trunc x n))
      (= (near x n) (away x n)))
  :hints (("Goal" :in-theory (enable near)))
  :rule-classes ())

;BOZO better r-c on these? :rewrite?
(defthm near-pos
  (implies (and (< 0 x)
                (< 0 n)
                (rationalp x)
                (integerp n)
                )
           (< 0 (near x n)))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use ((:instance near-choice)))))

(defthm near-neg
    (implies (and (< x 0)
		  (< 0 n)
                  (rationalp x)
		  (integerp n)
		  )
	     (< (near x n) 0))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use ((:instance near-choice)))))

(defthm near-rational-type-prescription
  (rationalp (near x n))
  :rule-classes (:rewrite :type-prescription))

(defthm near-non-negative-rational-type-prescription
  (implies (<= 0 x)
           (and (<= 0 (near x n))
                (rationalp (near x n))))
  :hints (("Goal" :use ((:instance near-choice))))
  :rule-classes :type-prescription)

(defthm near-non-positive-rational-type-prescription
  (implies (<= x 0)
           (and (<= (near x n) 0)
                (rationalp (near x n))))
  :hints (("Goal" :use ((:instance near-choice))))
  :rule-classes :type-prescription)


(local (defthm near1-1
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  ;(> n 0)
                  )
	     (= (- x (trunc x n))
		(* (expt 2 (- (1+ (expo x)) n)) (re (* (expt 2 (1- n)) (sig x))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable re a15)
		  :use ((:instance trunc)
			(:instance fp-rep))))))

(local (defthm near1-3
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
;		  (> n 0)
		  (not (integerp (* (expt 2 (1- n)) (sig x))))
                  )
	     (= (- (away x n) x)
		(* (expt 2 (- (1+ (expo x)) n)) (- 1 (re (* (expt 2 (1- n)) (sig x)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable re a15)
		  :use ((:instance away)
			(:instance fl-cg (x (* (expt 2 (1- n)) (sig x))))
			(:instance fp-rep)
		)))))


(local (defthm near1-6
    (implies (and (rationalp p)
		  (> p 0)
		  (rationalp f)
		  (< (* p f) (* p (- 1 f))))
	     (< f 1/2))
;    :hints (("Goal" :in-theory (disable LESS-THAN-MULTIPLY-THROUGH-BY-inverted-factor-FROM-RIGHT-HAND-SIDE)))
    :rule-classes ()))

(local (defthm near1-7
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (not (integerp (* (expt 2 (1- n)) (sig x)))) ;easy to drop, since trunc, away, and near all
                    ;= x
		  (< (- x (trunc x n)) (- (away x n) x)))
	     (= (near x n) (trunc x n)))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance near1-1)
			(:instance near1-3)
			(:instance near1-6
				   (p (expt 2 (- (1+ (expo x)) n)))
				   (f (re (* (expt 2 (1- n)) (sig x)))))
			(:instance near))))))

(local (defthm near1-8
    (implies (and (rationalp p)
		  (> p 0)
		  (rationalp f)
		  (> (* p f) (* p (- 1 f))))
	     (> f 1/2))
    :hints (("Goal" :in-theory (disable LESS-THAN-MULTIPLY-THROUGH-BY-inverted-factor-FROM-LEFT-HAND-SIDE)))
    :rule-classes ()))

(local (defthm near1-9
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (not (integerp (* (expt 2 (1- n)) (sig x))))
		  (> (- x (trunc x n)) (- (away x n) x)))
	     (= (near x n) (away x n)))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance near1-1)
			(:instance near1-3)
			(:instance near1-8
				   (p (expt 2 (- (1+ (expo x)) n)))
				   (f (re (* (expt 2 (1- n)) (sig x)))))
			(:instance near))))))


(defthm near1-a-helper
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (< (- x (trunc x n)) (- (away x n) x)))
	     (= (near x n) (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp)
		  :use ((:instance near1-7)
                        trunc-exactp-b
                        away-exactp-b
			;(:instance near1-4)
			;(:instance near1-5)
                        ))))

;disable re?
;use  near1-7? no, this is the "negative n case"
(defthm near1-a-negative-n
  (implies (and (rationalp x)
                (>= x 0)
                (integerp n)
                (<= n 0)
                (< (- x (trunc x n)) (- (away x n) x)))
           (= (near x n) (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable sgn
                                      re
;                                      sig
                                      near; expo>=-2
                                      expt-split)
                              '(;integerp-prod
                                expt-compare
                                a15
                                ;expo>=-2
                                ))
           :use ((:instance expt-weak-monotone (n n) (m 0))
                 (:instance expt-weak-monotone (n n) (m -1))
                 sig-upper-bound
                 (:instance fl-unique (x (* 1/2 (SIG X) (EXPT 2 N))) (n 0))))))


(local
 (defthm near1-a-support
   (implies (and (< (- x (trunc x n)) (- (away x n) x))
                 (rationalp x)
                 (>= x 0)
                 (integerp n)
; (> n 0)
                 )
            (equal (near x n)
                   (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near trunc away)
           :use (near1-a-helper near1-a-negative-n)))))

;; (i-am-here)
;; Thu Oct 12 14:41:22 2006

(local
  (defthm trunc-abs-reduce
    (implies (and (< x 0)
                  (integerp n)
                  (rationalp x))
             (equal (abs (+ x (* -1 (trunc x n))))
                    (- (trunc x n) x)))
    :hints (("Goal" :in-theory (enable trunc-minus)
             :use ((:instance trunc-upper-pos
                              (x (* -1 x))))))))


(local
  (defthm trunc-abs-reduce-2
    (implies (and (>= x 0)
                  (integerp n)
                  (rationalp x))
             (equal (abs (+ x (* -1 (trunc x n))))
                    (- x (trunc x n))))
    :hints (("Goal" :in-theory (enable trunc-minus)
             :use ((:instance trunc-upper-pos))))))




(local
  (defthm away-abs-reduce
    (implies (and (< x 0)
                  (integerp n)
                  (rationalp x))
             (equal (abs (+ (away x n) (* -1 x)))
                    (+ x (* -1 (away x n)))))
    :hints (("Goal" :in-theory (enable away-minus)
             :use ((:instance away-lower-pos
                              (x (* -1 x))))))))


(local
  (defthm away-abs-reduce-2
    (implies (and (>= x 0)
                  (integerp n)
                  (rationalp x))
             (equal (abs (+ (away x n) (* -1 x)))
                    (+ (away x n) (* -1 x))))
    :hints (("Goal" :in-theory (enable away-minus)
             :use ((:instance away-lower-pos))))))



(defthm near1-a
         (implies (and (< (abs (- x (trunc x n)))
                          (abs (- (away x n) x)))
                       (rationalp x)
     		  (integerp n))
     	     (equal (near x n)
                         (trunc x n)))
         :hints (("Goal" :cases ((< x 0))
                  :in-theory (enable trunc-minus away-minus abs near-minus))
                 ("Subgoal 2" :use ((:instance near1-a-support)
                                    (:instance away-lower-pos)))
                 ("Subgoal 1" :use ((:instance near1-a-support
                                               (x (* -1 x)))
                                    (:instance away-lower-pos
                                               (x (* -1 x))))))
       :rule-classes ())



(local
 (defthm near1-b-support
    (implies (and (> (- x (trunc x n)) (- (away x n) x))
                  (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  )
	     (equal (near x n)
                    (away x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp)
		  :use ((:instance near1-9)
                        trunc-exactp-b
                        away-exactp-b)))))


(local
 (defthm near1-b-lemma ;; the interesting case.
   (implies (and (> (abs (- x (trunc x n))) (abs (- (away x n) x)))
                 (rationalp x)
                 (> n 0)
                 (integerp n))
            (equal (near x n)
                   (away x n)))
   :hints (("Goal" :cases ((< x 0))
            :in-theory (enable trunc-minus away-minus abs near-minus))
           ("Subgoal 2" :use ((:instance near1-b-support)
                              (:instance trunc-upper-pos)))
           ("Subgoal 1" :use ((:instance near1-b-support
                                         (x (* -1 x)))
                              (:instance trunc-upper-pos
                                         (x (* -1 x))))))))



(encapsulate ()
         (local
          (encapsulate ()
                       (local
                        (defthm fl-1/2-sig-x-is-zero-lemma
                          (implies (and (rationalp x)
                                        (rationalp y)
                                        (< 0 y)
                                        (<= y 1/2))
                                   (equal (fl (* (sig x) y))
                                          0))
                          :hints (("Goal" :in-theory (disable sig-upper-bound
                                                              sig-lower-bound)
                                   :use ((:instance sig-upper-bound)
                                         (:instance sig-lower-bound))))))

                       (defthm near1-b-1-2-1
                         (implies (rationalp x)
                                  (equal (fl (* 1/2 (sig x)))
                                         0))
                         :hints (("Goal" :use ((:instance fl-1/2-sig-x-is-zero-lemma
                                                          (y 1/2))))))


                       (defthm near1-b-1-2-2
                         (implies (rationalp x)
                                  (equal (EXPT 2 (+ 1 (EXPO X)))
                                         (* 2 (EXPT 2 (expo x)))))
                         :hints (("Goal" :use ((:instance a15 (i 2) (j1 1) (j2 (expo x)))))))))

         (local
          (encapsulate ()
                       (local
                        (defthm local-expt-2-expand
                          (implies (rationalp x)
                                   (equal (EXPT 2 (+ 1 (EXPO X)))
                                          (* 2 (EXPT 2 (expo x)))))
                          :hints (("Goal" :use ((:instance a15 (i 2) (j1 1) (j2 (expo x))))))))


                       (defthm integer-n-less-than-expt
                         (implies (and (integerp n)
                                       (rationalp x)
                                       (< 0 x)
                                       (<= n 0)
                                       (not (equal n 0)))
                                  (< x (EXPT 2 (+ 1 (EXPO X) (* -1 N)))))
                         :hints (("Goal" :in-theory (disable expo-upper-bound
                                                             expt-compare
                                                             EXPO-BOUND-ERIC
                                                             EXPO-COMPARISON-REWRITE-TO-BOUND-2
                                                             expt-strong-monotone-linear)
                                  :use ((:instance expo-upper-bound)
                                        (:instance expt-strong-monotone-linear
                                                   (n (+ 1 (expo x)))
                                                   (m (+ 1 (expo x) (* -1 n)))))))
                         :rule-classes :linear)))


         (local
          (encapsulate ()
                       (local
                        (defthm local-expt-2-expand-2
                          (implies (rationalp x)
                                   (equal (EXPT 2 (+ 2 (EXPO X)))
                                          (* 4 (EXPT 2 (expo x)))))
                          :hints (("Goal" :use ((:instance a15 (i 2) (j1 2) (j2 (expo x))))))))



                       (defthm integer-n-less-than-expt-2
                         (implies (and (integerp n)
                                       (rationalp x)
                                       (< 0 x)
                                       (<= n 0)
                                       (not (equal n 0)))
                                  (<= (* 2 x) (EXPT 2 (+ 1 (EXPO X) (* -1 N)))))
                         :hints (("Goal" :in-theory (disable expo-comparison-rewrite-to-bound-2
                                                             EXPO-COMPARISON-REWRITE-TO-BOUND
                                                             expo-bound-eric
                                                             EXPT-COMPARE
                                                             expo-upper-bound)
                                  :use ((:instance expo-upper-bound)
                                        (:instance expt-weak-monotone-linear
                                                   (n (+ 2 (expo x)))
                                                   (m (+ 1 (expo x) (* -1 n))))))))))


         (defthm near1-b
           (implies (and (> (abs (- x (trunc x n))) (abs (- (away x n) x)))
                         (rationalp x)
                         (integerp n))
                    (equal (near x n)
                           (away x n)))
           :hints (("Goal" :cases ((not (> n 0)))
                    :in-theory (enable expt-strong-monotone-linear))
                   ("Subgoal 2" :use ((:instance near1-b-lemma)))
                   ("Subgoal 1" :in-theory (enable near away expo-minus re cg sgn)
                    :cases ((not (equal n 0))))
                   ("Subgoal 1.1" :cases ((not (< 0 x))))
                   ("Subgoal 1.1.2"
                    :in-theory (e/d (near away expo-minus re cg sgn)
                                    (expt-compare
                                     expo-bound-eric
                                     EXPO-COMPARISON-REWRITE-TO-BOUND-2)))
                   ("Subgoal 1.1.1" :use ((:instance expo-upper-bound)
                                          (:instance expo-lower-bound)
                                          (:instance integer-n-less-than-expt
                                                     (x (* -1 x)))
                                          (:instance integer-n-less-than-expt-2
                                                     (x (* -1 x))))))
                   :rule-classes ()))

;; (i-am-here)

;; (defthm near1-b
;;   (implies (and (> (abs (- x (trunc x n))) (abs (- (away x n) x)))
;;                 (rationalp x)
;;                 (integerp n))
;;            (equal (near x n)
;;                   (away x n)))
;;   :hints (("Goal" :cases ((not (> n 0)))
;;            :in-theory (enable expt-strong-monotone-linear))
;;           ("Subgoal 2" :use ((:instance near1-b-support)))
;;           ("Subgoal 1" :case ((not (equal n 0))))))




(defthm near2-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (>= x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp y n)
		  (= (near x n) (trunc x n)))
	     (>= (abs (- x y)) (- x (trunc x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable away-exactp-c
				      near trunc-exactp-c)
		  :use ((:instance near1-b)
			(:instance away-lower-bound)
			(:instance trunc-upper-bound)
			(:instance trunc-exactp-c (a y))
			(:instance away-exactp-c (a y))))))

(defthm near2-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp y n)
		  (= (near x n) (away x n)))
	     (>= (abs (- x y)) (- (away x n) x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable away-exactp-c
				      trunc-exactp-c)
		  :use ((:instance near1-a)
			(:instance away-lower-pos)
			(:instance trunc-upper-pos)
			(:instance trunc-exactp-c (a y))
			(:instance away-exactp-c (a y))))))



(defthm near2-original
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  )
	     (>= (abs (- x y)) (abs (- x (near x n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near)
		  :use ((:instance near2-1)
			(:instance near2-2)
			(:instance near-choice)
			(:instance away-lower-pos)
			(:instance trunc-upper-pos)))))




(encapsulate ()

     (local
     (defthm equal-diff-trunc-away-1
       (implies (and (exactp y n)
                     (rationalp x)
                     (> x 0)
                     (case-split (<= x y))
                     (rationalp y)
                     (equal (abs (- x (trunc x n))) (abs (- (away x n)
                                                            x)))
                     (integerp n)
                     (> n 0))
     	     (>= (abs (- x y)) (abs (- x (near x n)))))
       :hints (("Goal" :use ((:instance trunc-upper-pos)
                             (:instance near-choice)
                             (:instance away-lower-pos)
                             (:instance away-exactp-c
                                        (a y)))))))


     (local
     (defthm equal-diff-trunc-away-2
       (implies (and (exactp y n)
                     (rationalp x)
                     (> x 0)
                     (case-split (<= y x))
                     (rationalp y)
                     (equal (abs (- x (trunc x n))) (abs (- (away x n)
                                                            x)))
                     (integerp n)
                     (> n 0))
     	     (>= (abs (- x y)) (abs (- x (near x n)))))
       :hints (("Goal" :use ((:instance near-choice)
                             (:instance trunc-upper-pos)
                             (:instance away-lower-pos)
                             (:instance trunc-exactp-c
                                        (a y)))))))



     (local
     (defthm near2-lemma
         (implies (and (exactp y n)
                       (rationalp x)
                       (> x 0)
     		  (rationalp y)
                       (case-split (not (equal (abs (- x (trunc x n))) (abs (- (away x n)
                                                                               x)))))
     		  (integerp n)
     		  (> n 0))
     	     (>= (abs (- x y)) (abs (- x (near x n)))))
         :hints (("Goal" :cases ((not (> (abs (- x (trunc x n))) (abs (- (away x n)
                                                                         x))))))
                 ("Subgoal 2" :cases ((not (< x y))))
                 ("Subgoal 2.2" :use  ((:instance near1-b)
                                       (:instance trunc-upper-pos)
                                       (:instance away-lower-pos)
                                       (:instance away-exactp-c
                                                  (a y))))
                 ("Subgoal 2.1" :use  ((:instance near1-b)
                                       (:instance trunc-upper-pos)
                                       (:instance away-lower-pos)
                                       (:instance trunc-exactp-c
                                                  (a y))))
                 ("Subgoal 1" :cases ((not (< x y))))
                 ("Subgoal 1.2" :use  ((:instance near1-a)
                                       (:instance trunc-upper-pos)
                                       (:instance away-lower-pos)
                                       (:instance away-exactp-c
                                                  (a y))))
                 ("Subgoal 1.1" :use  ((:instance near1-a)
                                       (:instance trunc-upper-pos)
                                       (:instance away-lower-pos)
                                       (:instance trunc-exactp-c
                                                  (a y)))))))


     ;; (loca
     ;; (defthm exactp-equal-trunc-equal
     ;;   (implies (and (exactp x n)
     ;;                 (integerp n)
     ;;                 (rationalp x))
     ;;            (equal (trunc x n) x))
     ;;   :hints (("Goal" :in-theory (enable exactp trunc)
     ;;            :use ((:instance fp-rep)
     ;;                  (:instance a15
     ;;                             (i 2)
     ;;                             (j1 (+ -1 N))
     ;;                             (j2 (+ 1 (EXPO X) (* -1 N))))))))




     ;; (defthm exactp-equal-away-equal
     ;;   (implies (and (exactp x n)
     ;;                 (integerp n)
     ;;                 (rationalp x))
     ;;            (equal (away x n) x))
     ;;   :hints (("Goal" :in-theory (enable cg exactp away)
     ;;            :use ((:instance fp-rep)
     ;;                  (:instance a15
     ;;                             (i 2)
     ;;                             (j1 (+ -1 N))
     ;;                             (j2 (+ 1 (EXPO X) (* -1 N))))))))


     (local
     (defthm near2-lemma-futher
         (implies (and (exactp y n)
                       (rationalp x)
                       (> x 0)
     		  (rationalp y)
     		  (integerp n)
     		  (> n 0))
     	     (>= (abs (- x y)) (abs (- x (near x n)))))
         :hints (("Goal" :cases ((equal (abs (- x (trunc x n))) (abs (- (away x n)
                                                                               x)))))
                 ("Subgoal 2" :use ((:instance near2-lemma)))
                 ("Subgoal 1" :cases ((not (< x y))))
                 ("Subgoal 1.2" :use ((:instance equal-diff-trunc-away-1)))
                 ("Subgoal 1.1" :use ((:instance equal-diff-trunc-away-2))))))



     (defthm near2
         (implies (and (exactp y n)
                       (rationalp x)
     		  (rationalp y)
     		  (integerp n)
     		  (> n 0))
     	     (>= (abs (- x y)) (abs (- x (near x n)))))
         :rule-classes ()
         :hints (("Goal" :cases ((not (> x 0)))
                  :in-theory (enable near-minus trunc-minus away-minus
                                     exactp-minus))
                 ("Subgoal 2" :use ((:instance near2-lemma-futher)))
                 ("Subgoal 1" :use ((:instance near2-lemma-futher
                                               (x (* -1 x))
                                               (y (* -1 y))))))))

;;; Thu Oct 12 16:29:11 2006. replaced with Hanbing's version



(defthm near-exactp-a
  (implies (< 0 n) ;can't drop?
           (exactp (near x n) n))
  :hints (("Goal" :in-theory (disable near trunc-exactp-a away-exactp-a)
           :use ((:instance near-choice)
                 (:instance trunc-exactp-a)
                 (:instance away-exactp-a)))))

(defthm sgn-near-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (near x n))
		    (sgn x)))
  :hints (("Goal" :use (near-choice
			sgn-trunc
			sgn-away))))

(defthm near-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (near x n))
		  (exactp x n)))
  :rule-classes ()
  :hints (("Goal" :use (near-choice
			trunc-exactp-b
			away-exactp-b))))



(local
 (defthm near-exactp-c-support
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  )
	     (>= a (near x n)))
  :hints (("Goal" :use (near-choice
			away-exactp-c
			trunc-upper-pos)))))

(local
 (defthm near-exactp-d-support
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (near x n)))
  :hints (("Goal" :use (near-choice
			away-lower-pos
			trunc-exactp-c)))))


(local
  (defthmd near-minus
    (equal (near (* -1 x) n)
           (* -1 (near x n)))))

(defthmd near-exactp-c
  (implies (and (exactp a n)
                (>= a x)
                (rationalp x)
                (integerp n)
                (> n 0)
                (rationalp a)
                )
           (>= a (near x n)))
  :hints (("Goal" :cases ((< x 0))
           :in-theory (enable near-minus))
          ("Subgoal 2" :use ((:instance near-exactp-c-support)))
          ("Subgoal 1" :use ((:instance near-exactp-d-support
                                        (x (* -1 x))
                                        (a (* -1 a)))))))


;; (i-am-here)

(defthmd near-exactp-d
  (implies (and (rationalp x)
                (integerp n)
                (> n 0)
                (rationalp a)
                (exactp a n)
                (<= a x))
           (<= a (near x n)))
  :hints (("Goal" :cases ((<= x 0))
           :in-theory (enable near-minus))
          ("Subgoal 2" :use ((:instance near-exactp-d-support)))
          ("Subgoal 1" :use ((:instance near-exactp-c-support
                                        (x (* -1 x))
                                        (a (* -1 a)))))))




;BOZO gen!
(local
 (defthm near-monotone-support
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (< 0 x)
                (integerp n)
                (> n 0))
           (<= (near x n) (near y n)))
  :hints (("Goal" :in-theory (disable near trunc-exactp-a away-exactp-a)
           :use ((:instance near-pos)
                 (:instance near-pos (x y))
                 (:instance near2 (y (near y n)))
                 (:instance near2 (x y) (y (near x n))))))))


;(i-am-here) ;; Thu Oct 12 17:14:03 2006



(defthm near-positive
   (implies (and (< 0 x)
                 (< 0 n)
                 (rationalp x)
		  (integerp n))
            (< 0 (near x n)))
  :rule-classes (:type-prescription :linear))

(defthmd near-negative
  (implies (and (< x 0)
                (< 0 n)
                (rationalp x)
                (integerp n)
		)
           (< (near x n) 0))
  :hints (("Goal" :in-theory (enable near-neg)))
  :rule-classes (:type-prescription :linear))


(defthm near-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 0))
           (<= (near x n) (near y n)))
  :hints (("Goal" :in-theory (enable near-minus)
           :cases ((not (equal x 0))))
          ("Subgoal 2" :use ((:instance near-negative
                                          (x (* -1 y)))))
          ("Subgoal 1" :cases ((not (> x 0))))
          ("Subgoal 1.2" :use ((:instance
                                near-monotone-support)))
          ("Subgoal 1.1" :cases ((not (> y 0))))
          ("Subgoal 1.1.2" :use ((:instance near-positive (x y))
                                 (:instance near-positive (x (* -1 x)))))
          ("Subgoal 1.1.1" :use ((:instance near-monotone-support
                                            (x (* -1 y))
                                            (y (* -1 x)))
                                 (:instance near-positive (x (* -1 x)))))))


(defund near-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (near x n) (near y n)) 2)
    (expt 2 (expo y))))

(local
 (defthm near-near-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (expo x) (expo y))))
	     (and (<= x (near-witness x y n))
		  (<= (near-witness x y n) y)
		  (exactp (near-witness x y n) (1+ n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near-witness)
		  :use ((:instance exactp-2**n (n (expo y)) (m (1+ n)))
			(:instance expo-upper-bound)
			(:instance expo-monotone)
			(:instance expt-weak-monotone (n (1+ (expo x))) (m (expo y)))
			(:instance expo-lower-bound (x y)))))))

(local
 (defthm near-near-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (near x n) (near y n))
		  (= (expo x) (expo y)))
	     (and (<= x (near-witness x y n))
		  (<= (near-witness x y n) y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near-witness)
		  :use ((:instance near2 (y (near y n)))
			(:instance near2 (x y) (y (near x n)))
			(:instance near-pos)
			(:instance near-pos (x y)))))))

(local
 (defthm near-near-3
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (near x n) (near y n)))
		  (= (expo x) (expo y)))
	     (and (<= x (near-witness x y n))
		  (<= (near-witness x y n) y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near near-monotone
                                      near-monotone-support near-witness)
		  :use ((:instance near-near-2)
			(:instance near-monotone-support))))))

(defthm near<=away
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (near x n) (away x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near)
		  :use ((:instance near-choice)
			(:instance trunc-upper-pos)
			(:instance away-lower-pos)))))

(defthm near>=trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (near x n) (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near)
		  :use ((:instance near-choice)
			(:instance trunc-upper-pos)
			(:instance away-lower-pos)))))
(local
 (defthm near-near-4
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (near x n) (near y n))
		  (= (expo x) (expo y)))
	     (<= (expo (near-witness x y n)) (expo y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable near-witness)
                              '( abs-away  away-lower-pos))
		  :use ((:instance near<=away (x y))
			(:instance away-exactp-d (x y))
			(:instance near-pos)
;			(:instance away-pos (x y))
			(:instance expo-upper-2 (x (near-witness x y n)) (n (1+ (expo y)))))))))



(defthm near-0-0
  (implies (and (case-split (< 0 n))
                (case-split (rationalp x))
                (case-split (integerp n))
                )
           (equal (equal (near x n) 0)
		  (equal x 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near))))

(local
 (defthm near-near-5
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (near x n) (near y n))
		  (= (expo x) (expo y)))
	     (integerp (* (near x n) (expt 2 (- (1- n) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expo-trunc EXPO-COMPARISON-REWRITE-TO-BOUND-2)
		  :use ((:instance exactp-<=-expo (e (expo y)) (x (near x n)))
			(:instance expo-monotone (x (trunc x n)) (y (near x n)))
;			(:instance trunc-pos)
			(:instance near-pos)
			(:instance expo-trunc)
			(:instance near>=trunc))))))

(local
 (defthm near-near-6
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (near x n) (near y n))
		  (= (expo x) (expo y)))
	     (integerp (* (near y n) (expt 2 (- (1- n) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expo-trunc  EXPO-COMPARISON-REWRITE-TO-BOUND-2)
		  :use ((:instance exactp-<=-expo (e (expo y)) (x (near y n)))
			(:instance expo-monotone (x (trunc x n)) (y (near y n)))
			(:instance near-monotone)
;			(:instance trunc-pos)
			(:instance near-pos)
			(:instance expo-trunc)
			(:instance near>=trunc))))))

;gross?
(local
 (defthm near-near-7
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k))
	     (= (+ (* x (expt 2 (1- k)))
		   (* y (expt 2 (1- k))))
		(* (/ (+ x y) 2) (expt 2 k))))
    :hints (("Goal" :in-theory (enable expt))) ;yuck
  :rule-classes ()))

(local
 (defthm near-near-8
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
	          (integerp (* x (expt 2 (1- k))))
	          (integerp (* y (expt 2 (1- k)))))
	     (integerp (* (/ (+ x y) 2) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-near-7))))))

(local
 (defthm near-near-9
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (near x n) (near y n))
		  (= (expo x) (expo y)))
	     (exactp (near-witness x y n) (1+ n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near-witness)
           :use ((:instance near-near-5)
			(:instance near-near-6)
			(:instance near-near-4)
			(:instance near-near-8 (x (near x n)) (y (near y n)) (k (- n (expo y))))
			(:instance exactp->=-expo (n (1+ n)) (e (expo y)) (x (near-witness x y n))))))))

(defthm near-near-lemma
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (near x n) (near y n))))
	     (and (<= x (near-witness x y n))
		  (<= (near-witness x y n) y)
		  (exactp (near-witness x y n) (1+ n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near near-monotone-support
                                      near-monotone)
		  :use ((:instance near-near-2)
			(:instance near-near-1)
			(:instance near-near-9)
			(:instance near-monotone)))))

(local
 (defthm near-near-10
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (integerp n)
		  (integerp k)
		  (> k 0)
		  (>= n k)
		  (< 0 a)
		  (< a x)
		  (< 0 y)
		  (< x y)
		  (< y (fp+ a (1+ n)))
		  (exactp a (1+ n)))
	     (= (near y k) (near x k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near near-monotone)
		  :use ((:instance near-near-lemma (n k))
			(:instance exactp-<= (x (near-witness x y k)) (m (1+ k)) (n (1+ n)))
			(:instance fp+2 (x a) (y (near-witness x y k)) (n (1+ n))))))))

;bad name?
(defthm near-near
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (integerp n)
		  (integerp k)
		  (> k 0)
		  (>= n k)
		  (< 0 a)
		  (< a x)
		  (< 0 y)
		  (< y (fp+ a (1+ n)))
		  (exactp a (1+ n)))
	     (<= (near y k) (near x k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-near-10)
			(:instance near-monotone (n k) (x y) (y x))))))


;why disabled?
(defthmd near-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp k))
	     (= (near (* x (expt 2 k)) n)
		(* (near x n) (expt 2 k))))
  :hints (("goal" :in-theory (enable near)
		  :use (trunc-shift
			away-shift
			(:instance sig-expo-shift (n k))))))


(local
 (defthm near-a-a-1
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (integerp n) (> n 0)
                 (exactp a n)
                 (> (near x n) a))
            (>= (near x n) (+ a (expt 2 (- (1+ (expo a)) n)))))
   :rule-classes ()
   :hints (("goal" :use ((:instance fp+2 (x a) (y (near x n)))
)))))

(local
 (defthm near-a-a-2
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (rationalp d) (> d 0)
                 (integerp n) (> n 0)
                 (<= (near x n) a)
                 (> x (+ a d)))
            (> (abs (- (near x n) x))
               (abs (- (+ a d d)
                       x))))
   :rule-classes ()))

(local
 (defthm near-a-a-3
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (integerp n) (> n 0)
                 (<= (near x n) a)
                 (> x (+ a (expt 2 (- (expo a) n)))))
            (> (abs (- (near x n) x))
               (abs (- (+ a
                          (expt 2 (- (expo a) n))
                          (expt 2 (- (expo a) n)))
                       x))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;expt-pos
                               )
            :use ((:instance near-a-a-2 (d (expt 2 (- (expo a) n))))
;			(:instance expt-pos (x (- (expo a) n)))
                  )))))

(local
 (defthm near-a-a-4
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (integerp n) (> n 0)
                 (<= (near x n) a)
                 (> x (+ a (expt 2 (- (expo a) n)))))
            (> (abs (- (near x n) x))
               (abs (- (+ a (expt 2 (- (1+ (expo a)) n)))
                       x))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable expt-compare-equal)
            :use ((:instance near-a-a-3)
                         (:instance expt-split (r 2) (i (- (expo a) n)) (j 1)))))))

(defthm near-a-a
  (implies (and (rationalp x) (> x 0)
                (rationalp a) (> a 0)
                (integerp n) (> n 0)
                (exactp a n)
                (> x (+ a (expt 2 (- (expo a) n)))))
           (>= (near x n) (+ a (expt 2 (- (1+ (expo a)) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
           :use ((:instance near2 (y (+ a (expt 2 (- (1+ (expo a)) n)))))
                 (:instance near-a-a-4)
                 (:instance near-a-a-1)
                 (:instance fp+1 (x a))
;			(:instance expt-pos (x (- (1+ (expo a)) n)))
                 ))))

(local
 (defthm near-a-b-1
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (rationalp d) (> d 0)
                 (integerp n) (> n 0)
                 (>= (near x n) (+ a d d))
                 (< x (+ a d)))
            (> (abs (- (near x n) x))
               (abs (- a x))))
   :rule-classes ()))

(local
 (defthm near-a-b-2
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (integerp n) (> n 0)
                 (>= (near x n)
                     (+ a
                        (expt 2 (- (expo a) n))
                        (expt 2 (- (expo a) n))))
                 (< x (+ a (expt 2 (- (expo a) n)))))
            (> (abs (- (near x n) x))
               (abs (- a x))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;expt-pos
                               )
            :use ((:instance near-a-b-1 (d (expt 2 (- (expo a) n))))
;			(:instance expt-pos (x (- (expo a) n)))
                  )))))

(local
 (defthm near-a-b-3
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (integerp n) (> n 0)
                 (>= (near x n)
                     (+ a (expt 2 (- (1+ (expo a)) n))))
                 (< x (+ a (expt 2 (- (expo a) n)))))
            (> (abs (- (near x n) x))
               (abs (- a x))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable expt-compare-equal)
            :use ((:instance near-a-b-2)
                  (:instance expt-split (r 2) (i (- (expo a) n)) (j 1)))))))

(defthm near-a-b
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (<= (near x n) a))
  :rule-classes ()
  :hints (("goal" :use ((:instance near2 (y a))
			(:instance near-a-b-3)
			(:instance near-a-a-1)))))

(local
 (defthm near-a-c-1
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (integerp n) (> n 0)
                 (exactp a n)
                 (>= x a))
            (>= (near x n) a))
   :rule-classes ()
   :hints (("goal" :use ((:instance near-monotone (x a) (y x))
                         (:instance near-choice (x a))
                         (:instance trunc-exactp-b (x a))
                         (:instance away-exactp-b (x a)))))))

(local
 (defthm near-a-c-2
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a))
	     (>= a
		 (+ (expt 2 (expo x))
		    (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance expo-lower-bound)
			(:instance fp+2 (x (expt 2 (expo x))) (y a))
			(:instance exactp-2**n (n (expo x)) (m n)))))))

(local
 (defthm near-a-c-3
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (integerp n) (> n 0)
                 (> x (- a (expt 2 (- (expo x) n)))))
            (> x (- a (expt 2 (- (1+ (expo x)) n)))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable expt-compare)
            :use ((:instance expt-weak-monotone (n (- (expo x) n)) (m (- (1+ (expo x)) n))))))))

(local
 (defthm near-a-c-4
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (integerp n) (> n 0)
                 (exactp a n)
                 (< x a)
                 (> x (- a (expt 2 (- (expo x) n)))))
            (= (expo (- a (expt 2 (- (1+ (expo x)) n))))
               (expo x)))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;expt-pos
                               )
            :use ((:instance near-a-c-2)
                  (:instance near-a-c-3)
;			(:instance expt-pos (x (expo x)))
                  (:instance expo-upper-bound)
                  (:instance expo-unique
                             (x (- a (expt 2 (- (1+ (expo x)) n))))
                             (n (expo x))))))))

(local
(defthm near-a-c-5
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (integerp (* (- a (expt 2 (- (1+ (expo x)) n)))
			  (expt 2 (- (1- n) (expo x))))))
  :rule-classes ()
  :hints (("goal" :use ((:instance expt-split (r 2) (i (- (1+ (expo x)) n)) (j (- (1- n) (expo x))))
			(:instance exactp-<=-expo (x a) (e (expo x)))
			(:instance near-a-c-3)
			(:instance expo-monotone (x (- a (expt 2 (- (1+ (expo x)) n)))) (y a))
			(:instance expo-monotone (y a)))))))

(local
(defthm near-a-c-6
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (exactp (- a (expt 2 (- (1+ (expo x)) n)))
		     n))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance exactp2 (x (- a (expt 2 (- (1+ (expo x)) n)))))
			(:instance near-a-c-5)
			(:instance near-a-c-2)
;			(:instance expt-pos (x (expo x)))
			(:instance near-a-c-4))))))

(local
(defthm near-a-c-7
    (implies (and (rationalp x)
		  (rationalp a)
		  (rationalp e)
		  (> x (- a e)))
	     (> x (+ (- a (* 2 e))
		     e)))
  :rule-classes ()))

(local
 (defthm near-a-c-8
   (implies (and (rationalp x)
                 (rationalp a)
                 (integerp n)
                 (> x (- a (expt 2 (- (expo x) n)))))
            (> x (+ (- a (expt 2 (- (1+ (expo x)) n)))
                    (expt 2 (- (expo x) n)))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable expt-compare-equal)
            :use ((:instance expt-split (r 2) (i 1) (j (- (expo x) n)))
                  (:instance near-a-c-7 (e (expt 2 (- (expo x) n)))))))))

(local
 (defthm near-a-c-9
   (implies (and (rationalp x) (> x 0)
                 (rationalp a) (> a 0)
                 (integerp n) (> n 0)
                 (exactp a n)
                 (< x a)
                 (> x (- a (expt 2 (- (expo x) n)))))
            (> (- a (expt 2 (- (1+ (expo x)) n)))
               0))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;expt-pos
                               )
            :use ((:instance near-a-c-2)
;			(:instance expt-pos (x (expo x)))
                  )))))

(defthm near-a-c
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (>= (near x n) a))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-a-a (a (- a (expt 2 (- (1+ (expo x)) n)))))
			(:instance near-a-c-8)
			(:instance near-a-c-6)
			(:instance near-a-c-4)
			(:instance near-a-c-9)))))




(local
 (defthm near-exact-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (let ((f (re (* (expt 2 (1- n)) (sig x)))))
	       (and (< f 1) (< 0 f))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable re)
           :use ((:instance fl-def-linear (x (* (expt 2 (1- n)) (sig x))))
			(:instance exactp))))))

(local
 (defthm near-exact-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (exactp x (1+ n)))
	     (let ((f (re (* (expt 2 (1- n)) (sig x)))))
	       (integerp (* 2 f))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable expt re)
           :use ((:instance exactp (n (1+ n))))))))

(local
 (defthm near-exact-3
    (implies (and (integerp |2F|)
		  (< 0 |2F|)
		  (< |2F| 2))
	     (= |2F| 1))
  :rule-classes ()))

(local
 (defthm near-exact-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n)))
	     (= (re (* (expt 2 (1- n)) (sig x)))
		1/2))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-exact-1)
			(:instance near-exact-2)
			(:instance near-exact-3 (|2F| (* 2 (re (* (expt 2 (1- n)) (sig x)))))))))))

(local
 (defthm near-exact-5
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (evenp (fl (* (expt 2 (1- n)) (sig x)))))
	     (= (near x n)
		(* (fl (* (expt 2 (1- n)) (sig x)))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near)
			(:instance near-exact-4)
			(:instance trunc))))))

(local
 (defthm near-exact-6
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (evenp (fl (* (expt 2 (1- n)) (sig x)))))
	     (= (* (expt 2 (- (- n 2) (expo x)))
		   (near x n))
		(/ (fl (* (expt 2 (1- n)) (sig x)))
		   2)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable a15)
           :use ((:instance near-exact-5)
			(:instance expt-split (r 2) (i (- (- n 2) (expo x))) (j (expt 2 (- (1+ (expo x)) n)))))))))

(local
 (defthm near-exact-7
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (evenp (fl (* (expt 2 (1- n)) (sig x)))))
	     (integerp (* (expt 2 (- (- n 2) (expo x)))
			  (near x n))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-exact-6)
			(:instance evenp (x (fl (* (expt 2 (1- n)) (sig x))))))))))

(local
 (defthm near-exact-8
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (evenp (fl (* (expt 2 (1- n)) (sig x)))))
	     (= (expo (near x n)) (expo x)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-exact-4)
			(:instance near)
			(:instance expo-trunc))))))

(local
 (defthm near-exact-9
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (evenp (fl (* (expt 2 (1- n)) (sig x)))))
	     (exactp (near x n) (1- n)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-exact-7)
			(:instance near-exact-8)
			(:instance near-pos)
			(:instance exactp2 (x (near x n)) (n (1- n))))))))

(local
 (defthm near-exact-10
     (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (= (near x n)
		(* (cg (* (expt 2 (1- n)) (sig x)))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near)
			(:instance near-exact-4)
			(:instance away))))))

(local
 (defthm near-exact-11
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (= (near x n)
		(* (1+ (fl (* (expt 2 (1- n)) (sig x))))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable re)
           :use ((:instance near-exact-10)
			(:instance near-exact-1)
			(:instance fl-cg (x (* (expt 2 (1- n)) (sig x)))))))))

(local
 (defthm near-exact-12
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (= (* (expt 2 (- (- n 2) (expo x)))
		   (* (1+ (fl (* (expt 2 (1- n)) (sig x))))
		      (expt 2 (- (1+ (expo x)) n))))
		(/ (1+ (fl (* (expt 2 (1- n)) (sig x))))
		   2)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable a15)
           :use ((:instance expt-split (r 2) (i (- (- n 2) (expo x))) (j (expt 2 (- (1+ (expo x)) n)))))))))

(local
 (defthm near-exact-13
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (= (* (expt 2 (- (- n 2) (expo x)))
		   (near x n))
		(/ (1+ (fl (* (expt 2 (1- n)) (sig x))))
		   2)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-exact-11)
			(:instance near-exact-12))))))

(local
 (defthm near-exact-14
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (integerp (* (expt 2 (- (- n 2) (expo x)))
			  (near x n))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable a9; rearrange-fractional-coefs-equal
                                      distributivity)
		  :use ((:instance near-exact-13)
			(:instance evenp (x (fl (* (expt 2 (1- n)) (sig x)))))
			(:instance x-or-x/2 (x (fl (* (expt 2 (1- n)) (sig x))))))))))

(local
 (defthm near-exact-15
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (= (near x n) (expt 2 (1+ (expo x)))))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (= (expo (near x n)) (expo x)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-exact-4)
			(:instance near)
			(:instance away)
;			(:instance away-pos)
			(:instance expo-away))))))

(local
 (defthm near-exact-16
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (= (near x n) (expt 2 (1+ (expo x)))))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (exactp (near x n) (1- n)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-exact-14)
			(:instance near-exact-15)
			(:instance near-pos)
			(:instance exactp2 (x (near x n)) (n (1- n))))))))

(local
 (defthm near-exact-17
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (exactp (near x n) (1- n)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-exact-16)
			(:instance exactp-2**n (n (1+ (expo x))) (m (1- n))))))))


(encapsulate ()
        (local
         (defthm near-exact-support
         (implies (and (rationalp x) (> x 0)
                       (integerp n) (> n 1)
                       (exactp x (1+ n))
                       (not (exactp x n)))
                  (exactp (near x n) (1- n)))
         :rule-classes ()
         :hints (("goal" :use ((:instance near-exact-17)
               		(:instance near-exact-9))))))

 (defthm near-exact
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 1)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (near x n) (1- n)))
    :hints (("Goal" :cases ((not (equal x 0)))
             :in-theory (enable near-minus))
            ("Subgoal 2" :in-theory (enable exactp))
            ("Subgoal 1" :cases  ((not (> x 0))))
            ("Subgoal 1.2" :use near-exact-support)
            ("Subgoal 1.1" :use ((:instance near-exact-support
                                            (x (* -1 x))))))
  :rule-classes ()))



(local
 (defthm near-est-1
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (> (abs (- x (near x n)))
                    (expt 2 (- (expo x) n))))
            (< (trunc x n)
               (- x (expt 2 (- (expo x) n)))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable TRUNC-EXACTP-A REARRANGE-NEGATIVE-COEFS-<)
            :use ((:instance near2 (y (trunc x n)))
                  (:instance trunc-exactp-a)
;			(:instance trunc-pos)
                  (:instance trunc-upper-pos))))))

;; (i-am-here) ;; Thu Oct 12 16:34:52 2006

(local
 (defthm near-est-2
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near x n)))
		     (expt 2 (- (expo x) n))))
	     (> (away x n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable away-exactp-a
                                      near-exactp-c-support)
           :use ((:instance near2-original (y (away x n)))
                 (:instance away-exactp-a)
                 ;(:instance away-pos)
                 (:instance away-lower-pos))))))

(local
 (defthm near-est-3
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near x n)))
		     (expt 2 (- (expo x) n))))
	     (> (away x n)
		(+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable a15 expt-compare-equal)
		  :use ((:instance near-est-1)
			(:instance expt-split (r 2) (i (- (expo x) n)) (j 1))
			(:instance near-est-2))))))

(local
 (defthm near-est-4
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near x n)))
		     (expt 2 (- (expo x) n))))
	     (> x
		(+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-est-3)
			(:instance fp+1 (x (trunc x n)))
			(:instance trunc-exactp-a)
;			(:instance trunc-pos)
			(:instance expo-trunc)
			(:instance away-exactp-c (a (+ (trunc x n) (expt 2 (- (1+ (expo x)) n))))))))))

(local
 (defthm near-est-support
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0))
	     (<= (abs (- x (near x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-est-4)
			(:instance trunc-lower-1)
;			(:instance trunc-pos)
                        )))))


(defthm near-est
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (near x n)))
		 (expt 2 (- (expo x) n))))
    :hints (("Goal" :cases ((not (> x 0)))
             :in-theory (enable near-minus))
            ("Subgoal 2" :use ((:instance near-est-support)))
            ("Subgoal 1" :use ((:instance near-est-support
                                          (x (* -1 x))))))
  :rule-classes ())





(local
 (defthm near-power-a-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x))))))
	     (= (expo (near x n)) (expo x)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near)
			(:instance away)
;			(:instance away-pos)
			(:instance expo-trunc)
			(:instance expo-away))))))

(local
 (defthm near-power-a-2
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 0)
                 (not (= (near x n)
                         (expt 2 (1+ (expo x))))))
            (< (near x n) (expt 2 (1+ (expo x)))))
   :rule-classes ()
   :hints (("goal" :use ((:instance near-power-a-1)
                         (:instance expo-upper-bound (x (near x n)))
                         (:instance near-pos))))))

(local
 (defthm near-power-a-3
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 0)
                 (not (= (near x n)
                         (expt 2 (1+ (expo x))))))
            (<= (+ (near x n) (expt 2 (- (1+ (expo x)) n)))
                (expt 2 (1+ (expo x)))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable EXACTP-2**N-REWRITE EXACTP-2**N)
            :use ((:instance near-power-a-2)
                 (:instance near-power-a-1)
;                 (:instance exactp-near)
                 (:instance fp+2 (x (near x n)) (y (expt 2 (1+ (expo x)))))
                 (:instance exactp-2**n (n (1+ (expo x))) (m n))
                 (:instance near-pos))))))

(local
 (defthm near-power-a-4
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 0)
                 (not (= (near x n)
                         (expt 2 (1+ (expo x))))))
            (<= (+ (- x (expt 2 (- (expo x) n)))
                   (expt 2 (- (1+ (expo x)) n)))
                (expt 2 (1+ (expo x)))))
   :rule-classes ()
   :hints (("goal" :use ((:instance near-power-a-3)
                         (:instance near-est))))))

(local
 (defthm near-power-a-5
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 0)
                 (not (= (near x n)
                         (expt 2 (1+ (expo x))))))
            (<= (+ x (expt 2 (- (expo x) n)))
                (expt 2 (1+ (expo x)))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable expt-compare-equal)
            :use ((:instance near-power-a-4)
                  (:instance expt-split (r 2) (i (- (expo x) n)) (j 1)))))))

(local
 (defthm near-power-a-6
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (+ x (expt 2 (- (expo x) n)))
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-power-a-5))))))

(local
 (defthm near-power-a-7
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= x
		(- (expt 2 (1+ (expo x)))
		   (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-power-a-6))))))

(local
 (defthm near-power-a-8
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (integerp (* (- (expt 2 (1+ (expo x)))
			     (expt 2 (- (expo x) n)))
			  (expt 2 (- n (expo x))))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-power-a-7)
			(:instance expt-split (r 2) (i (- n (expo x))) (j (1+ (expo x))))
			(:instance expt-split (r 2) (i (- n (expo x))) (j (- (expo x) n))))))))

(local
 (defthm hack-90
    (implies (and (= x y)
		  (integerp (* y e)))
	     (integerp (* x e)))
  :rule-classes ()))

(local
 (defthm near-power-a-9
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (integerp (* x (expt 2 (- n (expo x))))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-power-a-7)
			(:instance hack-90
				   (y (- (expt 2 (1+ (expo x))) (expt 2 (- (expo x) n))))
				   (e (expt 2 (- n (expo x)))))
			(:instance near-power-a-8))))))

(local
 (defthm near-power-a-10
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (exactp x (1+ n)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable exactp2)
		  :use ((:instance near-power-a-9))))))

(local
 (defthm near-power-a-11
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (not (exactp x n)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-power-a-6)
			(:instance expo-upper-bound)
			(:instance fp+2 (y (expt 2 (1+ (expo x)))))
			(:instance exactp-2**n (n (1+ (expo x))) (m n))
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (- (1+ (expo x)) n))))))))

(local
 (defthm near-power-a-12
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (exactp (near x n) (1- n)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-power-a-10)
			(:instance near-power-a-11)
			(:instance near-exact))))))

(local
 (defthm near-power-a-13
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (not (= (near x n)
                         (expt 2 (1+ (expo x)))))
                 (>= (+ x (expt 2 (- (expo x) n)))
                     (expt 2 (1+ (expo x)))))
            (<= (+ (near x n) (expt 2 (- (+ (expo x) 2) n)))
                (expt 2 (1+ (expo x)))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable exactp-2**n exactp-2**n-rewrite)
            :use ((:instance near-power-a-12)
                  (:instance near-power-a-2)
                  (:instance near-pos)
                  (:instance fp+2 (x (near x n)) (n (1- n)) (y (expt 2 (1+ (expo x)))))
                  (:instance exactp-2**n (n (1+ (expo x))) (m (1- n)))
                  (:instance near-power-a-1))))))

(local
 (defthm near-power-a-14
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (not (= (near x n)
                         (expt 2 (1+ (expo x)))))
                 (>= (+ x (expt 2 (- (expo x) n)))
                     (expt 2 (1+ (expo x)))))
            (>= (+ (near x n) (expt 2 (- (+ (expo x) 1) n)))
                (expt 2 (1+ (expo x)))))
   :rule-classes ()
   :hints (("goal" :in-theory (enable expt-split)
            :use ((:instance near-est))))))

(defthm near-power-a
  (implies (and (rationalp x) (> x 0)
                (integerp n) (> n 1)
                (>= (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x)))))
           (= (near x n)
              (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable expt-compare)
           :use ((:instance near-power-a-13)
                 (:instance near-power-a-14)
                 (:instance expt-strong-monotone
                            (n (- (+ (expo x) 1) n))
                            (m (- (+ (expo x) 2) n)))))))

(local
(defthm near-power-b-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (>= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance exactp-2**n (n (1+ (expo x))) (m n))
;			(:instance expt-pos (x (- (expo x) n)))
			(:instance trunc-exactp-c
				   (x (+ x (expt 2 (- (expo x) n))))
				   (a (expt 2 (1+ (expo x))))))))))

(local
(defthm near-power-b-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x))))
		  (not (= (trunc (+ x (expt 2 (- (expo x) n))) n)
			  (expt 2 (1+ (expo x))))))
	     (> (trunc (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-power-b-1))))))

(local
(defthm near-power-b-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x))))
		  (not (= (trunc (+ x (expt 2 (- (expo x) n))) n)
			  (expt 2 (1+ (expo x))))))
	     (>= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 (+ (expt 2 (1+ (expo x)))
		    (expt 2 (- (+ 2 (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near-power-b-2)
			(:instance exactp-2**n (n (1+ (expo x))) (m n))
			(:instance trunc-exactp-a (x (+ x (expt 2 (- (expo x) n)))))
;			(:instance expt-pos (x (1+ (expo x))))
			(:instance expo-2**n (n (1+ (expo x))))
			(:instance fp+2
				   (x (expt 2 (1+ (expo x))))
				   (y (trunc (+ x (expt 2 (- (expo x) n))) n))))))))

(local
(defthm near-power-b-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x))))
		  (not (= (trunc (+ x (expt 2 (- (expo x) n))) n)
			  (expt 2 (1+ (expo x))))))
	     (> (trunc (+ x (expt 2 (- (expo x) n))) n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable expt-compare)
           :use ((:instance near-power-b-3)
			(:instance expo-upper-bound)
			(:instance expt-weak-monotone (n (- (expo x) n)) (m (- (+ 2 (expo x)) n))))))))

(defthm near-power-b
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (trunc (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near-power-b-4)
			(:instance trunc-upper-pos (x (+ x (expt 2 (- (expo x) n)))))
;			(:instance expt-pos (x (- (expo x) n)))
                        ))))

(local
 (defthm near-trunc-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (near x n)
		(if (and (exactp x (1+ n)) (not (exactp x n)))
		    (trunc (+ x (expt 2 (- (expo x) n))) (1- n))
		  (trunc (+ x (expt 2 (- (expo x) n))) n))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near-power-a)
			(:instance near-power-b)
			(:instance exactp-2**n (n (1+ (expo x))) (m (1- n)))
			(:instance trunc-trunc (x (+ x (expt 2 (- (expo x) n)))) (m (1- n)))
			(:instance trunc-exactp-b
				   (x (trunc (+ x (expt 2 (- (expo x) n))) n))
				   (n (1- n)))
;			(:instance expt-pos (x (- (expo x) n)))
                        )))))

(local
 (defthm near-trunc-2
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x)))))
            (= (expo (near x n))
               (expo x)))
   :rule-classes ()
   :hints (("goal" :use ((:instance near-power-a-1)
                         (:instance near-est))))))

(local
 (defthm near-trunc-3
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x)))))
            (= (expo (+ x (expt 2 (- (expo x) n))))
               (expo x)))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;expt-pos
                               )
            :use ((:instance expo-unique (x (+ x (expt 2 (- (expo x) n)))) (n (expo x)))
                  (:instance expo-lower-bound)
;			(:instance expt-pos (x (- (expo x) n)))
                  )))))

(local
 (defthm near-trunc-4
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (exactp x n))
            (>= (trunc (+ x (expt 2 (- (expo x) n))) n)
                x))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;expt-pos
                               )
            :use ((:instance trunc-exactp-c
                             (x (+ x (expt 2 (- (expo x) n))))
                             (a x))
;			(:instance expt-pos (x (- (expo x) n)))
                  )))))

(local
 (defthm near-trunc-5
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (exactp x n))
            (<(trunc (+ x (expt 2 (- (expo x) n))) n)
              (fp+ x n)))
   :rule-classes ()
   :hints (("goal" :in-theory (disable expt-compare
                                       )
            :use ((:instance trunc-upper-pos (x (+ x (expt 2 (- (expo x) n)))))
                  (:instance expt-strong-monotone (n (- (expo x) n)) (m (- (1+ (expo x)) n)))
;			(:instance expt-pos (x (- (expo x) n)))
                  )))))

(local
(defthm near-trunc-6
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x n))
	     (<= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 x))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near-trunc-5)
			(:instance fp+2 (y (trunc (+ x (expt 2 (- (expo x) n))) n)))
			(:instance trunc-exactp-b (x (+ x (expt 2 (- (expo x) n)))))
;			(:instance expt-pos (x (- (expo x) n)))
                        )))))

(local
(defthm near-trunc-7
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x n))
	     (= (trunc (+ x (expt 2 (- (expo x) n))) n)
		x))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-trunc-4)
			(:instance near-trunc-6))))))

(defthm near-exactp
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (exactp x n))
	     (equal (near x n) x))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-choice)
			(:instance trunc-exactp-b)
			(:instance away-exactp-b)))))

(local
 (defthm near-trunc-case-1
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (exactp x n))
            (= (trunc (+ x (expt 2 (- (expo x) n))) n)
               (near x n)))
   :rule-classes ()
   :hints (("goal" :use ((:instance near-trunc-7)
                         (:instance near-exactp)
                         (:instance trunc-exactp-b (x (+ x (expt 2 (- (expo x) n))))))))))

(local
 (defthm near-trunc-8
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (= (near x n)
                    (- x (expt 2 (- (expo x) n)))))
            (exactp x (1+ n)))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;exactp-near
                                       NEAR-EXACTP-D
                                       NEAR-EXACTP-D-SUPPORT
                                       )
            :use ((:instance near-trunc-2)
                  (:instance near-pos)
;	(:instance exactp-near)
                  (:instance fp+1 (x (near x n)) (n (1+ n)))
                  (:instance exactp-<= (x (near x n)) (m n) (n (1+ n))))))))

(local
 (defthm near-trunc-9
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (not (exactp x (1+ n))))
            (> (near x n)
               (- x (expt 2 (- (expo x) n)))))
   :rule-classes ()
   :hints (("goal" :use ((:instance near-trunc-8)
                         (:instance near-est))))))

(local
 (defthm near-trunc-10
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1))
            (<= (near x n)
                (trunc (+ x (expt 2 (- (expo x) n))) n)))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;exactp-near
                                       )
            :use (;(:instance exactp-near)
                  (:instance trunc-exactp-c (x (+ x (expt 2 (- (expo x) n)))) (a (near x n)))
                  (:instance near-est))))))

(local
 (defthm near-trunc-11
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (not (exactp x (1+ n))))
            (< (trunc (+ x (expt 2 (- (expo x) n))) n)
               (+ (near x n)
                  (expt 2 (- (expo x) n))
                  (expt 2 (- (expo x) n)))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;expt-pos
                               )
            :use ((:instance near-trunc-9)
                  (:instance trunc-upper-pos (x (+ x (expt 2 (- (expo x) n)))))
;			(:instance expt-pos (x (- (expo x) n)))
                  )))))

(local
 (defthm near-trunc-12
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (not (exactp x (1+ n))))
            (< (trunc (+ x (expt 2 (- (expo x) n))) n)
               (+ (near x n)
                  (expt 2 (- (1+ (expo x)) n)))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable expt-compare-equal)
            :use ((:instance near-trunc-11)
                         (:instance expt-split (r 2) (i (- (expo x) n)) (j 1)))))))

(local
 (defthm near-trunc-13
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (not (exactp x (1+ n))))
            (<= (trunc (+ x (expt 2 (- (expo x) n))) n)
                (near x n)))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;exactp-near
                                       trunc-exactp-a ;expt-pos
                                       NEAR-EXACTP-D-SUPPORT
                                       )
            :use ((:instance near-trunc-12)
                  (:instance fp+2
                             (x (near x n))
                             (y (trunc (+ x (expt 2 (- (expo x) n))) n)))
                  (:instance near-trunc-2)
;			(:instance expt-pos (x (- (expo x) n)))
;                  (:instance exactp-near)
                  (:instance near-pos)
                  (:instance trunc-exactp-a (x (+ x (expt 2 (- (expo x) n))))))))))

(local
 (defthm near-trunc-case-2
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (not (exactp x (1+ n))))
            (= (near x n)
               (trunc (+ x (expt 2 (- (expo x) n))) n)))
   :rule-classes ()
   :hints (("goal" :use ((:instance near-trunc-10)
                         (:instance near-trunc-13))))))

(local
 (defthm near-trunc-14
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (> (near x n) x))
	     (= (near x n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-est)
;			(:instance exactp-near)
			(:instance exactp-<= (x (near x n)) (m n) (n (1+ n)))
			(:instance fp+2 (n (1+ n)) (y (near x n))))))))

(local
 (defthm near-trunc-15
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (> (near x n) x))
	     (= (near x n)
		(trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-trunc-14)
			(:instance near-exact)
			(:instance trunc-exactp-b (x (near x n)) (n (1- n))))))))

(local
 (defthm near-trunc-16
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (< (near x n) x))
	     (<= (near x n)
		 (trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near-exact)
;			(:instance expt-pos (x (- (expo x) n)))
			(:instance trunc-exactp-c
				   (x (+ x (expt 2 (- (expo x) n))))
				   (n (1- n))
				   (a (near x n))))))))

(local
 (defthm near-trunc-17
   (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (< (near x n) x))
	     (>= (+ (near x n)
		    (expt 2 (- (1+ (expo x)) n)))
		 (trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable expt-split)

		  :use ((:instance trunc-upper-pos (x (+ x (expt 2 (- (expo x) n)))) (n (1- n)))
			(:instance near-est))))))

(local
 (defthm near-trunc-18
    (implies (and (rationalp x)
		  (integerp n))
	     (> (+ (near x n)
		   (expt 2 (- (+ 2 (expo x)) n)))
		(+ (near x n)
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance expt-strong-monotone
				   (n (- (1+ (expo x)) n))
				   (m (- (+ 2 (expo x)) n))))))))

(local
 (defthm near-trunc-19
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (exactp x (1+ n))
                 (not (exactp x n))
                 (< (near x n) x))
            (> (+ (near x n)
                  (expt 2 (- (+ 2 (expo x)) n)))
               (trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable  expt-compare)
            :use ((:instance near-trunc-17)
                  (:instance near-trunc-18))))))

(local
 (defthm near-trunc-20
   (implies (and (rationalp x) (> x 0)
                 (integerp n) (> n 1)
                 (< (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x))))
                 (exactp x (1+ n))
                 (not (exactp x n))
                 (< (near x n) x))
            (>= (near x n)
                (trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable ;expt-pos
                               near-exactp-d-support
                               )
            :use ((:instance near-exact)
;			(:instance expt-pos (x (- (expo x) n)))
                  (:instance trunc-exactp-a (x (+ x (expt 2 (- (expo x) n)))) (n (1- n)))
                  (:instance fp+2
                             (x (near x n))
                             (y (trunc (+ x (expt 2 (- (expo x) n))) (1- n)))
                             (n (1- n)))
                  (:instance near-pos)
                  (:instance near-trunc-19)
                  (:instance near-trunc-2))))))

(local
(defthm near-trunc-21
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (< (near x n) x))
	     (= (near x n)
		(trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-trunc-16)
			(:instance near-trunc-20))))))

(local
 (defthm near-trunc-case-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (near x n)
		(trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable near-exactp-a)
		  :use ((:instance near-trunc-21)
			(:instance near-exactp-a)
			(:instance near-trunc-15))))))

(defthm near-trunc
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (near x n)
		(if (and (exactp x (1+ n)) (not (exactp x n)))
		    (trunc (+ x (expt 2 (- (expo x) n))) (1- n))
		  (trunc (+ x (expt 2 (- (expo x) n))) n))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-trunc-1)
			(:instance near-trunc-case-1)
			(:instance near-trunc-case-2)
			(:instance near-trunc-case-3)))))

(defthm near-0
  (equal (near 0 n)
         0)
  :hints (("Goal" :in-theory (enable near))))


;; ;BOZO yuck?
;; (defthm sgn-near
;;   (implies (and (rationalp x)
;;                 (integerp n)
;;                 (> n 0))
;;            (= (near x n)
;;               (* (sgn x) (near (abs x) n))))
;;   :rule-classes ()
;;   :hints (("goal" :in-theory (enable abs))))




(defthm plus-near-1
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                )
           (= (re (* (expt 2 (1- k)) (sig y)))
              (re (* (expt 2 (1- (+ k (- (expo (+ x y)) (expo y)))))
                     (sig (+ x y))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable re sig exactp expt-split expt-minus))))

(defthm plus-near-2
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ -1 k (- (expo x) (expo y)))))
           (iff (evenp (fl (* (expt 2 (1- k)) (sig y))))
                (evenp (fl (* (expt 2
                                    (1- (+ k (- (expo (+ x y)) (expo y)))))
                              (sig (+ x y)))))))
  :otf-flg t
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (expt-split
                                   expt-minus
                                   exactp sig ; EXPT-SPLIT-leading-constant
                                   evenp ;this is sort of cheating...
                                   ) ())
           :use ((:instance exactp2 (n (+ k (expo x) (- (expo y)))))
                 (:instance exactp-<=
                            (m (+ -1 k (expo x) (- (expo y))))
                            (n (+ k (expo x) (- (expo y)))))))))

(defthm plus-near
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ -1 k (- (expo x) (expo y)))))
           (= (+ x (near y k))
              (near (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable near)
           :use (plus-trunc plus-away plus-near-1 plus-near-2
                            (:instance exactp-<=
                                       (m (+ -1 k (expo x) (* -1 (expo y))))
                                       (n (+ k (expo x) (* -1 (expo y)))))))))



