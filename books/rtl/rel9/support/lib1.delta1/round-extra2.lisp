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

(in-package "ACL2")



(include-book "../lib1/top")

(set-inhibit-warnings "theory")

;;;**********************************************************************
;;;                         Truncation
;;;**********************************************************************

;; (defund trunc (x n)
;;   (declare (xargs :guard (integerp n)))
;;   (* (sgn x)
;;      (fl (* (expt 2 (1- n)) (sig x)))
;;      (expt 2 (- (1+ (expo x)) n))))

;; (defthmd trunc-integer-type-prescription
;;   (implies (and (>= (expo x) n)
;;                 (case-split (integerp n))
;;                 )
;;            (integerp (trunc x n)))
;;   :rule-classes :type-prescription)

;; (defthmd trunc-rewrite
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (equal (trunc x n)
;; 		    (* (sgn x)
;; 		       (fl (* (expt 2 (- (1- n) (expo x))) (abs x)))
;; 		       (expt 2 (- (1+ (expo x)) n))))))

;; (defthmd abs-trunc
;;   (equal (abs (trunc x n))
;;          (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n)))))



;; (encapsulate ()
;;   (local
;;    (defthm fl-sig-expt-2-lemma-1
;;      (implies (and (<= n 0)
;;                    (integerp n))
;;               (< (* (SIG X) (EXPT 2 (+ -1 N))) 1))
;;      :hints (("Goal" :in-theory (enable expt-weak-monotone-linear)
;;               :cases ((not (<= (expt 2 (+ -1 n)) (/ 2)))))
;;              ("Subgoal 2"
;;               :use ((:instance sig-upper-bound)))
;;              ("Subgoal 1"
;;               :use ((:instance expt-weak-monotone-linear
;;                                (n (+ -1 n))
;;                                (m -1)))))))


;;   (local
;;    (defthm fl-is-0
;;      (implies (and (rationalp x)
;;                    (< x 1)
;;                    (<= 0 x))
;;               (equal (fl x) 0))
;;      :rule-classes nil))



;;   (local
;;    (defthm fl-sig-expt-2
;;      (implies (and (<= n 0)
;;                    (rationalp x)
;;                    (integerp n))
;;               (equal (fl (* (SIG X) (EXPT 2 (+ -1 N)))) 0))
;;      :hints (("Goal" :use ((:instance fl-is-0
;;                                       (x (* (sig x)
;;                                             (expt 2 (+ -1 n)))))
;;                            (:instance sig-lower-bound))))))


;;   (defthm trunc-to-0
;;       (implies (and (rationalp x)
;;   		  (integerp n)
;;   		  (<= n 0))
;;   	     (equal (trunc x n) 0))
;;       :hints (("Goal" :in-theory (enable trunc)))))

;; ;; moved to trunc.lisp
;; (defthm trunc-to-0
;;   (implies (and (rationalp x)
;;                 (integerp n)
;;                 (<= n 0))
;;            (equal (trunc x n) 0))
;;   :hints (("Goal" :in-theory (enable trunc))))


;; (defthmd sgn-trunc
;;       (implies (and (< 0 n)
;;                     (rationalp x)
;;   		  (integerp n))
;;   	     (equal (sgn (trunc x n))
;;     		    (sgn x))))


(encapsulate ()
  (local (include-book "../support/trunc"))
  (set-enforce-redundancy nil)
  (defthm trunc-to-0
    (implies (and (integerp n)
                  (<= n 0))
             (equal (trunc x n) 0))))

; (set-enforce-redundancy t)

;; (defthm trunc-positive
;;    (implies (and (< 0 x)
;;                  (case-split (rationalp x))
;;                  (case-split (integerp n))
;;                  (case-split (< 0 n))
;;                  )
;;             (< 0 (trunc x n)))
;;    :rule-classes (:rewrite :linear))


;; (defthm trunc-negative
;;   (implies (and (< x 0)
;;                 (case-split (rationalp x))
;;                 (case-split (integerp n))
;;                 (case-split (< 0 n)))
;;            (< (trunc x n) 0))
;;   :rule-classes (:rewrite :linear))


;; (defthm trunc-0
;;   (equal (trunc 0 n) 0))


;; (defthmd trunc-minus
;;   (equal (trunc (* -1 x) n)
;;          (* -1 (trunc x n))))


;; (defthmd trunc-shift
;;   (implies (integerp n)
;;            (equal (trunc (* x (expt 2 k)) n)
;;                   (* (trunc x n) (expt 2 k)))))


;; (defthmd trunc-upper-bound
;;     (implies (and (rationalp x)
;; 		  (integerp n))
;; 	     (<= (abs (trunc x n)) (abs x)))
;;   :rule-classes :linear)

;; (defthmd trunc-upper-pos
;;     (implies (and (<= 0 x)
;;                   (rationalp x)
;; 		  (integerp n))
;; 	     (<= (trunc x n) x))
;;   :rule-classes :linear)


;; (defthm expo-trunc
;;     (implies (and (< 0 n)
;;                   (rationalp x)
;; 		  (integerp n))
;; 	     (equal (expo (trunc x n))
;;                     (expo x))))


;; (defthm expo-trunc-strong
;;     (implies (and (nat n)
;;                   (rationalp x)
;; 		  (integerp n))
;; 	     (equal (expo (trunc x n))
;;                     (expo x))))
;;; wrong
;;;
(set-enforce-redundancy nil)

(encapsulate ()
 (local (include-book "../support/trunc"))
 (defthmd trunc-lower-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (> (abs (trunc x n)) (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
    :hints (("Goal" :by trunc-lower-1))
    :rule-classes (:linear))

 (defthmd trunc-lower-2
   (implies (and (rationalp x)
                 (not (= x 0))
                 (integerp n)
                 (> n 0))
            (> (abs (trunc x n)) (* (abs x) (- 1 (expt 2 (- 1 n))))))
   :rule-classes :linear)

 (defthmd trunc-lower-2-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (> (trunc x n) (* x (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear
  :hints (("Goal" :by trunc-lower-pos))))

;; moved into trunc.lisp ??


;----------------------------------------------------------------------

;; (defthm trunc-diff
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;;                   (> n 0))
;; 	     (< (abs (- x (trunc x n))) (expt 2 (- (1+ (expo x)) n))))
;;   :rule-classes ())

;; (defthm trunc-diff-pos
;;     (implies (and (rationalp x)
;; 		  (>= x 0)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (< (- x (trunc x n)) (expt 2 (- (1+ (expo x)) n))))
;;   :rule-classes ())


;; (defthm trunc-exactp-a
;;   (exactp (trunc x n) n)
;;   :hints (("Goal" :use ((:instance trunc-exactp-b---rtl-rel5-support)))))


;; (defthm trunc-diff-expo
;;     (implies (and (rationalp x)
;; 		  (not (exactp x n))
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (<= (expo (- x (trunc x n))) (- (expo x) n)))
;;   :rule-classes ())


;; (defthm trunc-exactp-b
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (iff (= x (trunc x n))
;; 		  (exactp x n)))
;;   :hints (("Goal" :use ((:instance trunc-exactp-a---rtl-rel5-support))))
;;   :rule-classes ())


;; (defthmd trunc-exactp-c
;;     (implies (and (exactp a n)
;; 		  (<= a x)
;;                   (rationalp x)
;; 		  (integerp n)
;; 		  (rationalp a))
;; 	     (<= a (trunc x n))))


;; (defthmd trunc-monotone
;;   (implies (and (<= x y)
;;                 (rationalp x)
;;                 (rationalp y)
;;                 (integerp n))
;;            (<= (trunc x n) (trunc y n)))
;;   :rule-classes :linear)

;----------------------------------------------------------------------


;; (defthm trunc-diff
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;;                   (> n 0))
;; 	     (< (abs (- x (trunc x n))) (expt 2 (- (1+ (expo x)) n))))
;;   :rule-classes ())

;; (defthm exactp-diff-cor
;;     (implies (and (rationalp x)
;; 		  (rationalp y)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (exactp x n)
;; 		  (exactp y n)
;; 		  (<= (abs (- x y)) (abs x))
;; 		  (<= (abs (- x y)) (abs y)))
;; 	     (exactp (- x y) n))
;;   :rule-classes ())


(encapsulate ()
  (local (include-book "../../arithmetic/basic"))
  (local
  (defthm not-exact-strictly-greater-than
    (implies (and (rationalp x)
                  (not (exactp x n))
                  (integerp n)
                  (> n 0)
                  (> x 0))
             (> x (expt 2 (expo x))))
    :hints (("Goal" :in-theory (enable exactp-2**n)
             :cases ((= x (expt 2 (expo x)))))
            ("Subgoal 2" :use ((:instance expo-lower-bound))))))

  ;; (defthm fp+2
  ;;     (implies (and (rationalp x)
  ;; 		  (> x 0)
  ;; 		  (rationalp y)
  ;; 		  (> y x)
  ;; 		  (integerp n)
  ;; 		  (> n 0)
  ;; 		  (exactp x n)
  ;; 		  (exactp y n))
  ;; 	     (>= y (fp+ x n)))
  ;;   :rule-classes ())


  (local
  (defthm strictly-greater-than-implies-no-less-than-fp+
    (implies (and (rationalp x)
                  (exactp x (1+ n))
                  (> x (expt 2 (expo x)))
                  (integerp n)
                  (> n 0))
            (>= x (+ (expt 2 (expo x))
                     (expt 2 (- (EXPO X) N)))))
    :hints (("Goal" :in-theory (enable exactp-2**n)
             :use ((:instance fp+2
                              (x (expt 2 (expo x)))
                              (y x)
                              (n (1+ n))))))))

  ;; (defthmd expo-monotone
  ;;   (implies (and (<= (abs x) (abs y))
  ;;                 (case-split (rationalp x))
  ;;                 (case-split (not (equal x 0)))
  ;;                 (case-split (rationalp y)))
  ;;            (<= (expo x) (expo y)))
  ;;   :rule-classes :linear)

  (local
   (defthm expo-of-x-minus-extra-bit-is-expo-x
     (implies (and (exactp x (1+ n))
                   (not (exactp x n))
                   (rationalp x)
                   (integerp n)
                   (> x 0)
                   (> n 0))
              (equal (expo (+  x (* -1 (expt 2 (+ (expo x) (* -1 n))))))
                     (expo x)))
     :hints (("Goal" :in-theory (enable exactp-2**n)
              :use ((:instance expo-monotone
                               (x (- x (expt 2 (- (expo x) n))))
                               (y x))
                    (:instance expo-monotone
                               (x (expt 2 (expo x)))
                               (y (- x (expt 2 (- (expo x) n)))))
                    (:instance strictly-greater-than-implies-no-less-than-fp+))))))

   ;; next we want to prove (- x (expt 2 (- (exp x) n))) is exactp  n

  (local
   (encapsulate ()
                (local (include-book "../../arithmetic/even-odd"))
                (defthm integerp-x-not-1/2x-lemma
                  (implies (and (integerp x)
                                (not (integerp (* x (/ 2)))))
                           (integerp (+ (* x (/ 2)) (* -1 (/ 2))))))))

   ;; may need some rule to merge 1/2 into expt 2
   (local
    (defthm merged-1/2-into-expt2
      (implies (and (integerp n)
                    (rationalp x))
               (equal (* 1/2 x (expt 2 n))
                      (* x (expt 2 (+ -1 n)))))
      :hints (("Goal"
               :use ((:instance a15
                                (i 2)
                                (j1 -1)
                                (j2 n)))))))


   (local
    (defthm a-is-n-exact
     (implies (and (not (exactp x n))
                   (exactp x (1+ n))
                   (> x 0)
                   (rationalp x)
                   (integerp n)
                   (> n 0))
              (exactp (+ x (* -1 (expt 2 (+ (expo x) (* -1 n)))))
                      n))
     :hints (("Goal" :in-theory (enable exactp2 a15)
              :use ((:instance integerp-x-not-1/2x-lemma
                               (x (* X (EXPT 2 (+ N (* -1 (EXPO X))))))))))))

   ;; (defthm fp+1
   ;;     (implies (and (rationalp x)
   ;; 		  (> x 0)
   ;; 		  (integerp n)
   ;; 		  (> n 0)
   ;; 		  (exactp x n))
   ;; 	     (exactp (fp+ x n) n))
   ;;   :rule-classes ())


   ;; (local
   ;; (defthm not-exact-strictly-greater-than
   ;;   (implies (and (rationalp x)
   ;;                 (not (exactp x n))
   ;;                 (integerp n)
   ;;                 (> n 0)
   ;;                 (> x 0))
   ;;            (> x (expt 2 (expo x))))
   ;;   :hints (("Goal" :in-theory (enable exactp-2**n)
   ;;            :cases ((= x (expt 2 (expo x)))))
   ;;           ("Subgoal 2" :use ((:instance expo-lower-bound))))))


   (local
    (defthm expt-2-minus-half
      (implies (integerp n)
               (equal (+ (EXPT 2 (+ 1 n))
                         (* -1 (EXPT 2 n)))
                      (expt 2 n)))
      :hints (("Goal"
               :use ((:instance a15
                                (i 2)
                                (j1 1)
                                (j2 n)))))))

  ;;; lots of stupid lemmas!!

   (local
    (defthm b-is-n-exact
      (implies (and (not (exactp x n))
                    (exactp x (1+ n))
                    (> x 0)
                    (rationalp x)
                    (integerp n)
                    (> n 0))
               (exactp (+ x (expt 2 (+ (expo x) (* -1 n)))) n))
      :hints (("Goal"
               :use ((:instance a-is-n-exact)
                     (:instance expo-lower-bound)
                     (:instance expt-strong-monotone-linear
                                (m (expo x))
                                (n (+ (expo x) (* -1 n))))
                     (:instance fp+1
                                (x (- x (expt 2 (+ (expo x) (* -1 n)))))))))))

  ;; (defthmd trunc-exactp-c
  ;;     (implies (and (exactp a n)
  ;; 		  (<= a x)
  ;;                   (rationalp x)
  ;; 		  (integerp n)
  ;; 		  (rationalp a))
  ;; 	     (<= a (trunc x n))))

   (local
    (defthm trunc-midpoint-lemma
      (implies (and (> n 0)
                    (integerp n)
                    (rationalp x) (> x 0)
                    (exactp x (1+ n))
                    (not (exactp x n)))
               (= (- x (expt 2 (- (expo x) n)))
                  (trunc x n)))
      :hints (("Goal" :in-theory (enable trunc-upper-pos)
               :cases ((< (- x (expt 2 (- (expo x) n))) (trunc x n))))
              ("Subgoal 2" :use ((:instance trunc-exactp-c
                                            (a (- x (expt 2 (- (expo x) n)))))))
              ("Subgoal 1" :use ((:instance fp+2
                                            (y (trunc x n))
                                            (x (- x (expt 2 (- (expo x) n)))))
                                 (:instance expo-lower-bound)
                                 (:instance expt-strong-monotone-linear
                                            (m (expo x))
                                            (n (+ (expo x) (* -1 n)))))))
      :rule-classes ()))

   ;; (defthmd sig-lower-bound
   ;;   (implies (and (rationalp x)
   ;;                 (not (equal x 0)))
   ;;            (<= 1 (sig x)))
   ;;   :rule-classes (:rewrite :linear))


   ;; (defthmd sig-upper-bound
   ;;   (< (sig x) 2)
   ;;   :rule-classes (:rewrite :linear))



   (local
    (defthm sig-x-integerp
      (implies (and (integerp (sig x))
                    (rationalp x)
                    (< 0 x))
               (equal (sig x) 1))
      :hints (("Goal" :in-theory (enable sig-lower-bound
                                         sig-upper-bound)))))



   ;;; The following are exported!!!
   ;;; Thu Oct 12 13:57:55 2006

   (defthm trunc-midpoint
     (implies (and (natp n)
                   (rationalp x) (> x 0)
                   (exactp x (1+ n))
                   (not (exactp x n)))
              (= (- x (expt 2 (- (expo x) n)))
                 (trunc x n)))
     :hints (("Goal" :cases ((equal n 0)))
             ("Subgoal 2" :use ((:instance trunc-midpoint-lemma)))
             ("Subgoal 1" :in-theory (enable exactp sgn trunc)
              :use ((:instance fp-rep (x x)))))
     :rule-classes ())


   (defthm expo-of-x-minus-extra-bit-is-expo-x
     (implies (and (exactp x (1+ n))
                   (not (exactp x n))
                   (rationalp x)
                   (integerp n)
                   (> x 0)
                   (> n 0))
              (equal (expo (+  x (* -1 (expt 2 (+ (expo x) (* -1 n))))))
                     (expo x))))



   (defthm a-is-n-exact
     (implies (and (not (exactp x n))
                   (exactp x (1+ n))
                   (> x 0)
                   (rationalp x)
                   (integerp n)
                   (> n 0))
              (exactp (+ x (* -1 (expt 2 (+ (expo x) (* -1 n)))))
                      n)))



   (defthm b-is-n-exact
     (implies (and (not (exactp x n))
                   (exactp x (1+ n))
                   (> x 0)
                   (rationalp x)
                   (integerp n)
                   (> n 0))
              (exactp (+ x (expt 2 (+ (expo x) (* -1 n))))
                      n)))


     )

;; TODO: consider move this to trunc.lisp and trunc-proofs.lisp
;; Thu Oct 12 09:28:40 2006


;----------------------------------------------------------------------

;; (defthmd trunc-trunc
;;     (implies (and (>= n m)
;;                   (integerp n)
;; 		  (integerp m))
;; 	     (equal (trunc (trunc x n) m)
;; 		    (trunc x m))))


;; (defthm plus-trunc
;;     (implies (and (rationalp x)
;; 		  (>= x 0)
;; 		  (rationalp y)
;; 		  (>= y 0)
;; 		  (integerp k)
;; 		  (exactp x (+ k (- (expo x) (expo y)))))
;; 	     (= (+ x (trunc y k))
;; 		(trunc (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
;;   :rule-classes ())

;----------------------------------------------------------------------

;;(i-am-here)
(encapsulate ()
  (local
   (defthm minus-trunc-1-lemma
     (implies (and (rationalp x)
                   (> x 0)
                  (rationalp y)
                  (> y 0)
                  (< x y)
                  (integerp k)
                  (> k 0)
                  (> (+ k (- (expo (- x y)) (expo y))) 0)
                  (= n (+ k (- (expo x) (expo y)))) ;; why we need "n"??
                  (exactp x (+ k (- (expo x) (expo y)))))
             (equal (- x (trunc y k))
                    (trunc (- x y) (+ k (- (expo (- x y)) (expo y))))))
    :hints (("Goal" :in-theory (enable trunc-rewrite exactp2 sgn a15)
             :use ((:instance fl+int-rewrite
                              (x (* Y (EXPT 2 (+ -1 K (* -1 (EXPO Y))))))
                              (n (* -1 X (EXPT 2 (+ -1 K (* -1 (EXPO Y))))))))))))


  (defthm minus-trunc-1
    (implies (and (rationalp x)
                  (> x 0)
                  (rationalp y)
                  (> y 0)
                  (< x y)
                  (integerp k)
                  (> k 0)
                  (> (+ k (- (expo (- x y)) (expo y))) 0)
                  (= n (+ k (- (expo x) (expo y)))) ;; why we need "n"??
                  (exactp x (+ k (- (expo x) (expo y)))))
             (equal (- x (trunc y k))
                    (- (trunc (- y x) (+ k (- (expo (- x y)) (expo y)))))))
    :hints (("Goal" :use ((:instance trunc-minus
                                     (x (- x y))
                                     (n (+ k (- (expo (- x y)) (expo y)))))
                          (:instance minus-trunc-1-lemma))))
    :rule-classes nil)


)

;----------------------------------------------------------------------

;; (defthm bits-trunc
;;   (implies (and (= n (1+ (expo x)))
;;                 (>= x 0)
;;                 (integerp k)
;;                 (> k 0))
;;            (= (trunc x k)
;;               (* (expt 2 (- n k))
;;                  (bits x (1- n) (- n k)))))
;;   :hints (("Goal" :use ((:instance bits-trunc-2---rtl-rel5-support))))
;;   :rule-classes ())


;; (defthm trunc-land
;;     (implies (and (>= x (expt 2 (1- n)))
;; 		  (< x (expt 2 n))
;;                   (integerp x) (> x 0)
;; 		  (integerp m) (>= m n)
;; 		  (integerp n) (> n k)
;; 		  (integerp k) (> k 0))
;; 	     (= (trunc x k)
;; 		(land x (- (expt 2 m) (expt 2 (- n k))) n)))
;;     :hints (("Goal" :use ((:instance bits-trunc-
;;   :rule-classes ())

;;
;; make change directly into rel5/lib/round.lisp, rel5/support/lextra.lisp
;;

;; (defthmd trunc-split
;;   (implies (and (= n (1+ (expo x)))
;;                 (>= x 0)
;;                 (integerp m)
;;                 (> m k)
;;                 (integerp k)
;;                 (> k 0))
;;            (equal (trunc x m)
;;                   (+ (trunc x k)
;;                      (* (expt 2 (- n m))
;;                         (bits x (1- (- n k)) (- n m)))))))


;;;**********************************************************************
;;;                    Rounding Away from Zero
;;;**********************************************************************


;; (defund away (x n)
;;   (* (sgn x)
;;      (cg (* (expt 2 (1- n)) (sig x)))
;;      (expt 2 (- (1+ (expo x)) n))))


(defthmd away-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n))
                )
           (integerp (away x n)))
  :hints (("Goal" :in-theory (enable away)))
  :rule-classes :type-prescription)

;; (defthmd away-rewrite
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (equal (away x n)
;; 		    (* (sgn x)
;; 		       (cg (* (expt 2 (- (1- n) (expo x))) (abs x)))
;; 		       (expt 2 (- (1+ (expo x)) n))))))


;; (defthmd abs-away
;;     (implies (and (rationalp x)
;; 		  (integerp n))
;; 	     (equal (abs (away x n))
;; 		    (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))))


;;; this is true??

;; ;; (local
;; ;;  (defthm fl-sig-is-minus-1
;; ;;    (implies (and (rationalp x)
;; ;;                  (not (equal x 0)))
;; ;;             (equal (FL (* -1/2 (SIG X)))
;; ;;                    -1))
;; ;;    :hints (("Goal"
;; ;;             :in-theory (enable fl-minus)
;; ;;             :use ((:instance sig-upper-bound)
;; ;;                   (:instance sig-lower-bound))))))



(encapsulate ()
   (local (include-book "../support/away"))
   (defthm away-to-0
     (implies (and (<= n 0)
                   (rationalp x)
                   (integerp n)
                   )
              (equal (away x n)
                  (* (sgn x) (expt 2 (+ 1 (expo x) (- n))))))
     :hints (("Goal" :by  away-to-0-or-fewer-bits))))




;;    (defthm away-to-0
;;      (implies (and (rationalp x) (not (= x 0)))
;;               (equal (away x 0)
;;                      (* (sgn x) (expt 2 (1+ (expo x))))))
;;
;; druss this is what you wrote in the  lemma



;; (defthmd sgn-away
;;   (equal (sgn (away x n))
;;          (sgn x)))

;; (defthm away-positive
;;   (implies (and (< 0 x)
;;                 (case-split (rationalp x))
;;                 )
;;            (< 0 (away x n)))
;;   :rule-classes (:rewrite :linear))

;; (defthm away-negative
;;     (implies (and (< x 0)
;;                   (case-split (rationalp x))
;;                   )
;; 	     (< (away x n) 0))
;;     :rule-classes (:rewrite :linear))

;; (defthm away-0
;;   (equal (away 0 n) 0))


;; (defthmd away-minus
;;   (= (away (* -1 x) n) (* -1 (away x n))))


;; (defthmd away-shift
;;     (implies (integerp n)
;; 	     (= (away (* x (expt 2 k)) n)
;; 		(* (away x n) (expt 2 k)))))


;; (defthmd away-lower-bound
;;     (implies (and (case-split (rationalp x))
;; 		  (case-split (integerp n)))
;; 	     (>= (abs (away x n)) (abs x)))
;;   :rule-classes :linear)

;; (defthmd away-lower-pos
;;     (implies (and (>= x 0)
;;                   (case-split (rationalp x))
;; 		  (case-split (integerp n)))
;; 	     (>= (away x n) x))
;;   :rule-classes :linear)


;; ;----------------------------------------------------------------------

(defthmd away-upper-bound
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (< (abs (away x n)) (+ (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use away-upper-1))
  :rule-classes :linear)

;; ;----------------------------------------------------------------------

;; (defthmd away-upper-2
;;     (implies (and (rationalp x)
;; 		  (not (= x 0))
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (< (abs (away x n)) (* (abs x) (+ 1 (expt 2 (- 1 n))))))
;;   :rule-classes :linear)


;; (defthmd away-diff
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (< (abs (- (away x n) x)) (expt 2 (- (1+ (expo x)) n))))
;;   :rule-classes :linear)

;; (defthmd away-diff-pos
;;     (implies (and (rationalp x)
;; 		  (>= x 0)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (< (- (away x n) x) (expt 2 (- (1+ (expo x)) n))))
;;   :rule-classes :linear)

;; ;; (defthm away-exactp-d
;; ;;     (implies (and (rationalp x)
;; ;; 		  (not (= x 0))
;; ;; 		  (integerp n)
;; ;; 		  (> n 0))
;; ;; 	     (<= (abs (away x n)) (expt 2 (1+ (expo x)))))
;; ;;   :rule-classes ())

(defthm away-expo-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (natp n))
	     (<= (abs (away x n)) (expt 2 (1+ (expo x)))))
    :hints (("Goal"
             :cases ((equal n 0)))
            ("Subgoal 2" :use ((:instance away-exactp-d)))
            ("Subgoal 1" :in-theory (enable abs away sgn natp)))
  :rule-classes ())
;; why not :linear?

;; (defthmd expo-away-lower-bound
;;     (implies (and (rationalp x)
;; 		  (natp n))
;; 	     (>= (expo (away x n)) (expo x)))
;;     :hints (("Goal" :cases ((equal n 0)))
;;             ("Subgoal 2" :use ((:instance
;;                                 expo-away-lower-bound---rtl-rel5-support)))
;;             ("Subgoal 1" :cases ((equal x 0))
;;              :in-theory (enable sgn))
;;             ("Subgoal 1.2" :use ((:instance expo-prod-lower
;;                                             (x (sgn x))
;;                                             (y (expt 2 (+ 1 (expo x))))))))
;;     :rule-classes (:linear))

;; included in round.lisp already.
;; Thu Oct 12 10:15:13 2006. Fixed (and (integerp n) (> n 0)) into (natp n)


(encapsulate ()
 (local
 (defthm away-x-zero-implies-zero
   (implies (rationalp x)
            (equal (equal (away x n) 0)
                   (equal x 0)))
   :hints (("Goal" :cases ((< 0 x)
                           (< x 0)
                           (equal x 0))))))

 (defthmd expo-away-upper-bound
    (implies (and (rationalp x)
		  (natp n))
	     (<= (expo (away x n)) (1+ (expo x))))
    :hints (("Goal" :in-theory (enable expo-monotone)
             :cases ((equal x 0)))
            ("Subgoal 2"
             :use ((:instance away-expo-upper)
                   (:instance expo-monotone
                              (x (away x n))
                              (y (expt 2 (+ 1 (expo x)))))
                   (:instance expo-monotone
                              (x (* -1 (away x n)))
                              (y (expt 2 (+ 1 (expo x))))))))
  :rule-classes :linear))

;;
;; TODO: refactor into away.lisp!!!
;; Thu Oct 12 10:17:09 2006


;; (defthm expo-away
;;     (implies (and (rationalp x)
;; 		  (natp n)
;; 		  (not (= (abs (away x n)) (expt 2 (1+ (expo x))))))
;; 	     (equal (expo (away x n))
;;                     (expo x)))
;;     :hints (("Goal" :cases ((equal x 0) (< x 0) (> x 0)))
;;             ("Subgoal 2" :in-theory (enable sgn)
;;              :use ((:instance expo-away---rtl-rel5-support)))
;;             ("Subgoal 1" :in-theory (enable sgn)
;;              :use ((:instance expo-away---rtl-rel5-support)))))


;; (defthm away-exactp-a
;;     (implies (case-split (< 0 n))
;; 	     (exactp (away x n) n))
;;     :hints (("Goal" :use ((:instance away-exactp-b---rtl-rel5-support)))))


;; (defthmd away-diff-expo
;;     (implies (and (rationalp x)
;; 		  (not (exactp x n))
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (<= (expo (- (away x n) x)) (- (expo x) n)))
;;   :rule-classes :linear)


;; (defthm away-exactp-b
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (iff (= x (away x n))
;; 		  (exactp x n)))
;;     :hints (("Goal" :use ((:instance away-exactp-a---rtl-rel5-support))))
;;   :rule-classes ())

;; (defthmd away-exactp-c
;;     (implies (and (exactp a n)
;; 		  (>= a x)
;;                   (rationalp x)
;; 		  (> x 0)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (rationalp a)
;; 		  )
;; 	     (>= a (away x n))))

;; (defthmd away-exactp-c
;;     (implies (and (exactp a n)
;; 		  (>= a x)
;;                   (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (rationalp a))
;; 	     (>= a (away x n))))


;; (defthmd away-monotone
;;     (implies (and (rationalp x)
;; 		  (rationalp y)
;; 		  (integerp n)
;; 		  (<= x y))
;; 	     (<= (away x n) (away y n)))
;;   :rule-classes :linear)


;; (defthm trunc-away
;;     (implies (and (rationalp x) (> x 0)
;; 		  (integerp n) (> n 0)
;; 		  (not (exactp x n)))
;; 	     (= (away x n)
;; 		(+ (trunc x n)
;; 		   (expt 2 (+ (expo x) 1 (- n))))))
;;   :rule-classes ())

;----------------------------------------------------------------------

(encapsulate ()

   (local
    (defthm local-expt-expand
      (implies (integerp n)
               (equal (EXPT 2 (+ 1 n))
                      (* 2 (expt 2 n))))
      :hints (("Goal" :use ((:instance a15
                                       (i 2)
                                       (j1 1)
                                       (j2 n)))))))

   (local
    (defthm away-midpoint-lemma
      (implies (and (> n 0)
                    (integerp n)
                    (rationalp x) (> x 0)
                    (exactp x (1+ n))
                    (not (exactp x n)))
               (= (+ x (expt 2 (- (expo x) n)))
                  (away x n)))
      :hints (("Goal" :in-theory (enable a15)
               :use ((:instance trunc-away)
                     (:instance trunc-midpoint)
                     (:instance local-expt-expand
                                (n (expt 2 (+ (expo x) (* -1 n))))))))
      :rule-classes ()))


   (local
    (defthm sig-x-integerp
      (implies (and (integerp (sig x))
                    (rationalp x)
                    (< 0 x))
               (equal (sig x) 1))
      :hints (("Goal" :in-theory (enable sig-lower-bound
                                         sig-upper-bound)))))

   (defthm away-midpoint
     (implies (and (natp n)
                   (rationalp x) (> x 0)
                   (exactp x (1+ n))
                   (not (exactp x n)))
               (= (away x n)
                  (+ x (expt 2 (- (expo x) n)))))
     :hints (("Goal" :cases ((equal n 0)))
             ("Subgoal 2" :use away-midpoint-lemma)
             ("Subgoal 1" :in-theory (enable exactp sgn)
              :use ((:instance fp-rep (x x)))))
      :rule-classes ())

)
;----------------------------------------------------------------------

;; (defthmd away-away
;;     (implies (and (rationalp x)
;; 		  (>= x 0)
;; 		  (integerp n)
;; 		  (integerp m)
;; 		  (> m 0)
;; 		  (>= n m))
;; 	     (equal (away (away x n) m)
;; 		    (away x m))))


;; (defthm plus-away
;;   (implies (and (exactp x (+ k (- (expo x) (expo y))))
;;                 (rationalp x)
;;                 (>= x 0)
;;                 (rationalp y)
;;                 (>= y 0)
;;                 (integerp k))
;;            (= (+ x (away y k))
;;               (away (+ x y)
;;                     (+ k (- (expo (+ x y)) (expo y))))))
;;   :rule-classes ())

;----------------------------------------------------------------------



;; (defthm minus-trunc-1
;;   (implies (and (rationalp x)
;;                 (> x 0)
;;                 (rationalp y)
;;                 (> y 0)
;;                 (< x y)
;;                 (integerp k)
;;                 (> k 0)
;;                 (> (+ k (- (expo (- x y)) (expo y))) 0)
;;                 (= n (+ k (- (expo x) (expo y)))) ;; why we need "n"??
;;                 (exactp x (+ k (- (expo x) (expo y)))))
;;            (equal (- x (trunc y k))
;;                   (- (trunc (- y x) (+ k (- (expo (- x y)) (expo y)))))))
;;   :hints (("Goal" :use ((:instance trunc-minus
;;                                    (x (- x y))
;;                                    (n (+ k (- (expo (- x y)) (expo y)))))
;;                         (:instance minus-trunc-1-lemma)))))


(defthm minus-trunc-2
  (implies (and (rationalp x)
                (> x 0)
                (rationalp y)
                (> y 0)
                (< y x)
                (integerp k)
                (> k 0)
                (> (+ k (- (expo (- x y)) (expo y))) 0)
                (= n (+ k (- (expo x) (expo y)))) ;; why we need "n"??
                (exactp x (+ k (- (expo x) (expo y)))))
           (equal (- x (trunc y k))
                  (away (- x y) (+ k (- (expo (- x y)) (expo y))))))
  :hints (("Goal" :in-theory (enable away-rewrite trunc-rewrite cg exactp2 sgn
                                     a15)))
  :rule-classes ())

;----------------------------------------------------------------------

(encapsulate ()

  (local
   (defthm trunc-minus-specific
     (equal (TRUNC (+ (* -1 X) (* -1 Y)) n)
            (* -1 (trunc (+ x y) n)))
     :hints (("Goal" :use ((:instance  trunc-minus
                                       (x (+ (* -1 x)
                                             (* -1 y)))))))))

  (local
   (defthm expo-minus-specific
     (equal (EXPO (+ (* -1 X) (* -1 Y)))
            (expo (+ x y)))
     :hints (("Goal" :use ((:instance  expo-minus
                                       (x (+ (* -1 x)
                                             (* -1 y)))))))))

  (local
   (defthm away-minus-specific
     (equal (away (+ (* -1 X) (* -1 Y)) n)
            (* -1 (away (+ x y) n)))
     :hints (("Goal" :use ((:instance  away-minus
                                       (x (+ (* -1 x)
                                             (* -1 y)))))))))


  (local
   (defthm trunc-plus-minus-lemmma
     (implies (and (rationalp x)
                   (rationalp y)
                   (> x 0)
                   (not (= y 0))
                   (not (= (+ x y) 0))
                   (integerp k)
                   (> k 0)
                   (= k1 (+ k (- (expo x) (expo y))))
                   (= k2 (+ k (expo (+ x y)) (* -1 (expo y))))
                   (exactp x k1)
                   (> k2 0))
              (equal (+ x (trunc y k))
                     (if (= (sgn (+ x y)) (sgn y))
                         (trunc (+ x y) k2)
                       (away (+ x y) k2))))
     :hints (("Goal" :cases ((< y 0))
              :in-theory (enable sgn trunc-minus away-minus expo-minus))
             ("Subgoal 2" :use ((:instance plus-trunc)))
             ("Subgoal 1" :cases ((< (* -1 y) x)))
             ("Subgoal 1.2" :use ((:instance minus-trunc-1
                                             (y (* -1 y))
                                             (n k1))))
             ("Subgoal 1.1" :use ((:instance minus-trunc-2
                                             (y (* -1 y))
                                             (n k1)))))))

  (defthm trunc-plus-minus
    (implies (and (rationalp x)
                  (rationalp y)
                  (not (= x 0))
                  (not (= y 0))
                  (not (= (+ x y) 0))
                  (integerp k)
                  (> k 0)
                  (= k1 (+ k (- (expo x) (expo y))))
                  (= k2 (+ k (expo (+ x y)) (* -1 (expo y))))
                  (exactp x k1)
                  (> k2 0))
             (equal (+ x (trunc y k))
                    (if (= (sgn (+ x y)) (sgn y))
                        (trunc (+ x y) k2)
                      (away (+ x y) k2))))
    :rule-classes ()
    :hints (("Goal" :cases ((not (< 0 x)))
             :in-theory (enable sgn trunc-minus away-minus expo-minus))
            ("Subgoal 2" :use ((:instance trunc-plus-minus-lemmma)))
            ("Subgoal 1" :use ((:instance trunc-plus-minus-lemmma
                                          (x (* -1 x))
                                          (y (* -1 y)))))))

)

;; (defthm away-imp
;;     (implies (and (rationalp x)
;; 		  (> x 0)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (integerp m)
;; 		  (>= m n)
;; 		  (exactp x m))
;; 	     (= (away x n)
;; 		(trunc (+ x
;; 			  (expt 2 (- (1+ (expo x)) n))
;; 			  (- (expt 2 (- (1+ (expo x)) m))))
;; 		       n)))
;;   :rule-classes ())

;;;**********************************************************************
;;;                    Unbiased Rounding
;;;**********************************************************************

;; (defun re (x)
;;   (- x (fl x)))


;; (defund near (x n)
;;   (let ((z (fl (* (expt 2 (1- n)) (sig x))))
;; 	(f (re (* (expt 2 (1- n)) (sig x)))))
;;     (if (< f 1/2)
;; 	(trunc x n)
;;       (if (> f 1/2)
;; 	  (away x n)
;; 	(if (evenp z)
;; 	    (trunc x n)
;; 	  (away x n))))))


;; (defthm near-choice
;;     (or (= (near x n) (trunc x n))
;; 	(= (near x n) (away x n)))
;;   :rule-classes ())


(defthmd sgn-near
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (near x n))
		    (sgn x)))
    :hints (("Goal" :in-theory (enable sgn-near-2))))

;; probably want to disable sgn-near in support/near.lisp
;; this is what originall is sgn-near-2 in the rel5

;; ;; (defthm near-pos
;; ;;     (implies (and (< 0 x)
;; ;;                   (< 0 n)
;; ;;                   (rationalp x)
;; ;; 		  (integerp n))
;; ;; 	     (< 0 (near x n)))
;; ;;   :rule-classes (:TYPE-PRESCRIPTION :LINEAR))

;; ;; (defthmd near-neg
;; ;;   (implies (and (< x 0)
;; ;;                 (< 0 n)
;; ;;                 (rationalp x)
;; ;;                 (integerp n)
;; ;; 		)
;; ;;            (< (near x n) 0))
;; ;;   :rule-classes (:TYPE-PRESCRIPTION :LINEAR))

;; ;; (defthm near-0
;; ;;   (equal (near 0 n)
;; ;;          0))


(defthm near-positive
    (implies (and (< 0 x)
                  (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (< 0 (near x n)))
    :hints (("Goal" :by near-pos))
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

(defthm near-0
   (equal (near 0 n)
          0))


;; (defthm near-exactp-a
;;     (implies (< 0 n)
;; 	     (exactp (near x n) n))
;;     :hints (("Goal" :use ((:instance near-exactp-b---rtl-rel5-support)))))


;; (defthm near-exactp-b
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (iff (= x (near x n))
;; 		  (exactp x n)))
;;     :hints (("Goal" :use ((:instance near-exactp-a---rtl-rel5-support))))
;;   :rule-classes ())


;; (encapsulate ()

;;  (local
;;   (defthmd near-minus
;;     (equal (near (* -1 x) n)
;;            (* -1 (near x n)))))

;;   (local
;;    (defthmd near-exactp-c-lemma
;;        (implies (and (exactp a n)
;;                      (> x 0)
;;    		  (>= a x)
;;                      (rationalp x)
;;    		  (integerp n)
;;    		  (> n 0)
;;    		  (rationalp a)
;;    		  )
;;    	     (>= a (near x n)))
;;        :hints (("Goal"
;;                 :use ((:instance near-exactp-c---rtl-rel5-support))))))

;;   (local
;;    (defthmd near-exactp-d-lemma
;;        (implies (and (rationalp x)
;;                      (> x 0)
;;    		  (integerp n)
;;    		  (> n 0)
;;    		  (rationalp a)
;;    		  (exactp a n)
;;    		  (<= a x))
;;    	     (<= a (near x n)))
;;        :hints (("Goal"
;;                 :use ((:instance near-exactp-d---rtl-rel5-support))))))


;;   (defthmd near-exactp-c
;;       (implies (and (exactp a n)
;;   		  (>= a x)
;;                     (rationalp x)
;;   		  (integerp n)
;;   		  (> n 0)
;;   		  (rationalp a)
;;   		  )
;;   	     (>= a (near x n)))
;;       :hints (("Goal" :cases ((< x 0))
;;                :in-theory (enable near-minus))
;;               ("Subgoal 2" :use ((:instance near-exactp-c-lemma)))
;;               ("Subgoal 1" :use ((:instance near-exactp-d-lemma
;;                                             (x (* -1 x))
;;                                             (a (* -1 a)))))))




;;   (defthmd near-exactp-d
;;       (implies (and (rationalp x)
;;   		  (integerp n)
;;   		  (> n 0)
;;   		  (rationalp a)
;;   		  (exactp a n)
;;   		  (<= a x))
;;   	     (<= a (near x n)))
;;       :hints (("Goal" :cases ((< x 0))
;;                :in-theory (enable near-minus))
;;               ("Subgoal 2" :use ((:instance near-exactp-d-lemma)))
;;               ("Subgoal 1" :use ((:instance near-exactp-c-lemma
;;                                             (x (* -1 x))
;;                                             (a (* -1 a)))))))

;; )



;; (defthm expo-trunc-strong
;;      (implies (and (natp n)
;;                    (rationalp x)
;;                    (not (= (abs (trunc x n)) (expt 2 (1+ (expo x))))))
;;  	     (equal (expo (trunc x n))
;;                     (expo x)))
;;      :hints (("Goal" :cases ((equal n 0)))))
;;              ("Subgoal 1" :in-theory (enable trunc-rewrite))))


(defthm expo-near
    (implies (and (rationalp x)
		  (> n 0)
                  (integerp n)
		  (not (= (abs (near x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (near x n))
                    (expo x)))
    :hints (("Goal" :cases ((equal (near x n) (trunc x n))))
            ("Subgoal 2"   :use ((:instance near-choice)
                                 (:instance expo-away))))
  :rule-classes ())


;; (defthm near<=away
;;     (implies (and (rationalp x)
;; 		  (> x 0)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (<= (near x n) (away x n)))
;;   :rule-classes ())


;; (defthm near>=trunc
;;     (implies (and (rationalp x)
;; 		  (> x 0)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (>= (near x n) (trunc x n)))
;;   :rule-classes ())


;; (defthmd near-shift
;;     (implies (and (rationalp x)
;;                   (integerp n)
;; 		  (integerp k))
;; 	     (= (near (* x (expt 2 k)) n)
;; 		(* (near x n) (expt 2 k)))))


;; (defthmd near-minus
;;   (equal (near (* -1 x) n)
;;          (* -1 (near x n))))



;----------------------------------------------------------------------

;; (encapsulate ()

;;      (local
;;      (defthm equal-diff-trunc-away-1
;;        (implies (and (exactp y n)
;;                      (rationalp x)
;;                      (> x 0)
;;                      (case-split (<= x y))
;;                      (rationalp y)
;;                      (equal (abs (- x (trunc x n))) (abs (- (away x n)
;;                                                             x)))
;;                      (integerp n)
;;                      (> n 0))
;;      	     (>= (abs (- x y)) (abs (- x (near x n)))))
;;        :hints (("Goal" :use ((:instance trunc-upper-pos)
;;                              (:instance near-choice)
;;                              (:instance away-lower-pos)
;;                              (:instance away-exactp-c
;;                                         (a y)))))))


;;      (local
;;      (defthm equal-diff-trunc-away-2
;;        (implies (and (exactp y n)
;;                      (rationalp x)
;;                      (> x 0)
;;                      (case-split (<= y x))
;;                      (rationalp y)
;;                      (equal (abs (- x (trunc x n))) (abs (- (away x n)
;;                                                             x)))
;;                      (integerp n)
;;                      (> n 0))
;;      	     (>= (abs (- x y)) (abs (- x (near x n)))))
;;        :hints (("Goal" :use ((:instance near-choice)
;;                              (:instance trunc-upper-pos)
;;                              (:instance away-lower-pos)
;;                              (:instance trunc-exactp-c
;;                                         (a y)))))))



;;      (local
;;      (defthm near2-lemma
;;          (implies (and (exactp y n)
;;                        (rationalp x)
;;                        (> x 0)
;;      		  (rationalp y)
;;                        (case-split (not (equal (abs (- x (trunc x n))) (abs (- (away x n)
;;                                                                                x)))))
;;      		  (integerp n)
;;      		  (> n 0))
;;      	     (>= (abs (- x y)) (abs (- x (near x n)))))
;;          :hints (("Goal" :cases ((not (> (abs (- x (trunc x n))) (abs (- (away x n)
;;                                                                          x))))))
;;                  ("Subgoal 2" :cases ((not (< x y))))
;;                  ("Subgoal 2.2" :use  ((:instance near1-b)
;;                                        (:instance trunc-upper-pos)
;;                                        (:instance away-lower-pos)
;;                                        (:instance away-exactp-c
;;                                                   (a y))))
;;                  ("Subgoal 2.1" :use  ((:instance near1-b)
;;                                        (:instance trunc-upper-pos)
;;                                        (:instance away-lower-pos)
;;                                        (:instance trunc-exactp-c
;;                                                   (a y))))
;;                  ("Subgoal 1" :cases ((not (< x y))))
;;                  ("Subgoal 1.2" :use  ((:instance near1-a)
;;                                        (:instance trunc-upper-pos)
;;                                        (:instance away-lower-pos)
;;                                        (:instance away-exactp-c
;;                                                   (a y))))
;;                  ("Subgoal 1.1" :use  ((:instance near1-a)
;;                                        (:instance trunc-upper-pos)
;;                                        (:instance away-lower-pos)
;;                                        (:instance trunc-exactp-c
;;                                                   (a y)))))))


;;      ;; (loca
;;      ;; (defthm exactp-equal-trunc-equal
;;      ;;   (implies (and (exactp x n)
;;      ;;                 (integerp n)
;;      ;;                 (rationalp x))
;;      ;;            (equal (trunc x n) x))
;;      ;;   :hints (("Goal" :in-theory (enable exactp trunc)
;;      ;;            :use ((:instance fp-rep)
;;      ;;                  (:instance a15
;;      ;;                             (i 2)
;;      ;;                             (j1 (+ -1 N))
;;      ;;                             (j2 (+ 1 (EXPO X) (* -1 N))))))))




;;      ;; (defthm exactp-equal-away-equal
;;      ;;   (implies (and (exactp x n)
;;      ;;                 (integerp n)
;;      ;;                 (rationalp x))
;;      ;;            (equal (away x n) x))
;;      ;;   :hints (("Goal" :in-theory (enable cg exactp away)
;;      ;;            :use ((:instance fp-rep)
;;      ;;                  (:instance a15
;;      ;;                             (i 2)
;;      ;;                             (j1 (+ -1 N))
;;      ;;                             (j2 (+ 1 (EXPO X) (* -1 N))))))))


;;      (local
;;      (defthm near2-lemma-futher
;;          (implies (and (exactp y n)
;;                        (rationalp x)
;;                        (> x 0)
;;      		  (rationalp y)
;;      		  (integerp n)
;;      		  (> n 0))
;;      	     (>= (abs (- x y)) (abs (- x (near x n)))))
;;          :hints (("Goal" :cases ((equal (abs (- x (trunc x n))) (abs (- (away x n)
;;                                                                                x)))))
;;                  ("Subgoal 2" :use ((:instance near2-lemma)))
;;                  ("Subgoal 1" :cases ((not (< x y))))
;;                  ("Subgoal 1.2" :use ((:instance equal-diff-trunc-away-1)))
;;                  ("Subgoal 1.1" :use ((:instance equal-diff-trunc-away-2))))))



;;      (defthm near2
;;          (implies (and (exactp y n)
;;                        (rationalp x)
;;      		  (rationalp y)
;;      		  (integerp n)
;;      		  (> n 0))
;;      	     (>= (abs (- x y)) (abs (- x (near x n)))))
;;          :hints (("Goal" :cases ((not (> x 0)))
;;                   :in-theory (enable near-minus trunc-minus away-minus
;;                                      exactp-minus))
;;                  ("Subgoal 2" :use ((:instance near2-lemma-futher)))
;;                  ("Subgoal 1" :use ((:instance near2-lemma-futher
;;                                                (x (* -1 x))
;;                                                (y (* -1 y)))))))
;; )

;; (defthm near-est
;;     (implies (and (integerp n)
;; 		  (> n 0)
;; 		  (rationalp x))
;; 	     (<= (abs (- x (near x n)))
;; 		 (expt 2 (- (expo x) n))))
;;     :hints (("Goal" :cases ((not (> x 0)))
;;              :in-theory (enable near-minus expo-minus))
;;             ("Subgoal 2" :use ((:instance near-est---rtl-rel5-support)))
;;             ("Subgoal 1" :use ((:instance near-est---rtl-rel5-support
;;                                           (x (* -1 x))))))
;;   :rule-classes ())



;; (encapsulate ()

;; (local
;;  (defthm fl-1/2-sig-x-is-zero-specific
;;    (implies (rationalp x)
;;             (equal (fl (* 1/2 (sig x)))
;;                    0))
;;    :hints (("Goal" :use ((:instance sig-upper-bound)
;;                          (:instance sig-lower-bound))))))


;; (defthm near-monotone
;;   (implies (and (<= x y)
;;                 (rationalp x)
;;                 (rationalp y)
;;                 (integerp n)
;;                 (natp n)
;;                 (> n 0))
;;            (<= (near x n) (near y n)))
;;   :hints (("Goal" :in-theory (enable near-minus)
;;            :cases ((not (equal x 0))))
;;           ("Subgoal 2" :use ((:instance near-negative
;;                                           (x (* -1 y)))))
;;           ("Subgoal 1" :cases ((not (> x 0))))
;;           ("Subgoal 1.2" :use ((:instance
;;                                 near-monotone---rtl-rel5-support)))
;;           ("Subgoal 1.1" :cases ((not (> y 0))))
;;           ("Subgoal 1.1.2" :use ((:instance near-positive (x y))
;;                                  (:instance near-positive (x (* -1 x)))))
;;           ("Subgoal 1.1.1" :use ((:instance near-monotone---rtl-rel5-support
;;                                             (x (* -1 y))
;;                                             (y (* -1 x)))
;;                                  (:instance near-positive (x (* -1 x)))))))

;; )


;;(i-am-here)

;; (defund near-witness (x y n)
;;   (if (= (expo x) (expo y))
;;       (/ (+ (near x n) (near y n)) 2)
;;     (expt 2 (expo y))))



;; (defthm near-near-lemma
;;     (implies (and (rationalp x)
;; 		  (rationalp y)
;; 		  (< 0 x)
;; 		  (< x y)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (not (= (near x n) (near y n))))
;; 	     (and (<= x (near-witness x y n))
;; 		  (<= (near-witness x y n) y)
;; 		  (exactp (near-witness x y n) (1+ n))))
;;   :rule-classes ())

;; (defthm near-near
;;     (implies (and (rationalp x)
;; 		  (rationalp y)
;; 		  (rationalp a)
;; 		  (integerp n)
;; 		  (integerp k)
;; 		  (> k 0)
;; 		  (>= n k)
;; 		  (< 0 a)
;; 		  (< a x)
;; 		  (< 0 y)
;; 		  (< y (fp+ a (1+ n)))
;; 		  (exactp a (1+ n)))
;; 	     (<= (near y k) (near x k)))
;;   :rule-classes ())


;----------------------------------------------------------------------

;;;
;;; either (near x n) < (near a n)
;;; or     (near a n) < (near y n)
;;;

;;(encapsulate ()
;----------------------------------------------------------------------

; i am here !!!

;;   (defthm a-is-n-exact
;;      (implies (and (not (exactp x n))
;;                    (exactp x (1+ n))
;;                    (> x 0)
;;                    (rationalp x)
;;                    (integerp n)
;;                    (> n 0))
;;               (exactp (+ x (* -1 (expt 2 (+ (expo x) (* -1 n)))))
;;                       n))
;;      :hints (("Goal" :in-theory (enable exactp2 a15)
;;               :use ((:instance integerp-x-not-1/2x-lemma
;;                                (x (* X (EXPT 2 (+ N (* -1 (EXPO X)))))))))))

;; >             (DEFTHM FP+2
;;                       (IMPLIES (AND (RATIONALP X)
;;                                     (> X 0)
;;                                     (RATIONALP Y)
;;                                     (> Y X)
;;                                     (INTEGERP N)
;;                                     (> N 0)
;;                                     (EXACTP X N)
;;                                     (EXACTP Y N))
;;                                (>= Y (FP+ X N)))
;;                       :RULE-CLASSES NIL)



(encapsulate ()
      (local (include-book "../../arithmetic/basic"))
      (local
      (defthm hack-artithm-1
        (implies (and (< 0 x)
                      (< x y)
                      (rationalp x)
                      (rationalp y)
                      (rationalp z)
                      (<= 1 z))
                 (< x (* z y)))))


      (local
      (defthm expo-a-less-than-specific
        (implies (and (integerp n)
                      (< 0 n)
                      (< 0 a)
                      (rationalp a))
                 (< (EXPT 2 (+ (EXPO A) (* -1 N))) a))
        :hints (("Goal" :in-theory (enable sgn)
                 :use ((:instance expt-strong-monotone-linear
                                  (n (+ (expo a) (* -1 n)))
                                  (m (expo a)))
                       (:instance fp-rep (x a))
                       (:instance sig-lower-bound (x a))
                       (:instance hack-artithm-1
                                  (x (expt 2 (+ (expo a) (* -1 n))))
                                  (y (expt 2 (expo a)))
                                  (z (sig a))))))
        :rule-classes :linear))

      (local
      (defthm abs-less-than-lemma
        (implies (and (equal (- a b) d)
                      (equal (- c a) d)
                      (> d 0)
                      (< 0 x)
                      (< x a)
                      (>= y c))
                 (< (abs (- b x))
                    (abs (- y x))))))


      ;; (defthm abs-less-than-lemma-2
      ;;   (implies (and (< x b)
      ;;                 (> y x)
      ;;                 (rationalp b)
      ;;                 (rationalp y)
      ;;                 (rationalp x))
      ;;            (< (abs (- b x))
      ;;               (abs (- y x)))))


      (local
       (defthm local-expt-2-expand
         (implies (and (rationalp x)
                       (integerp n))
                  (equal (EXPT 2 (+ 1 (EXPO X) (* -1 N)))
                         (* 2 (EXPT 2 (+ (expo x) (* -1 N))))))
         :hints (("Goal" :use ((:instance a15 (i 2) (j1 1) (j2 (+ (expo x)

                                                          (* -1 N)))))))))

      (local
      (defthm near-boundary-lemma-1-lemma
        (implies (and (rationalp x)
                      (rationalp a)
                      (< 0 x)
                      (< x a)
                      (< (+ a (* -1
                                     (expt 2 (+ (expo a)
                                                (* -1 n)))))
                         (near x n))
                      (integerp n)
                      (> n 0)
                      (exactp a (1+ n))
                      (not (exactp a n)))
                 (<  (abs (- (+ a (* -1
                                     (expt 2 (+ (expo a)
                                                (* -1 n)))))
                             x))
                     (abs (- (near x n) x))))
        :hints (("Goal" :in-theory (disable a-is-n-exact
                                            b-is-n-exact)
                :use ((:instance a-is-n-exact
                                 (x a))
                      (:instance fp+2
                                 (x (+ a (* -1
                                            (expt 2 (+ (expo a)
                                                       (* -1 n))))))
                                 (y (near x n)))
                      (:instance abs-less-than-lemma
                                 (a a)
                                 (b (+ a (* -1
                                            (expt 2 (+ (expo a)
                                                       (* -1 n))))))
                                 (c (+ a (expt 2 (+ (expo a)
                                                    (* -1 n)))))
                                 (d (expt 2 (+ (expo a) (* -1 n))))
                                 (y (near x n))
                                 (x x)))))))

      ;;      (defthm near2
      ;;          (implies (and (exactp y n)
      ;;                        (rationalp x)
      ;;      		  (rationalp y)
      ;;      		  (integerp n)
      ;;      		  (> n 0))
      ;;      	     (>= (abs (- x y)) (abs (- x (near x n)))))
      ;;          :hints (("Goal" :cases ((not (> x 0)))
      ;;                   :in-theory (enable near-minus trunc-minus away-minus
      ;;                                      exactp-minus))
      ;;                  ("Subgoal 2" :use ((:instance near2-lemma-futher)))
      ;;                  ("Subgoal 1" :use ((:instance near2-lemma-futher
      ;;                                                (x (* -1 x))
      ;;                                                (y (* -1 y)))))))

      (local
      (defthm near-boundary-lemma-1
        (implies (and (rationalp x)
                      (rationalp a)
                      (< 0 x)
                      (< x a)
                      (integerp n)
                      (> n 0)
                      (exactp a (1+ n))
                      (not (exactp a n)))
                 (<=  (near x n)
                      (+ a (* -1
                              (expt 2 (+ (expo a)
                                         (* -1 n)))))))
        :hints (("Goal" :in-theory (disable a-is-n-exact
                                            b-is-n-exact)
                :use
                ((:instance near-boundary-lemma-1-lemma)
                 (:instance a-is-n-exact (x a))
                 (:instance near2
                            (x x)
                            (y (+ a (* -1
                                       (expt 2 (+ (expo a)
                                                  (* -1 n))))))))))
        :rule-classes :linear))


      (local
      (defthm abs-less-than-lemma-2
        (implies (and (equal (- a b) d)
                      (equal (- c a) d)
                      (> d 0)
                      (< 0 a)
                      (< a y)
                      (<= near-y b)
                      (rationalp a)
                      (rationalp b)
                      (rationalp c)
                      (rationalp d)
                      (rationalp y)
                      (rationalp near-y))
                 (< (abs (- c y))
                    (abs (- near-y y))))
        :rule-classes nil))


      ;; (defthm fp-+
      ;;   (implies (and (rationalp x)
      ;;                 (> x 0)
      ;;                 (integerp n)
      ;;                 (> n 0)
      ;;                 (exactp x n))
      ;;            (equal (fp- (fp+ x n) n)
      ;;                   x)))

      (local
      (defthm near-boundary-lemma-2-lemma
        (implies (and (rationalp a)
                      (rationalp y)
                      (< 0 a)
                      (< a y)
                      (< (near y n)
                         (+ a (expt 2 (+ (expo a)
                                         (* -1 n)))))
                      (integerp n)
                      (> n 0)
                      (exactp a (1+ n))
                      (not (exactp a n)))
                 (<  (abs (- (+ a (expt 2 (+ (expo a)
                                             (* -1 n))))
                             y))
                     (abs (- (near y n) y))))
        :hints (("Goal" :in-theory (disable a-is-n-exact
                                            b-is-n-exact)
                :use ((:instance b-is-n-exact
                                 (x a))
                      (:instance a-is-n-exact
                                 (x a))
                      (:instance  fp-+
                                  (x (+ a (* -1 (expt 2 (+ (expo a)
                                                           (* -1 n))))))
                                  (n n))
                      (:instance fp-2
                                 (x (+ a (expt 2 (+ (expo a)
                                                    (* -1 n)))))
                                 (y (near y n)))
                      (:instance abs-less-than-lemma-2
                                 (a a)
                                 (b (- a (expt 2 (+ (expo a)
                                                    (* -1 n)))))
                                 (c (+ a (expt 2 (+ (expo a)
                                                    (* -1 n)))))
                                 (d (expt 2 (+ (expo a) (* -1 n))))
                                 (near-y (near y n))
                                 (y y)))))))

      (local
      (defthm near-boundary-lemma-2
        (implies (and (rationalp y)
                      (rationalp a)
                      (< 0 a)
                      (< a y)
                      (integerp n)
                      (> n 0)
                      (exactp a (1+ n))
                      (not (exactp a n)))
                 (<=  (+ a (expt 2 (+ (expo a)
                                      (* -1 n))))
                      (near y n)))
        :hints (("Goal" :in-theory (disable a-is-n-exact
                                            b-is-n-exact)
                :use
                ((:instance near-boundary-lemma-2-lemma)
                 (:instance b-is-n-exact (x a))
                 (:instance near2
                            (x y)
                            (y (+ a (expt 2 (+ (expo a)
                                               (* -1 n)))))))))
        :rule-classes :linear))



  (defthm near-boundary
      (implies (and (rationalp x)
  		  (rationalp y)
  		  (rationalp a)
  		  (< 0 x)
  		  (< x a)
  		  (< a y)
  		  (integerp n)
  		  (> n 0)
  		  (exactp a (1+ n))
  		  (not (exactp a n)))
  	     (< (near x n) (near y n)))
    :rule-classes ())

)

;; Thu Oct 12 17:22:29 2006. New.


;----------------------------------------------------------------------

;; (defthm near-exact
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 1)
;; 		  (exactp x (1+ n))
;; 		  (not (exactp x n)))
;; 	     (exactp (near x n) (1- n)))
;;     :hints (("Goal" :cases ((not (equal x 0)))
;;              :in-theory (enable near-minus))
;;             ("Subgoal 2" :in-theory (enable exactp))
;;             ("Subgoal 1" :cases  ((not (> x 0))))
;;             ("Subgoal 1.2" :use near-exact---rtl-rel5-support)
;;             ("Subgoal 1.1" :use ((:instance near-exact---rtl-rel5-support
;;                                             (x (* -1 x))))))
;;   :rule-classes ())


;; (defund near+ (x n)
;;   (if (< (re (* (expt 2 (1- n)) (sig x)))
;; 	 1/2)
;;       (trunc x n)
;;     (away x n)))


;; (defthm near+-choice
;;     (or (= (near+ x n) (trunc x n))
;; 	(= (near+ x n) (away x n)))
;;   :rule-classes ())


;; (defthm near+<=away
;;     (implies (and (rationalp x)
;; 		  (> x 0)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (<= (near+ x n) (away x n)))
;;   :rule-classes ())


;; (defthm near+>=trunc
;;     (implies (and (rationalp x)
;; 		  (> x 0)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (>= (near+ x n) (trunc x n)))
;;   :rule-classes ())


;; (defthmd near+-shift
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (integerp k))
;; 	     (= (near+ (* x (expt 2 k)) n)
;; 		(* (near+ x n) (expt 2 k)))))


;; (defthmd near+-minus
;;   (= (near+ (* -1 x) n) (* -1 (near+ x n))))

(defthm near+-positive
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (> (near+ x n) 0))
  :rule-classes :linear)

(defthm near+-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (near+ x n) 0))
  :rule-classes :linear)

;; (defthm near+-0
;;   (equal (near+ 0 n) 0))

;; (defthm near+-0-0
;;   (implies (and (case-split (< 0 n))
;;                 (case-split (rationalp x))
;;                 (case-split (integerp n)))
;;            (equal (equal (near+ x n) 0)
;; 		  (equal x 0)))
;;   :rule-classes ())

;; >             (DEFTHM SGN-NEAR+
;;                       (IMPLIES (AND (RATIONALP X) (INTEGERP N) (> N 0))
;;                                (= (NEAR+ X N)
;;                                   (* (SGN X) (NEAR+ (ABS X) N))))
;;                       :RULE-CLASSES NIL)

;; (defthm sgn-near+
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (equal (sgn (near+ x n))
;; 		    (sgn x)))
;;     :hints (("Goal" :use ((:instance sgn-near+---rtl-rel5-support)))))

;; (i-am-here) ;; Fri Oct 13 09:45:43 2006

;; (defthm near+-exactp-a
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (exactp (near+ x n) n))
;;     :hints (("Goal" :use ((:instance near+-exactp-b---rtl-rel5-support)))))


;; (defthm near+-exactp-b
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (iff (= x (near+ x n))
;; 		  (exactp x n)))
;;     :hints (("Goal" :use ((:instance near+-exactp-a---rtl-rel5-support))))
;;   :rule-classes ())


;;  (defthm near+-exactp-d
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (rationalp a)
;; 		  (exactp a n)
;; 		  (<= a x))
;; 	     (<= a (near+ x n)))
;;     :hints (("Goal" :cases ((not (equal x 0))))
;;             ("Subgoal 2" :in-theory (enable near+))
;;             ("Subgoal 1" :cases ((not (> x 0))))
;;             ("Subgoal 1.2" :use ((:instance near+-exactp-d---rtl-rel5-support)))
;;             ("Subgoal 1.1" :use ((:instance near+-exactp-c---rtl-rel5-support
;;                                             (x (* -1 x)) (a (* -1 a))))
;;              :in-theory (e/d (near+ trunc-minus away-minus fl-minus
;;                                     sig-minus) ()))))
;; )

;; ACL2 !>(expo (near+ (+ 1/4 1/8) 0))
;; -1
;; ACL2 !>(expo (+ 1/4 1/8))
;; -2

;;     :hints (("Goal" :cases ((equal (near x n) (trunc x n))))
;;             ("Subgoal 2"   :use ((:instance near-choice)
;
;                                  (:instance expo-away))))

;; (i-am-here) ;; Thu Oct 12 18:15:18 2006

(encapsulate ()
             (local
              (defthm fl-1/2-sig-x-is-zero-specific
                (implies (rationalp x)
                         (equal (fl (* 1/2 (sig x)))
                                0))
                :hints (("Goal" :use ((:instance sig-upper-bound)
                                      (:instance sig-lower-bound))))))

 (defthm expo-near+
   (implies (and (rationalp x)
                 (natp n)
                 (not (= (abs (near+ x n)) (expt 2 (1+ (expo x))))))
            (equal (expo (near+ x n))
                   (expo x)))
   :hints (("Goal" :in-theory (e/d (near+ sgn
                                          expo-trunc expo-away re
                                          sig-lower-bound)
                                   (trunc away))
            :cases ((equal (near+ x n) (trunc x n))))
           ("Subgoal 1" :cases ((equal n 0)))
           ("Subgoal 1.1" :cases ((not (equal x 0)))))
   :rule-classes ())
)

;----------------------------------------------------------------------

;;
;; (defthm near+1-a-1
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (< (abs (- x (trunc x n))) (abs (- (away x n) x))))
;; 	     (= (near+ x n) (trunc x n)))
;;     :hints (("Goal" :cases ((not (equal x 0)))
;;              :in-theory (enable trunc-minus near+-minus trunc-upper-pos
;;                                 away-lower-pos
;;                                 away-minus))
;;             ("Subgoal 1" :cases ((not (> x 0))))
;;             ("Subgoal 1.2" :use ((:instance near+1-a---rtl-rel5-support)))
;;             ("Subgoal 1.1" :use ((:instance near+1-a---rtl-rel5-support
;;                                             (x (* -1 x)))
;;                                  (:instance trunc-upper-pos
;;                                             (x (* -1 x)))
;;                                  (:instance away-lower-pos
;;                                             (x (* -1 x)))
;;                                  (:instance trunc-exactp-b)
;;                                  (:instance away-exactp-b))))
;;   :rule-classes ())


;; (defthm near+1-b-1
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (> (abs (- x (trunc x n))) (abs (- (away x n) x))))
;; 	     (= (near+ x n) (away x n)))
;;     :hints (("Goal" :cases ((not (equal x 0)))
;;              :in-theory (enable trunc-minus near+-minus trunc-upper-pos
;;                                 away-lower-pos
;;                                 away-minus))
;;             ("Subgoal 1" :cases ((not (> x 0))))
;;             ("Subgoal 1.2" :use ((:instance near+1-b---rtl-rel5-support)))
;;             ("Subgoal 1.1" :use ((:instance near+1-b---rtl-rel5-support
;;                                             (x (* -1 x)))
;;                                  (:instance trunc-upper-pos
;;                                             (x (* -1 x)))
;;                                  (:instance away-lower-pos
;;                                             (x (* -1 x)))
;;                                  (:instance trunc-exactp-b)
;;                                  (:instance away-exactp-b))))
;;   :rule-classes ())


;; (encapsulate ()
;;   (local
;;   (encapsulate ()
;;                (local
;;                 (defthm fl-1/2-sig-x-is-zero-lemma
;;                   (implies (and (rationalp x)
;;                                 (rationalp y)
;;                                 (< 0 y)
;;                                 (<= y 1/2))
;;                            (equal (fl (* (sig x) y))
;;                                   0))
;;                   :hints (("Goal" :use ((:instance sig-upper-bound)
;;                                         (:instance sig-lower-bound))))))


;;                (local
;;                 (defthm fl-1/2-sig-x-is-zero-lemma-2
;;                   (implies (and (rationalp x)
;;                                 (rationalp y)
;;                                 (not (equal x 0))
;;                                 (< 0 y)
;;                                 (<= y 1/2))
;;                            (equal (fl (* -1 (sig x) y))
;;                                   -1))
;;                   :hints (("Goal" :in-theory (enable sig fl-minus)
;;                            :use ((:instance fl-1/2-sig-x-is-zero-lemma))))))


;;                (local
;;                 (defthm expt-merge
;;                   (implies (and (rationalp x)
;;                                 (integerp n))
;;                            (equal (* (expt 2 (expo x))
;;                                      (EXPT 2 (+ -1 N))
;;                                      (EXPT 2 (* -1 (EXPO X))))
;;                                   (expt 2 (+ -1 n))))
;;                   :hints (("Goal" :in-theory (enable a15)))))

;;                (local (defthm expt-fact-1
;;                         (implies (and (integerp n)
;;                                       (<= n 0))
;;                                  (<= (* 2 (EXPT 2 (+ -1 N))) 1))
;;                         :hints (("Goal" :use ((:instance expt-weak-monotone-linear
;;                                                          (n (+ -1 n))
;;                                                          (m -1)))))
;;                         :rule-classes :linear))

;;                (local
;;                 (defthm fl-is-zero-if-n-less-than-minus-1
;;                   (implies (and (rationalp x)
;;                                 (> x 0)
;;                                 (integerp n)
;;                                 (<= n 0))
;;                            (equal (FL (* -1 X (EXPT 2 (+ -1 N))
;;                                          (EXPT 2 (* -1 (EXPO X)))))
;;                                   -1))
;;                   :hints (("Goal" :in-theory (e/d (expo-shift sgn)
;;                                                   (fl-1/2-sig-x-is-zero-lemma-2))
;;                            :use ((:instance fp-rep (x x))
;;                                  (:instance fl-1/2-sig-x-is-zero-lemma-2
;;                                             (y (expt 2 (+ -1 n)))))))))

;;                (local
;;                 (defthm fl-is-zero-if-n-less-than-zero
;;                   (implies (and (rationalp x)
;;                                 (> x 0)
;;                                 (integerp n)
;;                                 (<= n 0))
;;                            (equal (FL (* X (EXPT 2 (+ -1 N))
;;                                          (EXPT 2 (* -1 (EXPO X)))))
;;                                   0))
;;                   :hints (("Goal" :in-theory (e/d (expo-shift sgn)
;;                                                   (fl-1/2-sig-x-is-zero-lemma))
;;                            :use ((:instance fp-rep (x x))
;;                                  (:instance fl-1/2-sig-x-is-zero-lemma
;;                                             (y (expt 2 (+ -1 n)))))))))





;;                (local (defthm expt-fact-2
;;                         (implies (and (integerp n)
;;                                       (< n 0))
;;                                  (<= (* 4 (EXPT 2 (+ -1 N))) 1))
;;                         :hints (("Goal" :use ((:instance expt-weak-monotone-linear
;;                                                          (n (+ -1 n))
;;                                                          (m -2)))))
;;                         :rule-classes :linear))

;;                (local
;;                 (defthm arith-hack
;;                   (implies (and (< sig-x 2)
;;                                 (> y 0)
;;                                 (<= (* 4 y) 1)
;;                                 (rationalp y))
;;                            (< (* 2 sig-x y)
;;                               (* 1)))))



;;                (local
;;                 (defthm less-than-1-if-n-is-negative
;;                   (implies (and (rationalp x)
;;                                 (> x 0)
;;                                 (integerp n)
;;                                 (< n 0))
;;                            (< (* 2 X (EXPT 2 (+ -1 N))
;;                                  (EXPT 2 (* -1 (EXPO X))))
;;                               1))
;;                   :hints (("Goal" :in-theory (e/d (expo-shift  sgn) ())
;;                            :use ((:instance fp-rep (x x))
;;                                  (:instance sig-upper-bound)
;;                                  (:instance arith-hack
;;                                             (sig-x (sig x))
;;                                             (y (expt 2 (+ -1 n)))))))
;;                   :rule-classes :linear))

;;                (local
;;                 (encapsulate ()
;;                              (local
;;                               (defthm local-expt-expand
;;                                 (implies (rationalp x)
;;                                          (equal (EXPT 2 (+ 1 (EXPO X)))
;;                                                 (* 2 (expt 2 (expo x)))))
;;                                 :hints (("Goal" :use ((:instance a15 (i 2) (j1 1) (j2 (expo x))))))))

;;                              (defthm x-lower-bound
;;                                (implies (and (rationalp x)
;;                                              (> x 0))
;;                                         (>= (* 2 X) (EXPT 2 (+ 1 (EXPO X)))))
;;                                :hints (("Goal" :use ((:instance expo-lower-bound))))
;;                                :rule-classes :linear)))



;;      ;;;; these 4 are important!!!

;;                (defthm fl-is-zero-if-n-less-than-minus-1
;;                  (implies (and (rationalp x)
;;                                (> x 0)
;;                                (integerp n)
;;                                (<= n 0))
;;                           (equal (FL (* -1 X (EXPT 2 (+ -1 N))
;;                                         (EXPT 2 (* -1 (EXPO X)))))
;;                                  -1)))


;;                (defthm fl-is-zero-if-n-less-than-zero
;;                  (implies (and (rationalp x)
;;                                (> x 0)
;;                                (integerp n)
;;                                (<= n 0))
;;                           (equal (FL (* X (EXPT 2 (+ -1 N))
;;                                         (EXPT 2 (* -1 (EXPO X)))))
;;                                  0)))

;;                (defthm less-than-1-if-n-is-negative
;;                  (implies (and (rationalp x)
;;                                (> x 0)
;;                                (integerp n)
;;                                (< n 0))
;;                           (< (* 2 X (EXPT 2 (+ -1 N))
;;                                 (EXPT 2 (* -1 (EXPO X))))
;;                              1))
;;                  :rule-classes :linear)

;;                (defthm x-lower-bound
;;                  (implies (and (rationalp x)
;;                                (> x 0))
;;                           (>= (* 2 X) (EXPT 2 (+ 1 (EXPO X)))))
;;                  :rule-classes :linear)))

;;   (local
;;    (defthm near+1-a-2-2
;;      (implies (and (rationalp x)
;;                    (> x 0)
;;                    (integerp n)
;;                    (<= n 0)
;;                    (< (abs (- x (trunc x n))) (abs (- (away x n) x))))
;;               (= (near+ x n) (trunc x n)))
;;      :hints (("Goal" :in-theory (enable near+ sgn cg away trunc sig re)
;;               :cases ((equal n 0))))
;;      :rule-classes ()))



;;   (local (defthm x-upper-bound-1
;;          (implies (and (rationalp x)
;;                        (> x 0)
;;                        (integerp n)
;;                        (< n 0))
;;                   (> (EXPT 2 (+ 1 (EXPO X) (* -1 N))) X))
;;          :rule-classes :linear
;;          :hints (("Goal" :in-theory (enable expo-upper-bound)
;;                   :use ((:instance expt-strong-monotone-linear
;;                                    (n (+ 1 (expo x)))
;;                                    (m (+ 1 (expo x) (* -1 n)))))))))


;;   (local (defthm x-upper-bound-2
;;          (implies (and (rationalp x)
;;                        (> x 0)
;;                        (integerp n)
;;                        (< n 0))
;;                   (>= (EXPT 2 (+ 1 (EXPO X) (* -1 N))) (* 2 X)))
;;          :rule-classes :linear
;;          :hints (("Goal" :in-theory (enable expo-upper-bound)
;;                   :use ((:instance expt-weak-monotone-linear
;;                                    (n (+ 2 (expo x)))
;;                                    (m (+ 1 (expo x) (* -1 n))))
;;                         (:instance a15 (i 2)
;;                                    (j1 1) (j2 (+ 1 (expo x)))))))))


;;   (local (defthm x-upper-bound-3
;;          (implies (and (rationalp x)
;;                        (> x 0))
;;                   (> (EXPT 2 (+ 1 (EXPO X))) x))
;;          :rule-classes :linear
;;          :hints (("Goal" :in-theory (enable expo-upper-bound)))))






;; ;;      (defthm fl-is-zero-if-n-less-than-zero
;; ;;        (implies (and (rationalp x)
;; ;;                      (> x 0)
;; ;;                      (integerp n)
;; ;;                      (<= n 0))
;; ;;                 (equal (FL (* X (EXPT 2 (+ -1 N))
;; ;;                               (EXPT 2 (* -1 (EXPO X)))))
;; ;;                        0)))



;;   (local (defthm x-upper-bound-4
;;          (implies (and (rationalp x)
;;                        (> x 0))
;;                   (<= 1 (* X (EXPT 2 (* -1 (EXPO X))))))
;;          :rule-classes :linear
;;          :hints (("Goal" :use ((:instance fp-rep))
;;                   :in-theory (enable sgn a15 sig-lower-bound
;;                                      expo-shift)))))




;;   (local
;;      (defthm fl-is-zero-if-n-less-than-zero-2
;;        (implies (and (rationalp x)
;;                      (> x 0))
;;                 (equal (FL (* 1/2 X
;;                               (EXPT 2 (* -1 (EXPO X)))))
;;                        0))
;;        :hints (("Goal" :use ((:instance fl-is-zero-if-n-less-than-zero
;;                                         (n 0)))
;;                 :in-theory (disable fl-is-zero-if-n-less-than-zero)))))


;;   (local
;;    (defthm near+1-b-2-2
;;      (implies (and (rationalp x)
;;                    (> x 0)
;;                    (integerp n)
;;                    (<= n 0)
;;                    (> (abs (- x (trunc x n))) (abs (- (away x n) x))))
;;               (= (near+ x n) (away x n)))
;;      :hints (("Goal" :in-theory (enable away-lower-pos trunc-upper-pos
;;                                         near+ sgn cg away trunc sig re)
;;               :cases ((equal n 0))))
;;      :rule-classes ()))



;;   (defthm near+1-a-2
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;;                   (<= n 0)
;; 		  (< (abs (- x (trunc x n))) (abs (- (away x n) x))))
;; 	     (= (near+ x n) (trunc x n)))
;;     :hints (("Goal" :cases ((not (equal x 0)))
;;              :in-theory (enable  trunc-minus near+-minus trunc-upper-pos
;;                                  away-lower-pos
;;                                  away-minus))
;;             ("Subgoal 1" :cases ((not (> x 0))))
;;             ("Subgoal 1.2" :use ((:instance near+1-a-2-2)))
;;             ("Subgoal 1.1" :use ((:instance near+1-a-2-2
;;                                             (x (* -1 x))))))
;;     :rule-classes ())

;;   (defthm near+1-b-2
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;;                   (<= n 0)
;; 		  (> (abs (- x (trunc x n))) (abs (- (away x n) x))))
;; 	     (= (near+ x n) (away x n)))
;;     :hints (("Goal" :cases ((not (equal x 0)))
;;              :in-theory (enable  trunc-minus near+-minus trunc-upper-pos
;;                                  away-lower-pos
;;                                  away-minus))
;;             ("Subgoal 1" :cases ((not (> x 0))))
;;             ("Subgoal 1.2" :use ((:instance near+1-b-2-2)))
;;             ("Subgoal 1.1" :use ((:instance near+1-b-2-2
;;                                             (x (* -1 x))))))
;;     :rule-classes ()))





;; (defthm near+1-a
;;     (implies (and (rationalp x)
;; 		  (natp n)
;; 		  (< (abs (- x (trunc x n))) (abs (- (away x n) x))))
;; 	     (= (near+ x n) (trunc x n)))
;;     :hints (("Goal" :cases ((not (> n 0))))
;;             ("Subgoal 2" :use ((:instance near+1-a-1)))
;;             ("Subgoal 1" :use ((:instance near+1-a-2))))
;;   :rule-classes ())


;; (defthm near+1-b
;;     (implies (and (rationalp x)
;;                   (natp n)
;; 		  (> (abs (- x (trunc x n))) (abs (- (away x n) x))))
;; 	     (= (near+ x n) (away x n)))
;;     :hints (("Goal" :cases ((not (> n 0))))
;;             ("Subgoal 2" :use ((:instance near+1-b-1)))
;;             ("Subgoal 1" :use ((:instance near+1-b-2))))
;;   :rule-classes ())


;----------------------------------------------------------------------

;; (i-am-here) ;; Fri Oct 13 11:19:13 2006


;; (encapsulate ()

;;     (local
;;     (defthm equal-diff-trunc-away-1
;;       (implies (and (exactp y n)
;;                     (rationalp x)
;;                     (> x 0)
;;                     (case-split (<= x y))
;;                     (rationalp y)
;;                     (equal (abs (- x (trunc x n))) (abs (- (away x n)
;;                                                            x)))
;;                     (integerp n)
;;                     (> n 0))
;;     	     (>= (abs (- x y)) (abs (- x (near+ x n)))))
;;       :hints (("Goal" :use ((:instance trunc-upper-pos)
;;                             (:instance near+-choice)
;;                             (:instance away-lower-pos)
;;                             (:instance away-exactp-c
;;                                        (a y)))))))


;;     (local
;;     (defthm equal-diff-trunc-away-2
;;       (implies (and (exactp y n)
;;                     (rationalp x)
;;                     (> x 0)
;;                     (case-split (<= y x))
;;                     (rationalp y)
;;                     (equal (abs (- x (trunc x n))) (abs (- (away x n)
;;                                                            x)))
;;                     (integerp n)
;;                     (> n 0))
;;     	     (>= (abs (- x y)) (abs (- x (near+ x n)))))
;;       :hints (("Goal" :in-theory (disable NEAR+-EXACTP-D)
;;                :use ((:instance near+-choice)
;;                      (:instance trunc-upper-pos)
;;                      (:instance away-lower-pos)
;;                      (:instance trunc-exactp-c
;;                                 (a y)))))))



;;     (local
;;     (defthm near2+-lemma
;;         (implies (and (exactp y n)
;;                       (rationalp x)
;;                       (> x 0)
;;     		  (rationalp y)
;;                       (case-split (not (equal (abs (- x (trunc x n))) (abs (- (away x n)
;;                                                                               x)))))
;;     		  (integerp n)
;;     		  (> n 0))
;;     	     (>= (abs (- x y)) (abs (- x (near+ x n)))))
;;         :hints (("Goal" :cases ((not (> (abs (- x (trunc x n))) (abs (- (away x n)
;;                                                                         x)))))
;;                  :in-theory (disable near+-exactp-d))
;;                 ("Subgoal 2" :cases ((not (< x y))))
;;                 ("Subgoal 2.2" :use  ((:instance near+1-b)
;;                                       (:instance trunc-upper-pos)
;;                                       (:instance away-lower-pos)
;;                                       (:instance away-exactp-c
;;                                                  (a y))))
;;                 ("Subgoal 2.1" :use  ((:instance near+1-b)
;;                                       (:instance trunc-upper-pos)
;;                                       (:instance away-lower-pos)
;;                                       (:instance trunc-exactp-c
;;                                                  (a y))))
;;                 ("Subgoal 1" :cases ((not (< x y))))
;;                 ("Subgoal 1.2" :use  ((:instance near+1-a)
;;                                       (:instance trunc-upper-pos)
;;                                       (:instance away-lower-pos)
;;                                       (:instance away-exactp-c
;;                                                  (a y))))
;;                 ("Subgoal 1.1" :use  ((:instance near+1-a)
;;                                       (:instance trunc-upper-pos)
;;                                       (:instance away-lower-pos)
;;                                       (:instance trunc-exactp-c
;;                                                  (a y)))))))


;;     ;; (loca
;;     ;; (defthm exactp-equal-trunc-equal
;;     ;;   (implies (and (exactp x n)
;;     ;;                 (integerp n)
;;     ;;                 (rationalp x))
;;     ;;            (equal (trunc x n) x))
;;     ;;   :hints (("Goal" :in-theory (enable exactp trunc)
;;     ;;            :use ((:instance fp-rep)
;;     ;;                  (:instance a15
;;     ;;                             (i 2)
;;     ;;                             (j1 (+ -1 N))
;;     ;;                             (j2 (+ 1 (EXPO X) (* -1 N))))))))




;;     ;; (defthm exactp-equal-away-equal
;;     ;;   (implies (and (exactp x n)
;;     ;;                 (integerp n)
;;     ;;                 (rationalp x))
;;     ;;            (equal (away x n) x))
;;     ;;   :hints (("Goal" :in-theory (enable cg exactp away)
;;     ;;            :use ((:instance fp-rep)
;;     ;;                  (:instance a15
;;     ;;                             (i 2)
;;     ;;                             (j1 (+ -1 N))
;;     ;;                             (j2 (+ 1 (EXPO X) (* -1 N))))))))


;;     (local
;;     (defthm near2+-lemma-futher
;;         (implies (and (exactp y n)
;;                       (rationalp x)
;;                       (> x 0)
;;     		  (rationalp y)
;;     		  (integerp n)
;;     		  (> n 0))
;;     	     (>= (abs (- x y)) (abs (- x (near+ x n)))))
;;         :hints (("Goal" :cases ((equal (abs (- x (trunc x n))) (abs (- (away x n)
;;                                                                               x)))))
;;                 ("Subgoal 2" :use ((:instance near2+-lemma)))
;;                 ("Subgoal 1" :cases ((not (< x y))))
;;                 ("Subgoal 1.2" :use ((:instance equal-diff-trunc-away-1)))
;;                 ("Subgoal 1.1" :use ((:instance equal-diff-trunc-away-2))))))



;;     (defthm near+2
;;         (implies (and (exactp y n)
;;                       (rationalp x)
;;     		  (rationalp y)
;;     		  (integerp n)
;;     		  (> n 0))
;;     	     (>= (abs (- x y)) (abs (- x (near+ x n)))))
;;         :hints (("Goal" :cases ((not (> x 0)))
;;                  :in-theory (enable near+-minus trunc-minus away-minus
;;                                     exactp-minus))
;;                 ("Subgoal 2" :use ((:instance near2+-lemma-futher)))
;;                 ("Subgoal 1" :use ((:instance near2+-lemma-futher
;;                                               (x (* -1 x))
;;                                                    (y (* -1 y))))))
;;         :rule-classes ())
;;     )

;; (i-am-here) ;; Fri Oct 13 11:38:14 2006

;; (encapsulate ()
;;     (local
;;     (defthm fl-1/2-sig-x-is-zero-specific
;;       (implies (rationalp x)
;;                (equal (fl (* 1/2 (sig x)))
;;                       0))
;;       :hints (("Goal" :use ((:instance sig-upper-bound)
;;                             (:instance sig-lower-bound))))))


;;    (local
;;     (defthm near+-monotone-lemma1
;;       (implies (and (<= x y)
;;                     (rationalp x)
;;                     (rationalp y))
;;                (<= (near+ x 0) (near+ y 0)))
;;       :hints (("Goal" :in-theory (enable near+ sgn away-minus)
;;                :cases ((not (equal x 0))))
;;               ("Subgoal 2" :use ((:instance away-negative
;;                                             (x (* -1 y)) (n 0))))
;;               ("Subgoal 1" :cases ((not (> x 0))))
;;               ("Subgoal 1.2" :use ((:instance sig-lower-bound (x y))
;;                                    (:instance expt-weak-monotone-linear
;;                                               (n (+ 1 (expo x)))
;;                                               (m (+ 1 (expo y))))
;;                                    (:instance expo-monotone)))
;;               ("Subgoal 1.1" :cases ((not (> y 0)))
;;                :in-theory (enable away near+ sgn cg))
;;               ("Subgoal 1.1.1"
;;                :use ((:instance expt-weak-monotone-linear
;;                                 (n (+ 1 (expo y)))
;;                                 (m (+ 1 (expo x))))
;;                      (:instance expo-monotone
;;                                 (x y) (y x))
;;                      (:instance sig-lower-bound))))))


;;  (defthm near+-monotone
;;    (implies (and (<= x y)
;;                 (rationalp x)
;;                 (rationalp y)
;;                 (integerp n)
;;                 (natp n))
;;            (<= (near+ x n) (near+ y n)))
;;   :hints (("Goal" :cases ((not (equal n 0)))
;;            :in-theory (enable near+-minus))
;;           ("Subgoal 2" :use ((:instance near+-monotone-lemma1)))
;;           ("Subgoal 1" :cases ((not (equal x 0))))
;;           ("Subgoal 1.2" :use ((:instance near+-negative
;;                                           (x (* -1 y)))))
;;           ("Subgoal 1.1" :cases ((not (> x 0))))
;;           ("Subgoal 1.1.2" :use ((:instance
;;                                   near+-monotone---rtl-rel5-support)))
;;           ("Subgoal 1.1.1" :use ((:instance near+-monotone---rtl-rel5-support
;;                                             (x (* -1 y))
;;                                             (y (* -1 x)))))))

;; )

;----------------------------------------------------------------------

(encapsulate ()
  (local (include-book "../../arithmetic/top"))
  (local
   (defthm z-integerp-not-integer
     (implies (and (not (integerp x))
                   (rationalp x)
                   (integerp (* 2 x)))
              (equal (+ x (* -1 (fl x))) 1/2))))

  (local
     (defthm integerp-x-integerp-2*x
       (implies (and (integerp (* x (expt 2 n)))
                     (integerp n))
                (integerp (* 2 x (expt 2 (+ -1 n)))))
       :hints (("Goal"
                :use ((:instance a15
                                 (i 2)
                                 (j1 1)
                                 (j2 (+ -1 n))))))))

  (defthm near+-midpoint
      (implies (and (rationalp x)
  		  (integerp n)
  		  (exactp x (1+ n))
  		  (not (exactp x n)))
  	     (equal (near+ x n) (away x n)))
      :hints (("Goal" :in-theory (enable exactp near+)
               :use ((:instance z-integerp-not-integer
                                (x (* (sig x)
                                      (expt 2 (+ -1 n))))))))
    :rule-classes ())
)
;----------------------------------------------------------------------

;; (defthm near-power-a
;;     (implies (and (rationalp x) (> x 0)
;; 		  (integerp n) (> n 1)
;; 		  (>= (+ x (expt 2 (- (expo x) n)))
;; 		      (expt 2 (1+ (expo x)))))
;; 	     (= (near x n)
;; 		(expt 2 (1+ (expo x)))))
;;   :rule-classes ())


;; (defthm near-power-b
;;     (implies (and (rationalp x) (> x 0)
;; 		  (integerp n) (> n 1)
;; 		  (>= (+ x (expt 2 (- (expo x) n)))
;; 		      (expt 2 (1+ (expo x)))))
;; 	     (= (trunc (+ x (expt 2 (- (expo x) n))) n)
;; 		(expt 2 (1+ (expo x)))))
;;   :rule-classes ())


;; (defthm near+-power
;;     (implies (and (rationalp x) (> x 0)
;; 		  (integerp n) (> n 1)
;; 		  (>= (+ x (expt 2 (- (expo x) n)))
;; 		      (expt 2 (1+ (expo x)))))
;; 	     (= (near+ x n)
;; 		(expt 2 (1+ (expo x)))))
;;   :rule-classes ())


;----------------------------------------------------------------------

(encapsulate ()
  ;; referring to the folllowing
  ;;                            Fri Oct 13 12:05:54 2006
  ;; (defthm plus-trunc
  ;;     (implies (and (rationalp x)
  ;; 		  (>= x 0)
  ;; 		  (rationalp y)
  ;; 		  (>= y 0)
  ;; 		  (integerp k)
  ;; 		  (exactp x (+ k (- (expo x) (expo y)))))
  ;; 	     (= (+ x (trunc y k))
  ;; 		(trunc (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  ;;   :rule-classes ())



  ;; (defthm plus-away
  ;;   (implies (and (exactp x (+ k (- (expo x) (expo y))))
  ;;                 (rationalp x)
  ;;                 (>= x 0)
  ;;                 (rationalp y)
  ;;                 (>= y 0)
  ;;                 (integerp k))
  ;;            (= (+ x (away y k))
  ;;               (away (+ x y)
  ;;                     (+ k (- (expo (+ x y)) (expo y))))))
  ;;   :rule-classes ())

  ;; (local (include-book "../../arithmetic/top"))

  ;; Following the steps in Lemma 5.3.33. on
  ;; http://www.russinoff.com/libman/top.html

  (local
   (defun z (y k)
     (fl (* (sig y) (expt 2 (+ -1 k))))))

  (local
   (defun f (y k)
     (- (* (expt 2 (+ -1 k)) (sig y))  (z y k))))

  (local
   (defthm re-equal-if-f-equal
     (implies (equal (f y1 k1)
                     (f y2 k2))
              (equal (re (* (expt 2 (+ -1 k1)) (sig y1)))
                     (re (* (expt 2 (+ -1 k2)) (sig y2)))))
     :rule-classes nil))

  (local
  (defthm integerp-1/2-integerp
    (implies (and (integerp d)
                  (rationalp x))
             (iff (integerp (+ d x))
                  (integerp x)))))

  (local
  (defthm evenp-perserved-by-plus-even
    (implies (and (evenp d)
                  (integerp d)
                  (integerp x))
             (and (iff (evenp (+ x d))
                       (evenp x))
                  (iff (oddp (+ x d))
                       (oddp x))))))


  (local
   (defthm evenp-iff-difference
     (implies (and (evenp (- z1 z2))
                   (integerp z1)
                   (integerp z2))
              (iff (evenp z1)
                   (evenp z2)))
     :hints (("Goal" :use ((:instance evenp-perserved-by-plus-even
                                      (d (- z1 z2))
                                      (x z2)))))))


  (local
   (defthm evenp-iff-difference-specific
     (implies (evenp (+ (z y k) (* -1 (z (+ x y) (+ k (expo (+ x y)) (* -1 (expo y)))))))
              (iff (evenp (fl (* (sig (+ x y)) (expt 2 (+ -1 k  (* -1 (expo y)) (expo (+ x y)))))))
                   (evenp (fl (* (sig y) (expt 2 (+ -1 k)))))))
     :hints (("Goal" :in-theory (disable evenp EVENP-IFF-DIFFERENCE)
              :use ((:instance evenp-iff-difference
                                      (z1 (z y k))
                                      (z2 (z (+ x y) (+ k (expo (+ x y)) (* -1 (expo y)))))))))))


  (local
  (defthm near-plus-lemma-if-fl-equal
    (implies (and (exactp x (1- (+ k (- (expo x) (expo y)))))
                  (equal (f y k)
                         (f (+ x y) (+ k (expo (+ x y)) (* -1 (expo y)))))
                  (evenp (+ (z y k)
                            (* -1 (z (+ x y) (+ k (* -1 (expo y)) (expo (+ x y)))))))
                  (rationalp x)
                  (>= x 0)
                  (rationalp y)
                  (>= y 0)
                  (integerp k))
             (= (+ x (near y k))
                (near (+ x y)
                      (+ k (- (expo (+ x y)) (expo y))))))
    :hints (("Goal" :in-theory (e/d (near exactp-<=) (evenp z f re))
             :use ((:instance plus-trunc)
                   (:instance plus-away)
                   (:instance evenp-iff-difference-specific)
                   (:instance re-equal-if-f-equal
                              (y1 y) (k1 k)
                              (y2 (+ x y)) (k2 (+ k (- (expo (+ x y)) (expo y))))))))
    :rule-classes ()))

  ;; >             (DEFTHM FL+INT-REWRITE
  ;;                       (IMPLIES (AND (INTEGERP N) (RATIONALP X))
  ;;                                (EQUAL (FL (+ X N)) (+ (FL X) N))))

  (local
  (defthm f-equal-if-difference-integerp
    (implies (and (integerp (+ (* (sig y1) (expt 2 (+ -1 k1)))
                               (* -1 (sig y2) (expt 2 (+ -1 k2)))))
                  (rationalp y2))
             (equal (f y1 k1)
                    (f y2 k2)))
    :hints (("Goal"
             :use ((:instance fl+int-rewrite
                              (x (* (sig y2) (expt 2 (+ -1 k2))))
                              (n (+ (* (sig y1) (expt 2 (+ -1 k1)))
                                    (* -1 (sig y2) (expt 2 (+ -1 k2)))))))))
    :rule-classes nil))

  (local
  (defthm z-difference-evenp-evenp
    (implies (equal (f y1 k1)
                    (f y2 k2))
             (equal (+ (z y1 k1)
                       (* -1 (z y2 k2)))
                    (+ (* (sig y1) (expt 2 (+ -1 k1)))
                       (* -1 (sig y2) (expt 2 (+ -1 k2))))))
    :rule-classes nil))

  (local
  (defthm expo-normalize
    (implies (rationalp x)
             (equal (EXPO (* (SGN X)
                             (SIG X)
                             (EXPT 2 (EXPO X))))
                    (expo x)))
    :hints (("Goal" :use ((:instance fp-rep))))))

  (local
  (defthm sig-multiply-normalize
    (implies (and (rationalp x)
                  (>= x 0)
                  (integerp v)
                  (integerp w))
             (equal (* (sig x) (expt 2 (+ v w (expo x))))
                    (* x (expt 2 (+ v w)))))
    :hints (("Goal" :in-theory (enable sgn)
             :use ((:instance fp-rep (x x))
                          (:instance a15 (i 2)
                                     (j1 (expo x))
                                     (j2 (+ v w))))))
    :rule-classes nil))

  (local
  (defthm sig-y1-y2-equal
    (implies (and (rationalp y)
                  (>= x 0)
                  (>= y 0)
                  (integerp k)
                  (rationalp x))
             (equal (+ (* (sig (+ x y))
                          (expt 2 (+ -1 k (* -1 (expo y))
                                     (expo (+ x y)))))
                       (* -1 (sig y) (expt 2 (+ -1 k))))
                    (* x (expt 2 (+ -1 k (* -1 (expo y)))))))
    :hints (("Goal" :in-theory (enable sgn)
             :cases ((not (equal (* (sig (+ x y))
                                    (expt 2 (+ -1 k (* -1 (expo y))
                                               (expo (+ x y)))))
                                 (* (+ x y)
                                    (expt 2 (+ -1 k (* -1 (expo y)))))))
                     (not (equal (* (sig y)
                                    (expt 2 (+ -1 k)))
                                 (* y (expt 2 (+ -1 k (* -1 (expo y)))))))))
            ("Subgoal 2" :use ((:instance sig-multiply-normalize
                                          (x (+ x y))
                                          (v -1)
                                          (w (+ K (* -1 (EXPO Y)))))))
            ("Subgoal 1" :use ((:instance fp-rep (x y))
                               (:instance a15 (i 2) (j1 (expo y))
                                          (j2 (+ -1 K (* -1 (EXPO Y))))))))))



  (local
   (defthm local-expt-2-expand
     (implies (and (rationalp x)
                   (integerp k))
              (equal (EXPT 2 (+ -1 K (* -1 (EXPO Y))))
                     (* 2 (EXPT 2 (+ -2 K (* -1 (EXPO Y)))))))
     :hints (("Goal" :use ((:instance a15 (i 2) (j1 1)
                                      (j2 (+ -2 K (* -1 (EXPO Y))))))))))

  (local
  (defthm integerp-x-expt-k
    (implies (and (exactp x (1- (+ k (- (expo x) (expo y)))))
                  (rationalp x)
                  (integerp k))
             (integerp (* x (expt 2 (+ -1 k (* -1 (expo y)))))))
    :hints (("Goal" :use ((:instance exactp2 (x x)
                                     (n (1- (+ k (- (expo x) (expo y)))))))))))


  (local
  (defthm evenp-x-expt-k
    (implies (and (exactp x (1- (+ k (- (expo x) (expo y)))))
                  (rationalp x)
                  (integerp k))
             (evenp (* x (expt 2 (+ -1 k (* -1 (expo y)))))))
    :hints (("Goal" :use ((:instance exactp2 (x x)
                                     (n (1- (+ k (- (expo x) (expo y)))))))))))

  (local
   (defthm integerp-minus
     (implies (acl2-numberp x)
              (iff (integerp (* -1 x))
                   (integerp x)))
     :hints (("Goal" :in-theory (disable a2)
              :cases ((equal (* -1 x) (- x)))))))


  (local
   (defthm even-minus
     (implies (acl2-numberp x)
              (iff (evenp (* -1 x))
                   (evenp x)))
     :hints (("Goal" :in-theory (disable a2 a5)
              :cases ((equal (* -1 x) (- x)))))))

  (defthm near-plus
    (implies (and (exactp x (1- (+ k (- (expo x) (expo y)))))
                  (rationalp x)
                  (>= x 0)
                  (rationalp y)
                  (>= y 0)
                  (integerp k))
             (= (+ x (near y k))
                (near (+ x y)
                      (+ k (- (expo (+ x y)) (expo y))))))
    :hints (("Goal" :in-theory (disable evenp z f
                                        evenp-x-expt-k
                                        integerp-x-expt-k
                                        LOCAL-EXPT-2-EXPAND
                                        SIG-Y1-Y2-EQUAL near)
             :use ((:instance near-plus-lemma-if-fl-equal)
                   (:instance f-equal-if-difference-integerp
                              (k1 k) (k2 (+ k (expo (+ x y)) (* -1 (expo y))))
                              (y1 y) (y2 (+ x y)))
                   (:instance z-difference-evenp-evenp
                              (k1 k) (k2 (+ k (expo (+ x y)) (* -1 (expo y))))
                              (y1 y) (y2 (+ x y)))
                   (:instance sig-y1-y2-equal)
                   (:instance integerp-x-expt-k)
                   (:instance evenp-x-expt-k))))
    :rule-classes ())




  (local
    (defthm near+-plus-lemma-if-fl-equal
      (implies (and (exactp x (+ k (- (expo x) (expo y))))
                    (equal (f y k)
                           (f (+ x y) (+ k (expo (+ x y)) (* -1 (expo y)))))
                    (rationalp x)
                    (>= x 0)
                    (rationalp y)
                    (>= y 0)
                    (integerp k))
               (= (+ x (near+ y k))
                  (near+ (+ x y)
                         (+ k (- (expo (+ x y)) (expo y))))))
      :hints (("Goal" :in-theory (e/d (near+ exactp-<=) (evenp z f re))
               :use ((:instance plus-trunc)
                     (:instance plus-away)
                     (:instance re-equal-if-f-equal
                                (y1 y) (k1 k)
                                (y2 (+ x y)) (k2 (+ k (- (expo (+ x y)) (expo y))))))))
      :rule-classes ()))



  (local
    (defthm integerp-x-expt-k-2
      (implies (and (exactp x (+ k (- (expo x) (expo y))))
                    (rationalp x)
                    (integerp k))
               (integerp (* x (expt 2 (+ -1 k (* -1 (expo y)))))))
      :hints (("Goal" :use ((:instance exactp2 (x x)
                                       (n (+ k (- (expo x) (expo y))))))))))


  (defthm near+-plus
    (implies (and (exactp x (+ k (- (expo x) (expo y))))
                  (rationalp x)
                  (>= x 0)
                  (rationalp y)
                  (>= y 0)
                  (integerp k))
             (= (+ x (near+ y k))
                (near+ (+ x y)
                       (+ k (- (expo (+ x y)) (expo y))))))
    :hints (("Goal" :in-theory (disable evenp z f
                                        integerp-x-expt-k-2
                                        LOCAL-EXPT-2-EXPAND
                                        SIG-Y1-Y2-EQUAL near+)
             :use ((:instance near+-plus-lemma-if-fl-equal)
                          (:instance f-equal-if-difference-integerp
                                     (k1 k) (k2 (+ k (expo (+ x y)) (* -1 (expo y))))
                                     (y1 y) (y2 (+ x y)))
                          (:instance sig-y1-y2-equal)
                          (:instance integerp-x-expt-k-2))))
    :rule-classes ())
)


;----------------------------------------------------------------------

;----------------------------------------------------------------------

;; (defthm near-trunc
;;     (implies (and (rationalp x) (> x 0)
;; 		  (integerp n) (> n 1))
;; 	     (= (near x n)
;; 		(if (and (exactp x (1+ n)) (not (exactp x n)))
;; 		    (trunc (+ x (expt 2 (- (expo x) n))) (1- n))
;; 		  (trunc (+ x (expt 2 (- (expo x) n))) n))))
;;   :rule-classes ())


;; (defthm near+trunc
;;     (implies (and (rationalp x)
;; 		  (> x 0)
;; 		  (integerp n)
;; 		  (> n 0))
;; 	     (= (near+ x n)
;; 		(trunc (+ x (expt 2 (- (expo x) n))) n)))
;;   :rule-classes ())

;----------------------------------------------------------------------

(encapsulate ()
    ;; (defthm fp+2
    ;;     (implies (and (rationalp x)
    ;; 		  (> x 0)
    ;; 		  (rationalp y)
    ;; 		  (> y x)
    ;; 		  (integerp n)
    ;; 		  (> n 0)
    ;; 		  (exactp x n)
    ;; 		  (exactp y n))
    ;; 	     (>= y (fp+ x n)))
    ;;   :rule-classes ())


    (local (include-book "../../arithmetic/expt"))
    ;; we just want expt-weak-monotone-linear

    (local
     (defun y (x m)
       (+ (trunc x (+ 1 m))
          (expt 2 (+ (* -1 m) (expo x))))))




    ;; (local
    ;;  (defun y (x m)
    ;;    (+ (trunc x (+ 1 m))
    ;;       (expt 2 (+ -1 (* -1 m) (expo x))))))



    ;; (defthm expo-trunc
    ;;     (implies (and (< 0 n)
    ;;                   (rationalp x)
    ;; 		  (integerp n))
    ;; 	     (equal (expo (trunc x n))
    ;;                     (expo x))))


    (local
     (defthm expt-2-less-than-specific
       (implies (and (rationalp x)
                     (> x 0)
                     (integerp m)
                     (> m 0))
                (<= (expt 2 (+ (expo x) (* -1 M)))
                    (EXPT 2
                          (+ (* -1 M)
                             (EXPO (+ (TRUNC X (+ 1 M))
                                      (EXPT 2 (+ (EXPO X) (* -1 M)))))))))
       :hints (("Goal" :use ((:instance trunc-lower-bound
                                        (x x) (n (+ 1 m)))
                             (:instance expo-monotone
                                        (x (trunc x (+ 1 m)))
                                        (y (+ (trunc x (+ 1 m))
                                              (EXPT 2 (+ (EXPO X) (* -1 M))))))
                             (:instance expt-weak-monotone-linear
                                        (n (+ (EXPO X) (* -1 M)))
                                        (m (+ (* -1 M)
                                              (EXPO (+ (TRUNC X (+ 1 M))
                                                       (EXPT 2 (+ (EXPO X) (* -1 M)))))))))))
       :rule-classes :linear))



    ;; (local
    ;;  (defthm expt-2-less-than-specific
    ;;    (implies (and (rationalp x)
    ;;                  (> x 0)
    ;;                  (integerp m)
    ;;                  (> m 0))
    ;;             (<= (expt 2 (+ (expo x) (* -1 M)))
    ;;                 (EXPT 2
    ;;                       (+ (* -1 M)
    ;;                          (EXPO (+ (TRUNC X (+ 1 M))
    ;;                                   (EXPT 2 (+ -1 (EXPO X) (* -1 M)))))))))
    ;;    :hints (("Goal" :use ((:instance trunc-lower-bound
    ;;                                     (x x) (n (+ 1 m)))
    ;;                          (:instance expo-monotone
    ;;                                     (x (trunc x (+ 1 m)))
    ;;                                     (y (+ (trunc x (+ 1 m))
    ;;                                           (EXPT 2 (+ -1 (EXPO X) (* -1 M))))))
    ;;                          (:instance expt-weak-monotone-linear
    ;;                                     (n (+ (EXPO X) (* -1 M)))
    ;;                                     (m (+ (* -1 M)
    ;;                                           (EXPO (+ (TRUNC X (+ 1 M))
    ;;                                                    (EXPT 2 (+ -1 (EXPO X) (* -1 M)))))))))))
    ;;    :rule-classes :linear))

    (local
     (defthm trunc-less-than
       (implies (and (rationalp x)
                     (> x 0)
                     (integerp m))
                (< (trunc (+ x (expt 2 (+ (* -1 m) (expo x)))) m)
                   (fp+ (y x m) (+ 1 m))))
       :hints (("Goal" :use ((:instance trunc-upper-pos
                                        (x (+ x (expt 2 (+ (* -1 m) (expo x)))))
                                        (n m))
                             (:instance trunc-lower-bound
                                        (x x)
                                        (n (+ 1 m)))
                             (:instance expt-2-less-than-specific))))))




    ;; (local
    ;;  (defthm trunc-less-than
    ;;    (implies (and (rationalp x)
    ;;                  (> x 0)
    ;;                  (integerp m))
    ;;             (< (trunc (+ x (expt 2 (+ (* -1 m) (expo x)))) m)
    ;;                (fp+ (y x m) (+ 1 m))))
    ;;    :hints (("Goal" :use ((:instance trunc-upper-pos
    ;;                                     (x (+ x (expt 2 (+ (* -1 m) (expo x)))))
    ;;                                     (n m))
    ;;                          (:instance trunc-lower-bound
    ;;                                     (x x)
    ;;                                     (n (+ 1 m)))
    ;;                          (:instance expt-2-less-than-specific))))))



    (local
     (defthm exactp-fact
       (implies (and (rationalp x)
                     (integerp m)
                     (> m 0))
                (EXACTP (TRUNC (+ X (EXPT 2 (+ (EXPO X) (* -1 M))))
                               M)
                        (+ 1 M)))
       :hints (("Goal" :in-theory (enable trunc-exactp-a)
                :use ((:instance exactp-<=
                                 (m m)
                                 (x (TRUNC (+ X (EXPT 2 (+ (EXPO X) (* -1 M))))
                                           M))
                                 (n (+ 1 m))))))))



    (local
     (defthm exactp-fact-1
       (implies (and (rationalp x)
                     (integerp m)
                     (> m 0))
                (EXACTP (TRUNC (+ X (EXPT 2 (+ (EXPO X) (* -1 M))))
                               M)
                        M))
       :hints (("Goal" :in-theory (enable trunc-exactp-a)
                :use ((:instance exactp-<=
                                 (m m)
                                 (x (TRUNC (+ X (EXPT 2 (+ (EXPO X) (* -1 M))))
                                           M))
                                 (n (+ 1 m))))))))



    (local
     (defthm exactp-fact-2
          (implies (and (rationalp x)
                        (> x 0)
                        (integerp m)
                        (> m 0))
                   (EXACTP (+ (TRUNC X (+ 1 M))
                              (EXPT 2 (+ (EXPO X) (* -1 M))))
                           (+ 1 M)))
          :hints (("Goal" :use ((:instance fp+1
                                           (x (TRUNC X (+ 1 M)))
                                           (n (+ 1 m))))))))




    (local
     (defthm trunc-m+1-plus-is-trunc-plus-C-lemma
       (implies (and (integerp m)
                     (rationalp x)
                     (> x 0)
                     (> m 0))
                (>= (y x m)
                    (trunc (+ x (expt 2 (+ (* -1 m) (expo x)))) m)))
       :hints (("Goal" :in-theory (disable fp+)
                :use ((:instance fp+2
                                 (y (trunc (+ x (expt 2 (+ (* -1 m) (expo x)))) m))
                                 (x (y x m))
                                 (n (+ 1 m)))
                      (:instance trunc-less-than))))))



    ;; (local
    ;;  (defun y (x m)
    ;;    (+ (trunc x (+ 1 m))
    ;;       (expt 2 (+ (* -1 m) (expo x))))))




    (local
     (defthm trunc-m+1-plus-is-trunc-plus-C
       (implies (and (integerp m)
                     (rationalp x)
                     (> x 0)
                     (> m 0))
                (= (trunc (y x m) m)
                   (trunc (+ x (expt 2 (+ (* -1 m) (expo x)))) m)))
       :hints (("Goal" :in-theory (disable fp+)
                :use ((:instance trunc-m+1-plus-is-trunc-plus-C-lemma)
                      (:instance trunc-exactp-c
                                 (a (trunc (+ x (expt 2 (+ (* -1 m) (expo x)))) m))
                                 (x (y x m))
                                 (n m))
                      (:instance trunc-monotone
                                 (x (y x m))
                                 (y (+ x (expt 2 (+ (* -1 m) (expo x)))))
                                 (n m))
                      (:instance trunc-upper-pos
                                 (x x)
                                 (n (+ 1 m))))))
       :rule-classes nil))

    ;; (defthm near+trunc
    ;;     (implies (and (rationalp x)
    ;; 		  (> x 0)
    ;; 		  (integerp n)
    ;; 		  (> n 0))
    ;; 	     (= (near+ x n)
    ;; 		(trunc (+ x (expt 2 (- (expo x) n))) n)))
    ;;   :rule-classes ())

    (local
    (defthm near+-trunc-cor-lemma
        (implies (and (rationalp x)
                      (> x 0)
    		  (integerp m)
    		  (> m 0))
    	     (= (near+ (trunc x (+ 1 m)) m)
    		(near+ x m)))
        :hints (("Goal" :in-theory (enable trunc-trunc)
                 :use ((:instance near+trunc
                                  (x (trunc x (+ 1 m)))
                                  (n m))
                       (:instance near+trunc
                                  (x x)
                                  (n m))
                       (:instance trunc-m+1-plus-is-trunc-plus-C))))
      :rule-classes ()))

    (local
    (defthm near+-trunc-cor-lemma-2
        (implies (and (rationalp x)
    		  (integerp m)
    		  (> m 0))
    	     (= (near+ (trunc x (+ 1 m)) m)
    		(near+ x m)))
        :hints (("Goal" :cases ((not (equal x 0)))
                 :in-theory (enable trunc-minus near+-minus))
                ("Subgoal 1" :cases ((not (> x 0))))
                ("Subgoal 1.2" :use ((:instance near+-trunc-cor-lemma)))
                ("Subgoal 1.1" :use ((:instance near+-trunc-cor-lemma
                                                (x (* -1 x))))))
      :rule-classes ()))


    (defthm near+-trunc-cor
        (implies (and (rationalp x)
                      (integerp m)
                      (integerp n)
                      (> n m)
    		  (> m 0))
    	     (= (near+ (trunc x n) m)
    		(near+ x m)))
        :hints (("Goal" :cases ((not (> n (+ 1 m)))))
                ("Subgoal 2" :use ((:instance near+-trunc-cor-lemma-2
                                              (x (trunc x n))
                                              (m m))
                                   (:instance near+-trunc-cor-lemma-2
                                              (x x)
                                              (m m))
                                   (:instance trunc-trunc
                                              (x x)
                                              (n n)
                                              (m (+ 1 m)))))
                ("Subgoal 1" :use ((:instance near+-trunc-cor-lemma-2))))
      :rule-classes ())

)

;----------------------------------------------------------------------

;;;**********************************************************************
;;;                          Sticky Rounding
;;;**********************************************************************


;; (defund sticky (x n)
;;   (cond ((exactp x (1- n)) x)
;; 	(t (+ (trunc x (1- n))
;;               (* (sgn x) (expt 2 (1+ (- (expo x) n))))))))


;; (i-am-here)

(local
 (defthm sgn-x-plus-y
   (implies (and (equal (sgn x) (sgn y))
                 (rationalp x)
                 (rationalp y))
            (equal (sgn (+ x y))
                   (sgn x)))
   :hints (("Goal" :in-theory (enable sgn)))))

(local
 (defthm sgn-sgn-id
   (equal (sgn (sgn x))
          (sgn x))
   :hints (("Goal" :in-theory (enable sgn)))))

(local
 (defthm sgn-expt-1
   (equal (SGN (EXPT 2 n))
          1)
   :hints (("Goal" :in-theory (enable sgn)))))

(defthm sgn-sticky
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (sticky x n))
		    (sgn x)))
    :hints (("Goal" :in-theory (enable sticky
                                       sgn-trunc
                                       sgn-prod)
             :cases ((not (> n 1))))
            ("Subgoal 2"
             :use ((:instance sgn-x-plus-y
                              (x (trunc x (+ -1 n)))
                              (y (* (SGN X)
                                    (EXPT 2 (+ 1 (EXPO X) (* -1 N))))))))))

(local
 (defthm positive-sgn-1
   (implies (rationalp x)
            (iff (equal (sgn x) 1)
                 (> x 0)))
   :hints (("Goal" :in-theory (enable sgn)))))


(defthmd sticky-positive
    (implies (and (< 0 x)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (> (sticky x n) 0))
    :hints (("Goal" :use ((:instance sgn-sticky)
                          (:instance positive-sgn-1
                                     (x x))
                          (:instance positive-sgn-1
                                     (x (sticky x n))))))
  :rule-classes :linear)

(local
 (defthm positive-sgn-2
   (implies (rationalp x)
            (iff (equal (sgn x) -1)
                 (< x 0)))
   :hints (("Goal" :in-theory (enable sgn)))))


(defthmd sticky-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (< (sticky x n) 0))
    :hints (("Goal" :use ((:instance sgn-sticky)
                          (:instance positive-sgn-2
                                     (x x))
                          (:instance positive-sgn-2
                                     (x (sticky x n))))))
  :rule-classes :linear)

;; (defthm sticky-0
;;   (equal (sticky 0 n) 0))


;; (defthmd sticky-minus
;;   (equal (sticky (* -1 x) n) (* -1 (sticky x n))))


;; (defthm sticky-shift
;;     (implies (and (rationalp x)
;; 		  (integerp n) (> n 0)
;; 		  (integerp k))
;; 	     (= (sticky (* (expt 2 k) x) n)
;; 		(* (expt 2 k) (sticky x n))))
;;   :rule-classes ())


;; (defthm expo-sticky
;;     (implies (and (rationalp x) (> x 0)
;; 		  (integerp n) (> n 0))
;; 	     (= (expo (sticky x n))
;; 		(expo x)))
;;   :rule-classes ())


(local
 (defthm sticky-exactp-a-lemma
    (implies (and (rationalp x)
                  (> x 0)
		  (integerp n) (> n 0))
	     (exactp (sticky x n) n))
    :hints (("Goal" :in-theory (enable sgn exactp-2**n sticky)
             :cases ((not (equal n 1))))
            ("Subgoal 1"
             :use ((:instance trunc-exactp-a (n (- 1 n)))
                   (:instance fp+1
                              (x (trunc x (+ -1 n)))
                              (n n))
                   (:instance exactp-<=
                              (m (+ -1 n))
                              (n n)
                              (x (trunc x (+ -1 n))))
                   (:instance exactp-<=
                              (m (+ -1 n))
                              (n n)
                              (x x)))))
    :rule-classes ()))


(defthm sticky-exactp-a
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (exactp (sticky x n) n))
    :hints (("Goal" :cases ((not (equal x 0)))
             :in-theory (enable sticky-minus))
            ("Subgoal 2" :in-theory (enable sticky exactp))
            ("Subgoal 1" :cases ((not (> x 0))))
            ("Subgoal 1.2" :use ((:instance sticky-exactp-a-lemma)))
            ("Subgoal 1.1" :use ((:instance sticky-exactp-a-lemma
                                            (x (* -1 x))))))
    :rule-classes ())


(local
  (defthm sig-fact
    (implies (and (rationalp x)
                  (> x 0))
             (iff (equal (EXPT 2 (EXPO X)) x)
                  (INTEGERP (SIG X))))
    :hints (("Goal" :use ((:instance fp-rep)
                          (:instance sig-lower-bound)
                          (:instance sig-upper-bound))
             :in-theory (enable sgn))
            ("Subgoal 1" :cases ((not (< 1 (sig x))))))))


(local
 (defthm sticky-exactp-b-lemma
    (implies (and (rationalp x)
                  (> x 0)
		  (integerp n)
		  (> n 0))
	     (iff (= x (sticky x n))
		  (exactp x n)))
    :hints (("Goal" :in-theory (enable expo-trunc
                                       trunc-exactp-a
                                       sig-upper-bound
                                       sig-lower-bound
                                exactp-2**n sticky sgn)
             :cases ((not (exactp x (+ -1 n)))))
            ("Subgoal 2" :use ((:instance exactp-<=
                                          (m (+ -1 n))
                                          (n n)
                                          (x x))))
            ("Subgoal 1" :cases ((not (equal n 1))))
            ("Subgoal 1.2" :in-theory (enable exactp
                                              exactp-2**n
                                              sticky sgn))
            ("Subgoal 1.1" :use ((:instance trunc-midpoint
                                            (x x)
                                            (n (+ -1 n)))
                                 (:instance fp+1
                                            (x (trunc x (+ -1 n)))
                                            (n n))
                                 (:instance exactp-<=
                                          (m (+ -1 n))
                                          (n n)
                                          (x (trunc x (+ -1 n)))))))
  :rule-classes ()))


(defthm sticky-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (sticky x n))
		  (exactp x n)))
    :hints (("Goal" :cases ((not (equal x 0)))
             :in-theory (enable sticky-minus))
            ("Subgoal 2" :in-theory (enable sticky exactp))
            ("Subgoal 1" :cases ((not (> x 0))))
            ("Subgoal 1.2" :use ((:instance sticky-exactp-b-lemma)))
            ("Subgoal 1.1" :use ((:instance sticky-exactp-b-lemma
                                            (x (* -1 x))))))
    :rule-classes ())

;; (local
;;  (defthm fl-1/2-sig-x-is-zero-lemma
;;    (implies (and (rationalp x)
;;                  (rationalp y)
;;                  (< 0 y)
;;                  (<= y 1/2))
;;             (equal (fl (* (sig x) y))
;;                    0))
;;    :hints (("Goal" :use ((:instance sig-upper-bound)
;;                          (:instance sig-lower-bound))))))



;; (local
;;   (defthm |1/2-sig-x-not-integerp-lemma|
;;     (implies (and (rationalp x)
;;                   (not (equal x 0))
;;                   (rationalp y)
;;                   (< 0 y)
;;                   (<= y 1/2))
;;              (not (integerp (* (sig x) y))))
;;     :hints (("Goal" :use ((:instance sig-upper-bound)
;;                           (:instance sig-lower-bound))))))


;; (local (include-book "../../arithmetic/expt"))

;; (local
;;  (defthm exactp-minus-fact
;;    (implies (and (integerp n)
;;                  (rationalp x)
;;                  (not (equal x 0))
;;                  (<= n 0))
;;             (not (exactp x n)))
;;    :hints (("Goal" :in-theory (enable exactp)
;;             :use ((:instance sig-upper-bound)
;;                   (:instance sig-lower-bound)
;;                   (:instance |1/2-sig-x-not-integerp-lemma|
;;                              (y (expt 2 (+ -1 n))))
;;                   (:instance expt-weak-monotone-linear
;;                              (n (+ -1 n))
;;                              (m -1)))))))

;; (defthmd sticky-monotone
;;   (implies (and (<= x y)
;;                 (rationalp x)
;;                 (rationalp y)
;;                 (natp n))
;;            (<= (sticky x n) (sticky y n)))
;;   :hints (("Goal" :cases ((not (equal n 0)))
;;            :in-theory (enable sticky sgn))
;;           ("Subgoal 2" :cases ((not (equal y 0))))
;;           ("Subgoal 2.1" :use ((:instance expo-monotone
;;                                           (y x)
;;                                           (x y))
;;                                (:instance expo-monotone
;;                                           (x x)
;;                                           (y y))
;;                                (:instance expt-weak-monotone-linear
;;                                           (n (+ 1 (expo y)))
;;                                           (m (+ 1 (expo x))))
;;                                (:instance expt-weak-monotone-linear
;;                                           (n (+ 1 (expo x)))
;;                                           (m (+ 1 (expo y))))))
;;           ("Subgoal 1" :use ((:instance sticky-monotone---rtl-rel5-support))))
;;   :rule-classes :linear)


;; (defthm sticky-exactp-m
;;     (implies (and (rationalp x)
;; 		  (integerp m)
;; 		  (integerp n)
;; 		  (> n m)
;; 		  (> m 0))
;; 	     (iff (exactp (sticky x n) m)
;; 		  (exactp x m)))
;;   :rule-classes ())

;; (i-am-here)

;; (defthm trunc-sticky
;;     (implies (and (rationalp x)
;; 		  (integerp m) (> m 0)
;; 		  (integerp n) (> n m))
;; 	     (= (trunc (sticky x n) m)
;; 		(trunc x m)))
;;     :hints (("Goal" :cases ((not (equal x 0))))
;;             ("Subgoal 1" :cases ((not (> x 0))))
;;             ("Subgoal 1.2" :use ((:instance trunc-sticky---rtl-rel5-support)))
;;             ("Subgoal 1.1" :use ((:instance trunc-sticky---rtl-rel5-support
;;                                             (x (* -1 x))))
;;              :in-theory (enable trunc-minus sticky-minus)))
;;   :rule-classes ())


;; (defthm away-sticky
;;     (implies (and (rationalp x)
;; 		  (integerp m) (> m 0)
;; 		  (integerp n) (> n m))
;; 	     (= (away (sticky x n) m)
;; 		(away x m)))
;;     :hints (("Goal" :cases ((not (equal x 0))))
;;             ("Subgoal 1" :cases ((not (> x 0))))
;;             ("Subgoal 1.2" :use ((:instance away-sticky---rtl-rel5-support)))
;;             ("Subgoal 1.1" :use ((:instance away-sticky---rtl-rel5-support
;;                                             (x (* -1 x))))
;;              :in-theory (enable away-minus sticky-minus)))
;;   :rule-classes ())


;; (defthm near-sticky
;;     (implies (and (rationalp x)
;; 		  (integerp m) (> m 0)
;; 		  (integerp n) (> n (1+ m)))
;; 	     (= (near (sticky x n) m)
;; 		(near x m)))
;;     :hints (("Goal" :cases ((not (equal x 0))))
;;             ("Subgoal 1" :cases ((not (> x 0))))
;;             ("Subgoal 1.2" :use ((:instance near-sticky---rtl-rel5-support)))
;;             ("Subgoal 1.1" :use ((:instance near-sticky---rtl-rel5-support
;;                                             (x (* -1 x))))
;;              :in-theory (enable near-minus sticky-minus)))
;;   :rule-classes ())


;----------------------------------------------------------------------


;; (defthm near+-sticky
;;     (implies (and (rationalp x)
;; 		  (integerp m) (> m 0)
;; 		  (integerp n) (> n (1+ m)))
;; 	     (= (near+ (sticky x n) m)
;; 		(near+ x m)))
;;     :hints (("Goal" :use ((:instance near+-trunc-cor
;;                                      (x (sticky x n))
;;                                      (n (+ 1 m))
;;                                      (m m))
;;                           (:instance trunc-sticky
;;                                      (m (+ 1 m)))
;;                           (:instance near+-trunc-cor
;;                                      (x x)
;;                                      (n (+ 1 m))
;;                                      (m m)))))
;;   :rule-classes ())

;----------------------------------------------------------------------

;; (defthm sticky-sticky
;;     (implies (and (rationalp x)
;; 		  (integerp m)
;; 		  (> m 1)
;; 		  (integerp n)
;; 		  (>= n m))
;; 	     (= (sticky (sticky x n) m)
;; 		(sticky x m)))
;;   :rule-classes ())

;----------------------------------------------------------------------

;;
;; sticky-plus---rtl-rel5-support
;;     (implies (and (rationalp x)
;; 		  (> x 0)
;; 		  (rationalp y)
;; 		  (> y 0)
;; 		  (integerp k)
;; 		  (= k1 (+ k (- (expo x) (expo y))))
;; 		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
;; 		  (> k 1)
;; 		  (> k1 1)
;; 		  (> k2 1)
;; 		  (exactp x (1- k1)))
;; 	     (= (+ x (sticky y k))
;; 		(sticky (+ x y) k2)))
;;     :hints (("Goal" :by sticky-plus))
;;   :rule-classes ())
;;
;; doesn't support well. Tue Jan 31 12:56:09 2006
;;

;;   (defthm trunc-plus-minus
;;     (implies (and (rationalp x)
;;                   (rationalp y)
;;                   (not (= x 0))
;;                   (not (= y 0))
;;                   (not (= (+ x y) 0))
;;                   (integerp k)
;;                   (> k 0)
;;                   (= k1 (+ k (- (expo x) (expo y))))
;;                   (= k2 (+ k (expo (+ x y)) (* -1 (expo y))))
;;                   (exactp x k1)
;;                   (> k2 0))
;;              (equal (+ x (trunc y k))
;;                     (if (= (sgn (+ x y)) (sgn y))
;;                         (trunc (+ x y) k2)
;;                       (away (+ x y) k2))))



(encapsulate ()

   (local
    (defthm exactp-fact-1
      (implies (and (EXACTP X  (+ -1 K (EXPO X) (* -1 (EXPO Y))))
                    (rationalp x)
                    (rationalp y)
                    (integerp k))
               (iff (exactp (+ x y) (+ -1 K (* -1 (EXPO Y))
                                       (EXPO (+ X Y))))
                    (exactp y  (+ -1 k))))
      :hints (("Goal" :in-theory (enable exactp2)))))



   (local
    (defthm local-expt-2-expand
      (implies (and (rationalp x)
                    (integerp k))
               (equal (EXPT 2 (+ 2 (EXPO Y) (* -1 K)))
                      (* 2 (EXPT 2 (+ 1 (EXPO Y) (* -1 k))))))
      :hints (("Goal" :use ((:instance a15 (i 2) (j1 1)
                                       (j2 (+ 1 (EXPO Y)
                                              (* -1 k)))))))))

   (defthm sticky-plus
     (implies (and (rationalp x)
                   (rationalp y)
                   (not (= y 0))
                   (not (= (+ x y) 0))
                   (integerp k)
                   (= k1 (+ k (- (expo x) (expo y))))
                   (= k2 (+ k (- (expo (+ x y)) (expo y))))
                   (> k 1)
                   (> k1 1)
                   (> k2 1)
                   (exactp x (1- k1)))
              (= (+ x (sticky y k))
                 (sticky (+ x y) k2)))
     :hints (("Goal" :cases ((not (exactp y (+ -1 k))))
              :in-theory (enable sticky))
             ("Subgoal 1" :use ((:instance trunc-plus-minus
                                           (k1 (+ -1 k (expo x) (* -1 (expo y))))
                                           (k2 (+ -1 k (* -1 (expo y)) (expo (+
                                                                              x
                                                                              y))))
                                           (k (+ -1 k)))))
             ("Subgoal 1.1" :cases ((not (> (+ x y) 0))))
             ("Subgoal 1.1.2" :use ((:instance trunc-away
                                               (x (+ x y))
                                               (n (+ -1 K (* -1 (EXPO Y))
                                                     (EXPO (+ X Y))))))
              :in-theory (enable sgn expo-minus trunc-minus away-minus))
             ("Subgoal 1.1.1" :use ((:instance trunc-away
                                               (x (* -1 (+ x y)))
                                               (n (+ -1 K (* -1 (EXPO Y))
                                                     (EXPO (+ X Y))))))
              :in-theory (enable sgn expo-minus trunc-minus away-minus)))
     :rule-classes ()))



;;;**********************************************************************
;;;                    IEEE Rounding
;;;**********************************************************************

;; (i-am-here);; Fri Oct 13 15:10:44 2006
;; (defun inf (x n)
;;   (if (>= x 0)
;;       (away x n)
;;     (trunc x n)))


(defthmd inf-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (inf x n) x))
    :hints (("Goal" :use ((:instance trunc-upper-bound)
                          (:instance away-lower-bound)))
            ("Subgoal 1" :cases ((not (equal x 0)))))
  :rule-classes :linear)


;; (defun minf (x n)
;;   (if (>= x 0)
;;       (trunc x n)
;;     (away x n)))

(defthmd minf-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (<= (minf x n) x))
    :hints (("Goal" :use ((:instance trunc-upper-bound)
                          (:instance away-lower-bound))))
  :rule-classes :linear)

;; (defund IEEE-mode-p (mode)
;;   (member mode '(trunc inf minf near)))


;; (defun common-rounding-mode-p (mode)
;;   (or (IEEE-mode-p mode) (equal mode 'away) (equal mode 'near+)))

;; (defthmd ieee-mode-p-implies-common-rounding-mode-p
;;   (implies (IEEE-mode-p mode)
;;            (common-rounding-mode-p mode)))

;; (defund rnd (x mode n)
;;   (case mode
;;     (away (away x n))
;;     (near+ (near+ x n))
;;     (trunc (trunc x n))
;;     (inf (inf x n))
;;     (minf (minf x n))
;;     (near (near x n))
;;     (otherwise 0)))


;; (defthm rationalp-rnd
;;   (rationalp (rnd x mode n))
;;   :rule-classes (:type-prescription))


(defthm rnd-choice
  (implies (and (rationalp x)
                (integerp n)
                (common-rounding-mode-p mode))
           (or (= (rnd x mode n) (trunc x n))
	       (= (rnd x mode n) (away x n))))
  :hints (("Goal" :use ((:instance near+-choice)
                        (:instance near-choice))
           :in-theory (enable rnd IEEE-mode-p)))
  :rule-classes ())

;; (encapsulate ()
;;    (local
;;     (defthm not-rational-rnd-redcue-to-zero
;;       (implies (not (rationalp x))
;;                (equal (rnd x mode n) 0))
;;       :hints (("Goal" :in-theory (enable away near sig trunc near+ rnd)))))

;;    (local
;;     (defthm not-rational-sgn-redcue-to-zero
;;       (implies (not (rationalp x))
;;                (equal (sgn x) 0))
;;       :hints (("Goal" :in-theory (enable sgn)))))


;;    (defthmd sgn-rnd
;;        (implies (and (common-rounding-mode-p mode)
;;                      (integerp n)
;;                      (> n 0))
;;    	     (equal (sgn (rnd x mode n))
;;    		    (sgn x)))
;;        :hints (("Goal" :cases ((not (rationalp x)))
;;                 :in-theory
;;                 (enable sgn-away sgn-trunc
;;                      sgn-near rnd IEEE-mode-p)))))



(defthm rnd-positive
  (implies (and (< 0 x)
                (rationalp x)
                (integerp n)
                (> n 0)
                (common-rounding-mode-p mode))
           (> (rnd x mode n) 0))
  :hints (("Goal"
           :in-theory
           (enable rnd IEEE-mode-p)))
  :rule-classes (:type-prescription))

(defthm rnd-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-rounding-mode-p mode))
	     (< (rnd x mode n) 0))
  :hints (("Goal"
           :in-theory
           (enable rnd near IEEE-mode-p)))
  :rule-classes (:type-prescription))

;; (defthm rnd-0
;;   (equal (rnd 0 mode n)
;;          0))

; Unlike the above, we leave the following two as rewrite rules because we may
; want to use the rewriter to relieve their hypotheses.

;; (defthm rnd-non-pos
;;     (implies (<= x 0)
;; 	     (<= (rnd x mode n) 0))
;;   :rule-classes (:rewrite :type-prescription :linear))

;; (defthm rnd-non-neg
;;     (implies (<= 0 x)
;; 	     (<= 0 (rnd x mode n)))
;;   :rule-classes (:rewrite :type-prescription :linear))

;; (defund flip (m)
;;   (case m
;;     (inf 'minf)
;;     (minf 'inf)
;;     (t m)))

;; (defthm ieee-mode-p-flip
;;     (implies (ieee-mode-p m)
;; 	     (ieee-mode-p (flip m))))


;; (defthm common-rounding-mode-p-flip
;;     (implies (common-rounding-mode-p m)
;; 	     (common-rounding-mode-p (flip m))))


;; (defthmd rnd-minus
;;   (equal (rnd (* -1 x) mode n)
;;          (* -1 (rnd x (flip mode) n))))




;; (defthm rnd-exactp-a
;;     (implies (< 0 n)
;; 	     (exactp (rnd x mode n) n))
;;     :hints (("Goal" :by rnd-exactp-b---rtl-rel5-support)))


;; (defthm rnd-exactp-b
;;   (implies (and (rationalp x)
;;                 (common-rounding-mode-p mode)
;;                 (integerp n)
;;                 (> n 0))
;;            (equal (equal x (rnd x mode n))
;; 		  (exactp x n)))
;;   :hints (("Goal" :use ((:instance rnd-exactp-a---rtl-rel5-support)))))


;; (defthmd rnd-exactp-c
;;     (implies (and (rationalp x)
;; 		  (common-rounding-mode-p mode)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (rationalp a)
;; 		  (exactp a n)
;; 		  (>= a x))
;; 	     (>= a (rnd x mode n)))
;;     :hints (("Goal" :in-theory (enable trunc-minus
;;                                        ieee-mode-p flip rnd)
;;              :use ((:instance trunc-exactp-c
;;                               (x (* -1 x)) (a (* -1 a)))
;;                    (:instance away-exactp-c)
;;                    (:instance near-exactp-c)
;;                    (:instance near+-exactp-c)))))


;; (defthmd rnd-exactp-d
;;     (implies (and (rationalp x)
;; 		  (common-rounding-mode-p mode)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (rationalp a)
;; 		  (exactp a n)
;; 		  (<= a x))
;; 	     (<= a (rnd x mode n)))
;;     :hints (("Goal" :in-theory (enable away-minus
;;                                        ieee-mode-p flip rnd)
;;              :use ((:instance trunc-exactp-c)
;;                    (:instance away-exactp-c
;;                               (x (* -1 x)) (a (* -1 a)))
;;                    (:instance near-exactp-d)
;;                    (:instance near+-exactp-d)))))


;; (defthm rnd<=away
;;     (implies (and (rationalp x)
;; 		  (>= x 0)
;; 		  (common-rounding-mode-p mode)
;; 		  (natp n))
;; 	     (<= (rnd x mode n) (away x n)))
;;     :hints (("Goal" :in-theory (enable ieee-mode-p
;;                                        near near+
;;                                        minf inf
;;                                        trunc-upper-pos
;;                                        away-lower-pos
;;                                        flip rnd)))
;;   :rule-classes ())



;; (defthm rnd>=trunc
;;     (implies (and (rationalp x)
;; 		  (>= x 0)
;; 		  (common-rounding-mode-p mode)
;; 		  (natp n))
;; 	     (>= (rnd x mode n) (trunc x n)))
;;     :hints (("Goal" :in-theory (enable ieee-mode-p
;;                                        near near+
;;                                        inf minf
;;                                        common-rounding-mode-p
;;                                        trunc-upper-pos
;;                                        away-lower-pos
;;                                        flip rnd)))
;;   :rule-classes ())


;; (defthmd rnd-diff
;;   (implies (and (rationalp x)
;;                 (integerp n)
;;                 (> n 0)
;;                 (common-rounding-mode-p mode))
;;            (< (abs (- x (rnd x mode n))) (expt 2 (- (1+ (expo x)) n))))
;;   :hints (("Goal" :use ((:instance rnd-diff---rtl-rel5-support)))))

;; (i-am-here) ;; Fri Oct 13 15:29:42 2006

;; (defthm expo-rnd
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (common-rounding-mode-p mode)
;; 		  (not (= (abs (rnd x mode n))
;; 			  (expt 2 (1+ (expo x))))))
;; 	     (= (expo (rnd x mode n))
;; 		(expo x)))
;;   :hints (("Goal" :use ((:instance expo-rnd---rtl-rel5-support))))
;;   :rule-classes ())


;; (encapsulate ()

;; (local
;;  (defthm |Subgoal 5|
;;    (IMPLIES (AND (RATIONALP X)
;;                  (RATIONALP Y)
;;                  (INTEGERP N)
;;                  (<= 0 N)
;;                  (<= 0 Y)
;;                  (< X 0))
;;             (<= (TRUNC X N) (AWAY Y N)))
;;    :hints (("Goal" :cases ((not (equal y 0)))
;;             :in-theory (enable trunc-negative sgn
;;                                away-positive)))
;;    :rule-classes :linear))



;; ;; (defthm near+-monotone
;; ;;   (implies (and (<= x y)
;; ;;                 (rationalp x)
;; ;;                 (rationalp y)
;; ;;                 (< 0 x)    ;;; not good enough!!!
;; ;;                 (integerp n)
;; ;;                 (> n 0))
;; ;;            (<= (near+ x n) (near+ y n))))


;; (defthmd rnd-monotone
;;     (implies (and (<= x y)
;;                   (rationalp x)
;; 		  (rationalp y)
;; 		  (common-rounding-mode-p mode)
;;                   (integerp n)
;;                   (> n 0))
;; 	     (<= (rnd x mode n) (rnd y mode n)))
;;     :hints (("Goal" :in-theory (enable ieee-mode-p
;;                                        common-rounding-mode-p
;;                                 trunc-positive
;;                                 trunc-negative
;;                                 away-positive
;;                                 away-negative
;;                                 away-monotone
;;                                 trunc-monotone
;;                                 near-monotone
;;                                 near+-monotone
;;                                 flip rnd)
;;              :use ((:instance away-monotone)))))

;; )


;; (defthm rnd-shift
;;     (implies (and (rationalp x)
;; 		  (integerp n)
;; 		  (common-rounding-mode-p mode)
;; 		  (integerp k))
;; 	     (= (rnd (* x (expt 2 k)) mode n)
;; 		(* (rnd x mode n) (expt 2 k))))
;;     :hints (("Goal" :use ((:instance rnd-shift---rtl-rel5-support))))
;;   :rule-classes ())


;; (defthm plus-rnd
;;   (implies (and (rationalp x)
;;                 (>= x 0)
;;                 (rationalp y)
;;                 (>= y 0)
;;                 (integerp k)
;;                 (exactp x (+ -1 k (- (expo x) (expo y))))
;;                 (common-rounding-mode-p mode))
;;            (= (+ x (rnd y mode k))
;;               (rnd (+ x y)
;;                    mode
;;                    (+ k (- (expo (+ x y)) (expo y))))))
;;   :hints (("Goal" :use ((:instance plus-rnd---rtl-rel5-support))))
;;   :rule-classes ())


;; (defthmd rnd-sticky
;;   (implies (and (common-rounding-mode-p mode)
;;                 (rationalp x)
;;                 (integerp m)
;; 		(> m 0)
;;                 (integerp n)
;; 		(>= n (+ m 2)))
;;            (equal (rnd (sticky x n) mode m)
;;                   (rnd x mode m)))
;;   :hints (("Goal" :cases ((not (equal x 0)))
;;            :in-theory (enable rnd-minus flip rnd sticky-minus))
;;           ("Subgoal 1" :cases ((not (> x 0))))
;;           ("Subgoal 1.2"
;;            :use ((:instance rnd-sticky---rtl-rel5-support
;;                                         (k m))))
;;           ("Subgoal 1.1"
;;            :use ((:instance rnd-sticky---rtl-rel5-support
;;                                         (k m)
;;                                         (mode (flip mode))
;;                                         (x (* -1 x)))))))




;; (defun rnd-const (e mode n)
;;   (case mode
;;     ((near near+) (expt 2 (- e n)))
;;     ((inf away) (1- (expt 2 (1+ (- e n)))))
;;     (otherwise 0)))


;; (defthm rnd-const-thm
;;     (implies (and (common-rounding-mode-p mode)
;; 		  (integerp n)
;; 		  (> n 1)
;; 		  (integerp x)
;; 		  (> x 0)
;; 		  (>= (expo x) n))
;; 	     (= (rnd x mode n)
;; 		(if (and (eql mode 'near)
;; 			 (exactp x (1+ n))
;; 			 (not (exactp x n)))
;; 		    (trunc (+ x (rnd-const (expo x) mode n)) (1- n))
;; 		  (trunc (+ x (rnd-const (expo x) mode n)) n))))
;;     :hints (("Goal" :use rnd-const-thm---rtl-rel5-support))
;;   :rule-classes ())


;; (defun roundup (x mode n)
;;   (case mode
;;     (near+ (= (bitn x (- (expo x) n)) 1))
;;     (near (and (= (bitn x (- (expo x) n)) 1)
;;                (or (not (exactp x (1+ n)))
;;                    (= (bitn x (- (1+ (expo x)) n)) 1))))
;;     ((inf away) (not (exactp x n)))
;;     (otherwise ())))


;; (defthm roundup-thm
;;     (implies (and (common-rounding-mode-p mode)
;; 		  (integerp n)
;; 		  (> n 1)
;; 		  (integerp x)
;; 		  (> x 0)
;; 		  (>= (expo x) n))
;; 	     (= (rnd x mode n)
;;                 (if (roundup x mode n)
;;                     (fp+ (trunc x n) n)
;;                   (trunc x n))))
;;     :hints (("Goal" :use roundup-thm---rtl-rel5-support))
;;   :rule-classes ())

;;;
;;; very nice theorems!! good!! Tue Jan 31 16:37:49 2006
;;; relating bits and their rounded values!!
;;;

;;; Sun Oct 15 16:41:11 2006

;; (i-am-here) ;; Sun Oct 15 17:00:23 2006

;;;**********************************************************************
;;;                         Denormal Rounding
;;;**********************************************************************

;;; because of the drnd definition changed, we abandon all the proofs in
;;; lib/round.lisp
;;;
;;; we could prove that two definitions are the same thus reuse the older
;;; proofs!

(defund drnd (x mode p q)
  (rnd x mode (+ p (expo x) (- (expo (spn q))))))

(defthmd drnd-minus
  (equal (drnd (* -1 x) mode p q)
         (* -1 (drnd x (flip mode) p q)))
  :hints (("Goal" :in-theory (enable drnd expo-minus  rnd-minus))))

;----------------------------------------------------------------------

(local (include-book "../../arithmetic/expt"))

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
            :hints (("Goal" :use ((:instance sig-upper-bound)
                                  (:instance sig-lower-bound))))))

       ;; we really need these two lemma
       (defthm fl-1/2-sig-x-is-zero-lemma-2
         (implies (and (rationalp x)
                       (rationalp y)
                       (not (equal x 0))
                       (< 0 y)
                       (<= y 1/2))
                  (equal (fl (* -1 (sig x) y))
                         -1))
         :hints (("Goal" :in-theory (enable sig fl-minus)
                  :use ((:instance fl-1/2-sig-x-is-zero-lemma)))))

       (defthm expt-2-no-greater-than-1
            (implies (and (<= (+ p (expo x))
                              (expo (spn q)))
                          (integerp p))
                     (<= (* 2
                            (EXPT 2
                                  (+ -1 P (EXPO X)
                                     (* -1 (EXPO (SPN Q))))))
                         1))
            :hints (("Goal" :use ((:instance expt-weak-monotone-linear
                                             (n (+ -1 P (EXPO X)
                                                   (* -1 (EXPO (SPN Q)))))
                                             (m -1)))))
            :rule-classes :linear)

       (defthm fl-1/2-sig-x-is-zero
           (implies (and (rationalp x)
                         (case-split (not (equal x 0)))
                         (integerp p)
                         (<= (+ p (expo x))
                             (expo (spn q))))
                    (equal (FL (* (SIG X)
                                  (EXPT 2
                                        (+ -1 P (EXPO X)
                                           (* -1 (EXPO (SPN Q)))))))
                           0))
           :hints (("Goal" :use ((:instance fl-1/2-sig-x-is-zero-lemma
                                            (y (EXPT 2
                                                     (+ -1 P (EXPO X)
                                                        (* -1 (EXPO (SPN q)))))))))))


       (defthm fl-1/2-sig-x-is-zero-2
           (implies (and (rationalp x)
                         (case-split (not (equal x 0)))
                         (integerp p)
                         (<= (+ p (expo x))
                             (expo (spn q))))
                    (equal (FL (* -1 (SIG X)
                                  (EXPT 2
                                        (+ -1 P (EXPO X)
                                           (* -1 (EXPO (SPN Q)))))))
                           -1))
           :hints (("Goal" :use ((:instance fl-1/2-sig-x-is-zero-lemma-2
                                            (y (EXPT 2
                                                     (+ -1 P (EXPO X)
                                                        (* -1 (EXPO (SPN q)))))))))))))


;----------------------------------------------------------------------

(encapsulate ()


;;; prove the first condition in drepp
             ;;
             ;;L d            (DEFUN DREPP (X P Q)
             ;;                      (AND (RATIONALP X)
             ;;                           (NOT (= X 0))
             ;;                           (<= (- 2 P) (+ (EXPO X) (BIAS Q)))
             ;;                           (<= (+ (EXPO X) (BIAS Q)) 0)
             ;;                           (EXACTP X (+ -2 P (EXPT 2 (- Q 1)) (EXPO X)))))

             (local (encapsulate ()
;;;;
;;;;          (<= (+ (EXPO X) (BIAS Q)) 0)  if x < (spn q)
;;;;
                                 (local
                                  (defthm expo-less-than-minus-1-lemma
                                    (IMPLIES (AND (< N (EXPO X))
                                                  (< 0 X)
                                                  (integerp n)
                                                  (RATIONALP X))
                                             (<= (EXPT 2 (+ 1 N)) X))
                                    :hints (("Goal" :use ((:instance expt-weak-monotone-linear
                                                                     (n (+ 1 n))
                                                                     (m (expo x)))
                                                          (:instance expo-lower-bound))))))

                                 (local
                                  (defthm expo-less-than-minus-1
                                    (implies (and (< 0 x)
                                                  (integerp n)
                                                  (rationalp x)
                                                  (< X (EXPT 2 (+ 1 n))))
                                             (<= (expo x) n))
                                    :hints (("Goal" :cases ((> (expo x) n))))
                                    :rule-classes :linear))

                                 (defthm less-than-spn-implies-expo-less
                                   (implies (and (< (abs x) (spn q))
                                                 (> q 0)
                                                 (> x 0)
                                                 (integerp q)
                                                 (rationalp x))
                                            (>= 0 (+ (bias q) (expo x))))
                                   :hints (("Goal" :in-theory (enable spn expo-minus)
                                            :use ((:instance expo-monotone (x (abs x)) (y (spn q))))))
                                   :rule-classes :linear))

                    ) ;;; END OF    (<= (+ (EXPO X) (BIAS Q)) 0)  if x < (spn q)


             (local (encapsulate ()

;;;
;;;     (EXACTP X (+ -2 P (EXPT 2 (- Q 1)) (EXPO X)))))
;;;

                                 (defthm exactp-drnd-specific
                                   (implies (and (rationalp x)
                                                 (> (+ p (expo x))
                                                    (expo (spn q)))
                                                 (integerp p)
                                                 (integerp q)
                                                 (> q 0))
                                            (EXACTP (DRND X MODE P Q)
                                                    (+ -2 P (EXPO X) (EXPT 2 (+ -1 Q)))))
                                   :hints (("Goal" :in-theory (enable drnd spn bias)
                                            :use ((:instance RND-EXACTP-A
                                                             (X x) (mode MODE)
                                                             (n (+ -1 P (BIAS Q) (EXPO X)))))))))
                    ) ;;; END OF  (EXACTP X (+ -2 P (EXPT 2 (- Q 1)) (EXPO X)))))



             (local (encapsulate ()

                                 (local
                                  (defthm expt-equal-specific-lemma
                                    (implies (and (EQUAL 0 (+ y x))
                                                  (integerp x)
                                                  (integerp y))
                                             (equal (expt 2 (+ 1 x))
                                                    (expt 2 (+ 1 (* -1 y)))))
                                    :hints (("Goal" :cases ((equal x (* -1 y)))))))


                                 (defthm expt-equal-specific
                                   (implies (and (EQUAL 0 (+ (BIAS Q) (EXPO X)))
                                                 (rationalp x)
                                                 (integerp q)
                                                 (> q 0))
                                            (equal (expt 2 (+ 1 (expo x)))
                                                   (expt 2 (+ 1 (* -1 (bias q))))))
                                   :hints (("Goal" :cases ((equal (expo x)
                                                                  (* -1 (bias q)))))))
                                 )) ;; don't know why we need this.




             (local (encapsulate ()

                                 (defthm minus-expt-reduce
                                   (implies (and (integerp p)
                                                 (integerp q)
                                                 (> q 0)
                                                 (rationalp x))
                                            (equal (+ -1 P (EXPO X) (EXPT 2 (+ -1 Q)))
                                                   (+ 1 p (expo x) (* -1 (expo (spn q))))))
                                   :hints (("Goal" :in-theory (enable spn bias expo-2**n))))


                                 ))

             (local (encapsulate ()
;;;
;;;           (<= (- 2 P) (+ (EXPO X) (BIAS Q)))
;;;
                                 (defthm p-expo-x-expo-spn
                                   (implies (and (> (+ p (expo x))
                                                    (expo (spn q)))
                                                 (rationalp x)
                                                 (integerp p)
                                                 (integerp q)
                                                 (> q 0))
                                            (>= (+ (BIAS Q) (EXPO x))
                                                (+ 2 (* -1 p))))
                                   :hints (("Goal" :in-theory (enable spn)))
                                   :rule-classes :linear))

                    ) ;;;  END OF          (<= (- 2 P) (+ (EXPO X) (BIAS Q)))


             (local
              (defthm drnd-exactp-a-lemma
                (implies (and (rationalp x)
                              (< (EXPO (SPN Q)) (+ P (EXPO X)))
                              (> x 0)
                              (< (abs x) (spn q))
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (common-rounding-mode-p mode))
                         (or (drepp (drnd x mode p q) p q)
                             (= (drnd x mode p q) 0)
                             (= (drnd x mode p q) (* (sgn x) (spn q)))))
                :rule-classes ()
                :hints (("Goal"  :in-theory (e/d (drepp rnd) ())
                         :do-not '(fertilize)
                         :cases ((not (equal (expo (drnd x mode p q)) (expo x)))))
                        ("Subgoal 2" :use ((:instance less-than-spn-implies-expo-less)))
                        ("Subgoal 1" :in-theory (enable drepp exactp-2**n)
                         :cases ((not (equal (drnd x mode p q) (expt 2 (+ 1 (expo x)))))))
                        ("Subgoal 1.2" :cases ((not (equal (expo x) (* -1 (bias q))))))
                        ("Subgoal 1.2.2" :in-theory (enable sgn spn))
                        ("Subgoal 1.2.1" :use ((:instance less-than-spn-implies-expo-less)))
                        ("Subgoal 1.1" :in-theory (enable drnd)
                         :use ((:instance expo-rnd
                                          (n (+ P (EXPO X) (- (EXPO (SPN Q)))))))))))


             (defthm drepp-minus
               (implies (and (rationalp x)
                             (integerp p)
                             (integerp q))
                        (equal (drepp (* -1 x) p q)
                               (drepp x p q)))
               :hints (("Goal" :in-theory (enable expo-minus drepp))))

             (encapsulate ()
                          (local
                           (defthm bias-expo-reduce
                             (implies (and (integerp q)
                                           (> q 0))
                                      (equal (+ (bias q) (expo (spn q)))
                                             1))
                             :hints (("Goal" :in-theory (enable spn)))))

                          (local
                           (defthm integerp-less-than
                             (implies (and (integerp p)
                                           (integerp q)
                                           (> q 0)
                                           (> p 1))
                                      (<= (+ 1 (BIAS Q) (* -1 P) (EXPO (SPN Q))) 0))
                             :hints (("Goal" :in-theory (enable spn)))
                             :rule-classes :linear))

                          (local
                           (defthm exactp-fact
                             (implies (and (integerp p)
                                           (integerp q)
                                           (> q 0)
                                           (> p 1))
                                      (EXACTP (EXPT 2 (+ 1 (* -1 P) (EXPO (SPN Q))))
                                              (+ -1 (EXPO (SPN Q))
                                                 (EXPT 2 (+ -1 Q)))))
                             :hints (("Goal" :in-theory (enable spn exactp-2**n bias)))))



                          (local
                           (defthm expt-2-no-greater-than-2
                             (implies (and (integerp q)
                                           (> q 0))
                                      (<= (EXPT 2
                                                (+ 1 (* -1 q)))
                                          1))
                             :hints (("Goal" :use ((:instance expt-weak-monotone-linear
                                                              (n (+ 1 (* -1 q)))
                                                              (m 0)))))
                             :rule-classes :linear))

             (defthm exactp-spn-p
               (implies (and (integerp p)
                             (integerp q)
                             (> q 0)
                             (> p 1))
                        (exactp (spn q) p))
               :hints (("Goal" :in-theory (enable spn
                                                  exactp-2**n))))





             (defthm local-rewrite-hack
               (implies (and (equal (+ x (spn q)) 0)
                             (< (EXPO (SPN Q)) (+ P (EXPO X)))
                             (common-rounding-mode-p mode)
                             (integerp p)
                             (integerp q)
                             (> p 1)
                             (> q 0))
                        (EQUAL (+ (SPN Q)
                                  (RND X MODE
                                       (+ P (EXPO X)
                                          (* -1 (EXPO (SPN Q))))))
                               0))
               :hints (("Goal" :cases ((not (equal x (* -1 (spn
                                                            q)))))
                        :in-theory (enable rnd-exactp-b
                                           expo-minus
                                           rnd-minus))))



               (defthm drnd-exactp-a1
                 (implies (and (rationalp x)
                               (<= (abs x) (spn q))
                               (integerp p)
                               (> p 1)
                               (integerp q)
                               (> q 0)
                               (common-rounding-mode-p mode))
                          (or (drepp (drnd x mode p q) p q)
                              (= (drnd x mode p q) 0)
                              (= (drnd x mode p q) (* (sgn x) (spn q)))))
                 :hints (("Goal" :in-theory (enable rnd-minus drepp-minus
                                                    sgn
                                                    flip drnd rnd-exactp-b
                                                    expo-minus sgn-minus)
                          :cases ((not (<= (+ p (expo x) (- (expo (spn q))))
                                           0))))
                         ("Subgoal 2" :in-theory (enable drepp  expo-minus sgn
                                                         drnd near near+
                                                         away cg rnd))
                         ("Subgoal 1" :cases ((not (equal x 0))))
                         ("Subgoal 1.2" :in-theory (enable drnd))
                         ("Subgoal 1.1" :cases ((not (> x 0))))
                         ("Subgoal 1.1.2" :use ((:instance drnd-exactp-a-lemma)))
                         ("Subgoal 1.1.1" :use ((:instance drnd-exactp-a-lemma
                                                           (x (* -1 x))
                                                           (mode (flip
                                                                  mode)))
                                                (:instance rnd-exactp-b
                                                           (x (* -1 x))
                                                           (mode (flip mode))))))
                 :rule-classes ()))



         (defthm drnd-exactp-a
           (implies (and (rationalp x)
                         (<= (abs x) (spn q))
                         (integerp p)
                         (> p 1)
                         (integerp q)
                         (> q 0)
                         (common-rounding-mode-p mode))
                    (or (drepp (drnd x mode p q) p q)
                        (= (drnd x mode p q) 0)
                        (= (drnd x mode p q) (* (sgn x) (spn q)))))
           :hints (("Goal" :cases ((not (equal (abs x) (spn q))))
                    :in-theory (enable sgn drnd rnd-minus expo-minus))
                   ("Subgoal 2" :cases ((equal x (spn q))
                                        (equal x (* -1 (spn q)))))
                   ("Subgoal 1" :use drnd-exactp-a1))
           :rule-classes ())


             ) ;; end of drnd-exactp-a

;;;
;;; extremely bad proof!!
;;;
;;; We could resolve to mid-range, small-range, large range.
;;;

(defthmd drnd-exactp-b
     (implies (and (rationalp x)
   	        (drepp x p q)
                   (integerp p)
                   (> p 1)
                   (integerp q)
                   (> q 0)
                   (common-rounding-mode-p mode))
              (equal (drnd x mode p q)
                     x))
     :hints (("Goal" :in-theory (e/d (drepp spn bias drnd)
                                     (common-rounding-mode-p))
              :use ((:instance rnd-exactp-b
                               (n (+ P (EXPO X) (- (EXPO (SPN Q))))))))))


;----------------------------------------------------------------------



(defthm drnd-trunc
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (<= (abs (drnd x 'trunc p q))
               (abs x)))
  :hints (("Goal" :in-theory (enable drnd rnd)
           :use ((:instance trunc-upper-bound
                            (x x)
                            (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))))))

(defthm drnd-away
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (>= (abs (drnd x 'away p q))
               (abs x)))
  :hints (("Goal" :in-theory (enable drnd rnd)
           :use ((:instance away-lower-bound
                            (x x)
                            (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))))))

(defthm drnd-minf
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (<= (drnd x 'minf p q)
               x))
    :hints (("Goal" :in-theory (enable drnd rnd)
           :use ((:instance minf-lower-bound
                            (x x)
                            (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))))))



(defthm drnd-inf
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (>= (drnd x 'inf p q)
               x))
    :hints (("Goal" :in-theory (enable drnd rnd)
           :use ((:instance inf-lower-bound
                            (x x)
                            (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))))))



;----------------------------------------------------------------------


(local
 (defthm exactp-c-lemma-1
   (IMPLIES (AND (RATIONALP X)
                 (< 0 X)
                 (<= X (SPN Q))
                 (RATIONALP A)
                 (DREPP A P Q)
                 (<= X A)
                 (INTEGERP P)
                 (< 1 P)
                 (INTEGERP Q)
                 (< 0 Q))
            (<= (TRUNC X (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))
                A))
      :hints (("Goal"
               :use ((:instance trunc-upper-bound
                                (x x)
                                (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))
      :rule-classes :linear))


;; (i-am-here) ;; Sun Oct 15 17:16:34 2006


(local
   (encapsulate ()

      (local
       (encapsulate ()
         (local (include-book "float-extra2"))
           (defthmd spd-mult
             (implies (and (integerp p)
                           (> p 1)
                           (integerp q)
                           (> q 0)
                           (> r 0)
           		(rationalp r)
           		(= m (/ r (spd p q))))
           	   (iff (drepp r p q)
           		(and (natp m)
           		     (<= 1 m)
           		     (< m (expt 2 (1- p)))))))))

      (local
         (defthm equal-spd
           (implies (and (integerp p)
                         (integerp q)
                         (> p 1)
                         (> q 0))
                    (equal (spd p q)
                           (EXPT 2 (+ 1 (* -1 P) (EXPO (SPN Q))))))
           :hints (("Goal" :in-theory (enable spd spn bias)))))

      (local
           (defund denormal-norm (r p q)
             (/ r (spd p q))))

      (local
          (defthm spd-mult-specific
            (implies (and (integerp p)
                          (> p 1)
                          (integerp q)
                          (> q 0)
                          (> r 0)
                          (rationalp r))
                     (= r (* (denormal-norm r p q) (spd p q))))
            :hints (("Goal" :in-theory (enable denormal-norm)))
            :rule-classes nil))

      (local
          (defthm drepp-implies-denormal-norm-integerp
            (implies (and (drepp r p q)
                          (integerp p)
                          (> p 1)
                          (integerp q)
                          (> q 0)
                          (> r 0)
                          (rationalp r))
                     (integerp (denormal-norm r p q)))
            :hints (("Goal" :use ((:instance spd-mult
                                             (m (denormal-norm r p q)))
                                  (:instance spd-mult-specific))))
            :rule-classes :type-prescription))


      (local
          (defthm drepp-implies-denormal-norm-less-than
            (implies (and (drepp r p q)
                          (integerp p)
                          (> p 1)
                          (integerp q)
                          (> q 0)
                          (> r 0)
                          (rationalp r))
                     (<= (denormal-norm r p q)
                         (+ -1 (expt 2 (+ -1 p)))))
            :hints (("Goal" :use ((:instance spd-mult
                                             (m (denormal-norm r p q)))
                                  (:instance spd-mult-specific))))
            :rule-classes :linear))

      (local
          (defthm denormal-normal-monotone
            (implies (and (< r1 r2)
                          (integerp (denormal-norm r1 p q))
                          (integerp (denormal-norm r2 p q)))
                     (<= (+ 1 (denormal-norm r1 p q))
                         (denormal-norm r2 p q)))
            :hints (("Goal" :in-theory (enable spd denormal-norm)))
            :rule-classes :linear))

      (local
      (defthm drepp-diff
           (implies (and (rationalp r1)
                         (rationalp r2)
                         (> r1 r2)
                         (> r2 0)
                         (integerp p)
                         (integerp q)
                         (> p 1)
                         (> q 0)
                         (drepp r1 p q)
                         (drepp r2 p q))
                    (<= (+ r2 (EXPT 2 (+ 1 (* -1 P) (EXPO (SPN Q)))))
                        r1))
           :hints (("Goal" :use ((:instance spd-mult-specific
                                            (r r1))
                                 (:instance spd-mult-specific
                                            (r r2))
                                 (:instance denormal-normal-monotone
                                            (r1 r2)
                                            (r2 r1)))))
           :rule-classes nil))


      (local
       (defthm expt-merge
         (implies (and (integerp p)
                       (integerp q)
                       (> q 0))
                  (equal (* (EXPT 2 (+ -1 P))
                            (EXPT 2 (+ 2 (* -1 P) (* -1 (BIAS Q)))))
                         (expt 2 (+ 1 (* -1 (bias q))))))
         :hints (("Goal" :in-theory (enable a15)))))


      (local
       (encapsulate ()
                   (local (include-book "../../arithmetic/basic"))
                    (defthm arithm-hack-specific
                      (implies (and (<= (DENORMAL-NORM R P Q)
                                        (+ -1 (EXPT 2 (+ -1 P))))
                                    (rationalp r)
                                    (integerp p)
                                    (integerp q)
                                    (> q 0))
                               (<= (+ (EXPT 2 (+ 1 (* -1 P) (EXPO (SPN Q))))
                                      (* (EXPT 2 (+ 1 (* -1 P) (EXPO (SPN Q))))
                                         (denormal-norm r p q)))
                                   (spn q)))
                      :hints (("Goal" :in-theory (e/d (spn denormal-norm
                                                           spd) ())))
                      :rule-classes nil)))


      (defthm maximal-drepp
         (implies (and (drepp r p q)
                       (integerp p)
                       (> p 1)
                       (integerp q)
                       (> q 0)
                       (> r 0)
                       (rationalp r))
                  (<= (+ r (EXPT 2 (+ 1 (* -1 P) (EXPO (SPN Q)))))
                      (spn q)))
         :hints (("Goal" :use ((:instance drepp-implies-denormal-norm-less-than)
                               (:instance spd-mult-specific)
                               (:instance arithm-hack-specific))))
         :rule-classes :linear)


      (defthm drepp-diff
           (implies (and (rationalp r1)
                         (rationalp r2)
                         (> r1 r2)
                         (> r2 0)
                         (integerp p)
                         (integerp q)
                         (> p 1)
                         (> q 0)
                         (drepp r1 p q)
                         (drepp r2 p q))
                    (<= (+ r2 (EXPT 2 (+ 1 (* -1 P) (EXPO (SPN Q)))))
                        r1))
           :hints (("Goal" :use ((:instance spd-mult-specific
                                            (r r1))
                                 (:instance spd-mult-specific
                                            (r r2))
                                 (:instance denormal-normal-monotone
                                            (r1 r2)
                                            (r2 r1)))))
           :rule-classes nil)



   ))



(local
 (encapsulate ()
              (local
               (defthm spd-spd-less-than
                 (implies (and (integerp p)
                               (integerp q)
                               (> p 1)
                               (> q 0))
                          (iff (<= (SPD P Q) A)
                               (<= (EXPT 2 (+ 1 (* -1 P) (EXPO (SPN Q))))
                                   A)))
                 :hints (("Goal" :in-theory (enable spn spd)))))

              (defthm exactp-c-lemma-2
                (implies (and (integerp p)
                              (> p 1)
                              (> x 0)
                              (rationalp a)
                              (integerp q)
                              (> q 0)
                              (rationalp x)
                              (>= a x)
                              (drepp a p q)
                              (<= (abs x) (spn q)))
                         (<= (AWAY X (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))
                             a))
                :hints (("Goal" :cases ((not (>= (+ p (expo x)) (expo (spn q))))))
                        ("Subgoal 2"
                         :in-theory (enable drnd rnd sgn positive-spd)
                         :use ((:instance drnd-exactp-a
                                          (mode 'away))
                               (:instance away-upper-bound
                                          (x x)
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                               (:instance drepp-diff
                                          (r2 a)
                                          (r1 (AWAY X (+ P (EXPO X)
                                                         (* -1 (EXPO (SPN Q)))))))))
                        ("Subgoal 1" :in-theory (enable drnd rnd away cg sgn)
                         :use ((:instance smallest-spd (r a)))))
                :rule-classes :linear)))


(local
   (defthmd drnd-exactp-c-lemma
     (implies (and (rationalp x)
                   (> x 0)
                   (<= (abs x) (spn q))
   		(rationalp a)
                   (drepp a p q)
   		(>= a x)
                   (integerp p)
                   (> p 1)
                   (integerp q)
                   (> q 0)
                   (common-rounding-mode-p mode))
              (>= a (drnd x mode p q)))
     :hints (("Goal" :in-theory (enable sgn drnd rnd))
;fcd/Satriani v3.7 Moore - used to be Subgoal 5
             ("Subgoal 4"
              :use ((:instance near-choice
                               (x x)
                               (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))))
             ("Subgoal 2"
              :use ((:instance near+-choice
                               (x x)
                               (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))))




(local
    (defthm exactp-d-lemma-1
      (IMPLIES (AND (RATIONALP X)
                    (< 0 X)
                    (<= X (SPN Q))
                    (RATIONALP A)
                    (DREPP A P Q)
                    (<= A X)
                    (INTEGERP P)
                    (< 1 P)
                    (INTEGERP Q)
                    (< 0 Q))
            (<= A (AWAY X (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))
      :hints (("Goal"
               :use ((:instance away-lower-bound
                                (x x)
                                (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))
      :rule-classes :linear))



;;    (local
;;     (defthm never-zero-drepp
;;       (not (DREPP 0 P Q))
;;       :hints (("Goal" :in-theory (enable drepp)))))
;;

(local
    (defthm x-less-than-spd-if-negative
      (implies (and (<= (+ P (EXPO X) (* -1 (EXPO (SPN Q)))) 0)
                    (> x 0)
                    (rationalp x)
                    (integerp p)
                    (integerp q)
                    (> q 0))
               (< x (spd p q)))
      :hints (("Goal" :in-theory (enable spd spn)
               :use ((:instance expo-monotone
                                (x (spd p q))
                                (y x)))))))

(local
    (defthm exactp-d-lemma-2
      (IMPLIES (AND (RATIONALP X)
                    (<= X (SPN Q))
                    (< 0 X)
                    (RATIONALP A)
                    (DREPP A P Q)
                    (<= A X)
                    (INTEGERP P)
                    (< 1 P)
                    (INTEGERP Q)
                    (< 0 Q))
            (<= A
                (TRUNC X
                       (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))
      :hints (("Goal" :cases ((not (> (+ p (expo x)) (expo (spn q))))))
              ("Subgoal 2"
               :in-theory (enable drnd rnd sgn positive-spd)
               :use ((:instance drnd-exactp-a
                                (mode 'trunc))
                     (:instance trunc-lower-bound
                               (x x)
                               (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                     (:instance drepp-diff
                               (r1 a)
                               (r2 (trunc X (+ P (EXPO X)
                                               (* -1 (EXPO (SPN Q)))))))))
              ("Subgoal 1" :in-theory (enable drnd rnd spd trunc sgn)
               :use ((:instance smallest-spd (r a))
                     (:instance x-less-than-spd-if-negative))))
     :rule-classes :linear))


(defthmd drnd-exactp-d-lemma
     (implies (and (rationalp x)
                   (<= (abs x) (spn q))
                   (> x 0)
   		(rationalp a)
                   (drepp a p q)
   		(<= a x)
                   (integerp p)
                   (> p 1)
                   (integerp q)
                   (> q 0)
                   (common-rounding-mode-p mode))
              (<= a (drnd x mode p q)))
     :hints (("Goal" :in-theory (enable ieee-mode-p drnd rnd))
; fcd/Satriani v3.7 Moore - used to be Subgoal 1
             ("Subgoal 4"
              :use ((:instance near-choice
                               (x x)
                               (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))))
             ("Subgoal 2"
              :use ((:instance near+-choice
                               (x x)
                               (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))))))




(defthmd drnd-exactp-c
     (implies (and (rationalp x)
                   (<= (abs x) (spn q))
                   (rationalp a)
                   (drepp a p q)
                   (>= a x)
                   (integerp p)
                   (> p 1)
                   (integerp q)
                   (> q 0)
                   (common-rounding-mode-p mode))
              (>= a (drnd x mode p q)))
     :hints (("Goal" :cases ((not (equal x 0)))
              :in-theory (enable drnd-minus flip drepp-minus))
             ("Subgoal 2" :in-theory (enable drnd rnd))
             ("Subgoal 1" :cases ((not (> x 0))))
             ("Subgoal 1.2" :use ((:instance drnd-exactp-c-lemma)))
             ("Subgoal 1.1" :use ((:instance drnd-exactp-d-lemma
                                             (x (* -1 x))
                                             (a (* -1 a))
                                             (mode (flip mode)))))))



(defthmd drnd-exactp-d
     (implies (and (rationalp x)
                   (<= (abs x) (spn q))
   		(rationalp a)
                   (drepp a p q)
   		(<= a x)
                   (integerp p)
                   (> p 1)
                   (integerp q)
                   (> q 0)
                   (common-rounding-mode-p mode))
              (<= a (drnd x mode p q)))
     :hints (("Goal" :cases ((not (equal x 0)))
              :in-theory (enable drnd-minus flip drepp-minus))
             ("Subgoal 2" :in-theory (enable drnd rnd))
             ("Subgoal 1" :cases ((not (> x 0))))
             ("Subgoal 1.2" :use ((:instance drnd-exactp-d-lemma)))
             ("Subgoal 1.1" :use ((:instance drnd-exactp-c-lemma
                                             (x (* -1 x))
                                             (a (* -1 a))
                                             (mode (flip mode)))))))



;----------------------------------------------------------------------

(local
   (encapsulate ()

       (local
        (defthm equal-spd
          (implies (and (integerp p)
                        (integerp q)
                        (> p 1)
                        (> q 0))
                   (equal (spd p q)
                          (EXPT 2 (+ 1 (* -1 P) (EXPO (SPN Q))))))
          :hints (("Goal" :in-theory (enable spd spn bias)))))

       (local
        (defthm x-less-than-spd-if-negative
          (implies (and (<= (+ P (EXPO X) (* -1 (EXPO (SPN Q)))) 0)
                        (> x 0)
                        (rationalp x)
                        (integerp p)
                        (integerp q)
                        (> q 0))
                   (< x (spd p q)))
          :hints (("Goal" :in-theory (enable spd spn)
                   :use ((:instance expo-monotone
                                    (x (spd p q))))))))


       (defthm drnd-non-negative
         (implies (and (< 0 x)
                       (rationalp x)
                       (integerp p)
                       (integerp q)
                       (> p 1)
                       (> q 0)
                       (common-rounding-mode-p mode))
                  (>= (drnd x mode p q) 0))
         :hints (("Goal" :in-theory (enable ieee-mode-p near near+ drnd rnd)))
         :rule-classes (:type-prescription :linear))



       (defthm drnd-diff-lemma
         (implies (and (rationalp x)
                       (<= x (spn q))
                       (> x 0)
                       (integerp p)
                       (> p 1)
                       (integerp q)
                       (> q 0)
                       (common-rounding-mode-p mode))
                  (< (abs (- x (drnd x mode p q))) (spd p q)))
         :hints (("Goal" :cases ((not (> (+ p (expo x)) (expo (spn q))))))
                 ("Subgoal 2" :in-theory (enable drnd)
                  :use ((:instance rnd-diff
                                   (n (+ P (EXPO X) (* -1 (EXPO (SPN
                                                                 Q))))))))
                 ("Subgoal 1"
                  :use ((:instance drnd-exactp-c
                                   (a (spd p q)))
                        (:instance drepp-spd)
                        (:instance x-less-than-spd-if-negative)))))))

(defthm drnd-diff
        (implies (and (rationalp x)
                   (<= (abs x) (spn q))
                   (integerp p)
                   (> p 1)
                   (integerp q)
                   (> q 0)
                   (common-rounding-mode-p mode))
              (< (abs (- x (drnd x mode p q))) (spd p q)))
     :hints (("Goal" :cases ((not (equal x 0))))
             ("Subgoal 2" :in-theory (enable drnd rnd spd))
             ("Subgoal 1" :cases ((not (> x 0))))
             ("Subgoal 1.2" :use ((:instance drnd-diff-lemma)))
             ("Subgoal 1.1" :in-theory (enable flip drnd drnd-minus)
              :use ((:instance drnd-diff-lemma
                               (x (* -1 x))
                               (mode (flip mode)))))))



;----------------------------------------------------------------------

(encapsulate ()

             (local
              (defthm drnd-near-est-lemma-1
                (implies (and (rationalp x)
                              (equal (expo a) (expo x))
                              (<= x (spn q))
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near p q)))))
                :hints (("Goal"
                         :in-theory (enable rnd drnd bias DREPP spn)
                         :use ((:instance near2
                                          (y a)
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))))



             (local
              (defthm rationalp-drepp
                (implies (drepp a p q)
                         (rationalp a))
                :hints (("Goal" :in-theory (enable drepp)))
                :rule-classes :forward-chaining))

             (local
              (defthm drnd-near-est-lemma-2-1
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (equal (- x (trunc x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                                     (- (away x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))) x))
                              (> a 0)
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near p q)))))
                :hints (("Goal" :in-theory (enable drnd rnd)
                         :use ((:instance near-choice (x x)
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))))


             (local
              (defthm drnd-near-est-lemma-2-2
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (not (equal (expo x) (expo a)))
                              (<  (- x (trunc x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                                  (- (away x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))) x))
                              (> a 0)
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near p q)))))
                :hints (("Goal" :in-theory (enable drnd rnd)
                         :do-not '(fertilize)
                         :use ((:instance near1-a
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                               (:instance trunc-upper-bound
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))))




             (local
              (defthm drnd-near-est-lemma-2-3
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (not (equal (expo x) (expo a)))
                              (>  (- x (trunc x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                                  (- (away x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))) x))
                              (> a 0)
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near p q)))))
                :hints (("Goal" :in-theory (enable drnd rnd)
                         :do-not '(fertilize)
                         :use ((:instance near1-b
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                               (:instance away-lower-bound
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))))





             (local
              (defthm drnd-near-est-lemma-2
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (not (equal (expo a) (expo x)))
                              (> a 0)
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near p q)))))
                :hints (("Goal" :cases ((not (equal (- x (trunc x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                                                    (- (away x (+ P (EXPO X) (* -1 (EXPO (SPN
                                                                                          Q))))) x))))
                         :in-theory (disable abs drnd))
                        ("Subgoal 2" :use ((:instance drnd-near-est-lemma-2-1)))
                        ("Subgoal 1" :cases ((not (< (- x (trunc x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                                                     (- (away x (+ P (EXPO X) (* -1 (EXPO (SPN
                                                                                           Q))))) x)))))
                        ("Subgoal 1.2" :use ((:instance drnd-near-est-lemma-2-2)))
                        ("Subgoal 1.1" :use ((:instance drnd-near-est-lemma-2-3))))))




             (local
              (defthm drnd-near-est-lemma-3
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (not (equal (expo a) (expo x)))
                              (< a 0)
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near p q)))))
                :hints (("Goal" :use ((:instance smallest-spd (r a))
                                      (:instance drnd-diff
                                                 (mode 'near)))))))



             (local
              (defthm never-zero-drepp
                (not (DREPP 0 P Q))
                :hints (("Goal" :in-theory (enable drepp)))))

             (local
              (defthm drnd-near-est-lemma
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near p q)))))
                :hints (("Goal" :cases ((not (equal (expo a) (expo x)))))
                        ("Subgoal 2" :use ((:instance drnd-near-est-lemma-1)))
                        ("Subgoal 1":cases ((not (equal a 0))))
                        ("Subgoal 1.1":cases ((not (> a 0))))
                        ("Subgoal 1.1.2":use ((:instance drnd-near-est-lemma-2)))
                        ("Subgoal 1.1.1":use ((:instance drnd-near-est-lemma-3))))))

    (defthm drnd-near-est
      (implies (and (rationalp x)
                    (<= (abs x) (spn q))
                    (integerp p)
                    (> p 1)
                    (integerp q)
                    (> q 0)
                    (drepp a p q))
               (>= (abs (- x a)) (abs (- x (drnd x 'near p q)))))
      :hints (("Goal" :cases ((not (equal x 0))))
              ("Subgoal 2" :in-theory (enable drnd rnd))
              ("Subgoal 1" :cases ((not (> x 0))))
              ("Subgoal 1.2" :use ((:instance drnd-near-est-lemma)))
              ("Subgoal 1.1" :use ((:instance drnd-near-est-lemma
                                              (x (* -1 x))
                                              (a (* -1 a))))
               :in-theory (enable drnd-minus))))

             )

;----------------------------------------------------------------------

(encapsulate ()

             (local
              (defthm drnd-near+-est-lemma-1
                (implies (and (rationalp x)
                              (equal (expo a) (expo x))
                              (<= x (spn q))
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near+ p q)))))
                :hints (("Goal"
                         :in-theory (enable rnd drnd bias DREPP spn)
                         :use ((:instance near+2
                                          (y a)
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))))




             (local
              (defthm rationalp-drepp
                (implies (drepp a p q)
                         (rationalp a))
                :hints (("Goal" :in-theory (enable drepp)))
                :rule-classes :forward-chaining))



             (local
              (defthm drnd-near+-est-lemma-2-1
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (equal (- x (trunc x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                                     (- (away x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))) x))
                              (> a 0)
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near+ p q)))))
                :hints (("Goal" :in-theory (enable drnd rnd)
                         :use ((:instance near+-choice (x x)
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))))


;----------------------------------------------------------------------



             (local
              (defthm drnd-near+-est-lemma-2-2
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (not (equal (expo x) (expo a)))
                              (<  (- x (trunc x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                                  (- (away x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))) x))
                              (> a 0)
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near+ p q)))))
                :hints (("Goal" :in-theory (enable drnd rnd)
                         :do-not '(fertilize)
                         :use ((:instance near+1-a
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                               (:instance trunc-upper-bound
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))))

             (local
              (defthm drnd-near+-est-lemma-2-3
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (not (equal (expo x) (expo a)))
                              (>  (- x (trunc x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                                  (- (away x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))) x))
                              (> a 0)
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near+ p q)))))
                :hints (("Goal" :in-theory (enable drnd rnd)
                         :do-not '(fertilize)
                         :use ((:instance near+1-b
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                               (:instance away-lower-bound
                                          (n (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))))))


             (local
              (defthm drnd-near+-est-lemma-2
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (not (equal (expo a) (expo x)))
                              (> a 0)
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near+ p q)))))
                :hints (("Goal" :cases ((not (equal (- x (trunc x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                                                    (- (away x (+ P (EXPO X) (* -1 (EXPO (SPN
                                                                                          Q))))) x))))
                         :in-theory (disable abs drnd))
                        ("Subgoal 2" :use ((:instance drnd-near+-est-lemma-2-1)))
                        ("Subgoal 1" :cases ((not (< (- x (trunc x (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))
                                                     (- (away x (+ P (EXPO X) (* -1 (EXPO (SPN
                                                                                           Q))))) x)))))
                        ("Subgoal 1.2" :use ((:instance drnd-near+-est-lemma-2-2)))
                        ("Subgoal 1.1" :use ((:instance drnd-near+-est-lemma-2-3))))))


;----------------------------------------------------------------------

             (local
              (defthm drnd-near+-est-lemma-3
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (not (equal (expo a) (expo x)))
                              (< a 0)
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near+ p q)))))
                :hints (("Goal" :use ((:instance smallest-spd (r a))
                                      (:instance drnd-diff
                                                 (mode 'near+)))))))


             (local
              (defthm never-zero-drepp
                (not (DREPP 0 P Q))
                :hints (("Goal" :in-theory (enable drepp)))))



             (local
              (defthm drnd-near+-est-lemma
                (implies (and (rationalp x)
                              (<= x (spn q))
                              (> x 0)
                              (integerp p)
                              (> p 1)
                              (integerp q)
                              (> q 0)
                              (drepp a p q))
                         (>= (abs (- x a)) (abs (- x (drnd x 'near+ p q)))))
                :hints (("Goal" :cases ((not (equal (expo a) (expo x)))))
                        ("Subgoal 2" :use ((:instance drnd-near+-est-lemma-1)))
                        ("Subgoal 1":cases ((not (equal a 0))))
                        ("Subgoal 1.1":cases ((not (> a 0))))
                        ("Subgoal 1.1.2":use ((:instance drnd-near+-est-lemma-2)))
                        ("Subgoal 1.1.1":use ((:instance drnd-near+-est-lemma-3))))))

     (defthm drnd-near+-est
       (implies (and (rationalp x)
                     (<= (abs x) (spn q))
                     (integerp p)
                     (> p 1)
                     (integerp q)
                     (> q 0)
                     (drepp a p q))
                (>= (abs (- x a)) (abs (- x (drnd x 'near+ p q)))))
       :hints (("Goal" :cases ((not (equal x 0))))
               ("Subgoal 2" :in-theory (enable drnd rnd))
               ("Subgoal 1" :cases ((not (> x 0))))
               ("Subgoal 1.2" :use ((:instance drnd-near+-est-lemma)))
               ("Subgoal 1.1" :use ((:instance drnd-near+-est-lemma
                                               (x (* -1 x))
                                               (a (* -1 a))))
                :in-theory (enable drnd-minus))))

             )

;;
;; Sat Feb  4 12:35:01 2006 finally!
;;
;----------------------------------------------------------------------


(encapsulate ()


   (local (encapsulate ()

          (defthm fl-expt-n-minus-1-minus-1
            (implies (and (rationalp x)
                          (case-split (not (equal x 0)))
                          (integerp n)
                          (<= n 0))
                     (equal (fl (* -1 (sig x) (expt 2 (+ -1 n))))
                            -1))
            :hints (("Goal" :use ((:instance fl-1/2-sig-x-is-zero-lemma-2
                                             (y (expt 2 (+ -1 n))))
                                  (:instance expt-weak-monotone-linear
                                             (n (+ -1 n))
                                             (m -1))))))


         (defthm n-zero-away-reduce
           (implies (and (rationalp x)
                         (> x 0)
                         (integerp n)
                         (<= n 0))
                    (equal (away x n)
                           (EXPT 2 (+ 1 (EXPO X) (* -1 n)))))
           :hints (("Goal" :in-theory (enable sgn away cg))))


         (defthm drnd-lemma-trunc-small
           (implies (and (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x)
                         (<= (+ p (expo x)) (expo (spn q))))
                    (equal (drnd x 'trunc p q)  0))
           :hints (("Goal" :in-theory (enable drnd rnd))))


         (defthm drnd-lemma-away-small
           (implies (and (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x)
                         (<= (+ p (expo x)) (expo (spn q))))
                    (equal (drnd x 'away p q)
                           (expt 2 (+ 1 (EXPO (SPN Q)) (* -1 p)))))
           :hints (("Goal" :in-theory (enable drnd rnd))))



         (defthm drnd-lemma-minf-small
           (implies (and (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x)
                         (<= (+ p (expo x)) (expo (spn q))))
                    (equal (drnd x 'minf p q)  0))
           :hints (("Goal" :in-theory (enable drnd rnd))))



         (defthm drnd-lemma-inf-small
           (implies (and (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x)
                         (<= (+ p (expo x)) (expo (spn q))))
                    (equal (drnd x 'inf p q)
                           (expt 2 (+ 1 (EXPO (SPN Q)) (* -1 p)))))
           :hints (("Goal" :in-theory (enable drnd rnd))))



         (local
          (defthm local-expt-expand
            (implies (and (integerp p)
                          (integerp q)
                          (> q 0))
                     (equal (EXPT 2 (+ 1 (* -1 P) (EXPO (SPN Q))))
                            (* 2 (expt 2 (+  (* -1 p) (expo (spn q)))))))
            :hints (("Goal" :use ((:instance a15 (i 2) (j1 1)
                                             (j2 (+ (* -1 P) (EXPO (SPN Q))))))))))


         (defthm drnd-lemma-near-small-1
           (implies (and (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x)
                         (< x (expt 2 (+ (* -1 p) (expo (spn q)))))
                         (<= (+ p (expo x)) (expo (spn q))))
                    (equal (drnd x 'near p q)
                           0))
           :hints (("Goal" :in-theory (enable drnd rnd)
                    :use ((:instance near1-a (n (+ p (expo x) (* -1 (expo (spn
                                                                           q))))))))))


         (defthm drnd-lemma-near-small-2
           (implies (and (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x)
                         (> x (expt 2 (+ (* -1 p) (expo (spn q)))))
                         (<= (+ p (expo x)) (expo (spn q))))
                    (equal (drnd x 'near p q)
                           (expt 2 (+ 1 (EXPO (SPN Q)) (* -1 p)))))
           :hints (("Goal" :in-theory (enable drnd rnd)
                    :use ((:instance near1-b (n (+ p (expo x) (* -1 (expo (spn q))))))))))




         (defthm drnd-lemma-near+-small-1
           (implies (and (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x)
                         (< x (expt 2 (+ (* -1 p) (expo (spn q)))))
                         (<= (+ p (expo x)) (expo (spn q))))
                    (equal (drnd x 'near+ p q)
                           0))
           :hints (("Goal" :in-theory (enable drnd rnd)
                    :use ((:instance near+1-a (n (+ p (expo x) (* -1 (expo (spn
                                                                            q))))))))))


         (defthm drnd-lemma-near+-small-2
           (implies (and (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x)
                         (> x (expt 2 (+ (* -1 p) (expo (spn q)))))
                         (<= (+ p (expo x)) (expo (spn q))))
                    (equal (drnd x 'near+ p q)
                           (expt 2 (+ 1 (EXPO (SPN Q)) (* -1 p)))))
           :hints (("Goal" :in-theory (enable drnd rnd)
                    :use ((:instance near+1-b (n (+ p (expo x) (* -1 (expo (spn q))))))))))


         (encapsulate ()
                      (local
                       (defthm spd-/2-rewrite
                         (implies (and (integerp p)
                                       (integerp q)
                                       (> q 0))
                                  (equal (/ (spd p q) 2)
                                         (expt 2 (+ (* -1 p) (expo (spn q))))))
                         :hints (("Goal" :in-theory (enable spd spn)
                                  :use ((:instance a15 (i 2) (j1 1)
                                                   (j2 (+ 1 (* -1 P) (* -1 (BIAS Q))))))))))

                      (local
                       (defthm less-than-1/2-spd-implies-expo-x-small
                         (implies (and (< x (expt 2 (+ (* -1 p) (expo (spn q)))))
                                       (> x 0)
                                       (rationalp x)
                                       (integerp p)
                                       (integerp q)
                                       (> q 0))
                                  (<= (+ p (expo x)) (expo (spn q))))
                         :hints (("Goal" :use ((:instance expo-monotone
                                                          (x x)
                                                          (y (expt 2 (+ (* -1 p) (expo (spn
                                                                                        q)))))))
                                  :in-theory (enable expo-2**n)))))

                      (defthmd drnd-tiny
                        (implies (and (common-rounding-mode-p mode)
                                      (natp p)
                                      (> p 1)
                                      (natp q)
                                      (> q 0)
                                      (rationalp x)
                                      (< 0 x)
                                      (< x (/ (spd p q) 2)))
                                 (equal (drnd x mode p q)
                                        (if (member mode '(away inf))
                                            (spd p q)
                                          0)))
                        :hints (("Goal" :in-theory (enable ieee-mode-p))
                                ("Subgoal 1" :in-theory (disable spd-/2-rewrite) :use spd-/2-rewrite)
                                ("Subgoal 2" :in-theory (disable spd-/2-rewrite) :use spd-/2-rewrite)))

                      (defthm drnd-tiny-equal-lemma
                        (implies (and (common-rounding-mode-p mode)
                                      (natp p)
                                      (> p 1)
                                      (natp q)
                                      (> q 0)
                                      (rationalp x)
                                      (< 0 x)
                                      (< x (/ (spd p q) 2))
                                      (rationalp y)
                                      (< 0 y)
                                      (< y (/ (spd p q) 2)))
                                 (equal (drnd x mode p q)
                                        (drnd y mode p q)))
                        :hints (("Goal" :in-theory (enable ieee-mode-p)))
                        :rule-classes nil))


         (defthm sticky-never-increase-over-expt
           (implies (and (< x (expt 2 k))
                         (integerp k)
                         (rationalp x)
                         (> x 0)
                         (> n 0)
                         (integerp n))
                    (< (sticky x n)
                       (expt 2 k)))
           :hints (("Goal" :use ((:instance expo-sticky)
                                 (:instance expo-monotone
                                            (x (expt 2 k))
                                            (y (sticky x n)))
                                 (:instance expt-weak-monotone-linear
                                            (n k)
                                            (m (expo x)))
                                 (:instance expo-lower-bound
                                            (x x))))))

         (defthm sticky-preserves-inequality
           (implies  (and (< x (expt 2 (+ (* -1 p) (expo (spn q)))))
                          (rationalp x)
                          (> x 0)
                          (> n 0)
                          (integerp n)
                          (integerp p)
                          (integerp q)
                          (> p 1)
                          (> q 0))
                     (< (sticky x n)
                        (expt 2 (+ (* -1 p) (expo (spn q))))))
           :hints (("Goal"  :use ((:instance sticky-never-increase-over-expt
                                             (k (+ (* -1 p)
                                                   (expo (spn q)))))))))

         (defthm greater-than-1/2-spd-implies-n-no-less-than-2
           (implies (and (> x (expt 2 (+ (* -1 p) (expo (spn q)))))
                         (rationalp x)
                         (> x 0)
                         (> n 0)
                         (integerp n)
                         (integerp p)
                         (integerp q)
                         (>= n (+ p (expo x) (- (expo (spn q))) 2))
                         (> p 1)
                         (> q 0))
                    (>= n 2))
           :hints (("Goal" :use ((:instance expo-monotone
                                            (x (expt 2 (+ (* -1 p) (expo (spn q)))))
                                            (y x)))
                    :in-theory (enable expo-2**n)))
           :rule-classes nil)

         (local
          (defthm trunc-1-m-is-1
            (implies (and (integerp n)
                          (> n 0))
                     (equal (trunc 1 n)
                            1))
            :hints (("Goal" :in-theory (enable trunc a15)))))

         (defthm trunc-2**n
           (implies (and (integerp n)
                         (integerp m)
                         (> m 0))
                    (equal (trunc (expt 2 n) m)
                           (expt 2 n)))
           :hints (("Goal" :use ((:instance trunc-shift
                                            (x 1)
                                            (k n)
                                            (n m)))
                    :in-theory (enable trunc))))


         (defthm sticky-preserves-inequality-2-strong
           (implies  (and (> x (expt 2 (+ (* -1 p) (expo (spn q)))))
                          (rationalp x)
                          (> x 0)
                          (> n 0)
                          (integerp n)
                          (integerp p)
                          (integerp q)
                          (>= n (+ p (expo x) (- (expo (spn q))) 2))
                          (> p 1)
                          (> q 0))
                     (> (sticky x n)
                        (expt 2 (+ (* -1 p) (expo (spn q))))))
           :hints (("Goal" :in-theory (enable sticky trunc-shift sgn)
                    :use ((:instance trunc-monotone
                                     (x (expt 2 (+ (* -1 p) (expo (spn q)))))
                                     (y x)
                                     (n (+ -1 n)))
                          (:instance greater-than-1/2-spd-implies-n-no-less-than-2)))))


         (defthm exactp-expt-2-1
           (implies (and (integerp n)
                         (integerp m)
                         (> n 0))
                    (exactp (expt 2 m) n))
           :hints (("Goal" :in-theory (enable a15 sig exactp))))


         (defthm equal-x-1/2-spd-sticky-n-1/2-spd
           (implies (and (integerp p)
                         (integerp n)
                         (integerp q)
                         (> p 1)
                         (> q 0)
                         (> n 0))
                    (equal (sticky (expt 2 (+ (* -1 p) (expo (spn q)))) n)
                           (expt 2 (+ (* -1 p) (expo (spn q))))))
           :hints (("Goal" :in-theory (e/d (expo-2**n sticky)
                                           (exactp-expt-2-1))
                    :use ((:instance exactp-expt-2-1
                                     (m (+ (* -1 P) (EXPO (SPN Q))))
                                     (n (+ -1 n)))))))


         (defthm expo-sticky-strong
           (implies (and (rationalp x)
                         (integerp n) (> n 0))
                    (= (expo (sticky x n))
                       (expo x)))
           :hints (("Goal" :cases ((not (> x 0)))
                    :in-theory (enable expo-minus sticky-minus))
                   ("Subgoal 2" :use ((:instance expo-sticky)))
                   ("Subgoal 1" :use ((:instance expo-sticky
                                                 (x (* -1 x)))))))


;----------------------------------------------------------------------

         (defthm n-equal-zero-implies-ultra-small
           (implies (and (>= 0 (+ p (expo x) (- (expo (spn q))) 2))
                         (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x))
                    (< x (expt 2 (+ -1 (* -1 p) (expo (spn q))))))
           :hints (("Goal" :use ((:instance expo-upper-bound)
                                 (:instance expt-weak-monotone-linear
                                            (n (+ 1 (expo x)))
                                            (m (+ -1 (* -1 p) (expo (spn q)))))))))


         ;; (i-am-here) ;; Sun Oct 15 18:19:29 2006



         (defthm sticky-0-reduce
           (implies (and (> x 0)
                         (rationalp x))
                    (equal (sticky x 0)
                           (EXPT 2 (1+ (EXPO X)))))
           :hints (("Goal" :in-theory (e/d (sticky exactp sgn)
                                           (sig-lower-bound
                                            sig-upper-bound))
                    :use ((:instance  sig-lower-bound)
                          (:instance sig-upper-bound)))))



         (defthm small-fl-is-minus-1
           (implies (and (rationalp x)
                         (> x 0)
                         (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (< x (expt 2 (+ -1 (* -1 p) (expo (spn q))))))
                    (equal (FL (* -1 (SIG X)
                                  (EXPT 2
                                        (+ -1 P (EXPO X)
                                           (* -1 (EXPO (SPN Q)))))))
                           -1))
           :hints (("Goal" :use ((:instance fl-1/2-sig-x-is-zero-2)
                                 (:instance expo-monotone
                                            (x x)
                                            (y (expt 2 (+ -1 (* -1 p) (expo (spn q))))))))))


         (defthm small-fl-is-zero-1
           (implies (and (rationalp x)
                         (> x 0)
                         (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (< x (expt 2 (+ -1 (* -1 p) (expo (spn q))))))
                    (equal (FL (* (SIG X)
                                  (EXPT 2
                                        (+ -1 P (EXPO X)
                                           (* -1 (EXPO (SPN Q)))))))
                           0))
           :hints (("Goal" :use ((:instance fl-1/2-sig-x-is-zero)
                                 (:instance expo-monotone
                                            (x x)
                                            (y (expt 2 (+ -1 (* -1 p) (expo (spn q))))))))))




         (defthm small-fl-is-minus-1-v2
           (implies (and (rationalp x)
                         (> x 0)
                         (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (< x (expt 2 (+ -1 (* -1 p) (expo (spn q))))))
                    (equal (FL (* -1 (SIG (EXPT 2 (+ 1 (EXPO X))))
                                  (EXPT 2
                                        (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))
                           -1))
           :hints (("Goal" :use ((:instance fl-1/2-sig-x-is-zero-2
                                            (x (expt 2 (+ 1 (expo x)))))
                                 (:instance expo-monotone
                                            (x x)
                                            (y (expt 2 (+ -1 (* -1 p) (expo (spn q))))))))))



         (defthm small-fl-is-zero-1-v2
           (implies (and (rationalp x)
                         (> x 0)
                         (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (< x (expt 2 (+ -1 (* -1 p) (expo (spn q))))))
                    (equal (FL (* (SIG (EXPT 2 (+ 1 (EXPO X))))
                                  (EXPT 2
                                        (+ P (EXPO X) (* -1 (EXPO (SPN Q)))))))
                           0))
           :hints (("Goal" :use ((:instance fl-1/2-sig-x-is-zero
                                            (x (expt 2 (+ 1 (expo x)))))
                                 (:instance expo-monotone
                                            (x x)
                                            (y (expt 2 (+ -1 (* -1 p) (expo (spn q))))))))))


         ;; (defthm expo-monotone-strong
         ;;   (implies (and (< x (expt 2 n))
         ;;                 (equal
         ;;             (rationalp x)


         (defthm small-small-lemma
           (implies (<= (+ 2 P (EXPO X)) (EXPO (SPN Q)))
                    (<= (+ -1 p (expo x) (* -1 (expo (spn q))))
                        -3)))

         (defthm small-small-lemma-2
           (implies (<= (+ 2 P (EXPO X)) (EXPO (SPN Q)))
                    (<= (+ p (expo x) (* -1 (expo (spn q))))
                        -2)))

         (defthm small-is-small
           (implies (and (>= 0 (+ p (expo x) (- (expo (spn q))) 2))
                         (rationalp x)
                         (> x 0)
                         (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0))
                    (> 1
                       (* 2 (SIG X)
                          (EXPT 2
                                (+ -1 P (EXPO X)
                                   (* -1 (EXPO (SPN q))))))))
           :hints (("Goal" :use ((:instance sig-upper-bound)
                                 (:instance expt-weak-monotone-linear
                                            (n (+ -1 P (EXPO X)
                                                  (* -1 (EXPO (SPN q)))))
                                            (m -3)))))
           :rule-classes :linear)

         (encapsulate ()
                      (local
                       (defthm sig-expt-fact
                         (implies (integerp n)
                                  (equal (sig (expt 2 n)) 1))
                         :hints (("Goal" :in-theory (enable sig a15)))))

                      (defthm small-is-small-v2
                        (implies (and (>= 0 (+ p (expo x) (- (expo (spn q))) 2))
                                      (rationalp x)
                                      (> x 0)
                                      (natp p)
                                      (> x 0)
                                      (> p 1)
                                      (natp q)
                                      (> q 0))
                                 (> 1
                                    (* 2 (SIG (EXPT 2 (+ 1 (EXPO X))))
                                       (EXPT 2
                                             (+ P (EXPO X) (* -1 (EXPO (SPN Q))))))))
                        :hints (("Goal" :use ((:instance expt-weak-monotone-linear
                                                         (n (+ P (EXPO X)
                                                               (* -1 (EXPO (SPN q)))))
                                                         (m -2)))))
                        :rule-classes :linear))




         (defthm extra-small-drnd-is-equal
           (implies (and (< x (expt 2 (+ -1 (* -1 p) (expo (spn q)))))
                         (>= 0 (+ p (expo x) (- (expo (spn q))) 2))
                         (> x 0)
                         (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x))
                    (equal (drnd (sticky x 0) mode p q)
                           (drnd x mode p q)))
           :hints (("Goal" :in-theory (enable drnd trunc sgn cg near+ near away rnd sticky))))


         (defthm drnd-sticky-lemma
           (implies (and (common-rounding-mode-p mode)
                         (natp p)
                         (> x 0)
                         (> p 1)
                         (natp q)
                         (> q 0)
                         (rationalp x)
                         (<= x (spn q))
                         (>= n 0)
                         (integerp n)
                         (>= n (+ p (expo x) (- (expo (spn q))) 2)))
                    (equal (drnd (sticky x n) mode p q)
                           (drnd x mode p q)))
           :hints (("Goal" :cases ((not (> (+ p (expo x)) (expo (spn q))))))
                   ("Subgoal 2" :cases ((not (equal n 0))))
                   ("Subgoal 2.1"  :use ((:instance rnd-sticky
                                                    (m (+ p (expo x)
                                                          (- (expo (spn q)))))))
                    :in-theory (enable drnd))
                   ("Subgoal 1" :in-theory (e/d (common-rounding-mode-p
                                                 sticky-positive ieee-mode-p)
                                                (drnd rnd))
                    :cases ((not (equal x (expt 2 (+ (* -1 p)
                                                     (expo (spn q))))))))
                   ("Subgoal 1.1"  :cases ((not (equal n 0))))
                   ("Subgoal 1.1.2" :use ((:instance extra-small-drnd-is-equal)
                                          (:instance
                                           n-equal-zero-implies-ultra-small)))
                   ("Subgoal 1.1.1" :cases ((not (> x (expt 2 (+ (* -1 p)
                                                                 (expo (spn q)))))))))
           :rule-classes nil)))


  (defthm drnd-sticky
    (implies (and (common-rounding-mode-p mode)
		  (natp p)
		  (> p 1)
		  (natp q)
		  (> q 0)
		  (rationalp x)
                  (<= (abs x) (spn q))
		  (natp n)
		  (>= n (+ p (expo x) (- (expo (spn q))) 2)))
	     (equal (drnd (sticky x n) mode p q)
		    (drnd x mode p q)))
    :rule-classes ()
    :hints (("Goal" :cases ((not (equal x 0)))
             :in-theory (enable sticky-minus expo-minus
                                drnd-minus flip))
            ("Subgoal 1" :cases ((not (> x 0))))
            ("Subgoal 1.2" :use ((:instance drnd-sticky-lemma)))
            ("Subgoal 1.1" :use ((:instance drnd-sticky-lemma
                                            (x (* -1 x))
                                            (mode (flip mode)))))))




  (defthmd drnd-tiny
    (implies (and (common-rounding-mode-p mode)
                  (natp p)
                  (> p 1)
                  (natp q)
                  (> q 0)
                  (rationalp x)
                  (< 0 x)
                  (< x (/ (spd p q) 2)))
             (equal (drnd x mode p q)
                    (if (member mode '(away inf))
                        (spd p q)
                       0))))

  (defthm drnd-tiny-equal
    (implies (and (common-rounding-mode-p mode)
                  (natp p)
                  (> p 1)
                  (natp q)
                  (> q 0)
                  (rationalp x)
                  (< 0 x)
                  (< (abs x) (/ (spd p q) 2))
                  (rationalp y)
                  (< 0 y)
                  (< (abs y) (/ (spd p q) 2)))
             (equal (drnd x mode p q)
                    (drnd y mode p q)))
    :hints (("Goal" :use ((:instance drnd-tiny-equal-lemma))))
    :rule-classes nil)

)

;----------------------------------------------------------------------
(encapsulate ()

 (local (encapsulate ()

                     ;; (defthm plus-rnd
                     ;;   (implies (and (rationalp x)
                     ;;                 (>= x 0)
                     ;;                 (rationalp y)
                     ;;                 (>= y 0)
                     ;;                 (integerp k)
                     ;;                 (exactp x (+ -1 k (- (expo x) (expo y))))
                     ;;                 (common-rounding-mode-p mode))
                     ;;            (= (+ x (rnd y mode k))
                     ;;               (rnd (+ x y)
                     ;;                    mode
                     ;;                    (+ k (- (expo (+ x y)) (expo y))))))
                     ;;   :hints (("Goal" :use ((:instance plus-rnd---rtl-rel5-support))))
                     ;;   :rule-classes ())

                     (defthm exactp-spn-fact
                       (implies (and (integerp p)
                                     (> p 1)
                                     (integerp q)
                                     (> q 0))
                                (EXACTP (SPN Q) (+ -1 P)))
                       :hints (("Goal" :in-theory (enable spn exactp-2**n))))

                     (defthm exactp-spn-fact-2
                       (implies (and (integerp p)
                                     (> p 1)
                                     (integerp q)
                                     (> q 0))
                                (EXACTP (SPN Q) P))
                       :hints (("Goal" :in-theory (enable spn exactp-2**n))))

                     (defthm exactp-spn-fact-3
                       (implies (and (integerp p)
                                     (> p 1)
                                     (integerp q)
                                     (> q 0))
                                (EXACTP (* 2 (SPN Q)) P))
                       :hints (("Goal" :in-theory (enable spn exactp-2**n)
                                :use ((:instance a15 (i 2) (j1 1) (j2 (+ 1 (* -1 (BIAS Q)))))))))


                     ;; (defthm expo-unique
                     ;;   (implies (and (<= (expt 2 n) (abs x))
                     ;;                 (< (abs x) (expt 2 (1+ n)))
                     ;;                 (rationalp x)
                     ;;                 (integerp n))
                     ;;            (equal n (expo x)))
                     ;;   :rule-classes ())


                     (encapsulate ()
                                  (local
                                   (defthm local-expt-expand
                                     (implies (integerp n)
                                              (equal (EXPT 2 (+ 1 n))
                                                     (* 2 (expt 2 n))))
                                     :hints (("Goal" :use ((:instance a15 (i 2) (j1 1)
                                                                      (j2 n)))))))

                                  (defthm expo-x-plus-spn-equal-expo-spn-lemma
                                    (implies (and (rationalp x)
                                                  (> x 0)
                                                  (< x (expt 2 n))
                                                  (integerp n))
                                             (equal (expo (+ x (expt 2 n)))
                                                    n))
                                    :hints (("Goal" :use ((:instance expo-unique
                                                                     (x (+ x (expt 2 n)))
                                                                     (n n)))
                                             :in-theory (enable expo-2**n
                                                                spn)))
                                    :rule-classes nil))


                     (defthm expo-x-plus-spn-equal-expo-spn
                       (implies (and (rationalp x)
                                     (> x 0)
                                     (< x (spn q))
                                     (integerp q)
                                     (> q 0))
                                (equal (expo (+ x (spn q)))
                                       (expo (spn q))))
                       :hints (("Goal" :in-theory (e/d (spn expo-2**n) ())
                                :use ((:instance expo-x-plus-spn-equal-expo-spn-lemma
                                                 (n (expo (spn q))))))))




                     (defthmd drnd-rewrite-lemma
                       (implies (and (rationalp x)
                                     (>= x 0)
                                     (<= x (spn q))
                                     (common-rounding-mode-p mode)
                                     (integerp p)
                                     (> p 1)
                                     (integerp q)
                                     (> q 0))
                                (equal (drnd x mode p q)
                                       (- (rnd (+ x (* (sgn x) (spn q))) mode p)
                                          (* (sgn x) (spn q)))))
                       :hints (("Goal" :cases ((not (equal x (spn q)))))
                               ("Subgoal 2" :in-theory (e/d (drnd sgn)
                                                            (rnd-exactp-b))
                                :use ((:instance rnd-exactp-b (x (spn q))
                                                 (n p))
                                      (:instance rnd-exactp-b (x (* 2 (spn q)))
                                                 (n p))))
                               ("Subgoal 1" :use ((:instance
                                                   plus-rnd
                                                             (x (spn q))
                                                             (y x)
                                                             (k (+ p (expo x) (* -1 (expo (spn q)))))))
                                :in-theory (e/d (drnd sgn bias exactp-2**n) (common-rounding-mode-p)))))


                      (defthm collect-neg-specific
                        (equal (+ (* -1 X) (* -1 (SGN X) (SPN Q)))
                               (* -1 (+ x (* (sgn x) (spn q))))))))

        (defthmd drnd-rewrite
          (implies (and (rationalp x)
                        (<= (abs x) (spn q))
                        (common-rounding-mode-p mode)
                        (integerp p)
                        (> p 1)
                        (integerp q)
                        (> q 0))
                   (equal (drnd x mode p q)
                          (- (rnd (+ x (* (sgn x) (spn q))) mode p)
                             (* (sgn x) (spn q)))))
          :hints (("Goal" :cases ((not (>= x 0))))
                  ("Subgoal 2" :use ((:instance drnd-rewrite-lemma)))
                  ("Subgoal 1" :use ((:instance drnd-rewrite-lemma
                                                (x (* -1 x))
                                                (mode (flip mode))))
                   :in-theory (enable drnd-minus sgn-minus
                                      rnd-minus expo-minus flip))))

        )

;----------------------------------------------------------------------
