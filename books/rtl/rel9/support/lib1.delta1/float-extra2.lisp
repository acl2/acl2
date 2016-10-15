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

;; (include-book "log")

(set-enforce-redundancy nil)

(include-book "../lib1/top")

(set-inhibit-warnings "theory") ; avoid warning in the next event


(encapsulate ()
 (local
 (defthm lemma-expt-muliply-2-reduce
   (implies (integerp y)
            (equal (* 2 (expt 2 y))
                   (expt 2 (+ 1 y))))
   :hints (("Goal" :expand (expt 2 (+ 1 y))
            :in-theory (enable expt-split)))))


(defthmd smallest-spn
  (implies (and (nrepp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 1))
           (>= (abs x) (spn q)))
  :hints (("Goal" :in-theory (enable abs nrepp spn
                                     expo-minus)
           :cases ((< 0 x)))
          ("Subgoal 2" :use ((:instance expo<= (n (* -1 (bias q)))
                                        (x (* -1 x)))))
          ("Subgoal 1" :use ((:instance expo<= (n (* -1 (bias q)))))))
  :rule-classes
  ((:rewrite :match-free :once))))



;; (defund dencodingp (x p q)
;;   (and (bvecp x (+ p q))
;;        (= (iexpof x p q) 0)
;;        (not (= (isigf x p) 0))))


;; (defund ddecode (x p q)
;;   (* (if (= (isgnf x p q) 0) 1 -1)
;;      (isigf x p)
;;      (expt 2 (+ 2 (- (bias q)) (- p)))))


;; (defthmd sgn-ddecode
;;     (implies (and (dencodingp x p q)
;; 		  (integerp p)
;; 		  (> p 1)
;; 		  (integerp q)
;; 		  (> q 0))
;; 	     (equal (sgn (ddecode x p q))
;; 		    (if (= (isgnf x p q) 0) 1 -1))))


;; (defthmd expo-ddecode
;;     (implies (and (dencodingp x p q)
;; 		  (integerp p)
;; 		  (> p 1)
;; 		  (integerp q)
;; 		  (> q 0))
;; 	     (equal (expo (ddecode x p q))
;; 		    (+ 2 (- p) (- (bias q)) (expo (isigf x p))))))


;; (defthmd sig-ddecode
;;     (implies (and (dencodingp x p q)
;; 		  (integerp p)
;; 		  (> p 1)
;; 		  (integerp q)
;; 		  (> q 0))
;; 	     (equal (sig (ddecode x p q))
;; 		    (sig (isigf x p)))))


;; (defund drepp (x p q)
;;   (and (rationalp x)
;;        (not (= x 0))
;;        (<= (- 2 p) (+ (expo x) (bias q)))
;;        (<= (+ (expo x) (bias q)) 0)
;;        ;number of bits available in the sig field = p - 1 - ( - bias - expo(r))
;;        (exactp x (+ -2 p (expt 2 (- q 1)) (expo x)))))


;; (defund dencode (x p q)
;;   (cat (cat (if (= (sgn x) 1) 0 1)
;; 	    1
;;             0
;;             q)
;;        (1+ q)
;;        (* (sig x) (expt 2 (+ -2 p (expo x) (bias q))))
;;        (- p 1)))


;; (defthmd drepp-ddecode
;;     (implies (and (dencodingp x p q)
;; 		  (integerp p)
;; 		  (> p 1)
;; 		  (integerp q)
;; 		  (> q 0))
;; 	     (drepp (ddecode x p q) p q)))


;; (defthmd dencode-ddecode
;;     (implies (and (dencodingp x p q)
;; 		  (integerp p)
;; 		  (> p 1)
;; 		  (integerp q)
;; 		  (> q 0))
;; 	     (equal (dencode (ddecode x p q) p q)
;; 		    x)))


;; (defthmd dencodingp-dencode
;;     (implies (and (drepp x p q)
;; 		  (integerp p)
;; 		  (integerp q)
;; 		  (> q 0))
;; 	     (dencodingp (dencode x p q) p q)))


;; (defthmd ddecode-dencode
;;     (implies (and (drepp x p q)
;; 		  (integerp p)
;; 		  (> p 1)
;; 		  (integerp q)
;; 		  (> q 0))
;; 	     (equal (ddecode (dencode x p q) p q)
;; 		    x)))



;; (defund spd (p q)
;;      (expt 2 (+ 2 (- (bias q)) (- p))))



;; (defthmd positive-spd
;;   (implies (and (integerp p)
;;                 (> p 1)
;;                 (integerp q)
;;                 (> q 0))
;;            (> (spd p q) 0)))


;; (local
;;   (defthm sig-expt-2-reduce
;;     (equal (SIG (EXPT 2 n))
;;            1)
;;     :hints (("Goal" :use ((:instance SIG-SHIFT (x 1)))))))


;; (local
;;  (defthm expo-shift-specific
;;   (implies (integerp n)
;;            (equal (EXPO (EXPT 2 n))
;;                   n))
;;   :hints (("Goal" :in-theory (enable expo-shift)
;;            :cases ((equal (* (expt 2 n) 1)
;;                           (expt 2 n)))))))

;; (local (in-theory (disable LEMMA-EXPT-MULIPLY-2-REDUCE)))

;; (defthmd drepp-spd-2
;;   (implies (and (integerp p)
;;                 (> p 1)
;;                 (integerp q)
;;                 (> q 0))
;;            (drepp (spd p q) p q))
;;   :hints (("Goal" :in-theory (enable bias spd drepp exactp))))

;;(local (in-theory (enable LEMMA-EXPT-MULIPLY-2-REDUCE)))

;; (local
;;  (defthm lemma-expt-muliply-2-reduce
;;    (implies (integerp y)
;;             (equal (* 2 (expt 2 y))
;;                    (expt 2 (+ 1 y))))
;;    :hints (("Goal" :expand (expt 2 (+ 1 y))
;;             :in-theory (enable expt-split)))))

;; >  D          (DEFTHM EXPO<=
;;                       (IMPLIES (AND (< X (* 2 (EXPT 2 N)))
;;                                     (< 0 X)
;;                                     (RATIONALP X)
;;                                     (INTEGERP N))
;;                                (<= (EXPO X) N))
;;                       :RULE-CLASSES :LINEAR)

;; (defthm specific-plus-less
;;   (implies (and (<= z 0)
;;                 (<= (+ R (EXPT 2 (+ 3 (* -1 P)))) 0))
;;            (<= (+ R (EXPT 2 (+ 3 (* -1 P)))


;; >  D          (DEFTHM EXPO-LOWER-BOUND
;;                       (IMPLIES (AND (RATIONALP X) (NOT (EQUAL X 0)))
;;                                (<= (EXPT 2 (EXPO X)) (ABS X)))
;;                       :RULE-CLASSES :LINEAR)


;; (encapsulate ()
;;    (local (include-book "rtl/rel5/arithmetic/expt" :dir :system))
;;    (local
;;     (defthmd expt-weak-monotone-linear
;;       (implies (and (<= n m)
;;                     (case-split (integerp n))
;;                     (case-split (integerp m)))
;;                (<= (expt 2 n) (expt 2 m)))
;;       :rule-classes ((:linear :match-free :all))))

;;    (defthm expt-value-monotonic-specific
;;      (implies (and (integerp p)
;;                    (integerp q)
;;                    (< 0 q)
;;                    (<= 2 (+ P (BIAS Q) (EXPO R))))
;;               (<= (EXPT 2 (+ 2 (* -1 (BIAS Q)) (* -1 P)))
;;                   (expt 2 (expo r))))
;;      :hints (("Goal" :in-theory (enable bias)
;;               :use ((:instance expt-weak-monotone-linear
;;                                (n (+ 2  (* -1 (BIAS Q)) (* -1 P)))
;;                                (m (expo r))))))))



;; (defthmd smallest-spd-2
;;   (implies (and (integerp p)
;;                 (> p 1)
;;                 (not (= r 0))
;;                 (integerp q)
;;                 (> q 0)
;;                 (drepp r p q))
;;            (>= (abs r) (spd p q)))
;;   :hints (("Goal" :in-theory (enable drepp spd
;;                                      expo-minus)
;;            :use ((:instance expt-value-monotonic-specific)
;;                  (:instance expo-lower-bound
;;                             (x r))))))


;----------------------------------------------------------------------

;; (local
;;  (defthm local-inverse-specific
;;    (implies (integerp x)
;;             (equal (/ (expt 2 x))
;;                    (expt 2 (* -1 x))))
;;    :hints (("Goal" :in-theory (enable zip)))
;;    :rule-classes nil))

;; (local
;;  (defthm local-integerp-specific
;;   (implies (and (integerp p)
;;                 (integerp q)
;;                 (< 0 q))
;;            (equal (INTEGERP (* R
;;                                (/ (EXPT 2
;;                                         (+ 3 (* -1 P)
;;                                            (* -1 (EXPT 2 (+ -1 Q))))))))
;;                   (integerp (* r (expt 2 (+ -3 P (expt 2 (+ -1 q))))))))
;;   :hints (("Goal" :use ((:instance  local-inverse-specific
;;                                     (x (+ 3 (* -1 P)
;;                                           (* -1 (EXPT 2 (+ -1 Q)))))))
;;            :in-theory (disable EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE)))))

;----------------------------------------------------------------------


(local
 (defun am (m p g)
   (* m (spd p g))))

;; this probably a bad choice!! we could have used "+"

(local
 (defun am-induct (m p g)
   (if (zip m)
       (list m p g)
     (if (< m 1)
         (list m p g)
       (if (>= m (expt 2 (1- p)))
           (list m p g)
         (am-induct (- m 1) p g))))))



;; (defun fp+ (x n)
;;   (+ x (expt 2 (- (1+ (expo x)) n))))


(local
 (defthm expo-shift-specific
  (implies (integerp n)
           (equal (EXPO (EXPT 2 n))
                  n))
  :hints (("Goal" :in-theory (enable expo-shift)
           :cases ((equal (* (expt 2 n) 1)
                          (expt 2 n)))))))


;; (sig x) (expo (1- n))
(local
 (defthm am-is-fp+1
  (implies (and (integerp m)
                (<= 1 m)
                (< m (expt 2 (1- p)))
                (integerp p)
                (integerp q)
                (exactp (am m p q) (+ -2 P (EXPT 2 (- Q 1)) (EXPO (am m p q))))
                (< 0 q)
                (< 1 p))
           (equal (am (1+ m) p q)
                  (fp+ (am m p q)
                       (+ -2 P (EXPT 2 (- Q 1)) (EXPO (am m p q))))))
  :hints (("Goal" :in-theory (e/d (fp+ spd bias spn)
                                  (EXPO-SHIFT-SPECIFIC))))))



;; ;; (defthmd expo-monotone
;; ;;   (implies (and (<= (abs x) (abs y))
;; ;;                 (case-split (rationalp x))
;; ;;                 (case-split (not (equal x 0)))
;; ;;                 (case-split (rationalp y)))
;; ;;            (<= (expo x) (expo y)))
;; ;;   :rule-classes :linear)

;; ;; (defthmd expo-prod-upper
;; ;;     (implies (and (rationalp x)
;; ;; 		  (not (= x 0))
;; ;; 		  (rationalp y)
;; ;; 		  (not (= y 0)))
;; ;; 	     (>= (+ (expo x) (expo y) 1) (expo (* x y))))
;; ;;   :rule-classes :linear)

(local
 (defthm expo-m-<=-specific
  (implies (and (<= 1 m)
                (integerp m)
                (integerp p)
                (< m (expt 2 (+ -1 p))))
           (<= (EXPO M)
               (- p 1)))
  :hints (("Goal" :use ((:instance expo-monotone
                                   (x m)
                                   (y (expt 2 (+ -1 p)))))))))

(local
 (defthm expo-m-<=-specific-2
  (implies (and (<= 1 m)
                (integerp m)
                (integerp p)
                (< 1 p)
                (< m (expt 2 (+ -1 p))))
           (<= (EXPO M)
               (- p 2)))
  :hints (("Goal" :cases ((equal (expo m)
                                 (- p 1)))
           :in-theory (disable expo-m-<=-specific))
          ("Subgoal 2" :use ((:instance expo-m-<=-specific)))
          ("Subgoal 1" :use ((:instance expo-lower-bound
                                        (x m)))))
  :rule-classes :linear))

(local
 (defthm bias-big-enough-induct-step-drepp-am-1-6
 (implies (and (<= 1 m)
               (integerp p)
               (integerp q)
               (< 0 q)
               (< 1 p)
               (integerp m)
               (< m (expt 2 (+ -1 p))))
          (<= (+ (BIAS Q) (EXPO (* M (SPD P Q))))
              0))
 :hints (("Goal" :in-theory (e/d (spd expo-shift) ())
          :use ((:instance expo-m-<=-specific-2)
                (:instance expo-shift
                           (n (+ 2 (* -1 P) (* -1 (BIAS Q))))
                           (x m)))))
 :rule-classes :linear))



(local
 (defthm fact-expo-am-specific
   (implies (and (integerp m)
                 (< 0 x)
                 (rationalp x)
                 (< 1 m))
            (<= (expo (+ (* -1 x)
                         (* m x)))
                (expo (* m x))))
   :rule-classes :linear
   :hints (("Goal"
            :do-not '(fertilize)
            :in-theory (enable spd)
            :use ((:instance expo-monotone
                             (x (+ (* -1 x)
                                   (* m x)))
                             (y (* m x))))))))

(local
  (defthm induct-step-drepp-am-1-9
     (implies (and (integerp m)
                   (integerp p)
                   (integerp q)
                   (< 1 m)
                   (< 1 p)
                   (< 0 q)
                   (<= 2
                       (+ P (BIAS Q)
                          (EXPO (+ (* -1 (SPD P Q)) (* M (SPD P Q)))))))
              (<= 2
                  (+ P (BIAS Q) (EXPO (* M (SPD P Q))))))
     :hints (("Goal" :use ((:instance fact-expo-am-specific
                                      (x (spd p q))))))))



;; ;; >  D          (DEFTHM EXACTP-<=
;; ;;                       (IMPLIES (AND (EXACTP X M)
;; ;;                                     (<= M N)
;; ;;                                     (RATIONALP X)
;; ;;                                     (INTEGERP N)
;; ;;                                     (INTEGERP M))
;; ;;                                (EXACTP X N)))


(local (include-book "../../arithmetic/basic"))

;; (local (defthm rationalp-spd
;;          (rationalp (spd p q))))



(local
 (defthm induct-step-drepp-am-1-5
  (implies (and (integerp m)
                (integerp p)
                (integerp q)
                (< 0 q)
                (< 1 m)
                (< 1 p)
                (EXACTP (* M (SPD P Q))
                        (+ -2 P (EXPT 2 (+ -1 Q))
                           (EXPO (+ (* -1 (SPD P Q)) (* M (SPD P Q)))))))
           (EXACTP (* M (SPD P Q))
                   (+ -2 P (EXPT 2 (+ -1 Q))
                      (EXPO (* M (SPD P Q))))))
  :hints (("Goal" :in-theory (e/d (expo-monotone) (spd))
           :use ((:instance exactp-<=
                            (x (* M (SPD P Q)))
                            (m (+ -2 P (EXPT 2 (+ -1 Q))
                                  (EXPO (+ (* -1 (SPD P Q))
                                           (* m (SPD P q))))))
                            (n (+ -2 P (EXPT 2 (+ -1 Q))
                                  (EXPO (* M (SPD P Q)))))))))))


; Proof of induct-step-drepp-am modified April 2016 by Matt K. to accommodate
; addition of a type-set bit for the set {1}.  The :cases hint in
; induct-step-drepp-am no longer succeeded, but it was easy to separate out the
; interesting case as a lemma, as follows.  Now there are no subgoal hints.

(local
 (defthm induct-step-drepp-am-not-equal-m-1
   (IMPLIES (AND (DREPP (SPD P Q) P Q)
                 (<= 1 M)
                 (< M (EXPT 2 (+ -1 p)))
                 (DREPP (+ (* -1 (SPD P Q)) (* M (SPD P Q)))
                        P Q)
                 (INTEGERP P)
                 (< 1 P)
                 (INTEGERP Q)
                 (< 0 Q)
                 (INTEGERP M)
                 (not (equal m 1)))
            (DREPP (* M (SPD P Q)) P Q))
   :hints (("Goal" :in-theory (e/d (drepp positive-spd bias) (fp+ spd))
            :use ((:instance FP+1
                             (x (am (1- m) p q))
                             (n (+ -2 P (EXPT 2 (- Q 1))
                                   (EXPO (am (1- m) p q)))))
                  (:instance am-is-fp+1
                             (m (1- m)))
                  (:instance induct-step-drepp-am-1-5))))
   :rule-classes nil))

(local
 (defthm induct-step-drepp-am
   (IMPLIES (AND (DREPP (SPD P Q) P Q)
                 (<= 1 M)
                 (< M (EXPT 2 (+ -1 p)))
                 (DREPP (+ (* -1 (SPD P Q)) (* M (SPD P Q)))
                        P Q)
                 (INTEGERP P)
                 (< 1 P)
                 (INTEGERP Q)
                 (< 0 Q)
                 (INTEGERP M))
            (DREPP (* M (SPD P Q)) P Q))
   :hints (("Goal" :use induct-step-drepp-am-not-equal-m-1))))

(local
(defthmd spd-mult-1
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (<= 1 m)
                (integerp m)
                (< m (expt 2 (1- p))))
           (drepp (am m p q) p q))
  :hints (("Goal" :induct (am-induct m p q)
           :do-not '(generalize))
          ("Subgoal *1/2" :use drepp-spd))))


(local
 (defthm am-in-between-1
  (implies (and (> r 0)
                (rationalp r)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (<= (am (fl (/ r (spd p q))) p q)
               r))
  :rule-classes :linear))

;; (local (in-theory (enable positive-spd)))

(local
 (defthm fl-fact-specific
   (implies (and (> r 0)
                 (rationalp r)
                 (> x 0)
                 (rationalp x))
            (< r  (+ x (* x (fl (/ r x))))))
   :rule-classes :linear))


(local
 (defthm am-in-between-2
  (implies (and (> r 0)
                (rationalp r)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (< r
              (am (+ 1 (fl (/ r (spd p q)))) p q)))
  :rule-classes :linear))




;; (defthm expo-unique
;;   (implies (and (<= (expt 2 n) (abs x))
;;                 (< (abs x) (expt 2 (1+ n)))
;;                 (rationalp x)
;;                 (integerp n))
;;            (equal n (expo x)))
;;   :rule-classes ())


(local
 (defthm rationalp-is-am
  (implies (and (integerp p)
                (integerp q)
                (integerp m)
                (< 0 q))
           (RATIONALP (AM m P Q)))))



;; (defthmd smallest-spd
;;   (implies (and (integerp p)
;;                 (> p 1)
;;                 (not (= r 0))
;;                 (integerp q)
;;                 (> q 0)
;;                 (drepp r p q))
;;            (>= (abs r) (spd p q)))
;;   :hints (("Goal" :in-theory (enable drepp spd
;;                                      expo-minus)
;;            :use ((:instance expt-value-monotonic-specific)
;;                  (:instance expo-lower-bound
;;                             (x r))))))

;; (defthm expt-positive-specific
;;   (implies (integerp any)
;;            (< 0 (expt 2 any))))

;; (defthm equal-mulitply-positive-zero
;;   (implies (and (equal (* x p) 0)
;;                 (< 0 p)
;;                 (acl2-numberp p)
;;                 (acl2-numberp x))
;;            (equal x 0))
;;   :rule-classes :forward-chaining)

(local
 (defthm am-is-zero-implies-r-less-than-spd
  (implies (and (equal (am x p q) 0)
                (rationalp x)
                (integerp p)
                (< 1 p)
                (< 0 q)
                (integerp q))
           (equal x 0))
  :hints (("Goal" :in-theory (enable positive-spd)))
  :rule-classes :forward-chaining))

(local
 (defthm fl-zero-implies-less-than
  (implies (and (equal (fl (/ r x)) 0)
                (< 0 x)
                (< 0 r)
                (rationalp r)
                (rationalp x))
           (< r x))
  :rule-classes :forward-chaining))



;; (defthmd smallest-spd
;;   (implies (and (integerp p)
;;                 (> p 1)
;;                 (not (= r 0))
;;                 (integerp q)
;;                 (> q 0)
;;                 (drepp r p q))
;;            (>= (abs r) (spd p q)))
;;   :hints (("Goal" :in-theory (enable drepp spd
;;                                      expo-minus)
;;            :use ((:instance expt-value-monotonic-specific)
;;                  (:instance expo-lower-bound
;;                             (x r))))))

;; (skip-proofs
;;  (defthm am-positive
;;    (implies (and (rationalp r)
;;                  (integerp p)
;;                  (integerp q)
;;                  (< 1 p)
;;                  (< 0 q))
;;             (<= 0 (AM (FL (* R (/ (SPD P Q)))) P Q)))
;;    :hints (("Goal" :in-theory (enable positive-spd)))
;;    :rule-classes :type-prescription))



;; (defthm am-in-between-1
;;   (implies (and (> r 0)
;;                 (rationalp r)
;;                 (integerp p)
;;                 (> p 1)
;;                 (integerp q)
;;                 (> q 0))
;;            (<= (am (fl (/ r (spd p q))) p q)
;;                r))
;;   :rule-classes :linear)


;; (defthmd expo-monotone
;;   (implies (and (<= (abs x) (abs y))
;;                 (case-split (rationalp x))
;;                 (case-split (not (equal x 0)))
;;                 (case-split (rationalp y)))
;;            (<= (expo x) (expo y)))
;;   :rule-classes :linear)

;; (encapsulate ()
;;    (local (include-book "rtl/rel5/arithmetic/expt" :dir :system))
;;    (defthmd expt-weak-monotone-linear
;;       (implies (and (<= n m)
;;                     (case-split (integerp n))
;;                     (case-split (integerp m)))
;;                (<= (expt 2 n) (expt 2 m)))
;;       :rule-classes ((:linear :match-free :all))))


(local
 (defthm am-in-between-1-specific
  (implies (and (> r 0)
                (rationalp r)
                (integerp p)
                (> p 1)
                (drepp r p q)
                (integerp q)
                (> q 0))
           (<= (expt 2 (expo (am (fl (/ r (spd p q))) p q)))
               r))
  :hints (("Goal"
           :use ((:instance expo-lower-bound
                            (x (am (fl (/ r (spd p q))) p q)))
                 (:instance expo-monotone
                            (x (am (fl (/ r (spd p q))) p q))
                            (y r))
                 (:instance am-in-between-1)
                 (:instance fl-zero-implies-less-than
                            (x (spd p q)))
                 (:instance am-is-zero-implies-r-less-than-spd
                            (x (fl (/ r (spd p q)))))
                 (:instance smallest-spd))))
  :rule-classes :linear))



;; (defthm am-is-fp+1
;;   (implies (and (integerp m)
;;                 (<= 1 m)
;;                 (< m (expt 2 (1- p)))
;;                 (integerp p)
;;                 (integerp q)
;;                 (exactp (am m p q) (+ -2 P (EXPT 2 (- Q 1)) (EXPO (am m p q))))
;;                 (< 0 q)
;;                 (< 1 p))
;;            (equal (am (1+ m) p q)
;;                   (fp+ (am m p q)
;;                        (+ -2 P (EXPT 2 (- Q 1)) (EXPO (am m p q))))))
;;   :hints (("Goal" :in-theory (e/d (fp+ spd bias spn)
;;                                   (EXPO-SHIFT-SPECIFIC)))))

(local
 (defthm am-positive
  (implies (and (integerp m)
                (integerp p)
                (integerp q)
                (< 1 p)
                (< 0 q)
                (<= 0 m))
           (<= 0 (AM m P Q)))
  :hints (("Goal" :in-theory (enable positive-spd)))
  :rule-classes :type-prescription))

(local
 (defthm am-positive-strong
  (implies (and (integerp m)
                (integerp p)
                (integerp q)
                (< 1 p)
                (< 0 q)
                (<= 1 m))
           (< 0 (AM m P Q)))
  :hints (("Goal" :in-theory (enable positive-spd)))
  :rule-classes :linear))

;; (defthmd exactp-2**n
;;   (implies  (and (case-split (integerp m))
;;                  (case-split (> m 0)))
;;             (exactp (expt 2 n) m)))


;; (defthm expo-m-positive
;;   (implies (and (integerp p)
;;                 (integerp q)
;;                 (< 1 p)
;;                 (< 0 q)
;;                 (integerp m)
;;                 (<= 1 m)
;;                 (< m (expt 2 (1- p))))
;;            (< 0 (+ -2 P (EXPT 2 (+ -1 Q))
;;                     (EXPO (* M (SPD P Q))))))
;;   :hints (("


(local
 (defthm exactp-2**n-specific
  (implies (and (<= 2
                    (+ -1 P (EXPT 2 (+ -1 Q))
                       (EXPO (* M (SPD P Q)))))
                (integerp p)
                (integerp q)
                (integerp m)
                (< 0 q)
                (< 1 p)
                (<= 1 m))
           (EXACTP (EXPT 2 (+ 1 (EXPO (* M (SPD P Q)))))
                   (+ -2 P (EXPT 2 (+ -1 Q))
                      (EXPO (* M (SPD P Q))))))
  :hints (("Goal" :in-theory (enable exactp-2**n)))))

(local
 (defthm fp+2-specific
  (implies (and (integerp p)
                (integerp q)
                (< 0 q)
                (< 1 p)
                (integerp m)
                (<= 1 m)
                (< m (expt 2 (1- p)))
                (drepp (am m p q) p q)
                (< (am m p q)
                   (EXPT 2
                         (+ 1
                            (EXPO (am m p q))))))
           (<= (am (+ 1 m) p q)
               (EXPT 2
                     (+ 1
                        (EXPO (am m p q))))))
  :hints (("Goal"
           :in-theory (e/d (am bias drepp) (exactp-2**n))
           :use ((:instance fp+2
                            (x (am m p q))
                            (y (expt 2 (+ 1 (expo (am m p q)))))
                            (n (+ -2 P (EXPT 2 (- Q 1)) (EXPO (am m p q)))))
                 (:instance am-is-fp+1))))))


(local
 (encapsulate ()
  (local (include-book "../../arithmetic/basic"))
  (local
   (defthm expt-i+j-combine
     (implies (and (integerp j1)
                   (integerp j2))
              (equal (* (expt 2 j1) (expt 2 j2))
                     (expt 2 (+ j1 j2))))
     :hints (("Goal" :use ((:instance a15 (i 2)))))))

  (local
   (defthm equal-expt-2-1-p-is-1-q
     (implies (and (integerp p)
                   (< 1 p)
                   (< 0 q)
                   (integerp q))
              (equal (* (expt 2 (+ -1 p))
                        (spd p q))
                     (spn q)))
     :hints (("Goal" :in-theory (enable bias spd spn)))))


  (local (defthm expo-upper-bound-chain
           (implies (and (<= (expo r) y)
                         (rationalp r)
                         (< 0 r)
                         (integerp y))
                    (< r (expt 2 (+ 1 y))))
           :hints (("Goal" :use ((:instance expo-upper-bound
                                            (x r))
                                 (:instance expt-strong-monotone-linear
                                            (n (+ 1 (expo r)))
                                            (m (+ 1 y))))))))

  (local
   (defthm r-less-than-spn
     (implies (and (<= (+ (BIAS Q) (EXPO R)) 0)
                   (rationalp r)
                   (< 0 r)
                   (integerp p)
                   (integerp q)
                   (< 1 p)
                   (< 0 q))
              (< r  (spn q)))
     :hints (("Goal" :in-theory (enable expt-strong-monotone-linear
                                        spn)
              :use ((:instance EXPO-UPPER-BOUND-chain
                               (r r)
                               (y (* -1 (bias q)))))))))

  (defthm fl-r-spd-less-than
     (implies (and (DREPP R P Q)
                   (integerp p)
                   (< 0 r)
                  (< 1 p)
                  (< 0 q)
                  (integerp q)
                  (rationalp r))
             (< (fl (* r (/ (spd p q))))
                (expt 2 (+ -1 p))))
  :hints (("Goal" :in-theory (e/d (drepp)
                                  (EQUAL-EXPT-2-1-P-IS-1-Q
                                   r-less-than-spn))
           :use ((:instance r-less-than-spn)
                 (:instance equal-expt-2-1-p-is-1-q))))
  :rule-classes :linear)))

(local
 (defthm am-in-between-2-specific
  (implies (and (> r 0)
                (rationalp r)
                (integerp p)
                (> p 1)
                (DREPP R P Q)
                (integerp q)
                (> q 0))
           (< r
              (EXPT 2

                    (+ 1
                       (EXPO (AM (FL (* R (/ (SPD P Q)))) P Q))))))
  :hints (("Goal"
           :use ((:instance expo-upper-bound
                            (x (am (fl (/ r (spd p q))) p q)))
                   (:instance expo-monotone
                              (x r)
                              (y (am (+ 1 (fl (/ r (spd p q)))) p q)))
                   (:instance fp+2-specific
                              (m (fl (* R (/ (spd p q))))))
                   (:instance am-in-between-2)
                   (:instance fl-zero-implies-less-than
                              (x (spd p q)))
                   (:instance am-is-zero-implies-r-less-than-spd
                              (x (fl (/ r (spd p q)))))
                   (:instance spd-mult-1
                              (m (fl (* R (/ (spd p q))))))
                   (:instance smallest-spd))))
  :rule-classes :linear))

(local
 (defthm expo-r-equal-expo-am
  (implies (and (> r 0)
                (rationalp r)
                (integerp p)
                (> p 1)
                (drepp r p q)
                (integerp q)
                (> q 0))
           (equal (expo r)
                  (expo (am (fl (/ r (spd p q)))
                            p q))))
  :hints (("Goal" :in-theory (disable drepp am)
           :use ((:instance expo-unique
                            (x r)
                            (n (expo (am (fl (/ r (spd p q))) p q)))))))
  :rule-classes nil))


;;;;
;;;; not so useful!!!
;;;;


;; (defthmd diff-representable-r
;;   (implies (and (integerp p)
;;                 (> p 1)
;;                 (integerp q)
;;                 (> q 0)
;;                 (rationalp r)
;;                 (> r 0)
;;                 (drepp r p q))
;;            (drepp (- r (am (fl (/ r (spd p q)))
;;                            p q))
;;                   p q))
;;   :hints (("Goal" :in-theory (e/d (bias drepp) (am))
;;            :do-not '(generalize)
;;            :use ((:instance expo-r-equal-expo-am)
;;                  (:instance exactp-diff-cor
;;                             (x r)
;;                             (y (am (fl (/ r (spd p q))) p q))
;;                             (n (+ -2 P (EXPT 2 (- Q 1)) (EXPO r))))
;;                  (:instance smallest-spd)
;;                  (:instance spd-mult-1
;;                             (m (fl (* R (/ (spd p q))))))))))

;(i-am-here) ;;

(local
 (defthmd spd-mult-2
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp r)
                (> r 0)
                (drepp r p q))
           (equal (am (fl (/ r (spd p q))) p q)
                  r))
  :hints (("Goal" :in-theory (e/d (drepp bias) (am))
           :use ((:instance fp+2
                            (x (am (fl (/ r (spd p q))) p q))
                            (y r)
                            (n (+ -2 P (EXPT 2 (- Q 1)) (EXPO r))))
                 (:instance expo-r-equal-expo-am)
                 (:instance spd-mult-1
                            (m (fl (* R (/ (spd p q))))))
                 (:instance am-is-fp+1
                            (m (fl (* R (/ (spd p q))))))
                 (:instance smallest-spd))))))

(local
 (defthmd spd-mult-2-specific
   (implies (and (integerp p)
                 (> p 1)
                 (integerp q)
                 (> q 0)
                 (rationalp r)
                 (> r 0)
                 (drepp r p q))
            (equal (am (/ r (spd p q)) p q)
                   r))
   :hints (("Goal" :in-theory (e/d (am) (drepp bias spd))
            :use ((:instance spd-mult-2))))))


;;  (defthm fl-r-spd-less-than
;;    (implies (and (DREPP R P Q)
;;                  (integerp p)
;;                  (< 0 r)
;;                  (< 1 p)
;;                  (< 0 q)
;;                  (integerp q)
;;                  (rationalp r))
;;             (< (fl (* r (/ (spd p q))))
;;                (expt 2 (+ -1 p))))
;;    :hints (("Goal" :in-theory (enable bias drepp)))
;;    :rule-classes :linear))

(local
 (defthm drepp-maximal-r
  (implies (and  (DREPP R P Q)
                 (integerp p)
                 (< 0 r)
                 (< 1 p)
                 (< 0 q)
                 (integerp q)
                 (rationalp r))
           (< R (* (EXPT 2 (+ -1 P)) (SPD P Q))))
  :hints (("Goal" :in-theory (enable drepp)
           :use ((:instance fl-r-spd-less-than)
                 (:instance positive-spd))))))


(local
 (defthmd spd-mult-2-specific-further
   (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (> r 0)
		(rationalp r)
	        (drepp r p q))
      (and (natp (* r (/ (spd p q))))
           (<= 1 (* r (/ (spd p q))))
           (<    (* r (/ (spd p q))) (expt 2 (1- p)))))
  :hints (("Goal" :in-theory (disable spd-mult-2-specific
                                      spd-mult-2)
           :use ((:instance spd-mult-2)
                 (:instance smallest-spd))))))

(local
 (defthmd spd-mult-1-specific-further
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (> r 0)
		(rationalp r)
                (<= 1 m)
                (integerp m)
                (< m (expt 2 (1- p)))
                (equal (/ r (spd p q)) m))
           (drepp r p q))
  :hints (("Goal" :in-theory (disable spd-mult-1)
           :use ((:instance spd-mult-1))))))


; Modified 3/17/2016 by Matt K. for runic type-prescription mod (goal numbers
; changed).
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
		     (< m (expt 2 (1- p))))))
  :hints (("Goal" :in-theory (e/d () (am spd drepp
                                         spd-mult-1-specific-further
                                         spd-mult-2-specific-further))
           :use ((:instance spd-mult-1-specific-further
                            (m (/ r (spd p q))))
                 (:instance spd-mult-2-specific-further)))))

;------------------------------------------------------------------------------
