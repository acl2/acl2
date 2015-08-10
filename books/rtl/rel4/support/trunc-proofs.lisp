(in-package "ACL2")

;;;***************************************************************
;;;an acl2 library of floating point arithmetic

;;;david m. russinoff
;;;advanced micro devices, inc.
;;;february, 1998
;;;***************************************************************

;make local some of the events in this book

(include-book "ground-zero")
(local (include-book "float"))
(local (include-book "../arithmetic/top"))

;;Necessary defuns

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defun expo-measure (x)
;  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((not (rationalp x)) 0)
	((< x 0) '(2 . 0))
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defund expo (x)
  (declare (xargs :guard t
                  :measure (expo-measure x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
	((< x 0) (expo (- x)))
	((< x 1) (1- (expo (* 2 x))))
	((< x 2) 0)
	(t (1+ (expo (/ x 2))))))

;could redefine to divide by the power of 2 (instead of making it a negative power of 2)...
(defund sig (x)
  (declare (xargs :guard t))
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


;;
;; New stuff:
;;


(defund trunc (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

;generated automatically by ACL2 when we define trunc, but included here just to be safe
;could have disabled (:type-prescription trunc) for slight efficiency gain at the cost of making the output of :pe a
;little deceptive
(defthm trunc-rational-type-prescription
  (rationalp (trunc x n))
  :rule-classes :type-prescription)

(defthm trunc-of-non-rationalp-is-0
  (implies (not (rationalp x))
           (equal (trunc x n)
                  0))
  :hints (("goal" :in-theory (enable trunc sig))))

#| would be nice:
(defthm trunc-with-n-not-an-integer
  (implies (not (integerp n))
           (equal (trunc x n)
                  ...)))
|#



(defthm trunc-to-0-or-fewer-bits
  (implies (and (<= n 0)
                (integerp n)
                )
           (equal (trunc x n)
                  0))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable trunc expt-split)
                              '())
           :use ((:instance fl-unique
                            (x (* 1/2 (sig x) (expt 2 n)))
                            (n 0))
                 (:instance expt-weak-monotone
                            (n n)
                            (m 0))))))

;make alt version? use negative-syntaxp?
(defthm trunc-minus
  (equal (trunc (* -1 x) n)
         (* -1 (trunc x n)))
  :hints (("Goal" :in-theory (enable trunc))))


;change what trunc does with n not a positive int?
(defthm trunc-positive
  (implies (and (< 0 x)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n))
                )
           (< 0 (trunc x n)))
  :rule-classes (:rewrite :linear)
  :hints (("goal" :in-theory (e/d ( trunc expt-split) (SIG-LESS-THAN-1-MEANS-X-0 SIG-LOWER-BOUND))
           :use ((:instance sig-lower-bound)))))


;I think this rule has caused the "bad-ass" problem regarding the (case-split (< 0 n)) hyp.
;BOZO should this include rationalp, to have a more type-like conclusion?
(defthm trunc-positive-rational-type-prescription
  (implies (and (< 0 x)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n)))
           (< 0 (trunc x n)))
  :rule-classes :type-prescription)

(defthm trunc-negative
  (implies (and (< x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n)))
           (< (trunc x n) 0))
  :rule-classes (:rewrite :linear)
  :hints (("goal" :in-theory (e/d ( trunc expt-split) ( SIG-LESS-THAN-1-MEANS-X-0  SIG-LOWER-BOUND))
           :use ((:instance sig-lower-bound)))))

;BOZO should this include rationalp, to have a more type-like conclusion?
(defthm trunc-negative-rational-type-prescription
  (implies (and (< x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n))
                )
           (< (trunc x n) 0))
  :rule-classes :type-prescription)

(defthm trunc-0
  (equal (trunc 0 n)
         0)
  :hints (("goal" :in-theory (enable trunc))))

;trying the case-split
(defthm trunc-of-non-rationalp-is-0-alt
  (implies (case-split (not (rationalp x)))
           (equal (trunc x n)
                  0)))


(defthm trunc-non-negative-rational-type-prescription
  (implies (and (<= 0 x)
                (case-split (integerp n))
                )
           (and (<= 0 (trunc x n))
                (rationalp (trunc x n))))
  :hints (("Goal" :cases ((equal x 0) (and (not (equal x 0)) (<= n 0)))))
  :rule-classes :type-prescription)

(defthm trunc-non-positive-rational-type-prescription
  (implies (and (<= x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
;                (case-split (< 0 n))
                )
           (and (<= (trunc x n) 0)
                (rationalp (trunc x n))))
  :hints (("Goal" :cases ((equal x 0) (and (not (equal x 0)) (<= n 0)))))
  :rule-classes :type-prescription)

;make an away version?
(defthm trunc-non-negative-linear
  (implies (and (<= 0 x)
                (case-split (rationalp x))
                (case-split (integerp n))
                )
           (<= 0 (trunc x n)))
  :rule-classes :linear)

;make an away version?
(defthm trunc-non-positive-linear
  (implies (and (<= x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                )
           (<= (trunc x n) 0))
  :rule-classes :linear)

(defthm sgn-trunc
  (implies (and (< 0 n)
                (rationalp x)
                (integerp n)
                )
           (equal (sgn (trunc x n))
                  (sgn x)))
  :hints (("goal" :cases ((equal x 0) (< x 0)))))


;why not just open up trunc and sgn?
;keep this disabled, since it basically opens up TRUNC
(defthmd abs-trunc
  (equal (abs (trunc x n))
         (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))
  :hints (("goal" :in-theory (enable trunc)
           )))

(defthm trunc-upper-bound
  (implies (and (rationalp x)
                (integerp n))
           (<= (abs (trunc x n)) (abs x)))
  :rule-classes :linear
  :hints (("goal" :in-theory (e/d (abs-trunc)
                                  ( ;CANCEL-IN-PRODS-<-3-OF-3-WITH-2-OF-2
                                   EXPT-COMPARE-EQUAL ;BOZO why?
                                   CANCEL-COMMON-FACTORS-IN-<
                                   ))
           :use (trunc-to-0-or-fewer-bits
                 (:instance *-weakly-monotonic
                            (x (expt 2 (- (1+ (expo x)) n)))
                            (y (fl (* (sig x) (expt 2 (1- n)))))
                            (y+ (* (sig x) (expt 2 (1- n)))))
                 (:instance fp-abs)
                 (:instance expt-split (r 2) (i (1- n)) (j (- (1+ (expo x)) n)))
                 ))))




;BOZO bad name. should be trunc-equal-0
(defthm trunc-equal-0-rewrite
  (implies (and (> n 0)
                (rationalp x)
                (integerp n)
                )
           (equal (equal (trunc x n) 0)
                  (equal x 0)))
  :hints (("Goal" :cases ((< x 0) (equal x 0) (< 0 x))
           )))

(defthm trunc-upper-pos
    (implies (and (<= 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (trunc x n) x))
    :rule-classes :linear
    :hints (("goal" :in-theory (disable abs-trunc trunc)
             :use ((:instance trunc-upper-bound)
                   ))))

#| BOZO prove this and use below

(defthm fl-unique-rewrite
    (implies (and (<= n x)
		  (< x (1+ n))
                  (rationalp x)
		  (integerp n)
		  )
	     (equal (fl x)
                    n)))

(defthm fl-unique-rewrite-2
    (implies (and (< x n)
                  (<= (1- n) x)
                  (rationalp x)
		  (integerp n)
		  )
	     (equal (fl x)
                    (1- n))))

;gen to negative x?
(defthm expo-fl
  (implies (<= 0 x)
           (equal (expo (fl x))
                  (if (<= 1 (abs x))
                      (expo x)
                    0)
                  ))
  :otf-flg t
  :hints (("Goal" :in-theory (enable expo-equality-reduce-to-bounds
;expt-split
                                     ) ;BOZO consider enabling this gloablly?
;(or make a version for constants, same for expo-comparison...)
           :use (:instance expo-unique (x (fl x)) (n 0)))))


(defthm expo-trunc
   (implies (and (< 0 n)
                 (rationalp x)
                 (integerp n)
                 )
            (equal (expo (trunc x n))
                   (expo x)))
   :hints (("goal" :in-theory (e/d ( trunc sig)
                                   (LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE)))))


|#

(encapsulate
 ()
;BOZO this seems dumb, given expo-trunc
 (local (defthm expo-trunc-upper-bound
          (implies (and (< 0 n)
                        (rationalp x)
                        (integerp n)
                        )
                   (<= (expo (trunc x n)) (expo x)))
          :rule-classes nil
          :hints (("goal"
                   :use ((:instance trunc-upper-bound)

                         (:instance expo-monotone (x (trunc x n)) (y x)))))))

 (local (defthm expo-trunc-lower-bound
          (implies (and (rationalp x)
                        (not (= x 0))
                        (integerp n)
                        (> n 0))
                   (>= (abs (trunc x n)) (expt 2 (expo x))))
          :rule-classes nil
          :hints (("goal" :in-theory (e/d (abs-trunc) ( expt-compare-equal))
                   :use ((:instance sig-lower-bound)
                         (:instance *-weakly-monotonic
                                    (y (expt 2 (1- n)))
                                    (y+ (fl (* (sig x) (expt 2 (1- n)))))
                                    (x (expt 2 (- (1+ (expo x)) n))))
                         (:instance expt-split (r 2) (i (1- n)) (j (- (1+ (expo x)) n)))
                         (:instance fl-monotone-linear (x (expt 2 (1- n))) (y (* (expt 2 (1- n)) (sig x)))))))))

 (defthm expo-trunc
   (implies (and (< 0 n)
                 (rationalp x)
                 (integerp n)
                 )
            (equal (expo (trunc x n))
                   (expo x)))
   :hints (("goal" :in-theory (disable abs-trunc)
            :use ((:instance expo-trunc-lower-bound)
                  (:instance expo-trunc-upper-bound)
                  (:instance expo-upper-bound (x (trunc x n)))
                  (:instance expt-strong-monotone (n (expo x)) (m (1+ (expo (trunc x n)))))))))
 )

(local
   (defthm trunc-lower-1-2
     (implies (and (rationalp u)
                   (rationalp v)
                   (rationalp r)
                   (> r 0)
                   (< u (1+ v)))
              (< (* r u) (* r (1+ v))))
     :rule-classes ()))

(defthm trunc-lower-1-3
    (implies (and (rationalp u)
                  (rationalp v)
                  (rationalp r)
                  (> r 0)
                  (< u (1+ v)))
             (< (* r u) (+ r (* r v))))
    :rule-classes ()
    :hints (("goal" :in-theory (disable *-strongly-monotonic)
             :use ((:instance trunc-lower-1-2)))))

(defthm trunc-lower-1
  (implies (and (rationalp x)
                (integerp n))
           (> (abs (trunc x n))
              (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear
  :hints (("goal" :in-theory (set-difference-theories
                              (enable expt-split expt-minus abs-trunc)
                              '())
           :use ((:instance fp-abs)
                 (:instance trunc-lower-1-3
                            (u (* (sig x) (expt 2 (1- n))))
                            (v (fl (* (sig x) (expt 2 (1- n)))))
                            (r (expt 2 (- (1+ (expo x)) n))))))))


(defthm trunc-lower-2-1
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (<= (expt 2 (- (1+ (expo x)) n)) (* (abs x) (expt 2 (- 1 n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable abs EXPT-COMPARE-EQUAL)
		  :use ((:instance expo-lower-bound)
			(:instance expt-split (r 2) (i (expo x)) (j (- 1 n)))))))

(defthm trunc-lower-2
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (> (abs (trunc x n)) (* (abs x) (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear
  :hints (("goal" :in-theory (disable abs)
		  :use ((:instance trunc-lower-1)
			(:instance trunc-lower-2-1)))))

(defthm trunc-lower-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (> (trunc x n) (* x (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear
  :hints (("goal" :in-theory (disable abs-trunc abs-pos)
		  :use ((:instance trunc-lower-2)))))

(defthm trunc-lower-3
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (abs (trunc x n)) (* (abs x) (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear
  :hints (("goal" :in-theory (disable abs)
		  :use ((:instance trunc-lower-1)
			(:instance trunc-lower-2-1)))))
(local
 (defthm trunc-lower-4-1
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (abs (trunc x n)) (- (abs x) (* (abs x) (expt 2 (- 1 n))))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable abs-trunc)
		  :use ((:instance trunc-lower-3))))))

(local
 (defthm trunc-lower-4-2
    (implies (and (rationalp x)
		  (< x 0)
		  (integerp n)
		  (> n 0))
	     (>= (trunc x n) x))
  :rule-classes ()
  :hints (("goal" :in-theory (disable abs-trunc)
		  :use ((:instance trunc-upper-bound))))))

(defthm trunc-lower-4
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (trunc x n) (- x (* (abs x) (expt 2 (- 1 n))))))
  :rule-classes :linear
  :hints (("goal" :in-theory (disable abs-trunc)
		  :use ((:instance trunc-lower-4-1)
			(:instance trunc-lower-4-2)
;			(:instance trunc-pos)
	;		(:instance trunc-neg)
                        ))))

(defthm trunc-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- x (trunc x n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable abs-trunc)
		  :use (;(:instance trunc-diff-1 (y (trunc x n)))  ;drop?
;			(:instance trunc-neg)
	;		(:instance trunc-pos)
			(:instance trunc-upper-bound)
			(:instance trunc-lower-1)))))

(defthm trunc-diff-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (< (- x (trunc x n)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable abs-trunc)
		  :use ((:instance trunc-diff)
		;	(:instance trunc-pos)
			(:instance trunc-upper-bound)))))


(defthm trunc-diff-expo-1
    (implies (and (rationalp x)
		  (not (= x (trunc x n)))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- x (trunc x n))) (- (expo x) n)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable abs abs-trunc)
		  :use ((:instance trunc-diff)
			(:instance expo-lower-bound (x (- x (trunc x n))))
			(:instance expt-strong-monotone
				   (n (expo (- x (trunc x n))))
				   (m (- (1+ (expo x)) n)))))))
;just gets rid of sig...
(defthmd trunc-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0) ;gen?  this isn't in pos-rewrite!
                  )
	     (equal (trunc x n)
		    (* (sgn x)
		       (fl (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n)))))
    :hints (("Goal" :in-theory (enable trunc sig expt-split))))

;yuck?
(local
 (defthm trunc-exactp-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp z)
		  (not (= x 0))
		  (not (= z 0)))
	     (iff (= (* x y z) (* x (fl y) z))
		  (integerp y)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable fl-int fl-integerp fl)
		  :use ((:instance fl-integerp (x y))
			(:instance *cancell (x (fl y)) (z (* x z))))))))

(defthm trunc-exactp-a
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (iff (= x (trunc x n))
                (exactp x n)))
  :rule-classes ()
  :hints (("goal" :in-theory (set-difference-theories
                              (enable expt-split expt-minus trunc-rewrite exactp2)
                              '( REARRANGE-NEGATIVE-COEFS-EQUAL
                                 FL->-INTEGER
                                 FL-<-INTEGER
                                 FL-LESS-THAN-ZERO
                                 fl-strong-monotone
                                 ))
           :use ((:instance trunc-exactp-2
                            (x (sgn x))
                            (y (* (expt 2 (- (1- n) (expo x))) (abs x)))
                            (z (expt 2 (- (1+ (expo x)) n))))
                 ))))


(defthm trunc-diff-expo
    (implies (and (rationalp x)
		  (not (exactp x n))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- x (trunc x n))) (- (expo x) n)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable abs abs-trunc)
		  :use ((:instance trunc-diff-expo-1)
			(:instance trunc-exactp-a)))))
(local
 (defthm trunc-exactp-b-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
                  )
	     (integerp (* (trunc x n) (expt 2 (- (1- n) (expo x))))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable trunc-rewrite)
		  :use ()))))

(defthm trunc-with-n-not-an-integer
  (implies (not (integerp n))
           (equal (trunc x n)
                  (if (acl2-numberp n)
                      (sgn x)
                    0)))
  :hints (("Goal" :in-theory (enable trunc))))

(local (defthm trunc-exactp-b-helper
    (implies (and; (rationalp x)
		  (integerp n) ;drop?
                  )
	     (exactp (trunc x n) n))
  :hints (("goal" :in-theory (e/d (exactp2 expt-split) ())
		  :use (
                         (:instance trunc-exactp-b-2)
                        (:instance trunc-to-0-or-fewer-bits)
                        )))))

;improve by concluding (exactp (trunc x n) m+) if m+ >= m ??
(defthm trunc-exactp-b
  (exactp (trunc x n) n)
  :hints (("goal" :in-theory (e/d () (trunc-exactp-b-helper))
           :use (trunc-exactp-b-helper))))


(defthm trunc-exactp-c
    (implies (and (exactp a n)
		  (<= a x)
                  (rationalp x)
		  (integerp n)
		  (rationalp a)
		  )
	     (<= a (trunc x n)))
  :hints (("goal" :in-theory (disable abs-trunc trunc-exactp-b)
		  :use ((:instance trunc-exactp-b)
			(:instance trunc-exactp-a)
			(:instance fp+1 (x (trunc x n)) (y a))
			(:instance trunc-lower-1)
                        (:instance trunc-upper-bound)
;			(:instance trunc-pos)
                        (:instance only-0-is-0-or-negative-exact (x a))
;
;                        trunc-non-neg
                        ))))

(local
 (defthm trunc-monotone-old
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (>= x 0)
		  (> n 0)
		  (<= x y))
	     (<= (trunc x n) (trunc y n)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable abs-trunc
                                      trunc-exactp-b trunc-exactp-c)
		  :use ((:instance trunc-exactp-b)
			(:instance trunc-upper-pos)
			(:instance trunc-exactp-c (x y) (a (trunc x n))))))))

;bad :linear rule; has a free var
;disable, or not?
(defthmd trunc-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n)
                )
           (<= (trunc x n) (trunc y n)))
  :hints (("Goal" :in-theory (disable trunc-upper-pos)
           :use (trunc-monotone-old
                 (:instance trunc-monotone-old (x (- y))
                            (y (- x))))))
  :rule-classes :linear)

(defthmd trunc-pos-rewrite
  (implies (and (>= x 0)
                (rationalp x)
                (integerp n))
           (equal (trunc x n)
                  (* (fl (* (expt 2 (- (1- n) (expo x))) x))
                     (expt 2 (- (1+ (expo x)) n)))))
  :hints (("goal" :in-theory (enable trunc sgn a15)
           :use fp-abs)))

(local
 (defthm trunc-trunc-1
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (= (trunc (trunc x n) m)
		(* (fl (* (expt 2 (- (1- m) (expo x)))
			  (* (fl (* (expt 2 (- (1- n) (expo x))) x))
			     (expt 2 (- (1+ (expo x)) n)))))
		   (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("goal" :in-theory (set-difference-theories
                              (enable trunc-pos-rewrite)
                              '( expo-trunc))
		  :use (;(:instance trunc-pos)
			(:instance expo-trunc)
			(:instance expo-trunc (x (trunc x n)) (n m)))))))

(local
 (defthm trunc-trunc-2
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (= (trunc (trunc x n) m)
		(* (fl (* (fl (* (expt 2 (- (1- n) (expo x))) x)) (expt 2 (- m n))))
		   (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable EXPT-COMPARE-EQUAL)
		  :use ((:instance trunc-trunc-1)
			(:instance expt-split (r 2) (j (- (1- m) (expo x))) (i (- (1+ (expo x)) n))))))))

(local
 (defthm trunc-trunc-3
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (= (trunc (trunc x n) m)
		(* (fl (/ (fl (* (expt 2 (- (1- n) (expo x))) x)) (expt 2 (- n m))))
		   (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable expt-split expt-minus)
		  :use ((:instance trunc-trunc-2))))))

(local
 (defthm trunc-trunc-4
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (= (trunc (trunc x n) m)
		(* (fl (/ (* (expt 2 (- (1- n) (expo x))) x) (expt 2 (- n m))))
		   (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable fl/int-rewrite )
           :use (
                        (:instance trunc-trunc-3)
			(:instance fl/int-rewrite
				   (x (* (expt 2 (- (1- n) (expo x))) x))
				   (n (expt 2 (- n m)))))))))

(local
 (defthm trunc-trunc-5
   (implies (and (rationalp x)
                 (>= x 0)
                 (integerp n)
                 (integerp m)
                 (> m 0)
                 (>= n m))
            (= (trunc (trunc x n) m)
               (* (fl (* (expt 2 (- (1- m) (expo x))) x))
                  (expt 2 (- (1+ (expo x)) m)))))
   :rule-classes ()
   :hints (("goal" :in-theory (enable expt-split expt-minus)
            :use ((:instance trunc-trunc-4))))))

(local
 (defthm trunc-trunc-old
    (implies (and ;(rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (>= n m))
	     (equal (trunc (trunc x n) m)
		    (trunc x m)))
  :rule-classes ()
  :hints (("goal" :use ((:instance trunc-trunc-5)
                        (:instance TRUNC-POS-REWRITE (n m))
                        )))))


(defthm trunc-trunc
  (implies (and (>= n m) ;what about other case?
                (integerp n)
                (integerp m)
                )
           (equal (trunc (trunc x n) m)
                  (trunc x m)))
  :hints (("goal" :use (trunc-trunc-old
                        (:instance trunc-trunc-old (x (- x)))))))

(local
 (defthm plus-trunc-2
  (implies (and (rationalp x)
                (> x 0)
                (rationalp y)
                (> y 0)
                (integerp k)
                (> k 0)
                (= n (+ k (- (expo x) (expo y))))
                (exactp x n))
           (equal (+ x (trunc y k))
                  (* (fl (* (+ x y) (expt 2 (- (1- k) (expo y)))))
                     (expt 2 (- (1+ (expo y)) k)))))
  :rule-classes ()
  :hints (("goal" :in-theory (set-difference-theories
                              (enable exactp2 trunc-pos-rewrite a15)
                              '( fl+int-rewrite))
           :use ((:instance fl+int-rewrite
                            (x (* y (expt 2 (- (1- k) (expo y)))))
                            (n (* x (expt 2 (- (1- k) (expo y)))))))))))

(defthm plus-trunc
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ k (- (expo x) (expo y)))))
           (= (+ x (trunc y k))
              (trunc (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable exactp2 trunc-pos-rewrite a15)
           :use ((:instance plus-trunc-2)
                 (:instance expo-monotone (y (+ x y)))))))

(defthm trunc-plus-1
    (implies (and (rationalp y)
		  (> y 0)
		  (integerp e)
		  (< y (expt 2 e)))
	     (< (expo y) e))
  :rule-classes ()
  :hints (("goal" :in-theory (disable expo)
		  :use ((:instance expo-lower-bound (x y))
			(:instance expt-strong-monotone (n (expo y)) (m e))))))

(defthm trunc-plus-2
  (implies (and (rationalp y)
                (> y 0)
                (integerp e)
                (< y (expt 2 e)))
           (< (+ (expt 2 e) y) (expt 2 (1+ e))))
  :hints (("Goal" :in-theory (enable expt-split)))
  :rule-classes ())

#|
;proved elsewhere?
(defthm trunc-plus-3
    (implies (and (rationalp y)
		  (> y 0)
		  (integerp e)
		  (< y (expt 2 e)))
	     (= (expo (+ (expt 2 e) y)) e))
  :rule-classes ()
  :hints (("goal"
		  :use ((:instance expo-lower-bound (x (+ (expt 2 e) y)))
			(:instance expo-upper-bound (x (+ (expt 2 e) y)))
			(:instance trunc-plus-2)
			(:instance expt-strong-monotone (n (expo (+ (expt 2 e) y))) (m (1+ e)))
			(:instance expt-strong-monotone (n e) (m (1+ (expo (+ (expt 2 e) y)))))))))
|#

;a nice lemma?
(defthm trunc-plus-4
    (implies (and (rationalp y)
		  (> y 0)
		  (integerp e)
		  (< y (expt 2 e))
		  (integerp m)
		  (> m 0)
		  (integerp k)
		  (> k 0)
		  (<= m (1+ k)))
	     (= (+ (expt 2 e) (trunc y k))
		(trunc (+ (expt 2 e) y) (- (+ k e) (expo y)))))
  :rule-classes ()
  :hints (("goal" :in-theory (e/d (a15) (EXPO-COMPARISON-REWRITE-TO-BOUND))
		  :use (
                        (:instance trunc-plus-1)
;			(:instance trunc-plus-3)
			(:instance plus-trunc (x (expt 2 e)) )))))

(defthm trunc-plus
    (implies (and (rationalp y)
		  (> y 0)
		  (integerp e)
		  (< y (expt 2 e))
		  (integerp m)
		  (> m 0)
		  (integerp k)
		  (> k 0)
		  (<= m (1+ k)))
	     (= (trunc (+ (expt 2 e) (trunc y k)) m)
		(trunc (+ (expt 2 e) y) m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable EXPO-COMPARISON-REWRITE-TO-BOUND)
		  :use ((:instance trunc-plus-4)
			(:instance trunc-plus-1)
;			(:instance trunc-trunc (x (+ (expt 2 e) y)) (n (- (+ k e) (expo y))))
                        ))))

(defthm trunc-n+k-1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (= e (- (1+ (expo x)) n))
		  (= y (- x (trunc x n))))
	     (< y (expt 2 e)))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance trunc-diff-pos)))))

(defthm trunc-n+k-2
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (not (= x (trunc x n)))
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (= (trunc (+ (expt 2 e) y) (1+ k))
		(trunc (+ (expt 2 e) z) (1+ k))))
  :rule-classes ()
  :hints (("Goal"; :in-theory (disable expo)
		  :use ((:instance trunc-n+k-1)
			(:instance trunc-upper-pos)
			(:instance trunc-plus (k n) (m (1+ k)))))))

(defthm trunc-n+k-3
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (and (equal (trunc x n) (* (fl (* x (expt 2 (- e)))) (expt 2 e)))
		  (equal (trunc x (+ n k)) (* (fl (* x (expt 2 (- k e)))) (expt 2 (- e k))))))
    :hints (("Goal" :in-theory (enable trunc-pos-rewrite)))
  :rule-classes ())

(defthm trunc-n+k-4
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (= (- (trunc x (+ n k)) (trunc x n))
		(* (- (fl (* x (expt 2 (- k e))))
		      (* (expt 2 k) (fl (* x (expt 2 (- e))))))
		   (expt 2 (- e k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc-pos-rewrite a15))))

(defthm trunc-n+k-5
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (= (- (trunc x (+ n k)) (trunc x n))
		(* (fl (- (* x (expt 2 (- k e)))
			  (* (expt 2 k) (fl (* x (expt 2 (- e)))))))
		   (expt 2 (- e k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable   fl+int-rewrite)
		  :use ((:instance trunc-n+k-4)
			(:instance fl+int-rewrite
				   (x (* x (expt 2 (- k e))))
				   (n (* (expt 2 k) (fl (* x (expt 2 (- e)))))))))))

(defthm trunc-n+k-6
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (= (- (trunc x (+ n k)) (trunc x n))
		(* (fl (* y (expt 2 (- k e))))
		   (expt 2 (- e k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc-pos-rewrite a15)
		  :use ((:instance trunc-n+k-5)))))

(defthm trunc-n+k-7
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (= (- (trunc x (+ n k)) (trunc x n))
		(- (* (+ (expt 2 k) (fl (* y (expt 2 (- k e)))))
		      (expt 2 (- e k)))
		   (expt 2 e))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable a15 )
		  :use ((:instance trunc-n+k-6)))))

(defthm trunc-n+k-8
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (= (- (trunc x (+ n k)) (trunc x n))
		(- (* (fl (+ (expt 2 k) (* y (expt 2 (- k e)))))
		      (expt 2 (- e k)))
		   (expt 2 e))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable  fl+int-rewrite)
		  :use ((:instance trunc-n+k-7)
			(:instance fl+int-rewrite (x (* y (expt 2 (- k e)))) (n (expt 2 k)))))))

(defthm trunc-n+k-9
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (= (- (trunc x (+ n k)) (trunc x n))
		(- (* (fl (* (expt 2 (- k e)) (+ y (expt 2 e))))
		      (expt 2 (- e k)))
		   (expt 2 e))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-n+k-8)
			(:instance expt-split (r 2) (j e) (i (- k e)))))))

(defthm trunc-n+k-10
    (implies (and (rationalp y)
		  (integerp e)
		  (<= 0 y))
	     (< 0 (+ y (expt 2 e))))
  :rule-classes ())

(defthm trunc-n+k-11
    (implies (and (integerp k)
		  (> k 0)
		  (rationalp y)
		  (> y 0)
		  (integerp e)
		  (= (expo (+ (expt 2 e) y)) e))
	     (= (* (fl (* (expt 2 (- k e)) (+ y (expt 2 e))))
		   (expt 2 (- e k)))
		(trunc (+ (expt 2 e) y) (1+ k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-n+k-10)
			(:instance trunc-pos-rewrite (x (+ y (expt 2 e))) (n (1+ k)))))))

(defthm trunc-n+k-12
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (not (= x (trunc x n)))
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (= (- (trunc x (+ n k)) (trunc x n))
		(- (trunc (+ (expt 2 e) y) (1+ k))
		   (expt 2 e))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-n+k-9)
			(:instance trunc-n+k-1)
			(:instance trunc-n+k-11)
                        (:instance EXPO-X+2**K (x y) (k e))
;			(:instance trunc-plus-3)
			(:instance trunc-diff-pos)
			(:instance trunc-upper-pos)))))

(defthm trunc-n+k-13
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (not (= x (trunc x n)))
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (= (- (trunc x (+ n k)) (trunc x n))
		(- (* (sig (trunc (+ (expt 2 e) y) (1+ k))) (expt 2 e))
		   (expt 2 e))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (sig a15)
                                  ())
		  :use ((:instance trunc-n+k-12)
			(:instance trunc-n+k-1)
			(:instance trunc-n+k-11)
                        (:instance EXPO-X+2**K (x y) (k e))
;			(:instance trunc-plus-3)
			(:instance trunc-diff-pos)
			;(:instance trunc-pos)
			(:instance trunc-upper-pos)))))

(defthm trunc-n+k-14
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (not (= x (trunc x n)))
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
;		  (= y (- x (trunc x n))) ;removed by eric, had to mention y in
;the hints
                  )
	     (= (- (trunc x (+ n k)) (trunc x n))
		(* (1- (sig (trunc (+ (expt 2 e) z) (1+ k))))
		   (expt 2 e))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-n+k-2 (y (- x (trunc x n))))
			(:instance trunc-n+k-13 (y (- x (trunc x n))))))))

(defthm trunc-n+k
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  (not (exactp x n))  		  ;;this isn't really needed, but it won't hurt me.
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
;		  (= y (- x (trunc x n))) ;removed
                  )
	     (= (- (trunc x (+ n k)) (trunc x n))
		(* (1- (sig (trunc (+ (expt 2 e) z) (1+ k))))
		   (expt 2 e))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-n+k-14)
			(:instance trunc-exactp-a)))))


 (defthm trunc-shift
   (implies (integerp n)
            (equal (trunc (* x (expt 2 k)) n)
                   (* (trunc x n) (expt 2 k))))
   :hints (("Goal" :cases ((integerp k))
            :in-theory (set-difference-theories
                        (enable sig trunc expt-split)
                        '()))))

;bad t-p rule? make rewrite too?
(defthm trunc-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n))
                )
           (integerp (trunc x n)))
  :rule-classes :type-prescription
  :hints (("goal" :in-theory (set-difference-theories
                              (enable trunc)
                              '(EXPT-2-INTEGERP
                                expt-2-positive-integer-type))
           :use ((:instance expt-2-positive-integer-type (i (- (1+ (expo x)) n)))))))

;prove a them about trunc of a power of 2?


;add to lib?  (alternate form of plus-trunc)
(defthm plus-trunc-alt
  (implies (and (exactp x (+ j (expo x) (- (expo (+ x y)))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp j)
                )
           (= (trunc (+ x y) j)
              (+ x (trunc y (+ j (- (expo (+ x y))) (expo y))))))
  :rule-classes ()
  :hints (("goal"
           :use (:instance plus-trunc
                           (k (+ j (- (expo (+ x y))) (expo y)))))))

;add to lib?
(defthm plus-trunc-corollary
  (implies (and (< y (expt 2 (- (1+ (expo x)) n)))
                (exactp x n)
                (rationalp x)
                (> x 0)
                (rationalp y)
                (>= y 0)
                (integerp n)
                )
           (= (trunc (+ x y) n)
              x))
  :hints (("Goal"  :in-theory (e/d
                               (expt-split expt-minus)
                               ( TRUNC-TO-0-OR-FEWER-BITS
                                 EXPO-COMPARISON-REWRITE-TO-BOUND
                                 EXPT-COMPARE-EQUAL))
           :use ((:instance only-0-is-0-or-negative-exact)
                             (:instance trunc-exactp-a)
                              expo-of-sum-of-disjoint
                             (:instance expo<=
                                        (x y)
                                        (n (+ (EXPO X) (* -1 N))))
                             (:instance trunc-to-0-or-fewer-bits (x y)
                                        (n (+ N (EXPO Y) (* -1 (EXPO (+ X Y))))))
                             (:instance plus-trunc-alt
                                        (j n))))))

(defthm trunc-exactp-c-eric
    (implies (and (exactp a n)
                  (<= (abs a) (abs x))
                  (rationalp x)
		  (integerp n)
		  (rationalp a)
		  )
	     (<= (abs a) (abs (trunc x n))))
  :hints (("goal" :in-theory (disable abs-trunc trunc-rewrite trunc-exactp-b)
		  :use (trunc-exactp-c
                        trunc-upper-bound
;                        (:instance trunc-rarely-zero (k n))
                        (:instance trunc-exactp-c (x (- x)) (a a))
                        (:instance trunc-exactp-c (x x) (a (- a)))
                        (:instance trunc-exactp-c (x (- x)) (a (- a))))))
  :otf-flg t)

(defthm trunc-goes-down-rewrite
  (implies (and (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n))
                )
           (equal (< (trunc x n) x)
                  (and (< 0 x)
                       (not (exactp x n)))))
  :otf-flg t
  :hints (("Goal" :use (trunc-upper-bound
                        trunc-exactp-a))))

(defthm trunc-goes-up-rewrite
  (implies (and (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n))
                )
           (equal (< x (trunc x n))
                  (and (< x 0)
                       (not (exactp x n)))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable trunc-goes-down-rewrite)
           :use ((:instance trunc-upper-bound (x (- x)))
                 trunc-exactp-a))))