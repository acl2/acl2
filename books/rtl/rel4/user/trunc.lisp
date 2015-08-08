;;;***************************************************************
;;;an acl2 library of floating point arithmetic

;;;david m. russinoff
;;;advanced micro devices, inc.
;;;february, 1998
;;;***************************************************************

;some of the things in this book are cruft which can be deleted...

(in-package "ACL2")
(local (include-book "../support/trunc"))


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


(defund trunc (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

;; New stuff:

;generated automatically by ACL2 when we define trunc, but included here just to be safe could have disabled
;(:type-prescription trunc) for slight efficiency gain at the cost of making the output of :pe a little
;deceptive
(defthm trunc-rational-type-prescription
  (rationalp (trunc x n))
  :rule-classes :type-prescription)

(defthm trunc-of-non-rationalp-is-0
  (implies (not (rationalp x))
           (equal (trunc x n)
                  0)))

(defthm trunc-to-0-or-fewer-bits
  (implies (and (<= n 0)
                (integerp n)
                )
           (equal (trunc x n)
                  0)))

;make alt version? use negative-syntaxp?
(defthm trunc-minus
  (equal (trunc (* -1 x) n)
         (* -1 (trunc x n))))

;change what trunc does with n not a positive int?
(defthm trunc-positive
  (implies (and (< 0 x)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n))
                )
           (< 0 (trunc x n)))
  :rule-classes (:rewrite :linear))

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
  :rule-classes (:rewrite :linear))

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
         0))

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
  :rule-classes :type-prescription)

(defthm trunc-non-positive-rational-type-prescription
  (implies (and (<= x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                )
           (and (<= (trunc x n) 0)
                (rationalp (trunc x n))))
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
                  (sgn x))))


;why not just open up trunc and sgn?
;keep this disabled, since it basically opens up TRUNC
(defthmd abs-trunc
  (equal (abs (trunc x n))
         (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n)))))

(defthm trunc-upper-bound
  (implies (and (rationalp x)
                (integerp n))
           (<= (abs (trunc x n)) (abs x)))
  :rule-classes :linear)

;BOZO bad name. should be trunc-equal-0
(defthm trunc-equal-0-rewrite
  (implies (and (> n 0)
                (rationalp x)
                (integerp n)
                )
           (equal (equal (trunc x n) 0)
                  (equal x 0))))

(defthm trunc-upper-pos
    (implies (and (<= 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (trunc x n) x))
    :rule-classes :linear)

(defthm expo-trunc
   (implies (and (< 0 n)
                 (rationalp x)
                 (integerp n)
                 )
            (equal (expo (trunc x n))
                   (expo x))))

;which of these do we want to export?
(defthm trunc-lower-1
  (implies (and (rationalp x)
                (integerp n))
           (> (abs (trunc x n))
              (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear)

(defthm trunc-lower-2-1
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (<= (expt 2 (- (1+ (expo x)) n)) (* (abs x) (expt 2 (- 1 n)))))
  :rule-classes ())

(defthm trunc-lower-2
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (> (abs (trunc x n)) (* (abs x) (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthm trunc-lower-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (> (trunc x n) (* x (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthm trunc-lower-3
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (abs (trunc x n)) (* (abs x) (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthm trunc-lower-4
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (trunc x n) (- x (* (abs x) (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthm trunc-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- x (trunc x n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())

(defthm trunc-diff-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (< (- x (trunc x n)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())

(defthm trunc-diff-expo-1
    (implies (and (rationalp x)
		  (not (= x (trunc x n)))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- x (trunc x n))) (- (expo x) n)))
  :rule-classes ())

;just gets rid of sig...
(defthmd trunc-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0) ;gen?  this isn't in pos-rewrite!
                  )
	     (equal (trunc x n)
		    (* (sgn x)
		       (fl (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n))))))

(defthm trunc-exactp-a
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (iff (= x (trunc x n))
                (exactp x n)))
  :rule-classes ())

(defthm trunc-diff-expo
    (implies (and (rationalp x)
		  (not (exactp x n))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- x (trunc x n))) (- (expo x) n)))
  :rule-classes ())

;improve by concluding (exactp (trunc x n) m+) if m+ >= m ??
(defthm trunc-exactp-b
  (exactp (trunc x n) n))

(defthmd trunc-exactp-c
  (implies (and (exactp a n)
                (<= a x)
                (rationalp x)
                (integerp n)
                (rationalp a)
                )
           (<= a (trunc x n))))

;bad :linear rule; has a free var
;disable, or not?
(defthmd trunc-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n)
                )
           (<= (trunc x n) (trunc y n)))
  :rule-classes :linear)

(defthmd trunc-pos-rewrite
  (implies (and (>= x 0)
                (rationalp x)
                (integerp n))
           (equal (trunc x n)
                  (* (fl (* (expt 2 (- (1- n) (expo x))) x))
                     (expt 2 (- (1+ (expo x)) n))))))

(defthm trunc-trunc
  (implies (and (>= n m) ;what about other case?
                (integerp n)
                (integerp m)
                )
           (equal (trunc (trunc x n) m)
                  (trunc x m))))

(defthm plus-trunc
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ k (- (expo x) (expo y)))))
           (= (+ x (trunc y k))
              (trunc (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ())

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
  :rule-classes ())

;what's the purpose of this one?
(defthm trunc-n+k
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (> k 0)
                (integerp n)
                (>= n k)
                (not (exactp x n)) ;;this isn't really needed, but it won't hurt me.
                (= e (- (1+ (expo x)) n))
                (= z (trunc (- x (trunc x n)) n))
;		  (= y (- x (trunc x n))) ;removed
                )
           (= (- (trunc x (+ n k)) (trunc x n))
              (* (1- (sig (trunc (+ (expt 2 e) z) (1+ k))))
                 (expt 2 e))))
  :rule-classes ())

 (defthm trunc-shift
   (implies (integerp n)
            (equal (trunc (* x (expt 2 k)) n)
                   (* (trunc x n) (expt 2 k)))))

;bad t-p rule? make rewrite too?
(defthm trunc-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n))
                )
           (integerp (trunc x n)))
  :rule-classes :type-prescription)

;prove a them about trunc of a power of 2?