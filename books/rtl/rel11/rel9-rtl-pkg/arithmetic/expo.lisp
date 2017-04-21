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

(in-package "RTL")

;This book contains theorems mixing expt and expo and power2p.
;It is the top-level book for reasoning about powers of two.
;Eric believes that the function EXPO is intimately connected to EXPT (they are inverses).  Some of his
;theorems about EXPT require EXPO for their statements.

;Todo:
;1. Write a more general version of EXPO that isn't tied to using 2 as the base?
;2. Use more consistent names for lemmas, including using expt2 for lemmas which only apply when the r paramater
;to expt is 2.

(include-book "ground-zero")
(include-book "negative-syntaxp")
(include-book "power2p")
(local (include-book "expo-proofs"))  ;there's now a separate expo-proofs book !!!
;ad local in-thoery nil

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

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


;probably get this anyway when we define expo
(defthm expo-integer-type
  (integerp (expo x))
  :rule-classes :type-prescription)

;(:type-prescription expo) is no better than expo-integer-type and might be worse:
(in-theory (disable (:type-prescription expo)))

(defthm expo-of-not-rationalp
  (implies (not (rationalp x))
           (equal (expo x) 0)))


;be careful: if you enable expo, the x<0 case of expo can loop with expo-minus
;(see expo-minus-invariant)
(defthmd expo-minus
  (equal (expo (* -1 x))
         (expo x)))

;rename?
(defthm expo-minus-eric
  (implies (syntaxp (negative-syntaxp x))
           (equal (expo x)
                  (expo (* -1 x)))))


(theory-invariant
 (not (and (or (active-runep '(:rewrite expo-minus))
               (active-runep '(:rewrite expo-minus-eric)))
           (active-runep '(:definition expo))))
 :key expo-minus-invariant)

;Eric doesn't like the presence of ABS here...
(defthm expo-lower-bound
  (implies (and (rationalp x)
                (not (equal x 0)))
           (<= (expt 2 (expo x)) (abs x)))
  :rule-classes :linear)

(defthm expo-lower-pos
  (implies (and (< 0 x)
                (rationalp x)
                )
           (<= (expt 2 (expo x)) x))
  :rule-classes :linear)

;make expo-lower-neg? expo-upper-neg? bad names? expo-lower-neg would really be an upper bound!

(defthm expo-upper-bound
  (implies (rationalp x)
           (< (abs x) (expt 2 (1+ (expo x)))))
  :rule-classes :linear)

(defthm expo-upper-pos
  (implies (rationalp x)
           (< x (expt 2 (1+ (expo x)))))
  :rule-classes :linear)

(defthm expo-unique
  (implies (and (<= (expt 2 n) (abs x))
                (< (abs x) (expt 2 (1+ n)))
                (rationalp x)
                (integerp n)
                )
           (equal n (expo x)))
  :rule-classes ())

;bad to have the abs there?
(defthmd expo-monotone
  (implies (and (<= (abs x) (abs y))
                (case-split (rationalp x))
                (case-split (not (equal x 0)))
                (case-split (rationalp y))
                )
           (<= (expo x) (expo y)))
  :rule-classes :linear)

;BOZO. drop this in favor of expo-expt2?
(defthmd expo-2**n
  (implies (integerp n)
           (equal (expo (expt 2 n))
                  n)))

;dont export?
;like EXPO-2**N but better (now hypothesis-free)
;This rule, together with expt-compare allows any comparison using <, >, <=, or >= of two terms which have the
;form of powers of 2 to be rewritten to a claim about the exponents.  actually, we need a rule about (expo (/ <powerof2>))
;can kill more specialized rules
;use ifix?
(defthm expo-expt2
  (equal (expo (expt 2 i))
         (if (integerp i)
             i
           0)))

;Can loop with defn expo. See theory-invariant.
;expo-half (and expo-double, sort of) makes the proof of expo-shift go through
(defthm expo-half
  (implies (and (case-split (rationalp x))
                (case-split (not (equal x 0)))
                )
           (equal (expo (* 1/2 x))
                  (+ -1 (expo x)))))

(theory-invariant (incompatible (:rewrite expo-half)
                                (:definition expo)
                                )
                  :key expo-half-loops-with-defn-expo)

(theory-invariant (incompatible (:rewrite expo-double)
                                (:definition expo)
                                )
                  :key expo-double-loops-with-defn-expo)



;Can loop with defn expo.  See the theory-invariant.
(defthm expo-double
  (implies (and (case-split (rationalp x))
                (case-split (not (equal x 0)))
                )
           (equal (expo (* 2 x))
                  (+ 1 (expo x)))))

(defthm expo-x+a*2**k
  (implies (and (< (expo x) k)
                (< 0 a)
                (integerp a)
                (case-split (<= 0 x))
                (case-split (integerp k))
                (case-split (rationalp x))
                )
           (equal (expo (+ x (* a (expt 2 k))))
                  (expo (* a (expt 2 k))))))

;special case of the above
(defthm expo-x+2**k
    (implies (and (< (expo x) k)
                  (<= 0 x)
                  (case-split (integerp k))
		  (case-split (rationalp x))
		  )
	     (equal (expo (+ x (expt 2 k)))
		    k)))



(defthmd expo>=
  (implies (and (<= (expt 2 n) x)
                (rationalp x)
                (integerp n)
                )
           (<= n (expo x)))
  :rule-classes :linear)


(defthmd expo<=
  (implies (and (< x (* 2 (expt 2 n)))
                (< 0 x)
                (rationalp x)
                (integerp n)
                )
           (<= (expo x) n))
  :rule-classes :linear)

(defthm expo-of-integer-type
  (implies (integerp x)
           (and (integerp (expo x)) ;included to make the conclusion a "type" fact
                (<= 0 (expo x))))
  :rule-classes ((:type-prescription :typed-term (expo x))))

;!! rc?
;actually, maybe we should rewrite the conclusion instead? <-- how?
(defthm expo-of-integer
  (implies (integerp x)
           (<= 0 (expo x)))
  :rule-classes (:rewrite))



;expensive?
;n is a free var
;gotta get rid of the abs if we hope to bind n appropriately
(defthmd expo-unique-eric
  (implies (and (<= (expt 2 n) (abs x))
                (< (abs x) (expt 2 (1+ n)))
                (rationalp x)
                (integerp n)
                )
           (equal (expo x) n)))





;could be even better if move hyps into the conclusion? (perhaps only when n is a constant?)
; wow! this actually worked when the one above didn't! (probably because this one doesn't have a free var)
;expensive??
(defthm expo-unique-eric-2
  (implies (and (<= (expt 2 n) (abs x))
                (< (abs x) (expt 2 (1+ n)))
                (rationalp x)
                (integerp n)
                )
           (equal (equal (expo x) n)
                  t))
)

;find a way to make this hit (EQUAL (+ I (EXPO (/ X))) -1) to (i.e., an expression containing one call to expo)
(defthmd expo-equality-reduce-to-bounds
  (implies (and (case-split (rationalp x))
                (case-split (integerp n)))
           (equal (equal (expo x) n)
                  (if (equal 0 x)
                      (equal 0 n)
                    (and (<= (expt 2 n) (abs x))
                         (< (abs x) (expt 2 (1+ n))))))))






;these next 2 can be very expensive since (expt 2 k) gets calculated!  Meh.

;disable??
;restrict to constants k?
(defthm expo-comparison-rewrite-to-bound
  (implies (and (syntaxp (not (power2-syntaxp x))) ;helps prevent loops
                (case-split (not (equal 0 x)))
                (integerp k) ;gen?
                (case-split (rationalp x))
                )
           (equal (< (expo x) k)
                  (< (abs x) (expt 2 k)))))
;disable?
;restrict to constants k?
(defthm expo-comparison-rewrite-to-bound-2
  (implies (and (syntaxp (not (power2-syntaxp x))) ;helps prevent loops
                (case-split (not (equal 0 x)))
                (integerp k) ;gen?
                (case-split (rationalp x))
                )
           (equal (< k (expo x))
                  (<= (expt 2 (+ k 1)) (abs x)))))



(defthm power2p-expt2-i
  (power2p (expt 2 i)))


;have a better version but need this for the proofs - huh?
;BOZO, so don't export this! ??
(defthmd expo-expt2-inverse
  (equal (expo (/ (expt 2 i)))
         (if (integerp i)
             (- i)
           0)))

;why disabled?
(defthmd power2p-shift-special
  (equal (power2p (* (expt 2 i) x))
         (power2p x)))

(defthmd expo-/-power2p-1
  (equal (expo (/ (expt 2 i)))
         (- (expo (expt 2 i)))))

;drop, since we have the one below?
(defthmd expo-/-power2p
  (implies (power2p x)
           (equal (expo (/ x))
                  (- (expo x)))))

;restrict to only x's which look like powers of 2
(defthm expo-/-power2p-alt
  (implies (and (syntaxp (power2-syntaxp x))
                (force (power2p x)))
           (equal (expo (/ x))
                  (- (expo x)))))





(defthm expo-bound-eric
  (implies (case-split (rationalp x))
           (and (equal (< (* 2 (EXPT 2 (EXPO X))) X)
                       nil)
                (equal (< X (* 2 (EXPT 2 (EXPO X))))
                       t)
                (equal (< (EXPT 2 (+ 1 (EXPO X))) X)
                       nil)
                (equal (< X (EXPT 2 (+ 1 (EXPO X))))
                       t)
                )))



;if this loops, disable all the expo-shift rules!
(defthmd expo-/-notpower2p
  (implies (and (not (power2p x))
                (case-split (not (equal x 0)))
                (<= 0 x)
                (case-split (rationalp x))
                )
           (equal (expo (/ x))
                  (+ -1 (- (expo x))))))

(defthmd power2p-rewrite
  (equal (power2p x)
         (equal x (expt 2 (expo x)))))

;rename to powers-of-2-less-than?
;An inequality between powers of two can be rewritten to an inequality about their exponents...
;this allows LHS or RHS (or both) to be a gross term like, e.g., this: (* 2 (* (expt 2 j) (expt 2 (+ k (* -1 j)))))
;we expect the EXPO introduced in the conclusion go away (it will crawl to the leaves of RHS and LHS, each of which is
;either a constant or of the form (EXPT 2 I).
(defthm expt-compare
  (implies (and (syntaxp (and (power2-syntaxp lhs)
                              (power2-syntaxp rhs)))
                (case-split (power2p lhs)) ;use force?
                (case-split (power2p rhs)))
           (equal (< lhs rhs)
                  (< (expo lhs) (expo rhs))))

  :otf-flg t
  )

(defthm expt-compare-equal
  (implies (and (syntaxp (and (power2-syntaxp lhs)
                              (power2-syntaxp rhs)))
                (case-split (power2p lhs)) ;if the syntaxp hyp goes through we expect these to also
                (case-split (power2p rhs)) ;use force?
                )
           (equal (equal lhs rhs)
                  (equal (expo lhs) (expo rhs)))))


;this can be a powerful rule...
;We expect the call to EXPO in the conclusion to go away (it should be pushed to the leaves...)
(defthm power2-integer
  (implies (and (syntaxp (power2-syntaxp x))
                (force (power2p x)))
           (equal (integerp x)
                  (<= 0 (expo x))
                  )))



;BOZO dup with expo-lower-pos
(defthm expo-lower-bound-2
  (implies (and (case-split (rationalp x))
                (case-split (<= 0 x))
                (case-split (not (equal x 0)))
                )
           (<= (expt 2 (expo x)) x))
  :rule-classes :linear)


;we need these next 2, even though we have expt-shift-general
;why did i say the above??
;BOZO rename params.  put ifix around i
(defthm expo-shift
  (implies (and (rationalp x)
                (not (equal x 0))
                (integerp n))
           (equal (expo (* (expt 2 n) x))
                  (+ n (expo x)))))

(defthm expo-shift-alt
  (implies (and (rationalp x)
                (not (equal x 0))
                (integerp n))
           (equal (expo (* x (expt 2 n)))
                  (+ n (expo x)))))

(defthm expo-shift-16
  (implies (and (case-split (integerp n))
                (case-split (rationalp x))
                (case-split (not (equal x 0)))
                )
           (equal (expo (* (/ (expt 2 n)) x))
                  (+ (- n) (expo x)))))

;BOZO combine this with others?
(defthm expo-shift-constant
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (expo k))) ; use power2p?
                (rationalp x)
                (not (equal x 0)))
           (equal (expo (* k x))
                  (+ (expo k) (expo x)))))

(include-book "common-factor-defuns")

;An "expt-factor" has the shape (expt 2 i) or the shape (/ (expt 2 i))
;does not consider constants to be "expt-factors", so we have expo-shift-constant
(defun get-expt-factors (factor-list)
  (declare (xargs :guard (true-listp factor-list)))
  (if (endp factor-list)
      nil
    (let* ((factor (car factor-list)))
      (if (and (consp factor)
               (or (and (equal (car factor) 'expt)
                        (consp (cdr factor))
                        (equal (cadr factor) ''2))
                   (and (equal (car factor) 'unary-/)
                        (consp (cdr factor))
                        (consp (cadr factor))
                        (equal (caadr factor) 'expt)
                        (consp (cdadr factor))
                        (equal (cadadr factor) ''2))))
          (cons factor (get-expt-factors (cdr factor-list)))
        (get-expt-factors (cdr factor-list))))))


(defun find-common-expt-factors-to-cancel (expr)
  (declare (xargs :guard (and (pseudo-termp expr))))
  (get-expt-factors
   (remove-cancelling-factor-pairs
    (find-common-factors-in-sum-of-products expr))))

(defund bind-k-to-common-expt-factors (expr)
  (declare (xargs :guard-hints (("Goal" :use (:instance remove-cancelling-factor-pairs-preserves-true-listp
                                                        (l (MY-INTERSECTION-EQUAL (FIND-COMMON-FACTORS-IN-SUM-OF-PRODUCTS LHS)
                                                                                  (FIND-COMMON-FACTORS-IN-SUM-OF-PRODUCTS RHS))))))
                  :guard (and (pseudo-termp expr))))
  (let* ((common-factor-list (find-common-expt-factors-to-cancel expr)))
    (if (endp common-factor-list)
        nil
      (list (cons 'k (make-product-from-list-of-factors common-factor-list))))))



(defthm expo-shift-general
  (implies (and (bind-free (bind-k-to-common-expt-factors x) (k))
                (syntaxp (not (equal k x))) ;helps prevent loops
                (force (power2p k))
                (case-split (rationalp x)) ;if not, we want to know about it
                (case-split (not (equal x 0))) ;if x=0 we can simplify further
                )
           (equal (expo x)
                  (+ (expo k) (expo (* (/ k) x)))))
  :hints (("goal" :in-theory (enable power2p-rewrite)
           :use (:instance expo-shift (n (- (expo k)))))))


;BOZO think about this.  expo-shift-general depends on combining (expt 2 i) and (/ (expt 2 i)) but if we
;rewrite (/ (expt 2 i)) to (expt 2 (* -1 i)) then this may not happen...  (We don't have a complete set of
;rules for gathering expt terms, especially in cases like this: (* (expt 2 i) x y w z (expt 2 (* -1 i)))
;So currently one cannot have both expt-inverse and expt-shift enabled...
;We could address this by writing a rule which will always gather expt
;terms in a product, even if other terms intervene between them.  If we are guaranteed to always do all
;gathering, then expo-shift-general should work okay (i.e., shouldn't loop).
;Man, I can't figure out how to write an easy bind-free rule to do all gathering. Even if we walk through the
;term and decide what to cancel out, e.g., the (expt 2 i) and the (expt 2 (* -1 i)) in
;  (* (expt 2 i) x y w z (expt 2 (* -1 i)))
;we can't just multiply through by their inverses (which would be the standard way to cancel something in a
;product) because the inverting would get sucked in by expt-inverse.  So an attempt to cancel by multiplying
;through by (/ (expt 2 i)) and (/ (expt 2 (* -1 i))) would be the same as multipying through by (expt 2 (* -1 i))
;and (expt 2 (* -1 (* -1 i))) = (expt 2 i), respectively.  Yuck.  Maybe we can use some sort of bubble-down
;strategy like Rober Krug does.
;It's unfortunate that we don't get any expo-shifting if we are gathering exponents...
(theory-invariant (incompatible (:rewrite expo-shift-general)
                                (:rewrite expt-inverse)
                                )
                  :key expo-shift-general-can-loop-with-expt-inverse)



(defthm expo-times-2-not-a-factor
  (implies (rationalp x)
           (equal (integerp (* 1/2 x (/ (expt 2 (expo x)))))
                  (equal 0 x))))

(defthm expo-a-factor-means-power2
  (implies (acl2-numberp x)
           (equal (integerp (* x (/ (expt 2 (expo x)))))
                  (or (equal 0 x)
                      (power2p (abs x))))))
