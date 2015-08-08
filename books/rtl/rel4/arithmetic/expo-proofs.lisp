(in-package "ACL2")

;this book includes proofs mixing expo and expt and power2p.

;(include-book
; "include-book-macros")
;(include-book
; "float") ;remove!
(include-book "negative-syntaxp")
(include-book "power2p")
(include-book "unary-divide")
(include-book "arith2")
(include-book "integerp")
(local (include-book "fl"))
(local (include-book "expt"))
;(local (include-book "expo"))

(local (in-theory (enable expt-minus)))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

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


;probably get this anyway when we define expo
(defthm expo-integer-type
  (integerp (expo x))
  :rule-classes :type-prescription)

;(:type-prescription expo) is no better than expo-integer-type and might be worse:
(in-theory (disable (:type-prescription expo)))

(defthm expo-of-not-rationalp
  (implies (not (rationalp x))
           (equal (expo x) 0))
  :hints (("Goal" :in-theory (enable expo))))


;be careful: if you enable expo, the x<0 case of expo can loop with expo-minus
;(see expo-minus-invariant)
(defthmd expo-minus
  (equal (expo (* -1 x))
         (expo x))
  :hints (("Goal" :in-theory (enable expo))))

;rename?
(defthm expo-minus-eric
  (implies (syntaxp (negative-syntaxp x))
           (equal (expo x)
                  (expo (* -1 x))))
  :hints (("Goal" :in-theory (enable expo-minus))))


(theory-invariant
 (not (and (or (active-runep '(:rewrite expo-minus))
               (active-runep '(:rewrite expo-minus-eric)))
           (active-runep '(:definition expo))))
 :key expo-minus-invariant)


(local (in-theory (disable expo-minus expo-minus-eric)))

(defthm expo-lower-bound
  (implies (and (rationalp x)
                (not (equal x 0)))
           (<= (expt 2 (expo x)) (abs x)))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable expo expt-split))))

(defthm expo-lower-pos
  (implies (and (< 0 x)
                (rationalp x)
                )
           (<= (expt 2 (expo x)) x))
  :rule-classes :linear)

(local
 (defthm expo-upper-bound-old
  (implies (and (rationalp x)
                (not (equal x 0)))
           (< (abs x) (expt 2 (1+ (expo x)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expo expt-split)
                              '())
           :cases ((equal x 0))))))



(defthm expo-upper-bound
  (implies (rationalp x)
           (< (abs x) (expt 2 (1+ (expo x)))))
  :rule-classes :linear
  :hints (("Goal" :use (expo-upper-bound-old))))

(defthm expo-upper-pos
  (implies (rationalp x)
           (< x (expt 2 (1+ (expo x)))))
  :rule-classes :linear)



(local
 (defthm expo-unique-2
   (implies (and (rationalp x)
                 (not (equal x 0))
                 (integerp n)
                 (> n (expo x)))
            (> (expt 2 n) (abs x)))
   :rule-classes ()
   :hints (("Goal" :in-theory (disable abs)
            :use ( ;(:instance expo-upper-bound)
                  (:instance expt-weak-monotone (n (1+ (expo x))) (m n)))))))

(local
 (defthm expo-unique-1
   (implies (and (rationalp x)
                 (not (equal x 0))
                 (integerp n)
                 (< n (expo x)))
            (<= (expt 2 (1+ n)) (abs x)))
   :rule-classes ()
   :hints (("Goal" :in-theory (disable abs)
            :use ((:instance expt-weak-monotone (n (1+ n)) (m (expo x))))))))



(defthm expo-unique
  (implies (and (<= (expt 2 n) (abs x))
                (< (abs x) (expt 2 (1+ n)))
                (rationalp x)
                (integerp n)
                )
           (equal n (expo x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
           :use ((:instance expo-unique-1)
                 (:instance expo-unique-2)))))

;shouldn't have the abs??
(defthmd expo-monotone
  (implies (and (<= (abs x) (abs y))
                (case-split (rationalp x))
                (case-split (not (equal x 0)))
                (case-split (rationalp y))
                )
           (<= (expo x) (expo y)))
  :rule-classes :linear
  :hints (("Goal"
           :use (;(:instance expo-lower-bound)
                 (:instance expo-unique-2 (n (expo x)) (x y))))))

(defthm expo-2**n
  (implies (integerp n)
           (equal (expo (expt 2 n))
                  n))
  :hints (("Goal" :use ((:instance expo-unique (x (expt 2 n)))
			(:instance expt-strong-monotone (m (1+ n)))))))

;expo-half (and expo-double, sort of) makes the proof of expo-shift go through
;move
;worry about loops?
(defthm expo-half
  (implies (and (case-split (rationalp x))
                (case-split (not (equal x 0)))
                )
           (equal (expo (* 1/2 x))
              (+ -1 (expo x))))
  :hints (("Goal" :in-theory (enable expo expt))))

;move
;worry about loops?
(defthm expo-double
  (implies (and (case-split (rationalp x))
                (case-split (not (equal x 0)))
                )
           (equal (expo (* 2 x))
              (+ 1 (expo x))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expo expt)
                              '(expo-minus)))))

(theory-invariant (incompatible (:rewrite expo-half)
                                (:definition expo)
                                )
                  :key expo-half-loops-with-defn-expo)

(theory-invariant (incompatible (:rewrite expo-double)
                                (:definition expo)
                                )
                  :key expo-double-loops-with-defn-expo)

(defthm expo-shift
  (implies (and (rationalp x)
                (not (equal x 0))
                (integerp n))
           (equal (expo (* (expt 2 n) x))
                  (+ n (expo x))))
  :hints (("Goal" :in-theory (e/d (expt)
                                  ()))))

(defthm expo-shift-alt
  (implies (and (rationalp x)
                (not (equal x 0))
                (integerp n))
           (equal (expo (* x (expt 2 n)))
                  (+ n (expo x))))
  :hints (("Goal" :use  expo-shift
           :in-theory (e/d ()
                                  ( expo-shift)))))

(include-book "common-factor-defuns")

;BOZO pull this stuff into a different book:

;An "expt-factor" has the shape (expt 2 i) or the shape (/ (expt 2 i))
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



(defthmd power2p-rewrite
  (equal (power2p x)
         (equal x (expt 2 (expo x))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable power2p
                                      expt-split
                                      expt-between-one-and-two
                                      )

                              '(POWER2P-SHIFT)))))

(in-theory (disable EXPO-2**N)) ;why?

;dont export?
;like EXPO-2**N but better (now hypothesis-free)
(defthm expo-expt2
  (equal (expo (expt 2 i))
         (if (integerp i)
             i
           0))
  :hints (("goal" :in-theory (enable expt))))

(defthm power2p-expt2-i
  (power2p (expt 2 i))
  :hints (("Goal" :in-theory (enable expt power2p))))

(defthm power2p-shift-special
  (equal (power2p (* (expt 2 i) x))
         (power2p x))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '()))))

(defthm expo-expt2-inverse
  (equal (expo (/ (expt 2 i)))
         (if (integerp i)
             (- i)
           0))
  :hints (("goal" :in-theory (disable expo-expt2)
           :use (:instance expo-expt2 (i (- i))))))

(defthmd expo-/-power2p
  (implies (power2p x)
           (equal (expo (/ x))
                  (- (expo x))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable power2p)
                              '( power2p-shift EXPO-EXPT2  EXPO-EXPT2-INVERSE)))))

;restrict to only x's which look like powers of 2
(defthm expo-/-power2p-alt
  (implies (and (syntaxp (power2-syntaxp x))
                (force (power2p x)))
           (equal (expo (/ x))
                  (- (expo x))))
  :hints (("Goal" :in-theory (e/d ( expo-/-power2p) ( EXPO-EXPT2  EXPO-EXPT2-INVERSE)))))

;should we shift out by a constant using this rule?  or do we have another rule for that?
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

;BOZO think about this.  expo-shift-general depends on combining (expt 2 i) and (/ (expt 2 i)) but if
;we rewrite  (/ (expt 2 i)) to (expt 2 (* -1 i)) then this may not happen...
(theory-invariant (incompatible (:rewrite expo-shift-general)
                                (:rewrite expt-inverse)
                                )
                  :key expt-shift-general-can-loop-with-expt-inverse)



;BOZO defn expt loops


;(in-theory (disable expo-shift))

(defthm expo>=
  (implies (and (<= (expt 2 n) x)
                (rationalp x)
                (integerp n)
                )
           (<= n (expo x)))
  :otf-flg t
  :rule-classes :linear
  :hints (("goal" :use ((:instance expo-monotone (x (expt 2 n)) (y x))))))

(defthm expo<=
  (implies (and (< x (* 2 (expt 2 n)))
                (< 0 x)
                (rationalp x)
                (integerp n)
                )
           (<= (expo x) n))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable expt-split)
           :use (expo-lower-bound
                 (:instance expt-weak-monotone (n (1+ n)) (m (expo x)))))))

(in-theory (disable expo<= expo>=))

(local (in-theory (enable expo-minus)))

;more gen than expo-of-non-negative-integerp in irepsproofs
;sort of a weird way of proving this?
(encapsulate
 ()
 (local (defthm expo-of-non-negative-integerp
          (implies (and (integerp x)
                        (>= x 0))
                   (>= (expo x) 0))
          :hints (("Goal"
                   :use ((:instance expo>=
                                    (x x)
                                    (n 0)))))))

 (defthm expo-of-integer
   (implies (integerp x)
            (<= 0 (expo x)))
   :hints (("Goal" :in-theory (disable expo-of-non-negative-integerp)
            :use ((:instance  expo-of-non-negative-integerp (x x))
                  (:instance  expo-of-non-negative-integerp (x (- x))))))
   :rule-classes (:rewrite)))

(defthm expo-of-integer-type
  (implies (integerp x)
           (and (integerp (expo x)) ;included to make the conclusion a "type" fact
                (<= 0 (expo x))))
  :rule-classes ((:type-prescription :typed-term (expo x))))


(local (in-theory (disable expo-minus)))

(local (include-book "common-factor"))







;local in support/float:

;(local (in-theory (disable expt-compare)))

;kill
(local
 (defthm expo-unique-1
  (implies (and (rationalp x)
                (not (equal x 0))
                (integerp n)
                (< n (expo x)))
           (<= (expt 2 (1+ n)) (abs x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expo abs)
           :use ((:instance expt-weak-monotone (n (1+ n)) (m (expo x))))))))

;kill
(local
 (defthm expo-unique-2-alt
  (implies (and (rationalp x)
;                (not (equal x 0))
                (integerp n)
                (> n (expo x)))
           (> (expt 2 n) (abs x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expo abs)
           :use (;(:instance expo-upper-bound)
                 (:instance expt-weak-monotone (n (1+ (expo x))) (m n)))))))
;kill
;expensive?
;n is a free var
(defthmd expo-unique-eric
  (implies (and (<= (expt 2 n) (abs x))
                (< (abs x) (expt 2 (1+ n)))
                (rationalp x)
                (integerp n)
                )
           (equal (expo x) n))
  :hints (("goal" :in-theory (disable expo abs)
           :use ((:instance expo-unique-1)
                 (:instance expo-unique-2)))))





;could be even better if move hyps into the conclusion? (perhaps only when n is a constant?)
; wow! this actually worked when the one above didn't!
;reorder hyps
(defthm expo-unique-eric-2
  (implies (and (<= (expt 2 n) (abs x))
                (< (abs x) (expt 2 (1+ n)))
                (rationalp x)
                (integerp n)
                )
           (equal (equal (expo x) n)
                  t))
  :hints (("goal" :in-theory (disable expo abs)
           :use ((:instance expo-unique)))))

;find a way to make this hit (EQUAL (+ I (EXPO (/ X))) -1) to (i.e., an expression containing one call to expo)
(defthm expo-equality-reduce-to-bounds
  (implies (and (case-split (rationalp x))
                (case-split (integerp n)))
           (equal (equal (expo x) n)
                  (if (equal 0 x)
                      (equal 0 n)
                    (and (<= (expt 2 n) (abs x))
                         (< (abs x) (expt 2 (1+ n)))))))
  :hints (("goal" :in-theory (disable expo abs)
           :cases ((equal x 0)))))

(in-theory (disable expo-equality-reduce-to-bounds))

#|
(in-theory (enable expo-minus))

(defthm expo-minus-const-mult
  (implies (and (syntaxp (and (quotep k) (< (cadr k) 0))))
           (equal (EXPO (* k X))
                  (EXPO (* -1 k X)))))
|#

;combine this with others? ;BOZO delete comments?
(DEFTHM EXPO-SHIFT-constant
  (IMPLIES (AND (syntaxp (quotep k))
                (equal k (expt 2 (expo k))) ; use power2p?
                (RATIONALP X)
                (NOT (equal X 0)))
           (equal (EXPO (* k X))
              (+ (expo k) (EXPO X))))
  :HINTS (("Goal" :in-theory (disable  )
           :USE (:instance expo-shift (n (expo k))))))

;(local (in-theory (enable power2p)))


#|
(defthm expo-x+2**k-eric
    (implies (and (syntaxp (quotep k))
                  (power2p k)
		  (rationalp x)
		  (<= 0 x)
		  (< (expo x) (expo k)))
	     (equal (expo (+ k x))
		    (expo k)))
    :hints (("Goal" :in-theory (disable expo-x+2**k)
             :use (:instance expo-x+2**k (k (expo k))))))

|#



;these next 2 can be very expensive since (expt 2 k) gets calculated!

;restrict to constants k?
(defthm expo-comparison-rewrite-to-bound
  (implies (and (syntaxp (not (power2-syntaxp x))) ;helps prevent loops
                (case-split (not (equal 0 x)))
                (integerp k) ;gen?
                (case-split (rationalp x))
                )
           (equal (< (expo x) k)
                  (< (abs x) (expt 2 k))))
  :otf-flg t
  :hints (("Goal" :use ((:instance expo-monotone (x (expt 2 k)) (y x))
                        (:instance expo-monotone (y (expt 2 k)) (x x))))
          )
  )

;restrict to constants k?
(defthm expo-comparison-rewrite-to-bound-2
  (implies (and (syntaxp (not (power2-syntaxp x))) ;helps prevent loops
                (case-split (not (equal 0 x)))
                (integerp k) ;gen?
                (case-split (rationalp x))
                )
           (equal (< k (expo x))
                  (<= (expt 2 (+ k 1)) (abs x))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable EXPO-COMPARISON-REWRITE-TO-BOUND)
           :use ((:instance expo-monotone (x (expt 2 (+ 1 k))) (y x))
                 (:instance expo-monotone (y (expt 2 (+ 1 k))) (x x))))
          )
  )




;have a better version but need this for the proofs



#| true only for powers of 2
(defthm expo-/
  (equal (expo (/ x))
         (- (expo x)))
  :hints (("Goal" :in-theory (enable expo)))
)
|#


#| these might be nice:
(defthm expo-/-notpower2p
  (implies (and (not (equal x 0))
                (rationalp x)
                (not (power2p x)))
           (equal (expo (/ x))
                  (+ -1 (- (expo x)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expo expt-split  expo-equality-reduce-to-bounds)
                              '())))
)

|#









(defthm expo-bound-eric
  (implies (case-split (rationalp x))
           (and (equal (< (* 2 (expt 2 (expo x))) x)
                       nil)
                (equal (< x (* 2 (expt 2 (expo x))))
                       t)
                (equal (< (expt 2 (+ 1 (expo x))) x)
                       nil)
                (equal (< x (expt 2 (+ 1 (expo x))))
                       t)
                ))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '())
           :use expo-upper-bound)))



;if this loops, disable all the expo-shift rules!
(defthm expo-/-notpower2p
  (implies (and (not (power2p x))
                (case-split (not (equal x 0)))
                (<= 0 x)
                (case-split (rationalp x))
                )
           (equal (expo (/ x))
                  (+ -1 (- (expo x)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable power2p; expo
                                      expt-split expo-equality-reduce-to-bounds)
                              '( power2p-shift expo-shift-constant)))))

(in-theory (disable expo-/-notpower2p))

(in-theory (disable power2p-shift-special))


#|
(defthm power2p-quotient
  (implies (and (syntaxp (power2-syntaxp y))
                (case-split (power2p y)) ;this should be true if the syntaxp hyp is satisfied
                )
           (equal (power2p (/ y x))
                  (power2p x)))
  :hints (("Goal" :in-theory (disable power2p)
           :use (:instance power2p-shift (x (/ x))))))

(defthm power2p-quotient-2
  (implies (and (syntaxp (power2-syntaxp y))
                (case-split (power2p y)) ;this should be true if the syntaxp hyp is satisfied
                )
           (equal (power2p (/ x y))
                  (power2p x)))
  :hints (("Goal" :in-theory (disable power2p POWER2P-/)
           :use (:instance power2p-shift (y (/ y))))))
|#

#|
(include-book
 "abs")

(defthm expo-of-x-minus-1-nopower2-case
  (implies (and (integerp x)
                (not (power2p x))
                (<= 0 x) ;gen and add abs phrasing?
                )
           (equal (expo (+ -1 x))
                  (expo x)))
  :hints (("Goal" :use (:instance expo-unique
                                 (x (+ -1 x))
                                 (n (expo x)))
           :in-theory (enable power2p))))




(defthm expo-of-x-minus-1-power2-case
  (implies (and (integerp x) ;drop?
                (power2p x)
                (case-split (< 1 x)) ;gen?
                )
           (equal (expo (+ -1 x))
                  (+ -1 (expo x))))
  :hints (("Goal" :use (:instance expo-unique
                                  (x (+ -1 x))
                                  (n (+ -1 (expo x))))
           :in-theory (enable power2p expt-split))))


;add more conclusions.  is (expt 2...) < or <= n?
(defthm expt-expo-bound-1
  (implies (and (integerp n)
                (case-split (< 0 n))
                )
           (equal (< N (EXPT 2 (EXPO (+ -1 N))))
                  nil))
  :otf-flg t
  :hints (("Goal" :cases ((power2p n))
           :in-theory (enable expt-split)))
  )

|#

(defthm expt-compare
  (implies (and (syntaxp (and (power2-syntaxp lhs)
                              (power2-syntaxp rhs)))
                (case-split (power2p lhs))
                (case-split (power2p rhs)))
           (equal (< lhs rhs)
                  (< (expo lhs) (expo rhs))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable power2p-rewrite ; expt-strong-monotone
                                      )
                              '( ;EXPO-COMPARISON-REWRITE-TO-BOUND-1
                                EXPO-COMPARISON-REWRITE-TO-BOUND-2 ;yuck
                                power2p-shift))
           :use (:instance expt-strong-monotone (m (expo lhs)) (n (expo rhs)))
           ))
  :otf-flg t
  )


(defthm expt-compare
  (implies (and (syntaxp (and (power2-syntaxp lhs)
                              (power2-syntaxp rhs)))
                (case-split (power2p lhs))
                (case-split (power2p rhs)))
           (equal (< lhs rhs)
                  (< (expo lhs) (expo rhs))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable power2p-rewrite expt)
                              '( power2p-shift))
           :use (:instance expt-strong-monotone (m (expo lhs)) (n (expo rhs)))
           ))
  :otf-flg t
  )

(DEFTHM EXPT-COMPARE-equal
  (IMPLIES (AND (syntaxp (and (power2-syntaxp lhs)
                              (power2-syntaxp rhs)))
                (case-split (power2p lhs)) ;if the syntacp hyp goes through we expect these to also
                (case-split (power2p rhs))
                )
           (equal (equal lhs rhs)
                  (equal (expo lhs) (expo rhs))))
  :hints (("Goal"  :in-theory (set-difference-theories
                               (enable power2p-rewrite expt)
                               '( POWER2P-SHIFT))

           ))
)


(defthm power2-integer
  (implies (and (syntaxp (power2-syntaxp x))
                (force (power2p x)))
           (equal (integerp x)
                  (<= 0 (expo x))))
  :hints (("Goal" :use (:instance expt2-integer (i (expo x)))
             :in-theory (set-difference-theories
                         (enable power2p-rewrite expt)
                         '( POWER2P-SHIFT expt2-integer)))))

#| old stuff
(defthm a14
  (and
   (implies (and (integerp i)
                 (<= 0 i)
                 (<= 0 j))
            (and (integerp (expt i j))
                 (<= 0 (expt i j))))
   (implies (and (rationalp i)
                 (not (equal i 0)))
            (not (equal (expt i j) 0))))
  :hints
  (("Goal" :in-theory (enable expt)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (and (integerp i)
                  (<= 0 i)
                  (<= 0 j))
             (and (integerp (expt i j))
                  (<= 0 (expt i j)))))
   (:type-prescription
    :corollary
    (implies (and (rationalp i)
                  (not (equal i 0)))
             (not (equal (expt i j) 0))))))




(defthm a16
  (equal (expt (* a b) i)
         (* (expt a i) (expt b i)))
  :hints
  (("Goal" :in-theory (enable distributivity-of-expt-over-*))))
(defthm my-exponents-add
  (implies (and (not (equal 0 r))
                (acl2-numberp r)
                (integerp i)
                (integerp j))
           (equal (expt r (+ i j))
                  (* (expt r i)
                     (expt r j))))
  :rule-classes nil)

|#


#|
(defthm expt-2-reduce-leading-constant-gen
  (implies (case-split (integerp (+ k d)))
           (equal (expt 2 (+ k d))
                  (* (expt 2 (fl k)) (expt 2 (+ (mod k 1) d)))))
  :otf-flg t
   :hints (("Goal" :in-theory (set-difference-theories
                                (enable; fl
)
                                '(expt-split mod))
             :use (:instance expt-split (r 2) (i (fl k)) (j (+ (mod k 1) d))))))
|#



(defthm expo-shift-16
  (implies (and (case-split (integerp n))
                (case-split (rationalp x))
                (case-split (not (equal x 0)))
                )
           (equal (expo (* (/ (expt 2 n)) x))
                  (+ (- n) (expo x))))


  )

(defthm expo-lower-bound-2
  (implies (and (case-split (rationalp x))
                (case-split (<= 0 x))
                (case-split (not (equal x 0)))
                )
           (<= (expt 2 (expo x)) x))
  :rule-classes :linear
)

(defthmd expo-upper-bound-tight
  (implies (integerp x)
           (<= (abs x) (+ -1 (expt 2 (1+ (expo x))))))
  :hints (("Goal" :use (expo-upper-bound)))
  :rule-classes :linear)

;BOZO simplify the conclusion?
(defthm expo-x+a*2**k
  (implies (and (< (expo x) k)
                (< 0 a)
                (integerp a)
                (case-split (<= 0 x))
                (case-split (integerp k))
                (case-split (rationalp x))
                )
           (equal (expo (+ x (* a (expt 2 k))))
                  (expo (* a (expt 2 k)))))
  :hints (("goal" :in-theory (e/d (expt-split) ( ;EXPO-BOUND-ERIC
                                                 ;CANCEL-IN-PRODS-<-2-OF-2-WITH-2-OF-3
                                                 ))
           :use ((:instance expo-lower-bound (x (* a (expt 2 k))))
                 (:instance expo-upper-bound-tight (x a))
                 (:instance expo-unique
                            (x (+ x (* a (expt 2 k)))) (n (expo (* a (expt 2 k))))))))
  :otf-flg t)

(defthm expo-x+2**k
    (implies (and (< (expo x) k)
                  (<= 0 x)
                  (case-split (integerp k))
		  (case-split (rationalp x))
		  )
	     (equal (expo (+ x (expt 2 k)))
		    k))
  :hints (("Goal" :use (:instance  expo-x+a*2**k (a 1)))))





(local (defthmd between-0-and-1-means-not-integerp
  (implies (and (< 0 x) (< x 1))
           (not (integerp x)))))

(defthm expo-times-2-not-a-factor
  (implies (rationalp x)
           (equal (integerp (* 1/2 x (/ (expt 2 (expo x)))))
                  (equal 0 x)))
  :hints (("Goal" :in-theory (enable expt-minus expt-split)
           :use ( expo-lower-bound
                  expo-upper-bound
                  (:instance  BETWEEN-0-AND-1-MEANS-NOT-INTEGERP
                              (x  (* 1/2 (abs X) (EXPT 2 (* -1 (EXPO X))))))))))

(local (defthmd between-1-and-2-means-not-integerp
  (implies (and (< 1 x) (< x 2))
           (not (integerp x)))))

(local (defthm expo-a-factor-means-power2-helper
  (implies (and (<= 0 x)
                (rationalp x))
           (equal (integerp (* x (/ (expt 2 (expo x)))))
                  (or (equal 0 x)
                      (power2p (abs x)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d( expt-minus expt-split power2p-rewrite) ( EXPO-BOUND-ERIC))
           :use (expo-lower-bound
                 expo-upper-bound
                 (:instance BETWEEN-1-AND-2-MEANS-NOT-INTEGERP (x (* x (/ (expt 2 (expo x)))))))))))

(defthm expo-a-factor-means-power2
  (implies (acl2-numberp x)
           (equal (integerp (* x (/ (expt 2 (expo x)))))
                  (or (equal 0 x)
                      (power2p (abs x)))))
  :hints (("Goal" :in-theory (enable expo-minus-eric)
           :use ((:instance  expo-a-factor-means-power2-helper (x x))
                        (:instance  expo-a-factor-means-power2-helper (x (- x)))))))

