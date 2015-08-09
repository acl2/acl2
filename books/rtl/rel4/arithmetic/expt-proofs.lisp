(in-package "ACL2")

;this book contains very basic expt stuff (i couldn't include expt.lisp in basic.lisp because of a circular dependency)

;todo:
;make a separate expt-proofs book
;there's a distinction between expt and expt-2 rules
;make consistent names:  expt vs. expt2
;think about the rules to combine and split exponents
;generalize some of these rules to be about expt with any base (not just 2)

;remove this?
(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(include-book "ground-zero")
(include-book "negative-syntaxp")
(local (include-book "predicate"))
(local (include-book "fp2"))
(local (include-book "numerator"))
(local (include-book "denominator"))
(local (include-book "integerp"))
(local (include-book "fl")) ;or use floor?
(local (include-book "arith2"))

(encapsulate
 ()
 (local (include-book "arithmetic/top" :dir :system))
 (defthm a16
   (equal (expt (* a b) i)
          (* (expt a i) (expt b i)))
   :hints
   (("Goal" :in-theory (enable distributivity-of-expt-over-*))))

;gen
;split off the non-integer case
;make an expt2-split?
;instead of i1 and i2, use i and j?
 (defthmd expt-split
   (implies (and (integerp i)
                 (integerp j)
                 (case-split (acl2-numberp r)) ;(integerp r)
                 (case-split (not (equal r 0)))
                 )
            (equal (expt r (+ i j))
                   (* (expt r i) (expt r j))))
   :hints (("Goal" :in-theory (enable expt)))
   )
 )

(theory-invariant
  (not (and (active-runep '(:rewrite expt-split))
            (active-runep '(:rewrite a15))))
  :key expt-split-invariant)

(theory-invariant
  (not (and (active-runep '(:rewrite expt-split))
            (active-runep '(:definition expt))))
  :key expt-split-invariant-2)


;see also a14
;generalize?  use arith books?
(defthm expt-2-positive-rational-type
  (and (rationalp (expt 2 i))
       (< 0 (expt 2 i)))
  :hints (("Goal" :in-theory (enable expt) ))
  :rule-classes (:rewrite (:type-prescription :typed-term (expt 2 i))))

;like a14?
(defthm expt-2-positive-integer-type
  (implies (<= 0 i)
           (and (integerp (expt 2 i))
                (< 0 (expt 2 i))))
  :hints (("Goal" :in-theory (enable expt)))
  :rule-classes (:type-prescription))

;someday our rules may be better, but right now, ours only talk about when when the base is 2
;(in-theory (disable (:TYPE-PRESCRIPTION EXPT)))


;the rewrite rule counterpart to expt-2-positive-integer-type
(defthm expt-2-integerp
  (implies (<= 0 i)
           (integerp (expt 2 i))))

(defthm expt-2-type-linear
  (implies (<= 0 i)
           (<= 1 (expt 2 i)))
  :rule-classes ((:linear :trigger-terms ((expt 2 i)))))



;when you disable either of the two rules below, you might want to also disable expt-compare?
;took these rules out of :rewrite since we have expt-compare?
;are these bad :linear rules because they have free vars?

(encapsulate
 ()
 (local (defthm expt-strong-monotone-1
          (implies (and (integerp n)
                        (integerp k)
                        (> k 0))
                   (< (expt 2 n) (expt 2 (+ n k))))
          :hints (("Goal" :in-theory (enable expt
                                             )))
          :rule-classes ()))

 (defthmd expt-strong-monotone
   (implies (and (integerp n)
                 (integerp m))
            (equal (< (expt 2 n) (expt 2 m))
                   (< n m)))
   :hints (("Goal" :use ((:instance expt-strong-monotone-1 (k (- m n)))
                         (:instance expt-strong-monotone-1 (k (- n m)) (n m))
                         )))))

;improve to handle i non-integer?
(defthm expt2-integer
  (implies (case-split (integerp i))
           (equal (integerp (expt 2 i))
                  (<= 0 i)))
  :hints (("Goal" :use (:instance expt-strong-monotone (n i) (m 0)))))

;trying :match-free :all
;why disabled?
(defthmd expt-strong-monotone-linear
  (implies (and (< n m)
                (case-split (integerp n))
                (case-split (integerp m))
                )
           (< (expt 2 n) (expt 2 m)))
  :rule-classes ((:linear :match-free :all))
  :hints (("Goal" :use expt-strong-monotone)))

;why disabled?
(defthmd expt-weak-monotone
  (implies (and (integerp n)
                (integerp m))
           (equal (<= (expt 2 n) (expt 2 m))
		  (<= n m)))
  :hints (("Goal" :use (expt-strong-monotone
			(:instance expt-strong-monotone (m n) (n m))))))

;disabled because of the free var
;but is occasionally helpful
;make linear?
;BOZO rename params?
;trying :match-free :all
(defthmd expt-weak-monotone-linear
  (implies (and (<= n m)
                (case-split (integerp n))
                (case-split (integerp m)))
           (<= (expt 2 n) (expt 2 m)))
  :rule-classes ((:linear :match-free :all))
  :hints (("Goal" :use (expt-strong-monotone
			(:instance expt-strong-monotone (m n) (n m))))))

;generalize? rewrite (< (expt 2 i) k) to a comparison of (expt 2 i) and the greatest power of 2 <= k
;is this what expt-compare does?
(defthmd expt-between-one-and-two
  (implies (and (<= 1 (expt 2 i))
                (< (expt 2 i) 2))
           (equal (expt 2 i) 1))
  :hints (("goal"
           :in-theory (enable expt zip))
          ("subgoal *1/7" :use (:instance expt-weak-monotone (n (+ i 1)) (m 0)))))



;We could disable this if it causes problems (but it seems okay).
;should always use case-split n hyps that say exponents are integers
(defthm expt-with-i-non-integer
  (implies (not (integerp i))
           (equal (expt r i)
                  1))
  :hints (("Goal" :in-theory (enable expt))))

(defthmd expt-minus-helper
  (equal (expt r (* -1 i))
         (/ (expt r i)))
  :otf-flg t
  :hints (("Goal" :cases ((integerp i) (and (not (integerp i)) (acl2-numberp i)))
           :in-theory (enable expt))))

;BOZO disable or enable by default?
;Loops with expt-inverse. How do we want to handle this??
;I'd rather have the inverting done outside EXPT since most rules don't look inside EXPT.
;This rule can be said to scatter exponents...
(defthmd expt-minus
  (implies (syntaxp (negative-syntaxp i))
           (equal (expt r i)
                  (/ (expt r (* -1 i)))))
  :hints (("Goal" :in-theory (enable expt-minus-helper
                                     expt-split))))

(local (in-theory (enable expt-minus)))

;This can loop with expt-minus (see theory-invariant).
(defthmd expt-inverse
  (equal (/ (expt 2 i))
         (expt 2 (* -1 i))))

(theory-invariant
  (not (and (active-runep '(:rewrite expt-minus))
            (active-runep '(:rewrite expt-inverse))))
  :key expt-minus-invariant)


;could prove a rule for (expt (* -1 r) i) ... or maybe we have a rule for expt when r is a product...

;rename to expt-gather? !
;Note that this rule isn't enough to gather exponents in every situation.  For example, two factors, (expt 2 i)
;and (expt 2 j), won't be gathered if there are intervening factors between them.
;BOZO change param names
(defthmd a15
  (implies (and (rationalp i)
                (not (equal i 0))
                (integerp j1)
                (integerp j2))
           (and (equal (* (expt i j1) (expt i j2))
                       (expt i (+ j1 j2)))
                (equal (* (expt i j1) (* (expt i j2) x))
                       (* (expt i (+ j1 j2)) x))))
  :hints (("Goal" :in-theory (enable expt-split))))

(defthm expt-r-0
  (equal (expt r 0)
         1)
  :hints (("Goal" :in-theory (enable expt))))





(defthm expt-0-i
  (implies (and (case-split (integerp i))      ;since expt with a non-integer index is 1
                (case-split (not (equal 0 i))) ;since (expt 0 0) is 1
                )
           (equal (expt 0 i)
                  0))
  :hints (("Goal" :in-theory (enable expt))))





;==== A scheme for preventing massively expensive calls to expt =======

#| When ACL2 encounters a function call with constant arguments, the simplifier just evaluates the function on
those arguments.  However, calls of (expt r i) with huge i can be very expensive to compute.  (I suppose calls
with huge r might be very expensive too, but r is almost always 2 in my work.)  The scheme below prevents
(expt r i) from being evaluated when i is too large (but allows evaluation in the case of small i).

|#

(in-theory (disable (:executable-counterpart expt)))

(set-compile-fns t)
(defun expt-execute (r i) (expt r i))

;Allows expt calls with small exponents to be computed
;You can change 1000 to your own desired bound.
(defthm expt-execute-rewrite
  (implies (and (syntaxp (and (quotep r) (quotep i) (< (abs (cadr i)) 1000))))
           (equal (expt r i)
                  (expt-execute r i))))


#|
The rules below are not complete, I proved them as needed to simplify terms like:
(* x
   (EXPT 2 1000001)
   (/ (EXPT 2 1000000))
   y)

Note that we could just compute (EXPT 2 1000001) and (EXPT 2 1000000) but that would be very expensive.

Perhaps we can make this into a complete theory, based on the observation that if a product contains two
factors of the form (expt 2 k) of (/ (expt 2 k)), where k is a constant, those factors will be brought
together because they are very close in the term order used order arguments to * (recall that unary-/ is
ignored when we decide how to order arguments to *).
|#

;this could be made more general (replace the lhs with its second arg...)
(defthm expt2-constants-collect-special-1
  (implies (and (syntaxp (and (quotep i1) (quotep i2)))
                (case-split (rationalp y))
                (case-split (integerp i1))
                (case-split (integerp i2)))
           (equal  (* (EXPT 2 i1)
                      (/ (EXPT 2 i2))
                      y)
                   (* (expt 2 (- i1 i2)) y)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '())))
  )

(defthm expt2-constants-collect-special-2
  (implies (and (syntaxp (and (quotep i1) (quotep i2)))
                (case-split (integerp i1))
                (case-split (integerp i2)))
           (equal  (* (EXPT 2 i1)
                      (/ (EXPT 2 i2))
                      )
                   (expt 2 (- i1 i2))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '())))
  )

(defthm expt2-constants-collect-special-4
  (implies (and (syntaxp (and (quotep i1) (quotep i2)))
                (case-split (rationalp y))
                (case-split (integerp i1))
                (case-split (integerp i2)))
           (equal (* (/ (EXPT 2 i2)) (EXPT 2 i1) y)
                  (* (expt 2 (- i1 i2)) y)))

  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '()))))

(defthm expt2-constants-collect-special-5
  (implies (and (syntaxp (and (quotep i1) (quotep i2)))
                (case-split (integerp i1))
                (case-split (integerp i2)))
           (equal  (* (/ (EXPT 2 i2)) (EXPT 2 i1))
                   (expt 2 (- i1 i2))))

  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '()))))



;will this happen?
(defthm expt2-constants-collect-special-6
  (implies (and (syntaxp (and (quotep i1) (quotep i2)))
                (case-split (rationalp x))
                (case-split (integerp i1))
                (case-split (integerp i2)))
           (equal  (* (EXPT 2 i2) x (EXPT 2 i1))
                   (* (expt 2 (+ i1 i2)) x)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '()))))


;whoa this one is sort of different... (it rewrites an equality)
(defthm expt2-constants-collect-special-3
  (implies (and (syntaxp (and (quotep i1) (quotep i2)))
                (case-split (rationalp x))
                (case-split (integerp i1))
                (case-split (integerp i2)))
           (equal (equal (* x (EXPT 2 i1)) (EXPT 2 i2))
                  (equal x (expt 2 (- i2 i1)))))

  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '())))
)






;==================================================================

;expt-compare
;handle constants as args?
(defthm expt2-1-to-1
  (implies (and (integerp i1)
                (integerp i2))
           (equal (equal (expt 2 i1) (expt 2 i2))
                  (equal i1 i2)))
  :hints (("Goal"
           :use ((:instance expt-strong-monotone (n i1) (m i2))
                 (:instance expt-strong-monotone (n i2) (m i1))))))







;could gen? move hyps to concl?
(defthm expt-even
  (implies (and (< 0 i)
                (case-split (integerp i))
                )
           (integerp (* 1/2 (expt 2 i))))
  :hints (("goal" :in-theory (enable expt))))


;generalize rules like this with a power2-syntaxp (not power2p!) ?
;make conclusion an equality?
(defthm expt-quotient-integerp
  (implies (and (<= j i)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (integerp (* (expt 2 i) (/ (expt 2 j)))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (expt-split) ( expt-2-integerp))
           :use (:instance expt-2-positive-integer-type (i (- i j))))))

(defthm expt-quotient-integerp-alt
  (implies (and (<= j i)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (integerp (* (/ (expt 2 j)) (expt 2 i))))
  :rule-classes (:rewrite :type-prescription))


;is there a 2 term version?
(defthm expt-prod-integer-3-terms
  (implies (and (integerp n)
                (<= 0 (+ i j))
                (integerp i)
                (integerp j)
                )
           (integerp (* (expt 2 i) (expt 2 j) n)))
  :hints (("Goal" :in-theory (enable a15))))


;drop these?
;generalize to comparisons to any constant (any power of 2)?

;bad name?

(defthm expt2-inverse-integer
  (implies (case-split (integerp i))
           (equal (integerp (/ (expt 2 i)))
                  (<= i 0)))
  :hints (("Goal" :in-theory (disable expt2-integer)
           :use (:instance expt2-integer (i (- i))))))

;figure out a better solution to this problem
;perhaps say if a term is a power of 2, then it's an integer iff its expo is >=0
(defthm expt-prod-integer-3-terms-2
  (implies (and (<= 0 (+ i (- j) (- l)))
                (integerp i)
                (integerp j)
                (integerp l)
                )
           (integerp (* (expt 2 i) (/ (expt 2 j)) (/ (expt 2 l)))))
  :hints (("Goal" :in-theory (set-difference-theories (enable a15 expt-inverse)
                                                      '(expt-minus))))
  )

#| would be nice (use expt2-1-to-1)?
(defthm expt2-equal-1
  (implies (integerp i)
           (equal (EQUAL (EXPT 2 i) 1)
                  (equal i 0)))
;  :rule-classes nil
  :hints (("Goal" :in-theory (enable expt-split-rewrite)))
)
|#

(defthm expt2-inverse-even
  (implies (case-split (integerp i))
           (equal (integerp (* 1/2 (/ (expt 2 i))))
                  (<= (+ 1 i) 0)))
  :otf-flg t
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '(expt2-integer  EXPT2-INVERSE-INTEGER))
           :use (:instance expt2-integer (i (+ -1 (- i)))))))


;loops with a15?
; (expt (* 2 i)) was matching with (expt 2 0) (booo!) so I added the syntaxp hyp
(defthmd expt-2-split-product-index
  (implies (and (syntaxp (not (quotep i)))
                (case-split (rationalp r))
                (case-split (integerp i)))
           (equal (expt r (* 2 i))
                  (* (expt r i) (expt r i))))
  :hints (("Goal" :in-theory (disable expt-split)
           :use (:instance expt-split (i i) (j i)))))


;linear?
(defthm expt-bigger-than-i
  (implies (integerp i)
           (< i (expt 2 i)))
  :hints (("Goal" :in-theory (enable expt)))
  )

;BOZO this might loop with expt-split
;i'm not sure that this is a good rewrite anyway
(defthmd expt-compare-with-double
  (implies (and (integerp x)
                (integerp i))
           (equal (< (* 2 x) (expt 2 i))
                  (< x (expt 2 (+ -1 i)))))
  :hints (("Goal" :in-theory (enable expt-split))))

;leave this disabled?
(defthmd expt-2-reduce-leading-constant-gen
  (implies (case-split (integerp (+ k d)))
           (equal (expt 2 (+ k d))
                  (* (expt 2 (fl k)) (expt 2 (+ (mod k 1) d)))))
    :hints (("Goal" :in-theory (set-difference-theories
                                (enable mod)
                                '(expt-split))
             :use (:instance expt-split (r 2) (i (fl k)) (j (+ (mod k 1) d))))))


;handles the case when k isn't even an integer!
;loops with a15!  add theory invariant....
(defthmd expt-2-reduce-leading-constant
  (implies (and (syntaxp (and (quotep k)
                         (or (>= (cadr k) 1) (< (cadr k) 0))))
                (case-split (integerp (+ k d)))
                )
           (equal (expt 2 (+ k d))
                  (* (expt 2 (fl k)) (expt 2 (+ (mod k 1) d)))))
    :hints (("Goal" :in-theory (set-difference-theories
                                (enable)
                                '(expt-split))
             :use (expt-2-reduce-leading-constant-gen
                   (:instance expt-split (r 2) (i (fl k)) (j (+ (mod k 1) d)))))))

; BOZO better than a15?
(defthmd expt-combine
  (implies (and (case-split (rationalp r))
                (case-split (not (equal r 0)))
                (case-split (integerp i1))
                (case-split (integerp i2)))
           (and (equal (* (expt r i1) (expt r i2))
                       (expt r (+ i1 i2)))
                (equal (* (expt r i1) (* (expt r i2) x))
                       (* (expt r (+ i1 i2)) x))))
  :hints (("goal" :in-theory (enable a15))))


;remove since we have expt-compare?
(defthm expt-with-small-n
  (implies (<= n 0)
           (<= (expt 2 n) 1))
  :hints (("Goal" :use (:instance expt-weak-monotone (m 0))))
  :rule-classes (:linear))


#|
(include-book
 "factor-2")


;which way do we want to do this?
;disable later?
;add a "can have a 2 multiplied in" hyp to this series?
(defthm expt-2-combine-like-is
  (implies (and (syntaxp (should-have-a-2-factor-multiplied-in i))
                (integerp i))
           (equal (* (expt 2 i) (expt 2 i))
                  (expt 2 (* 2 i))))
  :hints (("Goal" :in-theory (disable expt-split)
           :use (:instance expt-split (r 2) (i i) (j i)))))

(defthm expt-2-combine-like-is-3-and-4-of-6
  (implies (and (syntaxp (should-have-a-2-factor-multiplied-in i))
                (integerp i)
                (rationalp a)
                (rationalp b)
                (rationalp c)
                (rationalp d)
                )
           (equal (* a b (expt 2 i) (expt 2 i) c d )
                  (* a b c d (expt 2 (* 2 i)))))
  :hints (("Goal" :in-theory (disable expt-split)
           :use (:instance expt-split (r 2) (i i) (j i)))))

(defthm expt-2-combine-like-is-4-and-5-of-6
  (implies (and (syntaxp (should-have-a-2-factor-multiplied-in i))
                (integerp i)
                (rationalp a)
                (rationalp b)
                (rationalp c)
                (rationalp d)
                )
           (equal (* a b c (expt 2 i) (expt 2 i) d )
                  (* a b c d (expt 2 (* 2 i)))))
  :hints (("Goal" :in-theory (disable expt-split)
           :use (:instance expt-split (r 2) (i i) (j i)))))



(defthm expt-2-combine-like-is-inverted
  (implies (and (syntaxp (should-have-a-2-factor-multiplied-in i))
                (integerp i))
           (equal (* (/ (EXPT 2 i))
                     (/ (EXPT 2 i)))
                  (/ (expt 2 (* 2 i)))))
  :hints (("Goal" :in-theory (disable
                              expt-2-combine-like-is
                              expt-split)
           :use (:instance  expt-split (r 2) (i (* 1/2 i)) (j (* 1/2 i))))))

|#







#|
(defthm expt-prod-integer-4-terms
  (implies (and (integerp i)
                (integerp j)
                (integerp l)
                (<= 0 (+ i (- j) l))
                (integerp n))
           (integerp (* (expt 2 i) (/ (expt 2 j)) (expt 2 l) n)))
  :hints (("Goal" :in-theory (set-difference-theories (enable a15 expt-inverse)
                                                      '(expt-minus))))
  )




would be nice (use expt2-1-to-1)?
(defthm expt2-equal-1
  (implies (integerp i)
           (equal (EQUAL (EXPT 2 i) 1)
                  (equal i 0)))
;  :rule-classes nil
  :hints (("Goal" :in-theory (enable expt-split)))
)


;remove?
;actually, maybe this is good whether we are scattering or gathering...
;bad name?
;in general, are there rules which are good for scattering and for gathering?
(defthm expt-simp
  (implies (integerp x)
           (equal (* 2 (EXPT 2 (+ -1 x)))
                  (expt 2 x)))
  :hints (("Goal" :use (:instance a15 (i 2) (j1 1) (j2 (+ -1 x))))))


(defthmd expt-next
  (implies (and (integerp i1)
                (integerp i2)
                (< (expt 2 i1) (expt 2 i2)))
           (<= (expt 2 i1) (expt 2 (+ -1 i2)))))



|#


(local (include-book "even-odd"))

;move? make fw-chaining rule?
(defthmd even-not-equal-odd
  (implies (and (evenp x)
                (oddp y))
           (not (equal x y)))
  :hints (("Goal" :in-theory (enable oddp))))

;this is sort of strange...
(defthm expt-2-is-not-odd
  (implies (and (evenp x)
                (< 0 i) ;drop?
                (integerp i)
                )
           (equal (equal (expt 2 i)
                         (+ 1 x))
                  nil))
  :hints (("Goal" :in-theory (enable evenp oddp  even-not-equal-odd)))  ;shouldn't have to enable oddp
  :otf-flg t)


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


#|
;this will get rewritten away?
(defthm expt-in-product-linear
  (implies (and (<= 0 i)
		(<= 0 x)
                (case-split (rationalp x))
                )
	   (<= x (* x (expt 2 i))))
  :rule-classes (:linear)
  )

;this will get rewritten away?
(defthm expt-in-product-linear-2
   (implies (and (case-split (<= i 0))
                 (case-split (<= 0 x))
                 (case-split (rationalp x))
                 )
            (<= (* x (expt 2 i)) x))
   :rule-classes (:linear)
   )

|#

;crap.  This unifies with (EXPT '2 '0), which we see because we disable the executable counterpart of expt to
;prevent massively expensive calls.
;loops with a15!!
;add theory invar!
;does this already exist?
(defthmd expt-with-product-exponent
  (implies (and (syntaxp (not (quotep i)))
                (case-split (integerp i)))
	   (equal (expt 2 (* 2 i))
		  (* (expt 2 i) (expt 2 i))))
  :hints (("Goal" :in-theory (enable a15))))



;yuck
;perhaps use only expt-2-positive-integer-type;
;don't need this if natp is enabled?
(defthmd natp-expt
  (implies (natp n)
           (and (integerp (expt 2 n))
                (< 0 (expt 2 n))))
  :rule-classes (:type-prescription :rewrite))



#|

these deal with arbitrary bases (not just 2):

(local (include-book
        "../../../arithmetic-2/meta/expt"))
(local
 (include-book
  "../arithmetic/product"))

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (>= x 0))))



;allows both a and b to be non-integers:
(defthm expt-non-negative
  (implies (and (<= 0 a)
		(<= 0 b)
		(case-split (rationalp a))
		)
	   (<= 0 (expt a b))))

(defthm expt-integerp
  (implies (and (natp a)
		(<= 0 b)
		)
	   (integerp (expt a b))))

|#


;there are funny little rules...

(defthm expt-exceeds-another-by-more-than-1
  (implies (and (<= 0 i)
                (<= 0 j)
                (integerp i)
                (integerp j)
                )
           (implies (< (+ 1 i) j)
                    (< (+ 1 (expt 2 i)) (expt 2 j))))
  :hints (("Goal" :in-theory (enable expt-split)
           :use (:instance expt-strong-monotone (n (+ 1 i)) (m j)))))


(defthm expt-exceeds-2
  (IMPLIES (AND (< i j)
                (<= 0 i)
                (<= 0 j)
                (INTEGERP i)
                (INTEGERP j)
                )
           (<= (+ 1 (EXPT 2 i)) (EXPT 2 j)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (:instance expt-strong-monotone (n i) (m j)))))

#|

Are there some rules (such as this one) which we want enabled for both scaterring and gathering exponents?

(defthm expt-hack
  (equal (* (expt 2 n) (expt 2 (* -1 n))) 1)
  :hints (("Goal" :in-theory (e/d () (EXPT-minus)))))

(defthm expt-hack-2
  (equal (* (expt 2 (* -1 n)) (expt 2 n)) 1)
  :hints (("Goal" :in-theory (e/d () (EXPT-minus)))))
|#


(defthm expt-with-i-non-integer-special
  (implies (not (integerp i))
           (equal (EXPT 2 (+ -1 i))
                  (if (acl2-numberp i)
                      1
                    1/2))))
