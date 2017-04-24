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

(include-book "ground-zero")
(include-book "../../arithmetic/negative-syntaxp")
(include-book "../../arithmetic/power2p")

(local (include-book "../../arithmetic/top"))
(local (include-book "bvecp"))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))


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

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))


;this book is still a mess

(defun fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

#|

The new version of bits is like Russinoff's "bits" but uses mod instead of rem.
The use of "mod" seems to allow nicer results to be proved.

For example, bits now *always* returns a non-negative integer.  Many hyps of other lemmas require
expressions to be non-negative integers, and with the old bits, this requires further checking of the
arguments (at worst, checking all the way to the leaves of the expression tree each time).

Add case-split to all hyps about i and j (indices to bits must be integers and j must be <= i or else weird
stuff may happen (but we can easily handle these cases).

|#

;In proofs about RTL terms, i and j should always be natural number constants

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defthm bits-nonnegative-integerp-type
  (and (<= 0 (bits x i j))
       (integerp (bits x i j)))
  :hints (("Goal" :in-theory (enable bits)))
  :rule-classes (:type-prescription))

;this rule is no better than bits-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription bits)))

;dup with bits-0!
(defthm bits-with-x-0
  (equal (bits 0 i j)
         0)
  :hints (("Goal" :in-theory (enable bits))))

(defthm bits-with-i-not-an-integer
  (implies (not (integerp i))
           (equal (bits x i j)
                  0))
  :hints (("Goal" :in-theory (enable bits))))

(defthm bits-with-j-not-an-integer
  (implies (not (integerp j))
           (equal (bits x i j)
                  0))
  :hints (("Goal" :in-theory (enable bits))))

(defthm bits-with-indices-in-the-wrong-order
  (implies (< i j)
           (equal (bits x i j)
                  0))
  :hints (("Goal" :in-theory (enable bits))))

(defthm bits-upper-bound
  (< (bits x i j) (expt 2 (+ 1 i (- j))))
  :rule-classes (:rewrite (:linear :trigger-terms ((bits x i j))))
  :hints (("Goal" :in-theory (enable bits
                                     expt-minus
                                     expt-split))))

;has the right pattern to rewrite stuff like this: (<= (EXPT 2 J) (BITS Y (+ -1 J) 0)) to nil
(defthm bits-upper-bound-special
  (< (BITS x (1- i) 0) (EXPT 2 i))
  :hints (("Goal" :use (:instance bits-upper-bound (i (1- i)) (j 0))))
  )

;tigher bound
(defthm bits-upper-bound-tighter
  (implies (case-split (<= j i))
           (<= (bits x i j) (1- (expt 2 (+ i 1 (- j))))))
  :rule-classes (:rewrite (:linear :trigger-terms ((bits x i j))))
  :hints (("Goal" :cases ((rationalp x) (not (acl2-numberp x)))
           :in-theory (enable bits
                              expt-minus
                              expt-split))))


;like  mod-upper-bound-3
(defthm bits-upper-bound-2
  (implies (and (<= (expt 2 (+ 1 i (- j))) z) ;backchain-limit?
                ;(case-split (integerp i))
                ;(case-split (integerp j))
                )
           (< (bits x i j) z)))



#|
;I have many theorems dealing with the simplification of bits of a sum

(include-book
 "lowbits")


;taking sort of a long time (3-4 secs)
(defthm bits-sum-lowbits
  (implies (and (rationalp x)
                (rationalp y)
                (integerp i)
                (integerp j))
           (equal (bits (+ x             y) i j)
                  (bits (+ (lowbits x i) y) i j)))
  :hints (("Goal" :in-theory (enable ;mod-cancel
                              bits
                              lowbits))))
(in-theory (disable bits-sum-lowbits))

;special case of the above -- helps rewrite the constant to a unique (positive) value
;make another rule to handle negative constants
(defthm bits-sum-reduce-leading-constant
  (implies (and (syntaxp (and (quotep x) (>= (cadr x) (expt 2 (+ (cadr i) 1)))))
                (rationalp x)
                (rationalp y)
                (integerp i)
                (integerp j))
           (equal (bits (+ x             y) i j)
                  (bits (+ (lowbits x i) y) i j)))
  :hints (("Goal" :use bits-sum-lowbits )))

(defun oldbits (x i j)
  (fl (/ (rem x (expt 2 (1+ i))) (expt 2 j))))

(in-theory (disable bits)) ;move up

;(in-theory (disable INTEGER-HAS-DENOM-1-OTHER-WAY))

(in-theory (disable rem))


|#

;a is a free var
(defthm bits-force
  (implies (and (<= (* a (expt 2 (+ i 1))) x)
                (< x (* (1+ a) (expt 2 (+ i 1))))
                (integerp x)
                (integerp i)
;                (<= 0 i)
                (integerp a)
                )
           (equal (bits x i 0) (- x (* a (expt 2 (+ i 1))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable bits)
           :use (:instance  mod-force-eric (y (expt 2 (+ i 1)))))))

(defthm bits-force-with-a-chosen-neg
  (implies (and (< x 0)
                (<= (* -1 (expt 2 (+ i 1))) x)
;                (<= 0 i)
                (integerp x)
                (integerp i)
                )
           (equal (bits x i 0) (- x (* -1 (expt 2 (+ i 1))))))
  :hints (("Goal"
           :use (:instance bits-force (a -1)))))

;remove:?
;(in-theory (disable bits-force))

;expensive?
;make a corollary?
(defthm bits-shift
  (implies (and ;(rationalp x)
            (case-split (integerp n))
            (case-split (integerp i))
            (case-split (integerp j))
            )
           (and (equal (bits (* (expt 2 n) x) i j)
                       (bits x (- i n) (- j n)))
                (equal (bits (* x (expt 2 n)) i j)
                       (bits x (- i n) (- j n)))))
  :hints (("Goal" :cases ((and (acl2-numberp n) (not (rationalp n)))
                          (and (rationalp n) (not (integerp n)))
                          (integerp n))
           :in-theory (e/d (expt-minus
                              mod-cancel
                              bits
                              expt-split

                              )
                           (  ;these are disabled to speed up he proof:
                            INTEGERP-PROD-OF-3-FIRST-AND-LAST
                              INTEGERP-PROD-OF-3-LAST-TWO
                              a10
                              a13)))))

; Basically a restatement of bits-shift:
(defthm bits-shift-up-1
  (implies (and (integerp k)
		(integerp i)
		(integerp j))
	   (equal (bits (* (expt 2 k) x) i j)
		  (bits x (- i k) (- j k))))
  :hints (("Goal" :use ((:instance bits-shift (n k)))))
  :rule-classes ())

#| original:
(defthm bits-shift
  (implies (and ;(rationalp x)
            (case-split (integerp n))
            (case-split (integerp i))
            (case-split (integerp j))
            )
           (and (equal (bits (* (expt 2 n) x) i j)
                       (bits x (- i n) (- j n)))
                (equal (bits (* x (expt 2 n)) i j)
                       (bits x (- i n) (- j n)))))
  :hints (("Goal" :cases ((and (acl2-numberp n) (not (rationalp n)))
                          (and (rationalp n) (not (integerp n)))
                          (integerp n))
           :in-theory (enable expt-minus
                              mod-cancel
                              bits
                              expt-split))))
|#

(local (in-theory (enable mod-cancel)))

;allows you to split bit vectors into two parts
;free var n (where to split)
;resembles doc's bits-plus-bits-1 and another rule in merge
(defthm bits-plus-bits2
  (implies (and ;(rationalp x)
                (integerp i)
                (integerp j)
                (integerp n)
                (<= j n)
                (<= n i)
                )
           (equal (bits x i j)
                  (+ (* (bits x i n) (expt 2 (- n j)))
                     (bits x (1- n) j))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable bits mod expt-split expt-minus))))

;a hint that worked for this before I made such nice rules is in junk.lisp under bits-plus-bits-hint

;(in-theory (disable bits-plus-bits-1)) ;keep disabled


#|
;use mbitn?
;could use even-odd phrasing?
(defthm bits-down-to-1-case-split
  (implies (and (integerp x)
                (<= 0 x)
                (integerp i)
                (<= 1 i))
           (equal (bits x i 1)
                  (if (equal (bitn x 0) 0)
                      (/ (bits x i 0) 2) ;use the fact that we know bit 0 is 0?
                    (/ (1- (bits x i 0)) 2) ;use the fact that we know bit 0 is 1?
                    )))
  :otf-flg t
  :hints (("Goal" :in-theory (enable bits mod bitn))))
|#

;this really has two separate cases
;generalize with j not 0?
(defthm bits-split-around-zero
  (implies (and (>= x (- (expt 2 (+ i 1))))
                (< x (expt 2 (+ i 1)))
                (integerp x)
                (case-split (integerp i))
                (case-split (<= 0 i))
                )
           (equal (bits x i 0)
                  (if (<= 0 x)
                      x
                    (+ x (expt 2 (+ i 1))))))
 :hints (("Goal" :in-theory (enable bits)
          :use ((:instance bits-force (a 0))
                (:instance bits-force (a -1))))))


;(local (in-theory (disable expt-inverse)))

(defthm bits-bvecp-simple
  (implies (equal k (+ 1 i (* -1 j)))
           (bvecp (bits x i j) k))
  :hints (("Goal" :in-theory (enable
                              bvecp))))



(defthm bits-bvecp
  (implies (and (<= (+ 1 i (- j)) k)
                (case-split (integerp k))
                )
           (bvecp (bits x i j) k))
  :hints (("Goal" :use ((:instance bits-bvecp-simple
                                   (k (+ 1 i (* -1 j)))))
           :in-theory (disable bits-bvecp-simple))))

(in-theory (disable bits-bvecp-simple))

;do we want this rule enabled?
(defthm bits-bvecp-fw
  (implies (equal n (- (1+ i) j)) ; note equal here to help with the fw chaining
           (bvecp (bits x i j) n))
  :rule-classes
  ((:forward-chaining :trigger-terms ((bits x i j)))))

;these may be made moot by my method of using lowbits with bits of a sum

#|
(defthm bits-sum-simplify-first-term
  (implies (and (>= (abs x) (expt 2 (+ j 1))) ;prevents loop
                (rationalp x)
                (rationalp y)
                (integerp j)
                (<= 0 j)
                )
           (equal (bits (+ x y) j 0)
                  (bits (+ (lowbits x j) y) j 0)))
  :hints (("Goal" :in-theory (enable lowbits
                                     bits))))

(defthm bits-sum-simplify-second-term
  (implies (and (>= (abs x) (expt 2 (+ j 1))) ;prevents loop
                (rationalp x)
                (rationalp y)
                (integerp j)
                (<= 0 j)
                )
           (equal (bits (+ y x) j 0)
                  (bits (+ (lowbits x j) y) j 0)))
  :hints (("Goal" :in-theory (enable lowbits
                                     bits))))

|#


(local (in-theory (disable mod-cancel)))

;better names: make the dropped term x, the others a,b,c,...
;;; more bits thms like this!

(defthm bits-sum-drop-irrelevant-term-2-of-2
  (implies (integerp (/ y (expt 2 (+ 1 i))))
           (equal (bits (+ x y) i j)
                  (bits x i j)))
  :hints (("Goal" :cases ((rationalp y) (not (acl2-numberp y)))
           :in-theory (enable bits))))

(defthm bits-sum-drop-irrelevant-term-1-of-2
  (implies (integerp (/ y (expt 2 (+ 1 i))))
           (equal (bits (+ y x) i j)
                  (bits x i j)))
  :hints (("Goal"  :cases ((rationalp y) (not (acl2-numberp y)))
           :in-theory (enable bits))))

(defthm bits-sum-drop-irrelevant-term-3-of-3
  (implies (integerp (/ y (expt 2 (+ 1 i))))
           (equal (bits (+ w x y) i j)
                  (bits (+ w x) i j)))
  :hints (("Goal" :in-theory (disable bits-sum-drop-irrelevant-term-1-of-2
                                      bits-sum-drop-irrelevant-term-2-of-2)
           :use (:instance bits-sum-drop-irrelevant-term-1-of-2 (x (+ w x))))))

(defthm bits-sum-drop-irrelevant-term-2-of-3
  (implies (integerp (/ y (expt 2 (+ 1 i))))
           (equal (bits (+ w y x) i j)
                  (bits (+ w x) i j)))
  :hints (("Goal" :in-theory (disable bits-sum-drop-irrelevant-term-3-of-3
                                      bits-sum-drop-irrelevant-term-1-of-2
                                      bits-sum-drop-irrelevant-term-2-of-2)
           :use (:instance bits-sum-drop-irrelevant-term-1-of-2 (x (+ w x))))))
#|
(defthm bits-sum-drop-irrelevant-term-1-of-3
  (implies (and (integerp x)
                (integerp y)
                (integerp w)

                (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j)

                (integerp (/ y (expt 2 (+ 1 i))))
                )
           (equal (bits (+ y w x) i j)
                  (bits (+ w x) i j)))
  :hints (("Goal" :in-theory (disable bits-sum-drop-irrelevant-term-2-of-3
                                      bits-sum-drop-irrelevant-term-3-of-3
                                      bits-sum-drop-irrelevant-term-1-of-2
                                      bits-sum-drop-irrelevant-term-2-of-2)
           :use (:instance bits-sum-drop-irrelevant-term-1-of-2 (x (+ w x))))))
|#


#|

This series of events deals with simplifying expressions like
(equal (bits x 8 0)
       (+ (bits x 6 0) k))
Intuitively, bits 6 down-to 0 appear on both sides of the sum and should be "cancelled".
The remaining bits will need to be "shifted" back into place.

More rules are probably needed to make the theory complete.
|#

#|
(defthm bits-cancel-lowbits-in-comparison
  (implies (and (> i+ i)
                (rationalp k)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)
                )
           (equal (equal (+ k (bits x i j))
                         (bits x i+ j))
                  (equal (* (expt 2 (+ 1 i (- j)))
                            (BITS X I+ (+ 1 I)))
                         k)))
  :hints (("Goal"
           :use (:instance bits-plus-bits-1 (n (+ i 1)) (i i+))
           :in-theory (enable expt-split)
           )))

(defthm bits-cancel-lowbits-in-comparison-alt-2
  (implies (and (> i+ i)
                (rationalp k)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)
                )
           (equal (equal (+ (bits x i j) k)
                         (bits x i+ j))
                  (equal (* (expt 2 (+ 1 i (- j)))
                            (BITS X I+ (+ 1 I)))
                         k)))
  :hints (("Goal"
           :use (:instance bits-plus-bits-1 (n (+ i 1)) (i i+))
           :in-theory (enable expt-split)
           )))
|#

#|
;todo: rephrase the conclusion of the above by moving the "constant" (* 2 (EXPT 2 I) (/ (EXPT 2 J))) to the other
;side
;a good idea since k is usually divisible by that quantity (with the rule above, we often end up with an
equality in which each side should have a power of 2 divided out of it
; not needed if we have good meta rules for cancelling factors from an inequality


(defthm bits-cancel-lowbits-in-comparison-2
  (implies (and (> i+ i)
                (rationalp k)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)

                )
           (equal (equal (+ k (bits x i j))
                         (bits x i+ j))
                  (equal (*
                            (BITS X I+ (+ 1 I)))
                         (/ k (expt 2 (+ 1 i (- j)))))))
  :hints (("Goal"
           :use (:instance bits-cancel-lowbits-in-comparison)
           :in-theory (set-difference-theories
                       (enable expt-split)
                       '(bits-cancel-lowbits-in-comparison))
           )))
|#

#|

(defthm bits-cancel-lowbits-in-comparison-3
  (implies (and (> i+ i)
                (rationalp k)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)
                (rationalp y)
                )
           (equal (equal (+ (bits x i+ j) k)
                         (+ y (bits x i j)))
                  (equal (* (expt 2 (+ 1 i (- j )))
                            (BITS X I+ (+ 1 I)))
                         (- y k))))
  :hints (("Goal"
           :use (:instance bits-plus-bits-1 (n (+ i 1)) (i i+))
           :in-theory (set-difference-theories
                       (enable expt-split)
                       '(
                         BITS-CANCEL-LOWBITS-IN-COMPARISON-ALT-2))
           )))

;better conclusion?
(defthm bits-cancel-lowbits-in-comparison-no-constant
  (implies (and (> i+ i)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)
                )
           (equal (equal (bits x i j)
                         (bits x i+ j))
                  (equal (* 2 (EXPT 2 I)
                           (/ (EXPT 2 J))
                           (BITS X I+ (+ 1 I)))
                         0)))
  :hints (("Goal"
           :use (:instance bits-plus-bits-1 (n (+ i 1)) (i i+))
           :in-theory (set-difference-theories
                       (enable expt-split)
                       '( BITS-CANCEL-LOWBITS-IN-COMPARISON-ALT-2
                          ))
           )))

(defthm bits-cancel-lowbits-in-comparison-no-constant-2
  (implies (and (> i+ i)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)
                )
           (equal (equal (bits x i+ j)
                         (bits x i j))
                  (equal (* 2 (EXPT 2 I)
                           (/ (EXPT 2 J))
                           (BITS X I+ (+ 1 I)))
                         0)))
  :hints (("Goal"
           :use (:instance bits-plus-bits-1 (n (+ i 1)) (i i+))
           :in-theory (set-difference-theories
                       (enable expt-split)
                       '( BITS-CANCEL-LOWBITS-IN-COMPARISON-ALT-2
))
           )))

;the theory above (cancelling bits in comparisons) is not complete
;it should also deal with bitn
;perhaps a bind-free rule would be a good idea here?

|#


;kind of yucky...
(defthm bits-minus
  (implies (and (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (<= j i))
                (case-split (integerp j))
                )
           (equal (bits (* -1 x) i j)
                  (if (integerp (* 1/2 x (/ (expt 2 i))))
                      0
                    (if (integerp (* x (/ (expt 2 j))))
                        (+ (* 2 (expt 2 i) (/ (expt 2 j))) (- (bits x i j)))
                      (+ -1 (* 2 (expt 2 i) (/ (expt 2 j))) (- (bits x i j)))))))
  :hints (("goal" :in-theory (enable mod-mult-of-n
                                     bits
                                     expt-split)))
  )





;expensive?
(defthm bits-minus-alt
  (implies (and (syntaxp (negative-syntaxp x))
                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (<= j i))
                (case-split (integerp j))
                )
           (equal (bits x i j)
                  (if (integerp (* 1/2 (- X) (/ (EXPT 2 I))))
                    0
                    (if (INTEGERP (* (- X) (/ (EXPT 2 J))))
                        (+ (* 2 (EXPT 2 I) (/ (EXPT 2 J))) (- (bits (- x) i j)))
                      (+ -1 (* 2 (EXPT 2 I) (/ (EXPT 2 J))) (- (bits (- x) i j)))))))
  :hints (("Goal" :in-theory (disable bits-minus)
           :use (:instance bits-minus (x (- x)))))
  )




#|
(defthm bits-shift-alt
  (implies (and (syntaxp (should-have-a-2-factor-divided-out x))
                (> j 0) ;restricts application
                (rationalp x)
;                (integerp n)
                (integerp i)
                (integerp j)
                )
           (equal (bits x i j)
                  (bits (/ x 2) (- i 1) (- j 1))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bits)
                              '(bits-shift))
           :use (:instance bits-shift (x (/ x 2)) (n 1)))))

|#


;drops hyps like this: (<= (BITS x 30 24) 253)
;Recall that <= gets rewritten to < during proofs
(defthm bits-drop-silly-upper-bound
  (implies (and (syntaxp (quotep k))
                (>= k (1- (expt 2 (+ 1 i (- j)))))
                (case-split (<= j i))
;                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
;                (case-split (rationalp k))
                )
           (equal (< k (bits x i j))
                  nil)))

;rewrite things like (<= 4096 (BITS x 23 12)) to false
;Recall that <= gets rewritten to < during proofs
(defthm bits-drop-silly-lower-bound
  (implies (and (syntaxp (quotep k))
                (> k (1- (expt 2 (+ 1 i (- j)))))
                (case-split (<= j i))
;                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
;                (case-split (rationalp k))
                )
  (equal (< (bits x i j) k)
         t)))

;rewrite (< -64 (BITS <signal> 64 59)) to t
(defthm bits-drop-silly-bound-3
  (implies (and (syntaxp (quotep k))
                (< k 0)
                )
  (equal (< k (bits x i j))
         t)))

(defthm bits-drop-silly-bound-4
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                )
  (equal (< (bits x i j) k)
         nil)))

(defthm bits-<-1
  (equal (< (bits x i j) 1)
         (equal (bits x i j) 0)))

;put bits-cancel- in the name?
(defthm bits-at-least-zeros
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (- j2 j)))
                (<= j j2)
                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp j2))
                )
  (equal (< (BITS x i j)
             (* k (BITS x i j2)))
         nil))
  :hints (("Goal" :use (:instance bits-plus-bits2 (n j2)))))

(defthm bits-upper-with-subrange
  (implies (and (syntaxp (quotep k))
                (<= j j2)
                (equal k (expt 2 (- j2 j)))
                (case-split (<= j2 i)) ;drop?
                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp j2))
                )
           (< (BITS x i j)
              (BINARY-+ k (BINARY-* k (BITS x i j2)))))
  :hints (("Goal" :use (:instance bits-plus-bits2 (j j) (n j2)))))

(defthm bits-upper-with-subrange-alt
  (implies (and (syntaxp (quotep k))
                (<= j j2)
                (equal k (expt 2 (- j2 j)))
                (case-split (<= j2 i)) ;drop?
                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp j2))
                )
           (equal (< (BINARY-+ k (BINARY-* k (BITS x i j2)))
                     (BITS x i j))
                  nil))
  :hints (("Goal" :use (:instance bits-plus-bits2 (j j) (n j2)))))


;make another version for k negative?
(defthm bits-equal-impossible-constant
  (implies (and (syntaxp (quotep k))
                (<= (expt 2 (+ 1 i (- j))) k)
                )
           (not (equal (bits x i j) k))))




#|
;degenerate case
;rename?
;expensive
(defthm bits-sum-drop-irrelevant-term-1-of-1
  (implies (and (rationalp x) ;(integerp x)

                (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j)

                (integerp (/ x (expt 2 (+ 1 i))))
                )
           (equal (bits x i j)
                  0))
  :hints (("Goal" :in-theory (enable bits bits)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil nil nil nil nil 1)))
)
|#

(defthm bits-with-x-not-rational
  (implies (not (rationalp x))
           (equal (bits x i j)
                  0))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bits)
                              '( ;REARRANGE-FRACTIONAL-COEFS-<
                                )))))



(defthm bits-compare-to-zero
  (implies (and (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (not (< 0 (bits x i j)))
                  (equal 0 (bits x i j)))))

;expensive?

(encapsulate
 ()

 (defthmd bits-ignore-negative-bits-of-integer-main-case
   (implies (and (<= j 0)
                 (integerp x)
                 (case-split (integerp j))
                 (case-split (<= j i))
                 )
            (equal (bits x i j)
                   (* (expt 2 (- j)) (bits x i 0))))
   :hints (("Goal" :cases ((<= j i))
            :in-theory (enable bits)))
   )

 (defthm bits-ignore-negative-bits-of-integer
   (implies (and (and (syntaxp (not (and (quotep j) (equal 0 (cadr j)))))) ;prevents loops
                 (<= j 0)
                 (integerp x)
                 (case-split (integerp j))
                 )
            (equal (bits x i j)
                   (* (expt 2 (- j)) (bits x i 0))))
   :hints (("Goal"; :cases ((<= j i))
            :use bits-ignore-negative-bits-of-integer-main-case
            :in-theory (enable)))
   )
 )


;disable since it can be bad to leave "naked" signals?
(defthmd bits-does-nothing-2
  (implies (and (<= j 0) ;a bit strange (j will usually be zero?)
                (bvecp x (+ i 1)) ;expand?
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits x i j)
                  (* (expt 2 (- j)) x)))
  :hints (("Goal" :cases ((<= j 0))
           :in-theory (enable bits bvecp))))






#|
;(include-book "factor-out")

(defthm bits-shift-better
  (implies (and (bind-free (can-take-out-numeric-power-of-2 x) (c))
                (force (power2p c))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits x i j)
                  (bits (/ x c) (- i (expo c)) (- j (expo c)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable power2p)
                              '(bits-shift))
           :use  (:instance bits-shift
                           (x (/ x c))
                           (n (expo c))
                           ))))

|#




(defthm bits-does-nothing
  (implies (and (bvecp x (1+ i))
                (case-split (integerp i))
;                (case-split (integerp j))
                )
           (equal (bits x i 0)
                  x))
  :hints (("Goal" :in-theory (enable bits-does-nothing-2)
           :cases ((<= i -1))))
  )

(in-theory (disable bits-does-nothing))



(defthm bits-with-bad-index-2
  (IMPLIES (NOT (INTEGERP i))
           (EQUAL (BITS x (1- i) 0)
                  0))
  :hints (("Goal" :in-theory (enable bits))))

(local (defthm bvecp-bits-0-aux
   (implies (and (case-split (natp i)) ;(natp i)
                 (case-split (<= j i))
                 (bvecp x j))
            (equal (bits x i j) 0))
   :hints (("Goal" :in-theory (enable bits bvecp)
            :use (;(:instance mod-equal (m x) (n (expt 2 (1+ i))))
                  (:instance expt-weak-monotone (n j) (m (1+ i))))))))

(defthmd bvecp-bits-0
   (implies (bvecp x j)
            (equal (bits x i j) 0))
   :hints (("Goal" :cases ((< i j))
            :in-theory (set-difference-theories
                        (enable natp)
                        '( bvecp )))))

;add case-split to hyps?
(local
 (defthm bits-drop-from-minus-original
   (implies (and (<= y x)
                 (bvecp x n)
                 (bvecp y n)
                 )
            (equal (bits (+ x (* -1 y)) (1- n) 0)
                   (+ x (* -1 y))
                   ))
   :hints (("Goal" :cases ((integerp n))
            :in-theory (enable bvecp)))
   ))

;add case-split to hyps?
(defthm bits-drop-from-minus
  (implies (and (bvecp x (1+ i))
                (bvecp y (1+ i))
                (<= y x)
		(case-split (acl2-numberp i)))
	   (equal (bits (+ x (* -1 y)) i 0)
		  (+ x (* -1 y))))
  :hints (("Goal" :use ((:instance bits-drop-from-minus-original
                                   (n (1+ i))))
           :in-theory (disable bits-drop-from-minus-original))))

(defthm bits-tail
   (implies (and (bvecp x (1+ i))
                 (case-split (acl2-numberp i)))
            (equal (bits x i 0)
                   x))
   :hints (("Goal" :in-theory (enable bvecp bits-does-nothing))))

(defthm bits-tail-special
   (implies (bvecp x i)
            (equal (bits x (1- i) 0)
                   x))
   :hints (("Goal" :cases ((acl2-numberp i)))))


#|

comments from bits.lisp (these may duplicate comments in this book)

;why have this?
(defthm bits-shift-out-even
  (implies (and (integerp x)
                (evenp x)
                (integerp i)
                (integerp j)
                (>= i j))
           (equal (bits x i j)
                  (bits (/ x 2) (- i 1) (- j 1) )))
  :hints (("Goal" :in-theory (enable expt-minus
                                     bits
                                     mod-cancel
                                     expt-split-rewrite)))
  )




;could use even-odd phrasing?
(defthm bits-down-to-1-case-split
  (implies (and (integerp x)
                (>= x 0)
                (integerp i)
                (>= i 1))
           (equal (bits x i 1)
                  (if (equal (bitn x 0) 0)
                      (/ (bits x i 0) 2) ;use the fact that we know bit 0 is 0?
                    (/ (1- (bits x i 0)) 2) ;use the fact that we know bit 0 is 1?
                    ))))


;would like these
;x<2^n
(defthm test2
  (IMPLIES (AND (INTEGERP N) (<= 0 N) (rationalP X) (<= 0 x))
         (EQUAL (FLOOR (* 1/2 x) 1)
                (FLOOR (* 1/2 (FLOOR x 1))
                       1)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable floor))))

  :otf-flg t
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable fl)
                              '())))
)


(defthm test
  (IMPLIES (AND (INTEGERP N) (<= 0 N) (INTEGERP X))
         (EQUAL (FL (* 1/2 X (/ (EXPT 2 N))))
                (FL (* 1/2 (FL (* X (/ (EXPT 2 N))))))))
  :otf-flg t
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable fl)
                              '()))))
)


;these may be made moot by my method of using lowbits with bits of a sum

(defthm bits-sum-simplify-first-term
  (implies (and (>= (abs x) (expt 2 (+ j 1))) ;prevents loop
                (rationalp x)
                (rationalp y)
                (integerp j)
                (<= 0 j)
                )
           (equal (bits (+ x y) j 0)
                  (bits (+ (lowbits x j) y) j 0))))

(defthm bits-sum-simplify-second-term
  (implies (and (>= (abs x) (expt 2 (+ j 1))) ;prevents loop
                (rationalp x)
                (rationalp y)
                (integerp j)
                (<= 0 j)
                )
           (equal (bits (+ y x) j 0)
                  (bits (+ (lowbits x j) y) j 0))))




This series of events deals with simplifying expressions like
(equal (bits x 8 0)
       (+ (bits x 6 0) k))
Intuitively, bits 6 down-to 0 appear on both sides of the sum and should be "cancelled".
The remaining bits will need to be "shifted" back into place.

More rules are probably needed to make the theory complete.


(defthm bits-cancel-lowbits-in-comparison
  (implies (and (> i+ i)
                (rationalp k)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)
                )
           (equal (equal (+ k (bits x i j))
                         (bits x i+ j))
                  (equal (* (expt 2 (+ 1 i (- j)))
                            (BITS X I+ (+ 1 I)))
                         k))))

(defthm bits-cancel-lowbits-in-comparison-alt-2
  (implies (and (> i+ i)
                (rationalp k)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)
                )
           (equal (equal (+ (bits x i j) k)
                         (bits x i+ j))
                  (equal (* (expt 2 (+ 1 i (- j)))
                            (BITS X I+ (+ 1 I)))
                         k))))



;todo: rephrase the conclusion of the above by moving the "constant" (* 2 (EXPT 2 I) (/ (EXPT 2 J))) to the other
;side
;a good idea since k is usually divisible by that quantity (with the rule above, we often end up with an
equality in which each side should have a power of 2 divided out of it
; not needed if we have good meta rules for cancelling factors from an inequality


(defthm bits-cancel-lowbits-in-comparison-2
  (implies (and (> i+ i)
                (rationalp k)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)

                )
           (equal (equal (+ k (bits x i j))
                         (bits x i+ j))
                  (equal (*
                            (BITS X I+ (+ 1 I)))
                         (/ k (expt 2 (+ 1 i (- j))))))))




(defthm bits-cancel-lowbits-in-comparison-3
  (implies (and (> i+ i)
                (rationalp k)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)
                (rationalp y)
                )
           (equal (equal (+ (bits x i+ j) k)
                         (+ y (bits x i j)))
                  (equal (* (expt 2 (+ 1 i (- j )))
                            (BITS X I+ (+ 1 I)))
                         (- y k)))))

;better conclusion?
(defthm bits-cancel-lowbits-in-comparison-no-constant
  (implies (and (> i+ i)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)
                )
           (equal (equal (bits x i j)
                         (bits x i+ j))
                  (equal (* 2 (EXPT 2 I)
                           (/ (EXPT 2 J))
                           (BITS X I+ (+ 1 I)))
                         0))))

(defthm bits-cancel-lowbits-in-comparison-no-constant-2
  (implies (and (> i+ i)
                (rationalp x)
                (integerp i)
                (integerp j)
                (<= j i)
                (integerp i+)
                )
           (equal (equal (bits x i+ j)
                         (bits x i j))
                  (equal (* 2 (EXPT 2 I)
                           (/ (EXPT 2 J))
                           (BITS X I+ (+ 1 I)))
                         0))))
;the theory above (cancelling bits in comparisons) is not complete
;it should also deal with bitn
;perhaps a meta rule would be a good idea here?


(defthm bits-shift-alt
  (implies (and (syntaxp (should-have-a-2-factor-divided-out x))
                (> j 0) ;restricts application
                (rationalp x)
                (integerp i)
                (integerp j)
                )
           (equal (bits x i j)
                  (bits (/ x 2) (- i 1) (- j 1)))))

(defthm bits-turn-bound-into-equal
  (implies (and (syntaxp (quotep k))
                (equal k (+ -2 (expt 2 (+ 1 i (- j)))))
                (case-split (<= j i))
                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (rationalp k))
                )
           (equal (< k (bits x i j))
                  (equal (bits x i j) (+ k 1))))
  :hints (("Goal" :in-theory (disable  bits-upper-bound-tighter
                                        bits-upper-bound
                                         bits-upper-bound-2)
           :use  bits-upper-bound-tighter))
)







;(in-theory (disable nbits-shift-out-even))


;...


;degenerate case
;rename?
;expensive
(defthm bits-sum-drop-irrelevant-term-1-of-1
  (implies (and (rationalp x) ;(integerp x)

                (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j)

                (integerp (/ x (expt 2 (+ 1 i))))
                )
           (equal (bits x i j)
                  0))
  :hints (("Goal" :in-theory (enable bits bits)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil nil nil nil nil 1)))
)


(defthm bits-shift-better
  (implies (and (bind-free (can-take-out-numeric-power-of-2 x) (c))
                (force (power2p c))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits x i j)
                  (bits (/ x c) (- i (expo c)) (- j (expo c))))))

;high bits don't matter - add syntaxp hyp that one addend is a constant with high bits still present
;huh?


|#


;It may be easier to reason about bits if we use this rule instead of expanding/enabling bits.
(defthmd bits-alt-def
  (equal (bits x i j)
         (if (or (not (integerp i))
                 (not (integerp j)))
             0
           (mod (fl (/ x (expt 2 j))) (expt 2 (+ 1 i (- j))))))
  :hints (("Goal" :in-theory (enable bits))))






(defthm bits-bvecp-simple-2
  (bvecp (bits x (1- i) 0) i)
  :hints (("Goal" :cases ((acl2-numberp i)))))


;Follows from BITS-SUM-DROP-IRRELEVANT-TERM-2-OF-2.
;change param names
(defthmd bits-plus-mult-2
   (implies (and (< n k)
                 (integerp y)
                 (integerp k)
                 )
            (equal (bits (+ x (* y (expt 2 k))) n m)
                   (bits x n m)))
   :hints (("Goal" :cases ((integerp n))))) ;why cases hint needed?

(defthmd bits-plus-mult-2-rewrite
   (implies (and (syntaxp (quotep c))
                 (equal (mod c (expt 2 (1+ n))) 0))
            (equal (bits (+ c x) n m)
                   (bits x n m)))
    :hints (("Goal" :use ((:instance bits-plus-mult-2
                                     (x x)
                                     (y (/ c (expt 2 (1+ n))))
                                     (k (1+ n))
                                     (n n)))
             :in-theory (enable mod))))

(defthm bits-plus-bits
   (implies (and (integerp m)
                 (integerp p)
                 (integerp n)
                 (<= m p)
                 (<= p n))
            (= (bits x n m)
               (+ (bits x (1- p) m)
                  (* (expt 2 (- p m)) (bits x n p)))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance bits-plus-bits2 (i n) (j m) (n p))))))

(defthm bits-less-than-x
  (implies (<= 0 x)
	   (<= (bits x i 0) x))
  :rule-classes (:rewrite :linear)
  :hints (("goal" :in-theory (enable bits))))

(defthm bits-less-than-x-gen
  (implies (and (<= 0 x)
                (case-split (<= 0 j))
                (case-split (not (complex-rationalp x)))
                )
	   (<= (bits x i j) x))
  :rule-classes (:rewrite :linear)
  :hints (("goal" :in-theory (enable bits x-times-something>=1))))

(defthm bits-bvecp-when-x-is
  (implies (and (bvecp x k)
                (case-split (<= 0 j))
                )
           (bvecp (bits x i j) k))
  :hints (("Goal" :in-theory (enable  bvecp))))

(defthmd bits-bits-1
  (implies (and (<= k (- i j))
                (case-split (<= 0 l))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (case-split (integerp l))
                )
           (equal (bits (bits x i j) k l)
                  (bits x (+ k j) (+ l j))))
  :hints (("Goal" :in-theory (enable bits expt-split))))

(defthmd bits-bits-2
  (implies (and (> k (- i j))
                (case-split (<= 0 l))
;                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (case-split (integerp l))
                )
           (equal (bits (bits x i j) k l)
                  (bits x i (+ l j))))
  :hints (("Goal" :in-theory (enable bits expt-split))))

(defthm bits-bits
  (implies (and (case-split (<= 0 l))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (case-split (integerp l))
                )
           (equal (bits (bits x i j) k l)
                  (if (<= k (- i j))
                      (bits x (+ k j) (+ l j))
                    (bits x i (+ l j)))))
:hints (("Goal" :in-theory (enable bits-bits-1 bits-bits-2))))


;The following trivial corollary of bits-bits is worth keeping enabled.

(defthm bits-bits-constants
  (implies (and (syntaxp (quotep i))
                (syntaxp (quotep j))
                (syntaxp (quotep k))
                (<= 0 l)
                (integerp i)
                (integerp j)
                (integerp k)
                (integerp l))
           (equal (bits (bits x i j) k l)
                  (if (<= k (- i j))
                      (bits x (+ k j) (+ l j))
                    (bits x i (+ l j))))))


(defthm bits-reduce
  (implies (and (< x (expt 2 (+ 1 i)))
                (case-split (integerp x))
                (case-split (<= 0 x))
                (case-split (integerp i))
                )
           (equal (bits x i 0) x)))

(defthm bits-0
  (equal (bits 0 i j) 0))





;could prove a version where we drop bits from both args?
(defthm bits-sum-drop-bits-around-arg-2
  (implies (and (<= i i+)
                (integerp y)
                (case-split (integerp i+))
                )
           (equal (bits (+ x (bits y i+ 0)) i j)
                  (bits (+ x y) i j)))
  :hints (("Goal" :in-theory (enable bits))))

;Follows from BITS-SUM-DROP-BITS-AROUND-ARG-2.
(defthm bits-sum-drop-bits-around-arg-1
  (implies (and (<= i i+)
                (integerp x)
                (case-split (integerp i+))
                )
           (equal (bits (+ (bits x i+ 0) y) i j)
                  (bits (+ x y) i j))))

(defthm bits-sum-drop-bits-around-arg-2-special-case
  (implies (integerp y) ;case-split?
           (equal (bits (+ x (bits y i 0)) i j)
                  (bits (+ x y) i j))))

(defthm bits-sum-drop-bits-around-arg-1-special-case
  (implies (integerp x) ;case-split?
           (equal (bits (+ (bits x i 0) y) i j)
                  (bits (+ x y) i j))))

;rename
;Follows from BVECP-SUM-OF-BVECPS.
(defthm bits-sum-1
  (equal (bits (+ (bits x (1- i) 0)
                  (bits y (1- i) 0))
               i ;actually, this could be anything >= i ??
               0)
         (+ (bits x (1- i) 0)
            (bits y (1- i) 0)))
  :hints (("Goal" :in-theory (enable bits-tail))))


;export!! enable?
;gen?
(defthmd bits-of-non-integer-special
  (implies (case-split (not (integerp i)))
           (equal (BITS X (1- i) 0)
                  0)))

(local
 (defthmd bits-fl-helper
   (implies (and (<= 0 j)
                 (<= -1 i)
                 )
            (equal (bits (fl x) i j)
                   (bits x i j)))
   :hints (("Goal" :in-theory (enable bits mod-fl-eric)))))

(defthm bits-fl
  (implies (<= 0 j)
           (equal (bits (fl x) i j)
                  (bits x i j)))
  :hints (("Goal" :use  bits-fl-helper)))

(defthmd bits-shift-down-eric
  (implies (and (<= 0 j)
                (integerp i)
                (integerp j)
                (integerp k)
                )
           (equal (bits (* x (/ (expt 2 k)))
                        i
                        j)
                  (bits x (+ i k) (+ j k))))
  :hints (("Goal" :in-theory (e/d (expt-minus) (bits-shift))
           :use (:instance bits-shift (n (- k))))))

(defthmd bits-shift-down-1
    (implies (and (<= 0 j)
                  (integerp i)
		  (integerp j)
                  (integerp k)
                  )
	     (equal (bits (fl (/ x (expt 2 k)))
			  i
			  j)
		    (bits x (+ i k) (+ j k))))
  :hints (("Goal" :in-theory (enable bits-fl bits-shift-down-eric))))

(local
 (defthm bits-fl-by-2-helper
   (implies (and (integerp i)
                 (<= 0 i)
                 )
            (equal (fl (* 1/2 (bits x i 0))) ;gen 0 to j?
                   (bits x i 1)))
   :rule-classes ()
   :hints (("Goal"  :in-theory (disable LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE)
            :use ((:instance bits-shift-down-1 (k 1) (i (1- i)) (j 0))
                  (:instance bits-plus-bits (n i) (m 0) (p 1))
                  (:instance fl-unique (x (/ (bits x i 0) 2)) (n (bits x i 1))))))))
;rename?
(defthmd bits-fl-by-2
  (equal (fl (* 1/2 (bits x i 0)))
         (bits x i 1))
  :hints (("Goal" :use (:instance  bits-fl-by-2-helper))))

(defthm mod-bits-by-2
  (implies (and (integerp x)
                (<= 0 i)
                (integerp i)
                )
           (equal (mod (bits x i 0) 2)
                  (mod x 2)))
  :hints (("Goal" :in-theory (enable bits))))


#|

;BOZO challenge:

(defthm bits-sum-drop-bits-around-arg-2-really-special-case
  (implies (rationalp y)
           (equal (bits (+ x (bits y i 0)) i 0)
                  (bits (+ x y) i 0)))
  :hints (("Goal" :in-theory (enable bits)))))

(defthm bits-sum-drop-bits-around-arg-1-really-special-case
  (implies (integerp x)
           (equal (bits (+ (bits x i 0) y) i 0)
                  (bits (+ x y) i 0))))

|#


(defthm bits-shift-by-constant-power-of-2
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits (* k x) i j)
                  (bits x (- i (expo k)) (- j (expo k)))))
  :hints (("Goal" :in-theory (enable power2p-rewrite))))


(defthm bits-shift-second-with-more
  (implies (and ;(rationalp x)
            (case-split (integerp n))
            (case-split (integerp i))
            (case-split (integerp j))
            )
           (equal (bits (* x (expt 2 n) y) i j)
                  (bits (* x y) (- i n) (- j n))))
  :hints (("Goal" :in-theory (disable bits-shift)
           :use (:instance bits-shift (x (* x y))))))

(defthmd bits-times-2
  (implies (and (acl2-numberp i)
                (acl2-numberp j)
                )
           (equal (bits (* 2 x) i j)
                  (bits x (1- i) (1- j))))
  :hints (("Goal" :use ((:instance bits-shift (n 1))))))

(defthmd bits+2**k-2
  (implies (and (< x (expt 2 k))
                (<= 0 x)
                (rationalp x) ;(integerp x)
                (<= k m)
                (integerp y)
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp k))
                )
           (equal (bits (+ x (* y (expt 2 k))) n m)
                  (bits y (- n k) (- m k))))
  :hints (("goal" :in-theory (disable FL-EQUAL-0)
           :use ((:instance bits-shift-down-1
                            (x (+ x (* y (expt 2 k))))
                            (i (- n k))
                            (j (- m k)))
                 (:instance fl-unique (x (/ (+ x (* y (expt 2 k))) (expt 2 k))) (n y))))))

(defthm bits+2**k-2-alt
  (implies (and (< x (expt 2 k))
                (<= 0 x)
                (rationalp x) ;(integerp x)
                (<= k m)
                (integerp y)
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp k))
                )
           (equal (bits (+ x (* (expt 2 k) y)) n m)
                  (bits y (- n k) (- m k))))

  :hints (("Goal" :in-theory (disable bits+2**k-2)
           :use (:instance bits+2**k-2))))

;basically the same as bits+2**k-2; drop one?
;move
(defthmd bits-plus-mult-1
  (implies (and (bvecp x k) ;actually, x need not be an integer...
                (<= k m)
                (integerp y)
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp k))
                )
           (equal (bits (+ x (* y (expt 2 k))) n m)
                  (bits y (- n k) (- m k))))
  :hints (("Goal" :in-theory (enable bvecp)
           :use (bits+2**k-2))))

(defthm bits-mod-0
  (implies (and (integerp x)
                (>= x 0)
                (integerp m)
                (>= m 0)
                (integerp n)
                (>= n 0))
           (iff (= (mod x (expt 2 (+ m n 1))) 0)
                (and (= (bits x (+ m n) n) 0)
                     (= (mod x (expt 2 n)) 0))))
  :rule-classes ()
  :hints (("goal" :in-theory (e/d (bits expt-split) (BITS-FL))
           :use ((:instance mod-0-0 (m x) (n (expt 2 n)) (p (expt 2 (1+ m))))
                 (:instance bits-shift-down-1 (k n) (i m) (j 0))))))

;this is silly? just open up bits!
(defthm mod-bits-equal
  (implies (= (mod x (expt 2 (1+ i))) (mod y (expt 2 (1+ i))))
           (= (bits x i j) (bits y i j)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits))))

(defthmd mod-bits-equal-cor
    (implies (and (integerp x)
		  (integerp n)
		  (integerp i)
		  (integerp j)
		  (< i n))
	     (equal (bits (mod x (expt 2 n)) i j)
		    (bits x i j)))
    :hints (("Goal" :use ((:instance mod-bits-equal
                                     (x (mod x (expt 2 n)))
                                     (y x))))))

;not needed?  just expand bits?
(defthmd bits-mod
  (implies (and (case-split (integerp x))
                (case-split (integerp i)) ;gen?
                ;(case-split (<= 0 i))
                )
           (equal (bits x i 0)
                  (mod x (expt 2 (1+ i)))))
  :hints (("Goal"
           :cases ((rationalp i) (complex-rationalp i))
           :in-theory (e/d (bits) ( EXPT-SPLIT)))))

(defthmd bits-bits-sum
  (implies (and (integerp x)
                (integerp y)
                (integerp i))
	   (equal (bits (+ (bits x i 0) y) i 0)
		  (bits (+ x y) i 0)))
  :hints (("Goal" :in-theory (enable bits mod-sum))))

;reorder? make rewrite?
(defthm bits-shift-up-2
  (implies (and (integerp x)
                (integerp k)
                (<= 0 k)
                (integerp i)
                )
           (equal (* (expt 2 k) (bits x i 0))
                  (bits (* (expt 2 k) x) (+ i k) 0)))
  :rule-classes ()
;:hints (("Goal" :cases ((equal 0 k))))
  )


;export!
(defthm bits-expt
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                )
           (equal (bits (expt 2 k) i j)
                  (if (or (< i j)
                          (< k j)
                          (< i k))
                      0
                    (expt 2 (- k j))))
           )
  :hints (("Goal" :use (:instance bits-shift (x 1) (n k))))
  )

(defthm bits-natp
  (natp (bits x i j)))


(defthmd bits-shift-down-eric
  (implies (and (<= 0 j)
                (integerp i)
                (integerp j)
                (integerp k)
                )
           (equal (bits (* x (/ (expt 2 k)))
                        i
                        j)
                  (bits x (+ i k) (+ j k))))
  :hints (("Goal" :use (:instance bits-shift-down-1)))
  )

;gen the 0?
(defthm mod-bits
  (implies (and (<= 0 i)
                (<= 0 j)
                (integerp j)
                (integerp i))
           (equal (mod (bits x i 0) (expt 2 j))
                  (bits x (min i (1- j)) 0)))
  :hints (("Goal" :in-theory (enable bits)))
  )

(defthm bits-expt-constant
  (implies (and (syntaxp (and (quotep k) (power2p (cadr k))))
                (force (power2p k))
                (case-split (integerp k)) ;gen?
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits k i j)
                  (if (or (< i j)
                          (< (expo k) j)
                          (< i (expo k)))
                      0
                    (expt 2 (- (expo k) j)))))
  :hints (("Goal" :in-theory (enable power2p-rewrite))))

#|

(defthm bits-minus-better-helper-1
  (implies (and (integerp x)
                (integerp i))
           (equal (equal 0 (bits x i 0))
                  (integerp (* 1/2 x (/ (expt 2 i))))
                  ))
  :hints (("Goal" :in-theory (enable expt-split mod-equal-0)
           :expand  (BITS X I 0)))
  )

(defthm bits-minus-better-helper-2
  (implies (and (integerp x)
                (integerp i))
           (equal (equal 0 (bits x (1- j) 0))
                  (integerp (* x (/ (expt 2 j))))
                  ))
  :hints (("Goal" :in-theory (enable expt-split mod-equal-0)
           :expand   (bits x (1- j) 0)))
  )

;note that although the RHS looks slightly gross,
;gen the (integerp x) hyp!!
(defthm bits-minus-better
  (implies (and (case-split (integerp x)) ;gen!
                (case-split (integerp i))
                (case-split (<= j i)) ;drop?
                (case-split (integerp j))
                )
           (equal (bits (* -1 x) i j)
                  (if (equal 0 (bits x i 0))
                      0
                    (if (equal 0 (bits x (1- j) 0))
                        (+ (* 2 (expt 2 i) (/ (expt 2 j))) (- (bits x i j)))
                      (+ -1 (* 2 (expt 2 i) (/ (expt 2 j))) (- (bits x i j)))))))
	:hints (("Goal" :use bits-minus
	:in-theory (enable mod-does-nothing expt-split mod-cancel)))
)

|#


;Unlike bits-tail, this allows j to be non-zero.
;Note that the conclusion is (bits x ...), not just x.
;i is a free variable
;watch out for loops with this rule
;BOZO export in lib/ or user/!
(defthm bits-tighten
  (implies (and (bvecp x i)
                (<= i n)
                (case-split (integerp n))
                )
           (equal (bits x n j)
                  (bits x (1- i) j)))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("goal" :use (:instance expt-weak-monotone (n i) (m (+ 1 n)))
           :in-theory (e/d (bits bvecp) (expt-compare)))))

(defthmd bits-mod-2
  (implies (and (integerp x)
                (integerp i)
                (integerp j)
                (>= i j))
           (equal (bits x (1- i) j)
                  (- (fl (/ x (expt 2 j)))
                     (* (expt 2 (- i j))
                        (fl (/ x (expt 2 i)))))))
  :hints (("Goal" :in-theory (enable bits mod))))

(defthmd bits-neg
  (implies (and (< i 0)
                (integerp x))
           (equal (bits x i j) 0))
  :hints (("Goal" :in-theory (enable bits))))

(defthmd bits-shift-down-2
  (implies (and (natp x)
		(natp i)
		(natp k))
	   (equal (fl (/ (bits x (+ i k) 0) (expt 2 k)))
		  (bits (fl (/ x (expt 2 k))) i 0)))
  :hints (("Goal" :use ((:instance bits-plus-bits (n (+ i k)) (m 0) (p k)))
           :in-theory (enable bits-shift-down-1))))
