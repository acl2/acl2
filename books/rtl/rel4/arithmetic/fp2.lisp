; This file was created by J Moore and Matt Kaufmann in 1995 in support of
; their proof of the AMD-K5 division code.

;this is eric's version of fp.lisp
;note that it doesn't mention fl

(in-package "ACL2")


(local (include-book "ihs/ihs-definitions" :dir :system))
(local (include-book "ihs/ihs-lemmas" :dir :system))
(local (include-book "ihs/ihs-lemmas" :dir :system))

; The following is (minimal-ihs-theory)
(local (PROGN (IN-THEORY NIL)
              (IN-THEORY (ENABLE BASIC-BOOT-STRAP
                                 IHS-MATH QUOTIENT-REMAINDER-RULES
                                 LOGOPS-LEMMAS-THEORY))))

(local (in-theory (enable logops-definitions-theory)))



(defthm a1 (equal (+ x (+ y z)) (+ y (+ x z))))
(defthm a2 (equal (- x) (* -1 x)))

(local (in-theory (disable functional-commutativity-of-minus-*-right
                           functional-commutativity-of-minus-*-left)))

(defthm a3
  (and (implies (syntaxp (and (quotep c1) (quotep c2)))
                (and (equal (+ (* c1 x) (* c2 x)) (* (+ c1 c2) x))
                     (equal (+ (* c1 x) (+ (* c2 x) y)) (+ (* (+ c1 c2) x) y))))
       (implies (syntaxp (quotep c2))
                (and (equal (+ x (* c2 x)) (* (+ 1 c2) x))
                     (equal (+ x (+ (* c2 x) y1)) (+ (* (+ 1 c2) x) y1))
                     (equal (+ x (+ y1 (* c2 x))) (+ (* (+ 1 c2) x) y1))
                     (equal (+ x (+ y1 (+ (* c2 x) y2))) (+ (* (+ 1 c2) x) y1 y2))
                     (equal (+ x (+ y1 (+ y2 (* c2 x)))) (+ (* (+ 1 c2) x) y1 y2))
                     (equal (+ x (+ y1 (+ y2 (+ y3 (* c2 x)))))
                            (+ (* (+ 1 c2) x) y1 y2 y3))
                     (equal (+ x (+ y1 (+ y2 (+ (* c2 x) y3))))
                            (+ (* (+ 1 c2) x) y1 y2 y3))))
       (and (equal (+ x x) (* 2 x))
            (equal (+ x (+ x y1)) (+ (* 2 x) y1)))))

(defthm a4
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (equal (+ c1 (+ c2 y1)) (+ (+ c1 c2) y1))))
(defthm a5
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (equal (* c1 (* c2 y1)) (* (* c1 c2) y1))))

(defthm a6
  (equal (/ (/ x)) (fix x)))

(defthm a7
  (equal (/ (* x y)) (* (/ x) (/ y))))

;replaced force with case-split
(defthm a8
  (implies (and (case-split (acl2-numberp x))
                (case-split (not (equal x 0))))
           (and (equal (* x (* (/ x) y)) (fix y))
                (equal (* x (/ x)) 1)))
  :hints (("Goal" :cases ((acl2-numberp x))))
)

(in-theory (disable inverse-of-*))

;separate these out?
(defthm a9
  (and (equal (* 0 x) 0)
       (equal (* x (* y z)) (* y (* x z)))
       (equal (* x (+ y z)) (+ (* x y) (* x z)))
       (equal (* (+ y z) x) (+ (* y x) (* z x)))))



#|

(local (defthm evenp--k
  (implies (integerp k) (equal (evenp (- k)) (evenp k)))
  :hints
  (("Goal" :in-theory (set-difference-theories
                       (enable evenp
                               functional-commutativity-of-minus-*-right
                               functional-commutativity-of-minus-*-left)
                       '(a2 a5))))))

(local (defthm evenp-2k
  (implies (integerp k) (evenp (* 2 k)))
  :hints (("Goal" :in-theory (enable evenp)))))

(local (defthm evenp-expt-2
  (implies (and (integerp k)
                (> k 0))
           (evenp (expt 2 k)))
  :hints (("Goal" :in-theory (enable evenp expt)))))

(local (defthm evenp-+-even
  (implies (evenp j) (equal (evenp (+ i j)) (evenp i)))
  :hints (("Goal" :in-theory (enable evenp)))))


|#

;I want to use some theoremes in arithmetic 2, but the theorems I want to prove have the same names as those,
;so I export them from the encapsulate with -alt appended to the names.


(local
 (encapsulate
  ()
  ;; [Jared] changed this to use arithmetic-3 instead of 2.
  (local (include-book "arithmetic-3/bind-free/top" :dir :system))

;BOZO generalize the (rationalp x) hyp (is it enough that, say, y be rational?)
 (defthm *-weakly-monotonic-alt
    (implies (and (<= y y+)
                  (<= 0 x) ;reordered to put this first!
                  (rationalp x) ; This does not hold if x, y, and z are complex!
                  )
             (<= (* x y) (* x y+)))
    :hints (("Goal" :cases ((equal x 0))))
    :rule-classes
    ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
     (:linear)
     (:forward-chaining
      :trigger-terms ((* y x) (* y+ x))
      :corollary
      (implies (and (<= y y+)
                    (<= 0 x)
                    (rationalp x)
                    )
               (<= (* y x) (* y+ x))))
     (:linear
      :corollary
      (implies (and (<= y y+)
                    (rationalp x)
                    (<= 0 x))
               (<= (* y x) (* y+ x))))))

  (defthm *-strongly-monotonic-alt
    (implies (and (< y y+)
                  (rationalp x)
                  (< 0 x))
             (< (* x y) (* x y+)))
    :rule-classes
    ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
     (:linear)
     (:forward-chaining
      :trigger-terms ((* y x) (* y+ x))
      :corollary
      (implies (and (< y y+)
                    (rationalp x)
                    (< 0 x))
               (< (* y x) (* y+ x))))
     (:linear
      :corollary
      (implies (and (< y y+)
                    (rationalp x)
                    (< 0 x))
               (< (* y x) (* y+ x))))))

  (defthm *-weakly-monotonic-negative-multiplier-alt
    (implies (and (<= y y+)
                  (rationalp x)
                  (< x 0))
             (<= (* x y+) (* x y)))
    :rule-classes
    ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
     (:linear)
     (:forward-chaining
      :trigger-terms ((* y x) (* y+ x))
      :corollary
      (implies (and (<= y y+)
                    (rationalp x)
                    (< x 0))
               (<= (* y+ x) (* y x))))
     (:linear
      :corollary
      (implies (and (<= y y+)
                    (rationalp x)
                    (< x 0))
               (<= (* y+ x) (* y x))))))

  (defthm *-strongly-monotonic-negative-multiplier-alt
    (implies (and (< y y+)
                  (rationalp x)
                  (< x 0))
             (< (* x y+) (* x y)))
    :rule-classes
    ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
     (:linear)
     (:forward-chaining
      :trigger-terms ((* y x) (* y+ x))
      :corollary
      (implies (and (< y y+)
                    (rationalp x)
                    (< x 0))
               (< (* y+ x) (* y x))))
     (:linear
      :corollary
      (implies (and (< y y+)
                    (rationalp x)
                    (< x 0))
               (< (* y+ x) (* y x))))))


  (defthm /-weakly-monotonic-alt
    (implies (and (<= y y+)
                  (rationalp y)
                  (rationalp y+)
                  (< 0 y))
             (<= (/ y+) (/ y)))
    :rule-classes
    ((:forward-chaining :trigger-terms ((/ y+) (/ y))) :linear))

  (defthm /-strongly-monotonic-alt
    (implies (and (< y y+)
                  (rationalp y)
                  (rationalp y+)
                  (< 0 y))
             (< (/ y+) (/ y)))
    :rule-classes
    ((:forward-chaining :trigger-terms ((/ y+) (/ y))) :linear))
  )
 )





(defthm /-weakly-monotonic
  (implies (and (<= y y+)
;                (not (equal 0 y))
                (< 0 y) ;gen?
                (case-split (rationalp y))
                (case-split (rationalp y+))
                )
           (<= (/ y+) (/ y)))
  :hints (("Goal" :use ( /-WEAKLY-MONOTONIC-ALT
                  )))
  :rule-classes
  ((:forward-chaining :trigger-terms ((/ y+) (/ y))) :linear))

(defthm /-strongly-monotonic
  (implies (and (< y y+)
                (< 0 y) ;gen?
                (case-split (rationalp y))
                (case-split (rationalp y+))
                )
           (< (/ y+) (/ y)))
  :hints (("Goal" :use ( /-strongly-MONOTONIC-ALT
                  )))
  :rule-classes
  ((:forward-chaining :trigger-terms ((/ y+) (/ y))) :linear))

(defthm *-weakly-monotonic
  (implies (and
                (<= y y+)
                (<= 0 x)                 ;this hyp was last... re-order bad?
                (case-split (rationalp x)) ; This does not hold if x, y, and z are complex!
                )
           (<= (* x y) (* x y+)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and
                  (<= y y+)
                  (<= 0 x)
                  (case-split (rationalp x))
                  )
             (<= (* y x) (* y+ x))))
   (:linear
    :corollary
    (implies (and
                  (<= y y+)
                  (<= 0 x)
                  (case-split (rationalp x))
                  )
             (<= (* y x) (* y+ x))))))

#| Here is the complex counterexample to which we alluded above.

(let ((y  #c(1 -1))
      (y+ #c(1 1))
      (x  #c(1 1)))
    (implies (and (<= y y+)
                  (<= 0 x))
             (<= (* x y) (* x y+))))
|#

;could we generalize the (rationalp x) hyp to (not (complex-rationalp)) ?
(defthm *-strongly-monotonic
  (implies (and (< y y+)
                (< 0 x)
                (case-split (rationalp x))
                )
           (< (* x y) (* x y+)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and
                  (< y y+)
                  (< 0 x)
                  (case-split (rationalp x))
                  )
             (< (* y x) (* y+ x))))
   (:linear
    :corollary
    (implies (and
                  (< y y+)
                  (< 0 x)
                  (case-split (rationalp x))
                  )
             (< (* y x) (* y+ x))))))

(defthm *-weakly-monotonic-negative-multiplier
  (implies (and (<= y y+)
                (< x 0)
                (case-split (rationalp x))
                )
           (<= (* x y+) (* x y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and
                  (<= y y+)
                  (< x 0)
                  (case-split (rationalp x))
                  )
             (<= (* y+ x) (* y x))))
   (:linear
    :corollary
    (implies (and
                  (<= y y+)
                  (< x 0)
                  (case-split (rationalp x))
                  )
             (<= (* y+ x) (* y x))))))

(defthm *-strongly-monotonic-negative-multiplier
  (implies (and
                (< y y+)
                (< x 0)
                (case-split (rationalp x))
                )
           (< (* x y+) (* x y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and
                  (< y y+)
                  (< x 0)
                  (case-split (rationalp x))
                  )
             (< (* y+ x) (* y x))))
   (:linear
    :corollary
    (implies (and
                  (< y y+)
                   (< x 0)
                  (case-split (rationalp x))
                  )
             (< (* y+ x) (* y x))))))



; We now prove a bunch of bounds theorems for *.  We are concerned with bounding the
; product of a and b given intervals for a and b.  We consider three kinds of intervals.
; We discuss only the a case.

; abs intervals mean (abs a) < amax or -amax < a < amax, where amax is positive.

; nonneg-open intervals mean 0<=a<amax.

; nonneg-closed intervals mean 0<=a<=amax, where amax is positive.

; We now prove theorems with names like abs*nonneg-open, etc. characterizing
; the product of two elements from two such interals.  All of these theorems
; are made with :rule-classes nil because I don't know how to control their
; use.

;BOZO move these to extra-rules? these are copied in fp.lisp!
(encapsulate nil
  (local
   (defthm renaming
    (implies (and (rationalp a)
                  (rationalp xmax)
                  (rationalp b)
                  (rationalp bmax)
                  (< (- xmax) a)
                  (<= a xmax)
                  (< 0 xmax)
                  (<= 0 b)
                  (< b bmax))
             (and (< (- (* xmax bmax)) (* a b))
                  (< (* a b) (* xmax bmax))))
    :hints (("Goal" :cases ((equal b 0))))))

; This lemma is for lookup * d and lookup * away.  We don't need to consider 0
; < b for the d case because we have 0 < 1 <= d and the conclusion of the new
; lemma would be no different.

  (defthm abs*nonneg-open
    (implies (and (rationalp a)
                  (rationalp amax)
                  (rationalp b)
                  (rationalp bmax)
                  (< (- amax) a)
                  (<= a amax)       ; (< a amax) is all we'll ever use, I bet.
                  (< 0 amax)
                  (<= 0 b)
                  (< b bmax))
             (and (< (- (* amax bmax)) (* a b))
                  (< (* a b) (* amax bmax))))
    :hints (("Goal" :by renaming))
    :rule-classes nil))

(defthm abs*nonneg-closed
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (< a amax)
                (< 0 amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (< (- (* amax bmax)) (* a b))
                (< (* a b) (* amax bmax))))
  :hints (("Goal" :cases ((equal b 0))))
  :rule-classes nil)

(defthm nonneg-closed*abs
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (< a amax)
                (< 0 amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (< (- (* amax bmax)) (* b a))
                (< (* b a) (* amax bmax))))
  :hints (("Goal" :use abs*nonneg-closed))
  :rule-classes nil)

(defthm nonneg-open*abs
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (<= a amax) ; (< a amax) is all we'll ever use, I bet.
                (< 0 amax)
                (<= 0 b)
                (< b bmax))
           (and (< (- (* bmax amax)) (* a b))
                (< (* a b) (* bmax amax))))
    :hints (("Goal" :use abs*nonneg-open))
    :rule-classes nil)

; The next three, which handle nonnegative open intervals in the first argument,
; can actually be seen as uses of the abs intervals above.  Simply observe that
; if 0<=a<amax then -amax<a<amax.

(defthm nonneg-open*nonneg-closed
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (< a amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (<= 0 (* a b))
                (< (* a b) (* amax bmax))))
  :hints (("Goal" :use abs*nonneg-closed))
  :rule-classes nil)

(defthm nonneg-open*nonneg-open
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (< a amax)
                (<= 0 b)
                (< b bmax))
           (and (<= 0 (* a b))
                (< (* a b) (* amax bmax))))
  :hints (("Goal" :use abs*nonneg-open))
  :rule-classes nil)

; and the commuted version
(defthm nonneg-closed*nonneg-open
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (< a amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (<= 0 (* b a))
                (< (* b a) (* amax bmax))))
  :hints (("Goal" :use nonneg-open*nonneg-closed))
  :rule-classes nil)

(defthm nonneg-closed*nonneg-closed
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (<= a amax)
                (< 0 amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (<= 0 (* a b))
                (<= (* a b) (* amax bmax))))
  :rule-classes nil)

(defthm abs*abs
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (< a amax)
                (< 0 amax)
                (< (- bmax) b)
                (<= b bmax)
                (< 0 bmax))
           (and (< (- (* amax bmax)) (* a b))
                (< (* a b) (* amax bmax))))
  :hints (("Goal" :cases ((< b 0) (> b 0))))
  :rule-classes nil)

;Apparenlty, ACL2 will match (- c) to -1...
;This rule is incomplete...
;make a bind-free rule for this...
(defthm rearrange-negative-coefs-<
  (and (equal (< (* (- c) x) z)
              (< 0 (+ (* c x) z)))
       (equal (< (+ (* (- c) x) y) z)
              (< y (+ (* c x) z)))
       (equal (< (+ y (* (- c) x)) z)
              (< y (+ (* c x) z)))
       (equal (< (+ y1 y2 (* (- c) x)) z)
              (< (+ y1 y2) (+ (* c x) z)))
       (equal (< (+ y1 y2 y3 (* (- c) x)) z)
              (< (+ y1 y2 y3) (+ (* c x) z)))
       (equal (< z (+ (* (- c) x) y))
              (< (+ (* c x) z) y))
       (equal (< z (+ y (* (- c) x)))
              (< (+ (* c x) z) y))
       (equal (< z (+ y1 y2 (* (- c) x)))
              (< (+ (* c x) z) (+ y1 y2)))
       (equal (< z (+ y1 y2 y3 (* (- c) x)))
              (< (+ (* c x) z) (+ y1 y2 y3)))))

;make a bind-free rule for this...
(defthm rearrange-negative-coefs-equal
  (and (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp z)))
                (equal (equal (* (- c) x) z)
                       (equal 0 (+ (* c x) z))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y))
                     (case-split (rationalp z)))
                (equal (equal (+ (* (- c) x) y) z)
                       (equal y (+ (* c x) z))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y))
                     (case-split (rationalp z)))
                (equal (equal (+ y (* (- c) x)) z)
                       (equal y (+ (* c x) z))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y1))
                     (case-split (rationalp y2))
                     (case-split (rationalp z)))
                (equal (equal (+ y1 y2 (* (- c) x)) z)
                       (equal (+ y1 y2) (+ (* c x) z))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y1))
                     (case-split (rationalp y2))
                     (case-split (rationalp y3))
                     (case-split (rationalp z)))
                (equal (equal (+ y1 y2 y3 (* (- c) x)) z)
                       (equal (+ y1 y2 y3) (+ (* c x) z))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y))
                     (case-split (rationalp z)))
                (equal (equal z (+ (* (- c) x) y))
                       (equal (+ (* c x) z) y)))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y))
                     (case-split (rationalp z)))
                (equal (equal z (+ y (* (- c) x)))
                       (equal (+ (* c x) z) y)))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y1))
                     (case-split (rationalp y2))
                     (case-split (rationalp z)))
                (equal (equal z (+ y1 y2 (* (- c) x)))
                       (equal (+ (* c x) z) (+ y1 y2))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y1))
                     (case-split (rationalp y2))
                     (case-split (rationalp y3))
                     (case-split (rationalp z)))
                (equal (equal z (+ y1 y2 y3 (* (- c) x)))
                       (equal (+ (* c x) z) (+ y1 y2 y3))))))

(include-book "inverted-factor")

;Sometimes we don't want these rules enabled (especially when we're doing linear reasoning about "quotients"
;like calls to / or floor or fl or nonnegative-integer-quotient).
(defthm equal-multiply-through-by-inverted-factor-from-left-hand-side
  (implies (and (bind-free (find-inverted-factor lhs) (k))
                (syntaxp (not (is-a-factor k lhs)))
                (syntaxp (sum-of-products-syntaxp lhs))
                (syntaxp (sum-of-products-syntaxp rhs))
                (syntaxp (not (quotep lhs))) ;if lhs is a constant (e.g., (equal x '1/2)) then do nothing
                (case-split (not (equal k 0)))
                (case-split (acl2-numberp k))
                (case-split (acl2-numberp lhs))
                (case-split (acl2-numberp rhs))
                )
           (equal (equal lhs rhs)
                  (equal (* lhs k) (* rhs k)))))

(defthm equal-multiply-through-by-inverted-factor-from-right-hand-side
  (implies (and (bind-free (find-inverted-factor rhs) (k))
                (syntaxp (not (is-a-factor k rhs)))
                (syntaxp (sum-of-products-syntaxp lhs))
                (syntaxp (sum-of-products-syntaxp rhs))
                (syntaxp (not (quotep rhs))) ;if rhs is a constant (e.g., (equal '1/2 x)) then do nothing
                (case-split (not (equal k 0)))
                (case-split (acl2-numberp k))
                (case-split (acl2-numberp lhs))
                (case-split (acl2-numberp rhs))
                )
           (equal (equal lhs rhs)
                  (equal (* lhs k) (* rhs k)))))

#|
;are the case splits caused by these 2 rules bad?
;prove more rules with positive (and then negative) hyps?
;maybe we can rewrite LHS first, to prevent loops.  can we rely on the rewriting to simplify LHS enough?  what
;about funny cases?
 Note on loops: Consider when LHS is (* k (/ k)).  This has not been
;simplified, but (very unfortunately), we cannot rely on ACL2 to have rewritten subterms before rewriting a
;term.
In this case, we must be sure that we don't multiply through by k (since we found the inverted factor (/ k).

|#
(defthm less-than-multiply-through-by-inverted-factor-from-left-hand-side
  (implies (and (bind-free (find-inverted-factor lhs) (k))
                (syntaxp (not (is-a-factor k lhs))) ;helps prevent loops.
                (syntaxp (sum-of-products-syntaxp lhs))
                (syntaxp (sum-of-products-syntaxp rhs))
                (case-split (not (equal k 0)))
                (case-split (rationalp k)) ;gen!
                )
           (equal (< lhs rhs)
                  (if (<= 0 k)
                      (< (* lhs k) (* rhs k))
                    (< (* rhs k) (* lhs k))))))

(defthm less-than-multiply-through-by-inverted-factor-from-right-hand-side
  (implies (and (bind-free (find-inverted-factor rhs) (k))
                (syntaxp (not (is-a-factor k rhs)))
                (syntaxp (sum-of-products-syntaxp lhs))
                (syntaxp (sum-of-products-syntaxp rhs))
                (case-split (not (equal k 0)))
                (case-split (rationalp k))
                )
           (equal (< lhs rhs)
                  (if (<= 0 k)
                      (< (* lhs k) (* rhs k))
                    (< (* rhs k) (* lhs k))))))

;move to extra?
(defthm x*/y=1->x=y
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal x 0))
                (not (equal y 0)))
           (equal (equal (* x (/ y)) 1)
                  (equal x y)))
  :rule-classes nil)

;move this stuff?
(defun point-right-measure (x)
  (floor (if (and (rationalp x) (< 0 x)) (/ x) 0) 1))

(defun point-left-measure (x)
  (floor (if (and (rationalp x) (> x 0)) x 0) 1))

(include-book "ordinals/e0-ordinal" :dir :system)

(defthm recursion-by-point-right
  (and (e0-ordinalp (point-right-measure x))
       (implies (and (rationalp x)
                     (< 0 x)
                     (< x 1))
                (e0-ord-< (point-right-measure (* 2 x))
                          (point-right-measure x)))))

(defthm recursion-by-point-left
  (and (e0-ordinalp (point-left-measure x))
       (implies (and (rationalp x)
                     (>= x 2))
                (e0-ord-< (point-left-measure (* 1/2 x))
                          (point-left-measure x)))))

(in-theory (disable point-right-measure point-left-measure))

(defthm x<x*y<->1<y
  (implies (and (rationalp x)
                (< 0 x)
                (rationalp y))
           (equal (< x (* x y))
                  (< 1 y)))
  :rule-classes nil)

(defthm cancel-equal-*
  (implies (and (rationalp r)
                (rationalp s)
                (rationalp a)
                (not (equal a 0)))
           (equal (equal (* a r) (* a s))
                  (equal r s)))
  :rule-classes nil)


;not used anywhere in support/
;i have a better rule...
(defthm cancel-<-*
  (implies (and (rationalp r)
                (rationalp s)
                (rationalp a)
                (< 0 a))
           (equal (< (* a r) (* a s))
                  (< r s)))
  :rule-classes nil)


