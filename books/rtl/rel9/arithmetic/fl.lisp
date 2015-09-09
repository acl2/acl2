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

;My approach (and I believe this is Russinoff's approach too) for reasoning about floor and related
;functions is to write everything in terms of fl.  Unlike floor, fl takes only 1 argument.  Furthermore, all
;calls to floor can be rewritten to calls to fl using floor-fl

(include-book "negative-syntaxp")
(local (include-book "fl-proofs"))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

;remove syntaxp hyp?
;weird rule...
(defthm integerp-<-non-integerp
  (implies (and (and (syntaxp (quotep x)))
                (not (integerp x))
                (integerp n) ;backchain limit?
                (case-split (rationalp x))
                )
           (equal (< n x)
                  (<= n (fl x)))))

;remove syntaxp hyp?
;weird rule...
(defthm non-integerp-<-integerp
  (implies (and (and (syntaxp (quotep x)))
                (not (integerp x))
                (integerp n) ;backchain limit?
                (case-split (rationalp x))
                )
           (equal (< x n)
                  (< (fl x) n))))

(defthm a10
  (and (implies (integerp i) (equal (fl i) i))
       (implies (and (integerp i)
                     (case-split (rationalp x1))) ;drop?
                (and (equal (fl (+ i x1)) (+ i (fl x1)))
                     (equal (fl (+ x1 i)) (+ i (fl x1)))))
       (implies (and (integerp i)
                     (case-split (rationalp x1))
                     (case-split (rationalp x2)))
                (and (equal (fl (+ x1 (+ i x2)))
                            (+ i (fl (+ x1 x2))))
                     (equal (fl (+ x1 (+ x2 i)))
                            (+ i (fl (+ x1 x2))))))
       (implies (and (integerp i)
                     (case-split (rationalp x1))
                     (case-split (rationalp x2))
                     (case-split (rationalp x3)))
                (and (equal (fl (+ x1 (+ x2 (+ i x3))))
                            (+ i (fl (+ x1 x2 x3))))
                     (equal (fl (+ x1 (+ x2 (+ x3 i))))
                            (+ i (fl (+ x1 x2 x3))))))
       (implies (and (integerp i)
                     (case-split (rationalp x1))
                     (case-split (rationalp x2))
                     (case-split (rationalp x3))
                     (case-split (rationalp x4)))
                (and (equal (fl (+ x1 (+ x2 (+ x3 (+ i x4)))))
                            (+ i (fl (+ x1 x2 x3 x4))))
                     (equal (fl (+ x1 (+ x2 (+ x3 (+ x4 i)))))
                            (+ i (fl (+ x1 x2 x3 x4))))))))

(defthm a12
  (implies (and (integerp i)
                (integerp j)
                (< 1 j)
                (< j i))
           (and (< (acl2-count (fl (/ i j))) (acl2-count i))
                (< (acl2-count (fl (* (/ j) i))) (acl2-count i))))
  :rule-classes :linear)

;why "fl-def" in the names?  this isn't a definition...

;make a separate rewrite-version
(defthm fl-def-linear-part-1
  (implies (case-split (not (complex-rationalp x)))
           (<= (fl x) x))
  :rule-classes (:rewrite (:linear :trigger-terms ((fl x)))))

(defthm fl-def-linear-part-2
  (implies (case-split (not (complex-rationalp x)))
           (< x (1+ (fl x))))
  :rule-classes (:rewrite (:linear :trigger-terms ((fl x)))))

;later, drop the hyp completely
;disabled since we have the rules above
;drop this whole rule
(defthmd a13
  (implies (case-split (rationalp x)) ;this hyp isn't needed for the first conslusion?
           (and (< (1- x) (fl x))
                (<= (fl x) x)))
  :rule-classes :linear)

;disabled since we have the next rules above
(defthmd fl-def-linear
  (implies (case-split (rationalp x)) ;gen?
           (and (<= (fl x) x)
                (< x (1+ (fl x)))))
  :rule-classes :linear)

;note that FL is not strongly monotonic.  That is, x<x+ does not always imply (fl x) < (fl x+)
;change param names to x, x+
;try match-free :all
(defthm fl-weakly-monotonic
  (implies (and (<= y y+)
                (case-split (rationalp y)) ;drop?
                (case-split (rationalp y+)) ;drop?
                )
           (<= (fl y) (fl y+)))
  :rule-classes ((:forward-chaining :trigger-terms ((fl y) (fl y+)))
                 (:linear)
                 (:forward-chaining
                  :trigger-terms ((fl y) (fl y+))
                  :corollary (implies (and (< y y+)
                                           (case-split (rationalp y))
                                           (case-split (rationalp y+)))
                                      (<= (fl y) (fl y+))))
                 (:linear
                  :corollary (implies (and (< y y+)
                                           (case-split (rationalp y))
                                           (case-split (rationalp y+)))
                                      (<= (fl y) (fl y+))))))

;add a separate "fl of complex is 0" ?
;because of this, I can put make (rationalp x) into (case-split (rationalp x)) for all arguments x of fl
; (since we always can simplify the other case, the split is nice)
(defthm fl-of-non-rational
  (implies (not (rationalp x))
           (equal (fl x)
                  0)))

(defthmd fl-minus
  (implies (rationalp x)
           (equal (fl (* -1 x))
                  (if (integerp x)
                      (* -1 x)
                    (1- (* -1 (fl x)))))))

;bad? free var.
(defthm fl-monotone-linear
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y))
           (<= (fl x) (fl y)))
  :rule-classes :linear)

(defthm n<=fl-linear
    (implies (and (<= n x)
		  (rationalp x)
		  (integerp n))
	     (<= n (fl x)))
  :rule-classes :linear)


;may need to disable?
(defthm fl+int-rewrite
    (implies (and (integerp n)
		  (rationalp x))
	     (equal (fl (+ x n)) (+ (fl x) n))))

(defthm fl/int-rewrite
  (implies (and (integerp n)
                (<= 0 n)
                (rationalp x))
           (equal (fl (* (fl x) (/ n)))
                  (fl (/ x n)))))

(defthm fl/int-rewrite-alt
  (implies (and (integerp n)
                (<= 0 n)
                (rationalp x))
           (equal (fl (* (/ n) (fl x)))
                  (fl (/ x n)))))

(defthm fl-integer-type
  (integerp (fl x))
  :rule-classes (:type-prescription))

;this rule is no better than fl-integer-type and might be worse
(in-theory (disable (:type-prescription fl)))

(defthm fl-int
  (implies (integerp x)
           (equal (fl x) x)))

;bad name?
(defthm fl-integerp
  (equal (equal (fl x) x)
         (integerp x)))

(defthm fl-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (<= n x)
		  (< x (1+ n)))
	     (equal (fl x) n))
  :rule-classes ())

;ACL2 already knows these facts about FL, but we include them anyway
(defthm fl-rational
  (rationalp (fl x)))

(defthm fl-integer
  (integerp (fl x)))

;add "fl of negative is negative" type rule? (actually 2 posibilities?)
(defthm fl-non-negative-integer-type-prescription
  (implies (<= 0 x)
           (and (<= 0 (fl x))
                (integerp (fl x))))
  :rule-classes (:type-prescription))

(defthm fl-less-than-zero
  (implies (case-split (rationalp x))
           (equal (< (fl x) 0)
                  (< x 0))))

;use rifx?
;prove a version for fl negative? (also t-p rules for that?)
(defthm fl-non-negative-linear
  (implies (<= 0 x)
           (<= 0 (fl x)))
  :rule-classes (:linear))



;rename to start with fl-
;needed? - any constant, not just integers
;replace the rule to pull out an integer?
;BOZO do we want to use rem here???
(defthm pull-constant-out-of-fl
  (implies (and (syntaxp (and (quotep c1) (>= (abs (cadr c1)) 1)))
                (rationalp c1)
                (rationalp x))
           (equal (fl (+ c1 x))
                  (+ (truncate c1 1) (fl (+ (rem c1 1) x))))))

;fl-minus?

;this can loop with fl-minus-gen (when the result of applying fl-minus-gen doesn't get simplfied before we
;build the linear pot list)??
;maybe fl-minus-gen is enough?
;why disabled?
(defthmd fl-minus-factor
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (rationalp k)
                (rationalp x))
           (equal (fl (* k x))
                  (if (integerp (* k x))
                      (* -1 (fl (* (- k) x)))
                      (+ -1 (- (fl (* (- k) x))))))))

(defthm fl-<-integer
  (implies (and (integerp y)
                (case-split (rationalp x)))
           (equal (< (fl x) y)
                  (< x y))))

(defthm fl->-integer
  (implies (and (integerp y)
                (case-split (rationalp x)))
           (equal (< y (fl x))
                  (<= (+ 1 y) x))))


;should this be disabled?
(defthm fl-equal-0
  (implies (case-split (rationalp x))
           (equal (equal (fl x) 0)
                  (and (<= 0 x)
                       (< x 1)))))

;kill this? or is this nice b/c it makes no change if its hyps fail to be satisfied?
(defthmd fl-equal-0-alt
  (implies (and (< x 1)
                (<= 0 x)
                (case-split (rationalp x))
                )
           (equal (fl x) 0)))

;bad names?
;fl-def-linear isn't rewrite!
;remove this??
(defthm fl-strong-monotone
  (implies (and (< x y)
                (rationalp x)
                (rationalp y)
                )
           (< (fl x) y)))

;remove this??
;make linear?
(defthm fl-weak-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                )
           (<= (fl x) y)))

;kill one of these?
(defthm fl-def-linear-quotient
  (implies (and (< 0 y)
                (case-split (rationalp x))
                (case-split (rationalp y))
                )
           (and (not (< X (* Y (FL (* X (/ Y))))))
                (not (< X (* Y (FL (* (/ Y) X))))))))

;Our scheme for dealing with FLOOR is to always rewrite calls of it to FL
(defthm floor-fl
  (equal (floor m n)
         (fl (/ m n))))

(theory-invariant (incompatible (:rewrite floor-fl)
                                (:definition fl))
                  :key floor-fl--and--fl--conflict)

;perhaps always split on even/odd for fl(x/2)
;needed? was in proof.lisp for x87 recip proof
(defthm fl-of-odd/2
  (implies (and (integerp x)
                (not (integerp (* 1/2 x)))
                )
           (equal (fl (* 1/2 x))
                  (- (* 1/2 x) 1/2))))

(defthm fl-of-even/2
  (implies (and (INTEGERP (* X (/ 2))))
           (equal (fl (* 1/2 x))
                  (* 1/2 x))))

;new version
;may be expensive
(defthmd fl-force-to-0
  (implies (case-split (rationalp x))
           (equal (equal 0 (fl x))
                  (and (<= 0 x)
                       (< x 1)))))

;generalize to any amount of shifting each time and to any base (2,3, etc.)?

;is there a linear rule missing?  why did we need to :use fl-def-linear?
;(both expressions shift x right n+1 spots and chop)


;attempted addition 1/7/02:

;make linear?
;bad name?
(defthm fl-factor-out-integer-bound
  (implies (and (integerp n)
                (> n 0)
                (rationalp x)
                )
           (<= (* n (fl x))
               (fl (* n x)))))

;make linear?
;bad name?
(defthm fl-factor-out-integer-bound-2
  (implies (and (integerp n)
                (> n 0)
                (rationalp m)
                )
           (<= (* n (fl (* m (/ n))))
               (fl m))))

;see sse-div.lisp for better versions of the above

#| for reference:
(DEFTHM FL-DEF-LINEAR
  (IMPLIES (RATIONALP X)
           (AND (<= (FL X) X) (< X (1+ (FL X)))))
  :RULE-CLASSES :LINEAR)
|#

;these thms are about getting rid of one of two (roughly) "nested" calls to fl

;why??
(defthm fl-plus-integer-eric
  (implies (and (integerp n)
                (case-split (rationalp x)) ;not true if x is a complex-rationalp
                )
           (equal (fl (+ x n))
                  (+ n (fl x)))))

(local (in-theory (disable floor-fl)))

;BOZO move!
;strictly better than the version in the arithmetic books
(defthm quotient-numer-denom-eric
  (implies (and (integerp x)
                (<= 0 x) ; was (< 0 x)
                (integerp y)
                (<= 0 y)) ;was (< 0 y)
           (equal (nonnegative-integer-quotient (numerator (/ x y))
                                                (denominator (/ x y)))
                  (nonnegative-integer-quotient x y))))

;(in-theory (disable QUOTIENT-NUMER-DENOM))

; rewrites things like (EQUAL (* 32768 (FL (* 1/32768 x))) x)
(defthmd fl-claim-rewrite-to-integerp-claim-gen
  (implies (and (equal k-inverse (/ k))
                (case-split (acl2-numberp k))
                (case-split (not (equal k 0)))
                (case-split (acl2-numberp x))
                )
           (and (equal (EQUAL (* k (FL (* k-inverse X))) X)
                       (integerp (* k-inverse x)))
                (equal (EQUAL (* k (FL (* X k-inverse))) X)
                       (integerp (* k-inverse x))))))

(defthm fl-claim-rewrite-to-integerp-claim-gen-2
  (implies (and (equal k-inverse (/ k))
                (case-split (acl2-numberp k))
                (case-split (not (equal k 0)))
                (case-split (acl2-numberp x))
                (case-split (acl2-numberp y))
                )
           (and (equal (EQUAL (* k (FL (* k-inverse X y))) (* X y))
                       (integerp (* k-inverse x y)))
                (equal (EQUAL (* k (FL (* X k-inverse y))) (* X y))
                       (integerp (* k-inverse x y)))
                (equal (EQUAL (* k (FL (* X y k-inverse))) (* X y))
                       (integerp (* k-inverse x y))))))

(defthm fl-claim-rewrite-to-integerp-claim
  (implies (and (syntaxp (and (quotep k-inverse)
                              (quotep k)))
                (equal k-inverse (/ k))
                (case-split (acl2-numberp k))
                (case-split (not (equal k 0)))
                (case-split (acl2-numberp x))
                )
           (and (equal (EQUAL (* k (FL (* k-inverse X))) X)
                       (integerp (* k-inverse x)))
                (equal (EQUAL (* k (FL (* X k-inverse))) X)
                       (integerp (* k-inverse x))))))

;move! rename?
(defthm y-is-odd
  (equal (EQUAL Y (+ 1 (* 2 (FL (* 1/2 Y)))))
         (and (integerp y)
              (not (integerp (* 1/2 y))))))

(defthm fl-minus-gen
  (implies (and (syntaxp (negative-syntaxp x))
                (case-split (rationalp x))
                )
          (EQUAL (FL x)
                 (IF (INTEGERP X)
                     (* -1 (FL (* -1 X)))
                     (+ -1 (- (FL (* -1 X))))))))

(defthmd fl-of-fraction-max-change-case-1
  (implies (and (not (integerp (/ p q))) ;this case
                (integerp p)
                (integerp q)
                (< 0 q)
                )
           (>= (+ 1 (fl (/ p q)))
               (+ (/ p q) (/ q)))))

(defthmd fl-of-fraction-max-change-case-2
  (implies (and (integerp (/ p q)) ;this case
                (integerp p)
                (integerp q)
                (< 0 q)
                )
           (>= (+ 1 (fl (/ p q)))
               (+ (/ p q) (/ q)))))

;fl(p/q) + 1 >= p/q + 1/q
;similar to  fl-of-fraction-upper-bound
;rephrase the conclusion
; if fl changes it argument, it does so by at most 1-1/q
(defthm fl-of-fraction-max-change
  (implies (and (< 0 q)
                (integerp p)
                (integerp q)
                )
           (>= (+ 1 (fl (/ p q)))
               (+ (/ p q) (/ q)))))

; Two integers, both in the interval (x,y], whose width is at most 1, must be equal.
;make other versions?
;move?
(defthm int-unique
  (implies (and (integerp i)
                (integerp j)
                (rationalp x)
                (rationalp y)
                (<= x y)
                (< x i) (<= i y)
                (< x j) (<= j y)
                (<= (- y x) 1)
                )
           (equal i j))
  :rule-classes nil
  )

;replace fl-unique?
(defthm fl-unique-2
  (implies (rationalp x)
           (equal (and (integerp n)
                       (<= n x)
                       (< x (1+ n)))
                  (equal (fl x) n)))
  :rule-classes nil)

(defthm fl-m+1
  (implies (and (integerp m)
                (integerp n)
                (>= m 0)
                (> n 0))
           (= (fl (- (/ (1+ m) n)))
              (1- (- (fl (/ m n))))))
  :rule-classes ())





;this was the point of nniq-eric-5 to nniq-8 in basic.  how does this get proved without nniq-eric-8?
;if fl changes its argument of p/q, it does so by at least a qth
;rephrase concl?
;make a linear rule?
(defthmd fl-of-fraction-min-change
  (implies (and (not (integerp (/ p q)))
                (integerp p)
                (integerp q)
                )
           (<= (/ q)
               (- (/ p q) (fl (/ p q)))))  ;the amt of change made by fl
  )

;bad name? improve this?
;BOZO call quot-bnd-2? or fl-bnd-2?
(defthm fl-bound
  (implies (and (< 0 y)
                (rationalp x)
                (rationalp y)
                )
           (<= (* y (FL (* x (/ y)))) x)))

;see fl-bound
;BOZO rename?, params
(defthm quot-bnd
  (implies (and (<= 0 x)
                (<= 0 y)
                (rationalp x)
                (rationalp y))
           (<= (* y (fl (/ x y)))
               x))
  :rule-classes :linear)

;move!
;i just added this; is it expensive?
;this was causing problems, so I disabled it.
(defthmd x-times-something>=1
  (implies (and (case-split (<= 1 y))
                (case-split (rationalp y))
                (case-split (rationalp x))
                (case-split (<= 0 x)))
           (<= x (* x y)))
  :rule-classes :linear
  )

(defthm fl-<=-y
  (implies (and (<= x y)
                (case-split (not (complex-rationalp x))))
           (<= (fl x) y)))

;make a version where n is a constant?
(defthmd fl-equal-rewrite
  (implies (and (rationalp x)
                (integerp n)) ;move to conclusion?
           (equal (equal (fl x) n)
                  (and (<= n x)
                       (< x (+ 1 n))))))

