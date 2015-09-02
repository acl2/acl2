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

;My approach (and I believe this is Russinoff's approach too) for reasoning about floor and related
;functions is to write everything in terms of fl.  Unlike floor, fl takes only 1 argument.  Furthermore, all
;calls to floor can be rewritten to calls to fl using floor-fl

;don't need everything in this book!
(local (include-book "numerator"))
(local (include-book "denominator"))
(local (include-book "nniq"))
(local (include-book "arith2"))
(local (include-book "ground-zero"))
(local (include-book "floor"))
(local (include-book "integerp"))
(local (include-book "rationalp"))
(local (include-book "unary-divide"))
(local (include-book "common-factor"))

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
                  (<= n (fl x))))
  :hints (("Goal" :in-theory (enable fl)))
)

;remove syntaxp hyp?
;weird rule...
(defthm non-integerp-<-integerp
  (implies (and (and (syntaxp (quotep x)))
                (not (integerp x))
                (integerp n) ;backchain limit?
                (case-split (rationalp x))
                )
           (equal (< x n)
                  (< (fl x) n)))
  :hints (("Goal" :in-theory (enable fl))))

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
                            (+ i (fl (+ x1 x2 x3 x4)))))))
  :hints (("Goal" :in-theory (enable fl)))
)

(defthm a12
  (implies (and (integerp i)
                (integerp j)
                (< 1 j)
                (< j i))
           (and (< (acl2-count (fl (/ i j))) (acl2-count i))
                (< (acl2-count (fl (* (/ j) i))) (acl2-count i))))
  :hints (("Goal" :in-theory (enable fl)))
  :rule-classes :linear
)

;why "fl-def" in the names?  this isn't a definition...

;make a separate rewrite-version
(defthm fl-def-linear-part-1
  (implies (case-split (not (complex-rationalp x)))
           (<= (fl x) x))
  :hints (("goal" :in-theory (enable fl floor)))
  :rule-classes (:rewrite (:linear :trigger-terms ((fl x))))
  )

(defthm fl-def-linear-part-2
  (implies (case-split (not (complex-rationalp x)))
           (< x (1+ (fl x))))
  :hints (("goal" :in-theory (enable fl floor)))
  :rule-classes (:rewrite (:linear :trigger-terms ((fl x)))))

;later, drop the hyp completely
;disabled since we have the rules above
;drop this whole rule
(defthmd a13
  (implies (case-split (rationalp x)) ;this hyp isn't needed for the first conslusion?
           (and (< (1- x) (fl x))
                (<= (fl x) x)))
  :hints (("Goal" :in-theory (enable fl)))
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
  :hints (("Goal" :in-theory (enable fl)))
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
                  0))
  :hints (("Goal" :in-theory (enable fl))))


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

(local
 (defthm fl/int-1
    (implies (and (rationalp x)
		  (integerp n)
		  (<= 0 n)
                  )
	     (<= (fl (/ (fl x) n))
		 (fl (/ x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable fl-def-linear-part-1
                                     fl-def-linear-part-2)
           :use ((:instance fl-def-linear))))))




(local
 (defthm fl/int-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (fl (/ (fl x) n))
		 (fl (/ x n))))
  :rule-classes ()
  :hints (("Goal"  :in-theory (disable fl-def-linear-part-1
                                       fl-def-linear-part-2)
           :use ((:instance fl-def-linear)
                 (:instance n<=fl-linear (n (* n (fl (/ x n)))))
                 (:instance n<=fl-linear (n (fl (/ x n))) (x (/ (fl x) n)))
                 (:instance fl-def-linear (x (/ x n)))
                 (:instance fl-def-linear (x (/ (fl x) n))))))))

;BOZO will this match?
(defthm fl/int-rewrite
  (implies (and (integerp n)
                (<= 0 n)
                (rationalp x))
           (equal (fl (/ (fl x) n))
                  (fl (/ x n))))
  :hints (("Goal" :use ((:instance fl/int-1)
			(:instance fl/int-2)))))

(defthm fl/int-rewrite-alt
  (implies (and (integerp n)
                (<= 0 n)
                (rationalp x))
           (equal (fl (* (/ n) (fl x)))
                  (fl (/ x n))))
  :hints (("Goal" :in-theory (disable fl/int-rewrite)
           :use ( fl/int-rewrite))))


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
                  (< x 0)))
  :hints (("Goal" :in-theory (enable fl)))
  )

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
                  (+ (truncate c1 1) (fl (+ (rem c1 1) x)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rem)
                              '(truncate)))))



;fl-minus?

(defthm fl-minus-factor
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
                (not (< X (* Y (FL (* (/ Y) X)))))))
  :hints (("Goal" :in-theory (disable fl-strong-monotone
                                      FL-WEAK-MONOTONE FL-DEF-LINEAR-part-1)
           :use (:instance FL-DEF-LINEAR-part-1 (x (/ x y))))))

;Our scheme for dealing with FLOOR is to always rewrite calls of it to FL
(defthm floor-fl
  (equal (floor m n)
         (fl (/ m n)))
  :hints (("goal" :in-theory (e/d (fl) ( RATIONALP-PRODUCT))
           :cases ((rationalp m) ;drop this hint?
                   ))))

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
                  (* 1/2 x)))
)

;new version
(defthm fl-force-to-0
  (implies (case-split (rationalp x))
           (equal (equal 0 (fl x))
                  (and (<= 0 x)
                       (< x 1)))))


(in-theory (disable fl-force-to-0)) ;may be expensive

;generalize to any amount of shifting each time and to any base (2,3, etc.)?

;is there a linear rule missing?  why did we need to :use fl-def-linear?
;(both expressions shift x right n+1 spots and chop)





#|
;represents the fractional part of a number
(defun md (x)
  (- x (fl x)))

(defthm fl-plus-md
  (implies (acl2-numberp x)
           (equal (+ (fl x) (md x))
                  x)))

(defthm md-nonnegative
  (implies (rationalp x)
           (<= 0 (md x))))

(defthm md-less-than-1
  (implies (rationalp x)
           (<= 0 (md x))))

(defthm md-type-rationalp
  (implies (rationalp x)
           (rationalp (md x))))


(in-theory (disable fl-plus-md))

(in-theory (disable md))

|#



;attempted addition 1/7/02:

;make linear?
(defthm fl-factor-out-integer-bound
  (implies (and (integerp n)
                (> n 0)
                (rationalp x)
                )
           (<= (* n (fl x))
               (fl (* n x)))))

;make linear?
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

;move
;strictly better than the version in the arithmetic books
(DEFTHM QUOTIENT-NUMER-DENOM-eric
  (IMPLIES (AND (INTEGERP X)
                (<= 0 X) ; was (< 0 x)
                (INTEGERP Y)
                (<= 0 Y)) ;was (< 0 y)
           (EQUAL (NONNEGATIVE-INTEGER-QUOTIENT (NUMERATOR (/ X Y))
                                                (DENOMINATOR (/ X Y)))
                  (NONNEGATIVE-INTEGER-QUOTIENT X Y)))
  :hints (("Goal" :cases ((and (= x 0) (=  y 0))
                          (and (not (= x 0)) (= y 0))
                          (and (= x 0) (not (= y 0)))))))

;(in-theory (disable QUOTIENT-NUMER-DENOM))







; rewrites things like (EQUAL (* 32768 (FL (* 1/32768 x))) x)
(defthm fl-claim-rewrite-to-integerp-claim-gen
  (implies (and (equal k-inverse (/ k))
                (case-split (acl2-numberp k))
                (case-split (not (equal k 0)))
                (case-split (acl2-numberp x))
                )
           (and (equal (EQUAL (* k (FL (* k-inverse X))) X)
                       (integerp (* k-inverse x)))
                (equal (EQUAL (* k (FL (* X k-inverse))) X)
                       (integerp (* k-inverse x)))))
  :hints (("Goal" :in-theory (disable FL-INTEGERP
                                      )
           :use (:instance fl-integerp (x (* k-inverse X)))
           )
          ))
(in-theory (disable fl-claim-rewrite-to-integerp-claim-gen))

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
                       (integerp (* k-inverse x y)))))
  :hints (("Goal" :in-theory (disable FL-INTEGERP
                                      )
           :use (:instance  fl-claim-rewrite-to-integerp-claim-gen
                            (x (* x y))))))




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
                       (integerp (* k-inverse x)))))
  :hints (("Goal" :in-theory (disable FL-INTEGERP
;                           (:type-prescription fl)
                                      )
           :use (:instance fl-integerp (x (* k-inverse X)))
           )
          ))

#|
(defthm fl-chops-off-1/2
  (implies (and (not (integerp x))
                (integerp (* 2 x))
                (case-split (rationalp x))
                )
           (equal (fl x)
                  (- x 1/2)))
  :hints (("Goal" :use (:instance fl-unique (n                  (- x 1/2)))))
)
(in-theory (disable  fl-chops-off-1/2))

(defthm fl-chops-off-1/2-2
  (implies (and (syntaxp (not (and (quotep x)
                                   (equal (cadr x) 1/2))))
                (not (integerp x))
                (integerp (* 2 x))
                (case-split (rationalp x))
                (case-split (rationalp y))
                )
           (and (equal (fl (+ y x))
                       (+ (fl x) (fl (+ 1/2 y))))
                (equal (fl (+ x y))
                       (+ (fl x) (fl (+ 1/2 y))))))
  :otf-flg t
    :hints (("Goal" :in-theory (enable  fl-chops-off-1/2)
             :use (:instance fl-unique
                             (x (+ x y))
                                    (n (+ (fl x) (fl (+ 1/2 y)))))))
    )
(in-theory (disable fl-chops-off-1/2-2))
|#

;rename?
(defthm y-is-odd
  (equal (EQUAL Y (+ 1 (* 2 (FL (* 1/2 Y)))))
         (and (integerp y)
              (not (integerp (* 1/2 y))))))

(include-book "negative-syntaxp")

(defthm fl-minus-gen
  (implies (and (syntaxp (negative-syntaxp x))
                (case-split (rationalp x))
                )
          (EQUAL (FL x)
                 (IF (INTEGERP X)
                     (* -1 (FL (* -1 X)))
                     (+ -1 (- (FL (* -1 X))))))))
;this can loop with fl-minus-gen (when the result of applying fl-minus-gen doesn't get simplfied before we
;build the linear pot list)
(in-theory (disable fl-minus-factor))


(defthmd fl-of-fraction-max-change-case-1
  (implies (and (not (integerp (/ p q))) ;this case
                (integerp p)
                (integerp q)
                (< 0 q)
                )
           (>= (+ 1 (fl (/ p q)))
               (+ (/ p q) (/ q))))
  :otf-flg t
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable fl floor)
                              '(floor-fl
                                ;quotient-numer-denom
                                ;nniq-lower-bound-non-integer-case
                                ))
           :use ((:instance  <=-transitive
                             (a (+ (/ Q) (* P (/ Q))))
                             (b (+ (* P (/ Q))
                                   (/ (DENOMINATOR (* P (/ Q))))))
                             (c (+ 1
                                   (NONNEGATIVE-INTEGER-QUOTIENT (NUMERATOR (* P (/ Q)))
                                                                 (DENOMINATOR (* P (/ Q)))))))
                 (:instance nniq-eric-8 (p (- p)))
                 (:instance quotient-numer-denom (x (- p)) (y q))
                 (:instance nniq-lower-bound-non-integer-case  (x (/ p q)))))))

(defthmd fl-of-fraction-max-change-case-2
  (implies (and (integerp (/ p q)) ;this case
                (integerp p)
                (integerp q)
                (< 0 q)
                )
           (>= (+ 1 (fl (/ p q)))
               (+ (/ p q) (/ q))))
  :otf-flg t
  :hints (("Goal" :use (:instance (:instance mult-both-sides-of-<-by-positive (a 1) (b (/ q)) (c q))))))

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
               (+ (/ p q) (/ q))))
  :otf-flg t
  :hints (("Goal" :use ( fl-of-fraction-max-change-case-2  fl-of-fraction-max-change-case-1))))

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

(encapsulate
 ()
 (local (defthm FL-M+1-1
          (implies (and (integerp m)
                        (integerp n)
                        (>= m 0)
                        (> n 0)
                        (INTEGERP (+ (/ N) (* M (/ N)))))
                   (= (fl (- (/ (1+ m) n)))
                      (1- (- (fl (/ m n))))))
          :hints (("Goal" :use (:instance fl-unique (x (* M (/ N)))
                                          (n (/ (+ 1 (- n) m) n)))))
          :rule-classes ()
          ))


 (local (defthm FL-M+1-2
          (implies (and (integerp m)
                        (integerp n)
                        (>= m 0)
                        (> n 0)
                        (not (INTEGERP (+ (/ N) (* M (/ N))))))
                   (= (fl (- (/ (1+ m) n)))
                      (1- (- (fl (/ m n))))))
          :otf-flg t
          :rule-classes ()
          :hints (("Goal" :in-theory (disable FL-INTEGER-TYPE ;yuck!  had to disable these!!
                                              FL-NON-NEGATIVE-INTEGER-TYPE-PRESCRIPTION
                                              ;; The following needed disabling
                                              ;; for v2-8-alpha-12-30-03; I
                                              ;; (mattk) don't know why.
                                              FL-DEF-LINEAR-PART-2)
                   :use( (:instance fl-def-linear (x (+ (/ N) (* M (/ N)))))
                         (:instance fl-of-fraction-max-change (p m) (q n))
                         (:instance fl-unique-2 (x (* M (/ N)))
                                    (n (+ -1 (/ N) (* M (/ N)))))
                         (:instance int-unique
                                    (i (FL (+ (/ N) (* M (/ N)))))
                                    (j (FL (* M (/ N))))
                                    (x (+ (/ m n) (/ n) -1))
                                    (y (+ (/ m n) (/ n))))))
                  )))


 (defthm fl-m+1
   (implies (and (integerp m)
                 (integerp n)
                 (>= m 0)
                 (> n 0))
            (= (fl (- (/ (1+ m) n)))
               (1- (- (fl (/ m n))))))
   :hints (("Goal" :use(fl-m+1-1 fl-m+1-2)))
   :rule-classes ()))





;this was the point of nniq-eric-5 to nniq-8 in basic.  how does this get proved without nniq-eric-8?
;if fl changes its argument of p/q, it does so by at least a qth
;rephrase concl?
;make a linear rule?
(defthmd fl-of-fraction-min-change
  (implies (and (not (integerp (/ p q)))
;                (<= 0 q)
                (integerp p)
                (integerp q)
                )
           (<= (/ q)
               (- (/ p q) (fl (/ p q)))))  ;the amt of change made by fl
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (set-difference-theories
                              (enable fl floor)
                              '(nniq-eric-8
                                fl-of-fraction-max-change
                                ))
          :use (;(:instance nniq-eric-8 (p (- p)) )
                (:instance fl-of-fraction-max-change (p (- p)))
                (:instance fl-of-fraction-max-change (q (- q)))
;                 nniq-eric-8
                ))))

;bad name? improve this?
;BOZO call quot-bnd-2? or fl-bnd-2?
(defthm fl-bound
  (implies (and (< 0 y)
                (rationalp x)
                (rationalp y)
                )
           (<= (* y (FL (* x (/ y)))) x))
  :hints (("Goal" :use  (:instance floor-upper-bound (i x) (j y) )
           :in-theory (e/d (fl) (floor-upper-bound)))))

;see fl-bound
;BOZO rename params
(defthm quot-bnd
  (implies (and (<= 0 x)
                (<= 0 y)
                (rationalp x)
                (rationalp y))
           (<= (* y (fl (/ x y)))
               x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable  FL-WEAK-MONOTONE FL-DEF-LINEAR-PART-1) ;how similar are the 2 rules I
    ;had to disable?
           :use (:instance FL-DEF-LINEAR-PART-1 (x (/ x y))))))

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

