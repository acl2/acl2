; A lightweight book about the built-in function floor.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "numerator"))
(local (include-book "denominator"))
(local (include-book "times"))
(local (include-book "plus"))
(local (include-book "minus"))
(local (include-book "divides"))
(local (include-book "times-and-divides"))
(local (include-book "nonnegative-integer-quotient"))
(local (include-book "integerp"))
(local (include-book "expt"))
(local (include-book "../../meta/meta-plus-lessp"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;move
(defthm <-of-numerator-and-denominator-same
  (implies (rationalp x)
           (equal (< (numerator x) (denominator x))
                  (if (<= x 0)
                      t
                    (< x 1))))
  :hints (("Goal" :use (:instance rational-implies2)
           :in-theory (disable rational-implies2))))

(in-theory (disable floor))

(defthm floor-of-0-arg1
  (equal (floor 0 j)
         0)
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-of-0-arg2
  (equal (floor i 0)
         0)
  :hints (("Goal" :in-theory (enable floor))))

;could be expensive?
(defthm floor-of-1-when-integerp
  (implies (integerp i)
           (equal (floor i 1)
                  i))
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-self
  (equal (floor i i)
         (if (equal (fix i) 0)
             0
           1))
  :hints (("Goal" :in-theory (enable floor)
           :cases ((acl2-numberp i)))))

;; pretty powerful
(defthmd floor-normalize-denominator
  (implies (syntaxp (not (equal j ''1))) ;prevent loops
           (equal (floor i j)
                  (floor (/ i j) 1)))
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-weak-monotone
  (implies (and (<= i1 i2)
                (<= 0 j)
                (rationalp i1)
                (rationalp i2)
                (rationalp j))
           (<= (floor i1 j) (floor i2 j)))
  :hints (("Goal" :in-theory (e/d (floor <=-of-*-and-*-same-linear)
                                  (nonnegative-integer-quotient-lower-bound-linear2))
           :cases ((rationalp i2))
           :use ((:instance nonnegative-integer-quotient-lower-bound-linear2
                            (i (numerator (* i2 (/ j))))
                            (j (denominator (* i2 (/ j)))))
                 (:instance nonnegative-integer-quotient-lower-bound-linear2
                            (i (- (numerator (* i1 (/ j)))))
                            (j (denominator (* i1 (/ j)))))))))

(defthm floor-weak-monotone-linear-1
  (implies (and (<= free i)
                (<= 0 j)
                (rationalp free)
                (rationalp i)
                (rationalp j))
           (<= (floor free j) (floor i j)))
  :rule-classes ((:linear :trigger-terms ((floor i j)))))

(defthm floor-weak-monotone-linear=-2
  (implies (and (<= i free)
                (<= 0 j)
                (rationalp free)
                (rationalp i)
                (rationalp j))
           (<= (floor i j) (floor free j)))
  :rule-classes ((:linear :trigger-terms ((floor i j)))))

(defthmd floor-when-multiple
  (implies (integerp (* i (/ j)))
           (equal (floor i j)
                  (/ i j)))
  :hints (("Goal" :in-theory (enable floor))))

;if n is an integer in the appropriate range, then it *is* the floor
(defthmd floor-unique
  (implies (and (integerp n)
                (<= n (/ i j))
                (< (+ -1 (/ i j)) n)
                (< 0 j)
                (rationalp i)
                (rationalp j))
           (equal (floor i j)
                  n))
  :hints (("Goal" :in-theory (enable floor))))

;disable?
(defthm floor-unique-equal-version
  (implies (and (<= n (/ i j))
                (< (+ -1 (/ i j)) n)
                (< 0 j)
                (rationalp i)
                (rationalp j))
           (equal (equal (floor i j) n)
                  (integerp n)))
  :hints (("Goal" :use (:instance floor-unique)
           :in-theory (disable floor-unique))))

;enable?
(defthmd my-floor-lower-bound ;floor-lower-bound is a theorem in rtl
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (< (+ -1 (/ i j)) (floor i j)))
  :hints (("Goal" :in-theory (e/d (floor) (<-OF-*-OF-/-ARG1)))))

(defthm my-floor-lower-bound-linear
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (< (+ -1 (/ i j)) (floor i j)))
  :rule-classes ((:linear :trigger-terms ((floor i j))))
  :hints (("Goal" :by my-floor-lower-bound)))

;; In this version, we have multiplied through by j.
(defthm my-floor-lower-bound-alt
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (< i (+ j (* j (floor i j)))))
  :hints (("Goal"
           :use ((:instance my-floor-lower-bound)
                 (:instance <-of-*-and-*-cancel
                            (x1 (+ -1 (* i (/ j))))
                            (x2 (floor i j))
                            (y j)))
           :in-theory (disable my-floor-lower-bound
                               <-of-*-and-*-cancel))))

(defthm my-floor-lower-bound-alt-linear
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (< i (+ j (* j (floor i j)))))
  :rule-classes ((:linear :trigger-terms ((* j (floor i j)))))
  :hints (("Goal" :by my-floor-lower-bound-alt)))

(defthmd my-floor-upper-bound ;floor-upper-bound is a theorem in rtl
  (implies (and (rationalp i)
                (rationalp j))
           ;; the phrasing of the * term matches our normal form
           (<= (floor i j) (* i (/ j))))
  :hints (("Goal" :in-theory (e/d (floor) (<-of-*-of-/-arg1)))))

(defthm floor-upper-bound-linear
  (implies (and (rationalp i)
                (rationalp j))
           ;; the phrasing of the * term matches our normal form
           (<= (floor i j) (* i (/ j))))
  :rule-classes ((:linear :trigger-terms ((floor i j))))
  :hints (("Goal" :by my-floor-upper-bound)))

(defthm *-of-floor-upper-bound-linear
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (<= (* j (floor i j)) i))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable floor))))

;; In this version, we have multiplied through by j.
(defthmd my-floor-upper-bound-alt
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (<= (* j (floor i j)) i))
  :hints (("Goal" :use ((:instance my-floor-upper-bound)
                        (:instance <-of-*-and-*-cancel
                                   (x2 (floor i j))
                                   (x1 (* i (/ j)))
                                   (y j)))
           :in-theory (disable my-floor-upper-bound
                               <-of-*-and-*-cancel))))

(defthm floor-upper-bound-strict
  (implies (and (not (integerp (/ i j)))
                (rationalp i)
                (rationalp j))
           (< (floor i j) (/ i j))))

(defthm floor-upper-bound-strong-linear-cheap
  (implies (and (not (integerp (* (/ j) i)))
                (rationalp i)
                (rationalp j))
           (< (floor i j) (* (/ j) i)))
  :rule-classes ((:linear :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (disable <-OF-*-OF-/-ARG2))))

;; generalizing this is hard since even if j is not rational, the quotient may be.
(defthm floor-when-not-rationalp-arg1
  (implies (and (not (rationalp i))
                (rationalp j))
           (equal (floor i j)
                  0))
  :hints (("Goal" :in-theory (enable floor))))

(defthmd floor-when-rationalp-and-complex-rationalp
  (implies (and (rationalp i)
                (complex-rationalp j))
           (equal (floor i j)
                  0))
  :hints (("Goal" :in-theory (enable floor))))

(defthmd divisibility-in-terms-of-floor
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (equal (integerp (/ i j))
                  (equal (* j (floor i j)) i)))
  :hints (("Goal" :in-theory (enable floor-when-multiple))))

(defthmd floor-of---arg1
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal j 0)))
           (equal (floor (- i) j)
                  (if (integerp (* i (/ j)))
                      (- (floor i j))
                    (+ -1 (- (floor i j))))))
  :hints (("Goal" :in-theory (enable floor))))

(encapsulate
  ()
  (local
   (defthm floor-of-sum-case-1
     (implies (and (< (+ (mod i1 j) (mod i2 j)) j) ;case 1
                   (rationalp j)
                   (< 0 j) ;gen?
                   (rationalp i1)
                   (rationalp i2)
                   )
              (equal (floor (+ i1 i2) j)
                     (+ (floor i1 j)
                        (floor i2 j))))
     :hints (("Goal"
              :in-theory (e/d (mod) (floor-upper-bound-linear <-of-*-and-*-cancel))
              :use ((:instance <-of-*-and-*-cancel (x1 (+ -1 (* I1 (/ J)) (* I2 (/ J)))) (x2 (+ (FLOOR I1 J) (FLOOR I2 J))) (y j))
                    (:instance floor-upper-bound-linear (i i1) (j j))
                    (:instance floor-upper-bound-linear (i i2) (j j))
                    (:instance floor-unique
                               (i (+ i1 i2))
                               (n (+ (floor i1 j)
                                     (floor i2 j)))))
              :do-not '(generalize eliminate-destructors)))))

  (local
   (defthm floor-of-sum-case-2
     (implies (and (<= j (+ (mod i1 j) (mod i2 j))) ;case 2
                   (rationalp j)
                   (< 0 j)
                   (rationalp i1)
                   (rationalp i2)
                   )
              (equal (floor (+ i1 i2) j)
                     (+ 1 (floor i1 j) (floor i2 j))))
     :hints (("Goal"
              :in-theory (e/d (mod) (<-of-*-and-*-cancel))
              :use ((:instance <-of-*-and-*-cancel
                               (x1 (+ (* I1 (/ J)) (* I2 (/ J))))
                               (x2 (+ 1 (FLOOR I1 J) (FLOOR I2 J)))
                               (y j))
                    (:instance <-of-*-and-*-cancel
                               (x1 (+ -1 (* I1 (/ J)) (* I2 (/ J))))
                               (x2 (+ 1 (FLOOR I1 J) (FLOOR I2 J)))
                               (y j))
                    (:instance my-floor-lower-bound-alt (i i1) (j j))
                    (:instance my-floor-lower-bound-alt (i i2) (j j))
                    (:instance floor-unique
                               (i (+ i1 i2))
                               (n (+ 1 (floor i1 j) (floor i2 j)))))
              :do-not '(generalize eliminate-destructors)))))

  ;;if we had / instead of floor, then (i1+i2)/j = i1/j + i2/j
  ;; with floor, things are a bit more complicated
  ;;this may be a powerful lemma for splitting into cases when we have goals with floor and mod...
  (defthmd floor-of-sum
    (implies (and (rationalp j)
                  (< 0 j) ;gen?
                  (rationalp i1)
                  (rationalp i2)
                  )
             (equal (floor (+ i1 i2) j)
                    (if (< (+ (mod i1 j) (mod i2 j)) j)
                        (+ (floor i1 j)
                           (floor i2 j))
                      (+ 1
                         (floor i1 j)
                         (floor i2 j)))))
    :hints (("Goal" :do-not '(generalize eliminate-destructors)))))

;could be expensive
(defthm floor-of-+-when-mult-arg1
  (implies (and (equal i (/ i1 j)) ; binds i
                (integerp i)
                (rationalp i2)
                (rationalp j))
           (equal (floor (+ i1 i2) j)
                  (+ i (floor i2 j))))
  :hints (("Goal" :cases ((and (acl2-numberp i2) (acl2-numberp i1))
                          (and (acl2-numberp i2) (not (acl2-numberp i1)))
                          (and (not (acl2-numberp i2)) (not (acl2-numberp i1))))
           :in-theory (enable floor))))

;could be expensive
(defthm floor-of-+-when-mult-arg2
  (implies (and (equal i (/ i2 j)) ; binds i
                (integerp i)
                (rationalp i1)
                (rationalp j))
           (equal (floor (+ i1 i2) j)
                  (+ i (floor i1 j))))
  :hints (("Goal" :use (:instance floor-of-+-when-mult-arg1 (i1 i2) (i2 i1))
           :in-theory (disable floor-of-+-when-mult-arg1))))

(defthm equal-of-0-and-floor
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (equal (equal 0 (floor i j))
                  (and (< i j)
                       (<= 0 i))))
  :hints (("Goal" :in-theory (enable floor))))

;drop the non-gen one?
(defthm equal-of-0-and-floor-gen
  (implies (and (rationalp i)
                (rationalp j))
           (equal (equal 0 (floor i j))
                  (if (< 0 j)
                      (and (< i j)
                           (<= 0 i))
                    (if (equal 0 j)
                        t
                      ;; (< j 0):
                      (and (< j i)
                           (<= i 0))))))
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-of-1-arg1
  (implies (natp j) ;allow non nats somehow? ;allow negatives?
           (equal (floor 1 j)
                  (if (equal j 1)
                      1
                    0)))
  :hints (("Goal" :cases ((equal 0 j)))))

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

;proved by ihs/quotient-remainder-lemmas
(defthm floor-of-floor
  (implies (and (rationalp i)
                (natp j1)
                (natp j2))
           (equal (floor (floor i j1) j2)
                  (floor i (* j1 j2))))
  :hints (("Goal" :cases ((and (equal j1 0) (equal j2 0))
                          (and (not (equal j1 0)) (equal j2 0))
                          (and (not (equal j1 0)) (not (equal j2 0)))))))

(local (include-book "arithmetic/inequalities" :dir :system)) ;for <-*-/-LEFT

;move
(defthm <-*-/-left-with-addend
  (implies (and (< 0 y)
                (real/rationalp x)
                (rationalp k)
                (real/rationalp y)
                (real/rationalp a))
           (equal (< (+ k (* x (/ y))) a)
                  (< (+ (* k y) x) (* a y))))
  :hints (("Goal" :use (:instance <-*-/-left (x (+ (* k y) x)))
           :in-theory (disable <-*-/-left))))

;move
(defthm <-*-/-left-with-addend-alt
  (implies (and (< 0 y)
                (real/rationalp x)
                (rationalp k)
                (real/rationalp y)
                (real/rationalp a))
           (equal (< a (+ k (* x (/ y))))
                  (< (* a y) (+ (* k y) x))))
  :hints (("Goal" :use (:instance <-*-right-cancel (x a) (y (+ k (* x (/ y)))) (z y))
           :in-theory (disable <-*-right-cancel))))

(in-theory (disable floor ceiling mod))

;;this term should be negated: (+ 447 (- N)), but not (+ -447 N)
(defun all-vars-negated (term)
  (if (variablep term)
      nil
    (if (fquotep term)
        t
      (let ((fn (ffn-symb term)))
        (if (eq 'binary-+ fn)
            (and (all-vars-negated (second term))
                 (all-vars-negated (third term)))
          (if (eq 'unary-- fn)
              (variablep (second term)) ;todo: generalize?
            nil                         ;unsupported
            ))))))

(defthmd floor-minus-eric
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal j 0))
                (syntaxp (all-vars-negated i)))
           (equal (floor i j)
                  (if (integerp (* i (/ j)))
                      (- (floor (- i) j))
                    (+ (- (floor (- i) j)) -1))))
  :hints (("Goal" :in-theory (enable floor))))

(theory-invariant (incompatible (:definition mod) (:rewrite mod-recollapse-lemma2)))

;floor-minus should be split into two lemmas

;FIXME all-vars-negated returns true for a constant (even 0).  quotep help fixes it for this rule
;todo: i think i've seen this loop
;ifix this - it fired on 1 <-- old comment?
(defthmd floor-minus-eric-better
  (implies (and (syntaxp (and (all-vars-negated i)
                              (not (quotep i))))
                (rationalp i)
                (rationalp j)
                (not (equal j 0)))
           (equal (floor i j)
                  (if (integerp (* i (/ j))) ;(equal (* y (floor (- x) y)) (- x)) ;i want to express the divisibility test in terms of floor, but putting in (floor x y) loops
                      (- (floor (- i) j))
                    (+ (- (floor (- i) j)) -1))))
  :hints (("Goal" :use (:instance floor-of---arg1)
           :in-theory (disable floor-of---arg1))))

;what should we do with (FLOOR (+ -447 N) 512)?
;i'd prefer the constant to always be in [0,511]

;this makes the constant added in the range [0,y-1] if y is an integer
;FIXME add a version for constants that are too big
(defthm floor-of-plus-normalize-negative-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep y) ;; relax this?
                              ))
                (<= k 0)
;                (< (- y) k) ;FIXME add a different amount if this is not true...
                (rationalp y)
                (not (equal 0 y))
                (rationalp n)
                (rationalp k))
           (equal (floor (+ k n) y)
                  (+ (- (ceiling (- k) Y)) ;gets computed
                     (floor (+             ;gets computed:
                             (+ (* y (ceiling (- k) Y)) ;amount to add to adjust the constant
                                k)
                             n)
                            y))))
  :hints (("Goal" :use (:instance floor-of-+-when-mult-arg1
                                  (i (ceiling (- k) Y))
                                  (i1 (* y (ceiling (- k) Y)))
                                  (i2 (+ k n))
                                  (j y))
           :in-theory (disable floor-of-+-when-mult-arg1))))

(defthm <-*-/-left-with-addends-middle
  (implies (and (< 0 y)
                (real/rationalp x)
                (rationalp k)
                (rationalp k2)
                (real/rationalp y)
                (real/rationalp a))
           (equal (< (+ k (* x (/ y)) k2) a)
                  (< (+ (* k y) (* k2 y) x) (* a y))))
  :hints (("Goal" :use (:instance <-*-/-left (x (+ (* k y) (* k2 y) x)))
           :in-theory (disable <-*-/-left))))

(defthmd floor-equal-split
  (equal (equal (floor x y) (floor z y))
         (and (not (< (floor x y) (floor z y)))
              (not (> (floor x y) (floor z y))))))

;gen?
(defthm floor-bound-lemma
  (implies (and (posp y)
                (natp n)
                (< k y) ;gen and change conclusion?
                (natp k))
           (<= (floor (+ k n) y) (+ 1 (floor n y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (disable floor-weak-monotone)
           :use (:instance floor-weak-monotone
                           (i1 (+ k n))
                           (i2 (+ y n))
                           (j y)))))

;(local (include-book "ihs/quotient-remainder-lemmas" :dir :system)) ;why? for FLOOR-BOUNDED-BY-/? and to prove FLOOR-PEEL-OFF-CONSTANT

(defthm floor-peel-off-constant
  (implies (and (syntaxp (quotep k))
                (< k y) ;the constant should be normalized already?
                (rationalp n)
                ;; (rationalp y)
                ;; (< 0 y)
                ;; (not (equal 0 y))
                (natp y)
                (natp k)
                )
           (equal (floor (+ k n) y)
                  (if (< (mod n y) (- y k))
                      (floor n y)
                    (+ 1 (floor n y)))))
  :hints (("Goal" :in-theory (enable floor-of-sum))))

;gen
(defthm floor-bound
  (implies (natp x)
           (<= (floor x 2) (/ x 2))))


;gen floor-bound!
(defthm floor-bound-negative
  (implies (and (<= x 0)
                (integerp x))
           (<= (floor x 2) (/ x 2)))
  :hints (("Goal" :in-theory (enable floor))))

;gen
;get rid of the other..
(defthm floor-bound-better
  (implies (integerp x)
           (<= (floor x 2) (/ x 2))))

;drop?
(defthm floor-bound-better-linear
  (implies (integerp x)
           (<= (floor x 2) (/ x 2)))
  :rule-classes ((:linear :trigger-terms ((floor x 2)))))

(defthm floor-of-times-1/2
  (equal (floor (* 1/2 a) 1)
         (floor a 2))
  :hints (("Goal" :in-theory (enable floor))))

;gen!
(defthm equal-of-floor-same
  (implies (and (integerp j) ;(rationalp j);
                (natp i) ;(not (equal 0 i)) (integerp i)
                )
           (equal (equal (floor i j) i)
                  (or (equal i 0)
                      (equal j 1))))
  :hints (("Goal" :use ((:instance my-floor-upper-bound))
           :in-theory (disable my-floor-upper-bound
                               <-*-/-left)
           :cases ((< 1 j)
;                  (equal j 0)
                   (< j 1)))))

(defthm floor-of-one-less
  (implies (natp i)
           (equal (floor (+ -1 i) i)
                  0))
  :hints (("Goal" :in-theory (disable floor-minus-eric-better)
           :cases ((equal i 0)))))

(defthm floor-of-minus-and-minus
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal 0 y)))
           (equal (floor (- x) (- y))
                  (floor x y))))

(defthm floor-when-<
  (implies (and (< i j)
                (>= i 0)
                ;; (> j 0)
                (force (rationalp j)))
           (equal (floor i j)
                  0))
  :hints (("Goal" :cases ((rationalp i)))))

;todo: compare to *-of-floor-upper-bound-linear
(defthm floor-upper-bound-alt-linear
  (implies (and (<= 0 i)
                (rationalp i)
                (<= 0 j)
                (rationalp j))
           (<= (* j (floor i j)) i))
  :rule-classes ((:linear))
  :hints (("Goal" :in-theory (enable mod))))

(defthm floor-type-1-part-1-better
  (implies (and (< x 0)
                (> y 0)
                (rationalp x)
                (rationalp y))
           (< (floor x y) 0))
  :rule-classes ((:type-prescription)))

;why disabled?
(defthmd floor-minus-arg1
  (implies (and (rationalp x)
                (rationalp y)
                )
           (equal (floor (- x) y)
                  (if (integerp (* x (/ y)))
                      (- (floor x y))
                      (- (- (floor x y)) 1))))
  :hints (("Goal" :cases ((equal '0 y)))))

(defthm floor-minus-arg2
  (implies (and (force (rationalp x))
                (rationalp y)
                (not (equal '0 y))
                )
           (equal (floor x (- y))
                  (if (integerp (* x (/ y)))
                      (- (floor x y))
                    (- (- (floor x y)) 1)))))

(defthm floor-minus-arg1-hack
  (implies (and (syntaxp (quotep k))
                (rationalp x)
                (rationalp k)
                (rationalp y))
           (equal (floor (+ k (- x)) y)
                  (if (integerp (* (- x k) (/ y)))
                      (- (floor (- x k) y))
                      (- (- (floor (- x k) y)) 1))))
  :hints (("Goal" :use (:instance floor-minus-arg1 (x (- k x)))
           :in-theory (disable floor-minus-arg1))))

(defthm floor-minus-arg2-hack
  (implies (and (syntaxp (quotep k))
                (rationalp x)
                (rationalp k)
                (rationalp y))
           (equal (floor x (+ k (- y)))
                  (if (integerp (* x (/ (- y k))))
                      (- (floor x (- y k)))
                      (- (- (floor x (- y k))) 1))))
  :hints (("Goal" :use (:instance floor-minus-arg2 (y (- y k)))
           :in-theory (disable floor-minus-arg2))))

;rename?
(defthm floor-minus-negative-constant
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (rationalp x)
                (rationalp k)
                (rationalp y))
           (equal (floor k y)
                  (if (integerp (* (- k) (/ y)))
                      (- (floor (- k) y))
                    (- (- (floor (- k) y)) 1))))
  :hints (("Goal" :use (:instance floor-minus-arg1 (x (- k)))
           :in-theory (disable floor-minus-arg1))))

;this is better than (part of) floor-type-1
(defthm <-of-floor-and-0
  (implies (rationalp j)
           (equal (< (floor i j) 0)
                  (and (rationalp i)
                       (or (and (< i 0) (> j 0))
                           (and (> i 0) (< j 0))))))
  :hints (("Goal" :use (:instance floor-type-1 (x i) (y j))
           :in-theory (disable floor-type-1))))

;reverse of DIVISIBILITY-IN-TERMS-OF-FLOOR?
(defthmd equal-of-i-and-*-of-floor
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (equal (equal i (* j (floor i j)))
                  (integerp (* i (/ j))))))

;fixme can we do better? floor is always an integer...
(defthm natp-of-floor
  (implies (and (natp x)
                (natp y))
           (natp (floor x y)))
  :hints (("Goal" :in-theory (e/d (natp) (floor-bounded-by-/)))))

(defthm floor-of-+-of-minus
  (implies (and (not (equal 0 j))
                (rationalp j)
                (rationalp i))
           (equal (floor (+ i (- j)) j)
                  (+ -1 (floor i j)))))

(defthmd floor-bound-lemma-1
  (implies (and (rationalp x)
                (< 0 j)
                (rationalp j)
                (rationalp k)
                (<= (+ 1 k) (floor x j)))
           (<= (+ j (* j k)) x))
  :hints (("Goal" :use ((:instance my-floor-upper-bound-alt (i x))
                        (:instance <-*-left-cancel (x (floor x j)) (y (+ 1 k)) (z j)))
           :in-theory (disable <-*-left-cancel
                               my-floor-upper-bound-alt))))
;move or drop
(defthmd <-bound-hack
  (implies (and (< x y)
                (integerp x)
                (integerp y)
                (posp j))
           (< (* j x) (+ j (* j y))))
  :hints (("Goal" :use (:instance <-*-left-cancel (x y) (y (+ 1 x)) (z j))
           :in-theory (disable <-*-left-cancel))))

(defthmd floor-bound-lemma-2
  (implies (and (< (floor i j) (+ 1 k))
                (rationalp i)
                (rationalp j)
                (< 0 j)
                (integerp k) ; gen to (rationalp k)?
                )
           ;; says that k+1 is greater than the quotient
           (< i (+ j (* j k))))
  :hints (("Goal" :cases ((integerp k))
           :use ((:instance my-floor-lower-bound-alt (i i))
                        (:instance <-*-left-cancel (x k) (y (floor i j)) (z j)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (disable <-*-left-cancel
                               *-preserves->=-for-nonnegatives
                               my-floor-lower-bound-alt))))

(defthmd <-of-floor-arg2
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j)
                (integerp k) ;gen?
                )
           (equal (< k (floor i j))
                  (if (integerp k)
                      (<= (* j (+ 1 k)) i) ; the quotient is at least k+1
                    (<= (+ 1 (floor k 1)) (/ i j)))
                    ))
  :hints (("Goal":use ((:instance floor-bound-lemma-1 (x i))
                       (:instance floor-bound-lemma-2)))))

;ffixme other way?
;kill the version for 4
(defthmd <-of-constant-and-floor
  (implies (and (syntaxp (and (quotep k) (quotep j)))
                (rationalp i)
                (rationalp j)
                (< 0 j)
                (integerp k) ;gen?
                )
           (equal (< k (floor i j))
                  (<= (* j (+ 1 k)) i)))
  :hints (("Goal" :use (:instance <-of-floor-arg2))))

(defthm <-of-0-and-floor
  (implies (and (integerp x)
                (posp y))
           (equal (< 0 (floor x y))
                  (<= y x))))

(defthmd bound-from-floor-bound
  (implies (and (<= k (floor i j))
                (< 0 j)
                (rationalp i)
                (rationalp k)
                (rationalp j))
           (<= (* k j) i))
  :hints (("Goal" :in-theory (disable my-floor-upper-bound
                                      <-*-left-cancel)
           :use ((:instance <-*-left-cancel (x (floor i j)) (y m) (z j))
                 (:instance my-floor-upper-bound)))))

(defthmd bound-from-floor-bound-back
  (implies (and (<= (* k j) i)
                (< 0 j)
                (rationalp i)
                (integerp k) ;gen?
                (integerp j))
           (<= k (floor i j)))
  :hints  (("Goal" :in-theory (disable ;floor-bound-lemma2
                                       my-floor-lower-bound-alt
                                       <-*-left-cancel)
            :use (;(:instance <-*-left-cancel (x  (floor x n)) (y  m) (z n))
;                  (:instance floor-lower-bound (y n))
                  (:instance floor-weak-monotone (i1 (* k j)) (i2 i))
                  ))))

;do we want this?
;; (defthmd bound-from-floor-bound-back-gen
;;   (implies (and (<= (* (floor k 1) j) i)
;;                 (< 0 j)
;;                 (rationalp i)
;;                 (rationalp k) ; not this
;;                 (integerp j))
;;            (<= (floor k 1) (floor i j)))
;;   :hints (("Goal" :use (:instance bound-from-floor-bound-back
;;                                   (k (floor k 1)))
;;            :in-theory (disable bound-from-floor-bound-back))))

(defthmd <-of-floor-arg1
  (implies (and (< 0 j)
                (rationalp i)
                (integerp k) ;gen?
                (integerp j))
           (equal (< (floor i j) k)
                  (< i (* k j))))
  :hints (("Goal" :use (bound-from-floor-bound
                        bound-from-floor-bound-back))))

(defthmd <-of-floor-arg1-gen
  (implies (and (< 0 j)
                (rationalp i)
                (rationalp k)
                (integerp j) ;gen?
                )
           (equal (< (floor i j) k)
                  (if (integerp k)
                      ;; check whether k is bigger than the quotient:
                      (< i (* k j))
                    ;; round k up to an integer, and check whether that is
                    ;; bigger than the quotient:
                    (< (/ i j) (+ 1 (floor k 1))))))
  :hints (("Goal" :use ((:instance <-of-floor-arg1)
                        (:instance <-of-floor-arg1 (k (floor k 1))))
           :cases ((equal (floor k 1) (floor i j))))))

(defthmd <-of-floor-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep j)))
                (< 0 j)
                (rationalp i)
                (integerp k)
                (integerp j))
           (equal (< (floor i j) k)
                  (< i (* k j))))
  :hints (("Goal" :use (:instance <-of-floor-arg1)
           :in-theory (disable <-of-floor-arg1))))



;disable?
(defthm <-of-times-of-floor-and-same
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (equal (< (* j (floor i j)) i)
                  (not (integerp (/ i j)))))
  :hints (("Goal" :use (:instance my-floor-upper-bound)
           :in-theory (disable my-floor-upper-bound))))

;enable?
(defthmd <-of-*-of-floor-and-same
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (equal (< (* j (floor i j)) i)
                  (not (equal 0 (mod i j))))))

(defthm floor-when-i-is-not-an-acl2-numberp
  (implies (not (acl2-numberp i))
           (equal (floor i j)
                  0))
  :hints (("Goal" :in-theory (enable floor))))

;see also (yikes!):
;; FLOOR-MINUS-ARG1
;; FLOOR-MINUS-NEGATIVE-CONSTANT
;; FLOOR-MINUS-ERIC-BETTER
;; FLOOR-MINUS-ERIC
;; FLOOR-MINUS

;; (defthm <-of-constant-and-floor
;;   (implies (and (syntaxp (and (quotep k)
;;                               (quotep j)))
;;                 (integerp x)
;;                 (posp j)
;;                 (equal j 4) ;;gen!!
;;                 (natp k))
;;            (equal (< k (floor x j))
;;                   (<= (* j (+ 1 k)) x)))
;;   :hints (("Goal" :in-theory (enable FLOOR-BOUNDED-BY-/))))

(defthmd floor-divide-by-same
  (implies (and (rationalp i)
                (rationalp k)
                (not (equal 0 k))
                (rationalp j)
                (not (equal 0 j))
                )
           (equal (floor (/ i k) (/ j k))
                  (floor i j))))

(defthmd equal-of-constant-and-floor
  (implies (and (syntaxp (and (quotep k)
                              (quotep y)))
                (posp y)
                (integerp k)
                (integerp x))
           (equal (equal k (floor x y))
                  (and (<= (* k y) x)
                       (< x (* (+ 1 k) y)))))
  :hints (("Goal" :in-theory (disable ;floor-bound-lemma2
                                      ;floor-bound-lemma3
                                      my-floor-lower-bound-alt)
           :use ((:instance my-floor-lower-bound)
                 (:instance my-floor-upper-bound)))))

;put in more parts of floor-type-3?
(defthm floor-type-non-negative
  (implies (and (<= 0 i)
                (<= 0 j)
                (or (rationalp i)
                    (rationalp j)))
           (<= 0 (floor i j)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable floor)
           :cases ((rationalp j)))))

(defthm floor-type-when-nonpositive-and-nonnegative
  (implies (and (<= i 0)
                (<= 0 j)
                (or (rationalp i)
                    (rationalp j)))
           (<= (floor i j) 0))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable floor)
           :cases ((rationalp j)))))

;almost subsumed by <-of-floor-and-0
(defthm <-of-floor-and-0-2
  (implies (and (<= 0 i)
                (<= 0 j)
                (or (rationalp i)
                    (rationalp j)))
           (not (< (floor i j) 0))))

(defthm floor-bound-hack-eric
  (IMPLIES (AND (<= 1 j)
                (<= 0 i)
                (rationalp i)
                (rationalp j))
           (<= (* i (/ j)) i)))

;gen?
(defthm floor-bound-arg1
  (IMPLIES (AND (rationalp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j)
                )
           (equal (< i (FLOOR i j))
                  nil))
  :hints (("Goal"
;           :cases ((equal j 0))
           :use (floor-bound-hack-eric (:instance my-floor-upper-bound))
           :in-theory (e/d (posp) (floor-bounded-by-/ my-floor-upper-bound ;floor-bound-lemma3
                                                <-*-/-left
                                                <-y-*-y-x
                                                <-*-/-right
                                                floor-bound-hack-eric
                                                <-OF-*-OF-/-ARG1
                                                <-OF-*-OF-/-ARG2
                                                <-OF-*-SAME-ARG2)))))

(defthm floor-bound-arg1-linear
  (implies (and (<= 0 i)
                ;; The only bad values of j are in in interval (0,1).
                (or (integerp j)
                    (<= 1 j)
                    (<= j 0))
                (rationalp i))
           (<= (floor i j) i))
  :rule-classes ((:linear :trigger-terms ((floor i j))))
  :hints (("Goal" :cases ((< j 0))))
  )

;todo
;; (defthm floor-bound-arg1-linear-negative
;;   (implies (and (rationalp i)
;;                 (<= i 0) ; this case
;;                 ;; The only bad values of j are in in interval (0,1).
;;                 (or (integerp j)
;;                     (<= 1 j)
;;                     (<= j 0)))
;;            (<= i (floor i j)))
;;   :rule-classes ((:linear :trigger-terms ((floor i j))))
;;   :hints (("Goal" :cases ((< j 0))
;;            :use (:instance my-floor-lower-bound)
;;            :in-theory (disable my-floor-lower-bound
;;                                my-floor-lower-bound-alt))))

;todo
;; (defthm equal-of-floor-and-i
;;   (implies (and (integerp i)
;;                 (< 1 j)
;;                 (integerp j))
;;            (equal (equal (floor i j) i)
;;                   (if (<= 0 i)
;;                       (equal i 0)
;;                     (equal i -1))))
;;   :hints (("Goal"
;;            :use (:instance floor-upper-bound-strict)
;;            :in-theory (disable floor-upper-bound-strict
;;                                <-of-times-of-floor-and-same
;;                                floor-mod-elim))))

;; ;we now have a more general version
;; ;gen!
;; (defthm <-of-floor-of-constant-and-constant
;;   (implies (integerp x)
;;            (equal (< (floor x 4) 16)
;;                   (< x 64)))
;;   :hints (("Goal"
;;            :in-theory (disable floor-bound-lemma2 floor-bound-lemma3
;;                                floor-of-64-when-usb-64
;;                                floor-of-64-when-usb-31
;;                                floor-when-<
;;                                my-floor-lower-bound-alt)
;;            :use ((:instance floor-upper-bound (y 4))
;;                  (:instance floor-lower-bound (y 4))))))

(defthm <-of-floor-of-constant-and-constant-gen
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k)))
                (rationalp i)
                (integerp k)
                (posp k1))
           (equal (< (floor i k1) k)
                  (< i (* k k1))))
  :hints (("Goal"
           :use ((:instance bound-from-floor-bound (j k1) (k k))
                 (:instance bound-from-floor-bound-back (j k1) (k k))))))

;slow?
(defthm *-of-floor-of-same-when-multiple
  (implies (and (equal 0 (mod y x))
                (rationalp y)
                (rationalp x))
           (equal (* x (floor y x))
                  y))
  :hints (("Goal" :cases ((equal 0 x)))))

;; Might need other variants of this
(defthm floor-of-*-same
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (equal (floor (* j i) j)
                  (floor i 1))))

(defthm floor-of-/-arg2
  (implies (and (rationalp i)
                (rationalp j1))
           (equal (floor i (/ j1))
                  (floor (* i j1) 1))))

(defthm floor-of-*-of-/-arg2
  (implies (and (rationalp i)
                (rationalp j1)
                (rationalp j2))
           (equal (floor i (* j1 (/ j2)))
                  (floor (* i j2) j1))))

(defthmd floor-when-negative-and-small
  (implies (and (< i 0)
                (<= (- j) i)
                (rationalp i)
                (rationalp j))
           (equal (floor i j)
                  -1)))

(defthm floor-when-negative-and-small-cheap
  (implies (and (< i 0)
                (<= (- j) i)
                (rationalp i)
                (rationalp j))
           (equal (floor i j)
                  -1))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 nil nil))))

(defthm floor-of-one-less-gen
  (implies (and (syntaxp (not (quotep i))) ;defeat acl2's overly aggressive matching
                (natp i)
                (posp j))
           (equal (floor (+ -1 i) j)
                  (if (equal 0 (mod i j))
                      (+ -1 (floor i j))
                    (floor i j))))
  :hints (("Goal" :in-theory (enable floor-of-sum))))

;; (defthm nonnegative-integer-quotient-of-minus-of-numerator-and-denominator
;;   (implies (and (<= x 0)
;; ;                (integerp x)
;;                 )
;;            (equal (nonnegative-integer-quotient (- (numerator x))
;;                                                 (denominator x))
;;                   (- x))))

;; (defthm floor-bound-when-negative
;;   (implies (and (< i 0)
;;                 (<= 1 j)
;;                 (natp j)
;;                 (rationalp i)
;;                 )
;;            (<= i (floor i j)))
;;   :hints (("Goal" :in-theory (enable floor)))
;;   )

(defthm floor-of-1-move-integer-addend
  (implies (and (integerp n)
                (rationalp x))
           (equal (floor (+ x n) 1)
                  (+ n (floor x 1)))))

(defthmd nonnegative-integer-quotient-of-numerator-and-denominator
  (implies (and (rationalp x)
                (<= 0 x))
           (equal (nonnegative-integer-quotient (numerator x)
                                                (denominator x))
                  (floor x 1)))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

;move
(defthmd nonnegative-integer-quotient-of---of-numerator-and-denominator
  (implies (and (rationalp x)
                (< x 0))
           (equal (- (nonnegative-integer-quotient (- (numerator x))
                                                   (denominator x)))
                  (truncate x 1)))
  :hints (("Goal" :use (:instance nonnegative-integer-quotient-of-numerator-and-denominator (x (- x)))
           :in-theory (disable nonnegative-integer-quotient-of-numerator-and-denominator))))

;move
(in-theory (disable truncate))

(defthm floor-of-*-of-/-and-1
  (implies (and (integerp i)
                (<= 0 pos)
                (integerp pos))
           (equal (floor (* i (/ j)) 1)
                  (floor i j)))
  :hints (("Goal" :in-theory (enable floor))))

(theory-invariant (incompatible (:rewrite floor-of-*-of-/-and-1) (:rewrite floor-normalize-denominator)))

(defthmd my-floor-lower-bound-2
  (implies (and (integerp i)
                (<= 0 i) ;gen
                (posp j))
           (<= (+ -1 (/ i j) (/ j)) (floor i j)))
  :rule-classes ((:linear :trigger-terms ((floor i j))))
  :hints (("Goal"
           :use (<=-of-denominator-of-*-of-/
                 (:instance <=-of-/-linear
                            (x0 (denominator (* i (/ j))))
                            (x (* i (/ j))))
                 (:instance nonnegative-integer-quotient-lower-bound-linear2
                            (i (numerator (* i (/ j))))
                            (j (denominator (* i (/ j))))))
           :in-theory (e/d (floor)
                           (<=-of-denominator-of-*-of-/
                            <-of-+-arg2-when-negative-constant)))))

;; Disabled since it turns floor into division
(defthmd floor-when-integerp-of-quotient
  (implies (integerp (* x (/ y)))
           (equal (floor x y)
                  (* x (/ y))))
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-when-not-rationalp-of-quotient
  (implies (not (rationalp (* x (/ y))))
           (equal (floor x y)
                  0))
  :hints (("Goal" :in-theory (enable floor))))

(defthm split-low-bit
  (implies (rationalp i)
           (equal i (+ (* 2 (floor i 2)) (mod i 2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable mod))))

(defthmd floor-of-2-cases
  (implies (integerp i)
           (equal (floor i 2)
                  (if (equal 0 (mod i 2))
                      (/ i 2)
                    (+ -1/2 (/ i 2)))))
  :hints (("Goal" :use ((:instance floor-unique
                                   (j 2)
                                   (n (if (equal 0 (mod i 2))
                                          (/ i 2)
                                        (+ 1/2 (/ i 2)))))
                        (:instance split-low-bit)))))

(defthmd floor-when-evenp
  (implies (and (evenp x)
                (integerp x))
           (equal (floor x 2)
                  (/ x 2)))
  :hints (("Goal" :in-theory (enable floor evenp))))

;; this one uses evenp
(defthmd floor-of-2-cases-2
   (implies (integerp i)
            (equal (floor i 2)
                   (if (evenp i)
                       (/ i 2)
                     (+ -1/2 (/ i 2)))))
   :hints (("Goal" :in-theory (enable floor-of-2-cases evenp))))

(defthm unsigned-byte-p-of-floor-by-2-strong
  (implies (integerp x)
           (equal (unsigned-byte-p n (floor x 2))
                  (and (natp n)
                       (unsigned-byte-p (+ 1 n) x))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     expt-of-+
                                     <-of-floor-arg1
                                     ))))

(defthm equal-of-floor-and-*-of-/
  (equal (equal (floor i j) (* i (/ j)))
         (integerp (* i (/ j)))))

;; quite strong!
;rephrase the rhs?
;; If something is equal to the floor, it must be an integer, be no bigger than
;; the quotient, and be strictly bigger than the quotient minus 1.
(defthmd equal-of-floor
  (implies (and (rationalp i)
                (rationalp j))
           (equal (equal val (floor i j))
                  (and (integerp val)
                       (<= val (/ i j))
                       (< (/ i j) (+ 1 val)))))
  :hints (("Goal" :in-theory (disable <-OF-*-OF-/-ARG1
                                      <-OF-*-OF-/-ARG1-alt))))

;disable?
(defthm equal-x-times-2-floor-x
  (implies (rationalp x)
           (equal (equal x (* 2 (floor x 2)))
                  (evenp x)))
  :hints (("Goal" :in-theory (enable evenp floor))))

;; Not sure exactly where this should go
(defthm unsigned-byte-p-of-floor
  (implies (and (unsigned-byte-p size x)
                (natp y))
           (unsigned-byte-p size (floor x y)))
  :hints (("Goal"
           :cases ((equal 0 y))
           :in-theory (enable unsigned-byte-p))))

(defthm floor-of-*-and-*-cancel-arg2-arg2
  (equal (floor (* x z) (* y z))
         (if (equal (fix z) 0)
             0
           (floor x y)))
  :hints (("Goal" :in-theory (enable floor))))

(local
 (defthm helper1
   (IMPLIES (AND (RATIONALP I)
                 (RATIONALP J)
                 (< 0 J)
                 (RATIONALP K)
                 (< k (floor i j)))
            (<= (+ 1 (FLOOR K 1)) (FLOOR I J)))))

(local
 (defthm helper2
   (IMPLIES (AND (RATIONALP I)
                 (RATIONALP J)
                 (< 0 J)
                 (integerp Kup)
                 (< kup (/ i j)))
            (<= kup (FLOOR I J)))))

(defthmd <-of-floor-arg2-gen
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j)
                (rationalp k))
           (equal (< k (floor i j))
                  ;; the quotient is at least k-rounded-up:
                  (<= (+ 1 (floor k 1)) (/ i j))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (helper1
                 (:instance helper2 (kup (+ 1 (floor k 1)))))
           :in-theory (disable <-*-/-LEFT
                               <-OF-*-OF-/-ARG1-ARG2
                               <-OF-*-OF-/-ARG1
                               helper1))))

(defthm floor-bound-strict-linear
  (implies (and (< 1 j)
                (< 0 i) ;i can't be 0
                (rationalp i)
                (rationalp j))
           (< (floor i j) i))
  :rule-classes (:linear))

;strengthen?
(defthm floor-bound-strict
  (implies (and (< 1 j)
                (<= 0 i)
                (rationalp i)
                (rationalp j))
           (equal (< (floor i j) i)
                  (not (equal i 0)))))
