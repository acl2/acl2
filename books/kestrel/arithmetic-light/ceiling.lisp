; A lightweight book about the built-in function ceiling.
;
; Copyright (C) 2019-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "integerp"))
(local (include-book "times"))
(local (include-book "divide"))
(local (include-book "times-and-divide"))
(local (include-book "floor"))
(local (include-book "numerator"))
(local (include-book "denominator"))
(local (include-book "minus"))
(local (include-book "mod"))
(local (include-book "nonnegative-integer-quotient"))

(in-theory (disable ceiling))

(local (in-theory (disable floor)))

;move
(local
 (defthm integerp-of-*-of---arg2
   (equal (integerp (* x (- y)))
          (integerp (* x y)))
   :hints (("Goal" :use (:instance integerp-of-- (x (* x y)))
            :in-theory (disable integerp-of--)))))

(defthm ceiling-of-0-arg1
  (equal (ceiling 0 j)
         0)
  :hints (("Goal" :in-theory (enable ceiling floor))))

(defthm ceiling-of-0-arg2
  (equal (ceiling i 0)
         0)
  :hints (("Goal" :in-theory (enable ceiling floor))))

(defthmd ceiling-in-terms-of-floor
  (equal (ceiling i j)
         (- (floor (- i) j)))
  :hints (("Goal" :cases ((and (rationalp i) (rationalp j)))
           :in-theory (enable ceiling floor))))

;introduces an IF
(defthmd ceiling-in-terms-of-floor2
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)) ; todo
                )
           (equal (ceiling i j)
                  (if (equal 0 (mod i j))
                      (/ i j)
                      (+ 1 (floor i j)))))
  :hints (("Goal" :in-theory (enable ceiling floor equal-of-0-and-mod))))

;introduces an IF
(defthmd ceiling-in-terms-of-floor-alt
  (implies (and (rationalp i)
                (rationalp j))
           (equal (ceiling i j)
                  (if (integerp (/ i j))
                      (/ i j)
                    (+ 1 (floor i j)))))
  :hints (("Goal" :in-theory (enable ceiling floor))))

;introduces an IF
(defthmd ceiling-in-terms-of-floor3
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (equal (ceiling i j)
                  (if (equal 0 (mod i j))
                      (floor i j)
                    (+ 1 (floor i j)))))
  :hints (("Goal" :in-theory (enable ceiling floor equal-of-0-and-mod))))

(defthm ceiling-when-<=
  (implies (and (<= i j)
                (natp i)
                (posp j))
           (equal (ceiling i j)
                  (if (equal 0 i)
                      0
                    1)))
  :hints (("Goal"
           :cases ((equal i 0)
                   (equal i j))
           :use (:instance integerp-squeeze (x (/ i j)))
           :in-theory (enable ceiling-in-terms-of-floor))))

;;gen - replace the with below
(defthm ceiling-of-+-of-minus-8
 (implies (rationalp x)
          (equal (ceiling (+ -8 x) 8)
                 (+ -1 (ceiling x 8))))
 :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor))))

;todo: put back
;; (include-book "../bv/floor")
;; (defthm ceiling-of-+-of-when-multiple-arg1
;;   (implies (and (integerp (/ i1 j))
;;                 (rationalp i2)
;;                 (rationalp j)
;;                 (not (equal 0 j)))
;;           (equal (ceiling (+ i1 i2) j)
;;                  (+ (/ i1 j) (ceiling i2 j))))
;;  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor))))

(defthmd ceiling-in-terms-of-floor-cases
  (implies (and (rationalp i)
                (rationalp j))
           (equal (ceiling i j)
                  (if (integerp (/ i j))
                      (/ i j)
                    (+ 1 (floor i j)))))
  :hints (("Goal" :in-theory (enable ceiling floor))))

;; (thm
;;  (implies (and (rationalp x)
;;                (posp n) ;gen?
;;                )
;;           (equal (CEILING (+ (- N) x) N)
;;                  (+ -1 (CEILING x N))))
;;  :hints (("Goal" :in-theory (enable ceiling))))

(encapsulate ()
  (local (defthm ceiling-upper-bound-pos
           (implies (and (< 0 j)
                         (rationalp i)
                         (rationalp j))
                    (< (ceiling i j) (+ 1 (/ i j))))
           :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor)))))

  (local (defthm ceiling-upper-bound-neg
           (implies (and (< j 0) ; unusual
                                 ;                (< 0 i) ; todo
                         (rationalp i)
                         (rationalp j))
                    (< (ceiling i j) (+ 1 (/ i j))))
           :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor)))))

  (defthm ceiling-upper-bound
    (implies (and (rationalp i)
                  (rationalp j))
             (< (ceiling i j) (+ 1 (/ i j))))
    :hints (("Goal" :cases ((< j 0) (equal j 0))))))

;; We've multiplied through by j
(defthm ceiling-upper-bound-pos-linear
  (implies (and (< 0 j)
                (rationalp i)
                (rationalp j))
           (< (* j (ceiling i j)) (+ j i)))
  :rule-classes ((:linear :trigger-terms ((* j (ceiling i j)))))
  :hints (("Goal" :use ((:instance ceiling-upper-bound)
                        )
           :in-theory (disable ceiling-upper-bound))))

;; We've multiplied through by j (and flipped the inequality since j is negative)
(defthm ceiling-upper-bound-neg-linear
  (implies (and (< j 0) ; unusual
                (rationalp i)
                (rationalp j))
           (< (+ j i) (* j (ceiling i j))))
  :rule-classes ((:linear :trigger-terms ((* j (ceiling i j)))))
  :hints (("Goal" :use ((:instance ceiling-upper-bound)
                        (:instance <-of-*-and-*-cancel-gen
                                   (x2 (ceiling i j))
                                   (x1 (+ 1 (* i (/ j))))
                                   (y j)))
           :in-theory (disable ceiling-upper-bound
                               <-of-*-and-*-cancel-gen))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; move these up?

(defthm ceiling-lower-bound
  (implies (and (rationalp i)
                (rationalp j))
           (<= (/ i j) (ceiling i j)))
  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor))))

(defthm ceiling-lower-bound-linear
  (implies (and (rationalp i)
                (rationalp j))
           (<= (/ i j) (ceiling i j)))
  :rule-classes ((:linear :trigger-terms ((ceiling i j)))))

;; We've multiplied through by j
(defthm *-of-ceiling-same-linear-pos
  (implies (and (< 0 j)
                (rationalp i)
                (rationalp j))
           (<= i (* j (ceiling i j))))
  :rule-classes :linear
  :hints (("Goal" :use ceiling-lower-bound
           :in-theory (disable ceiling-lower-bound))))

;; We've multiplied through by j (and flipped the inequality since j is negative)
(defthm *-of-ceiling-same-linear-neg
  (implies (and (< j 0) ; unusual
                (rationalp i)
                (rationalp j))
           (<= (* j (ceiling i j)) i))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor))))

;; not quite subsumed by *-of-ceiling-same-linear-neg
(defthmd *-of-ceiling-same-linear-pos-neg
  (implies (and (<= j 0) ; unusual
                (<= 0 i)
                (rationalp i)
                (rationalp j))
           (<= (* j (ceiling i j)) i))
  :rule-classes :linear
  :hints (("Goal" :cases ((equal j 0))
           :in-theory (enable ceiling-in-terms-of-floor))))

;gen?
(defthm <-of-ceiling-arg1
  (implies (and (rationalp i)
                (integerp k)
                (rationalp j)
                (< 0 j))
           (equal (< k (ceiling i j))
                  (< (* j k) i)))
  :hints (("Goal" :use (my-floor-lower-bound
                        (:instance <-of-*-of-/-arg2-arg1
                                   (z k)
                                   (y i)
                                   (x j)))
           :cases ((< (* j k) i))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (ceiling-in-terms-of-floor)
                           (my-floor-lower-bound-alt
                            <-of-*-of-/-arg2-arg1
                            <-of-*-of-/-arg2-arg2
                            )))))

;; k is bigger than the ceiling if it at least the quotient plus 1
(defthm <-of-ceiling-arg2
  (implies (and (<= (+ 1 (/ i j)) k)
                (rationalp i)
                (integerp k)
                (rationalp j)
                (< 0 j))
           (< (ceiling i j) k))
  :hints (("Goal" :use ceiling-upper-bound
           :in-theory (disable ceiling-upper-bound))))

(defthm ceiling-of-*-same
  (implies (and (posp x)
                (integerp y))
           (equal (ceiling (* x y) x)
                  y))
  :hints (("Goal" :in-theory (enable ceiling))))

(defthm ceiling-when-multiple
  (implies (and (integerp (* (/ j) i))
                (posp j)
                (integerp i)
                )
           (equal (ceiling i j)
                  (/ i j)))
  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor-cases))))

(defthm ceiling-of-+-when-multiple
  (implies (and (integerp (* (/ j) x))
                (posp j)
                (integerp x)
                (integerp y))
           (equal (ceiling (+ x y) j)
                  (+ (/ x j) (ceiling y j))))
  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor-cases))))

(defthm equal-of-0-and-ceiling
  (implies (and (natp i)
                (posp j))
           (equal (equal 0 (ceiling i j))
                  (equal 0 i)))
  :hints (("Goal" :in-theory (enable ceiling))))

(defthm <-of-0-and-ceiling
  (implies (and (posp i)
                (posp j))
           (< 0 (ceiling i j)))
  :hints (("Goal" :in-theory (enable ceiling))))

(defthm ceiling-monotone
  (implies (and (<= i1 i2)
                (rationalp i1)
                (rationalp i2)
                (rationalp j)
                (< 0 j))
           (<= (ceiling i1 j) (ceiling i2 j)))
  :hints (("Goal" :use floor-weak-monotone
           :in-theory (e/d (ceiling-in-terms-of-floor
                            floor-when-multiple)
                           (floor-weak-monotone)))))

(defthm ceiling-upper-bound-when-<-constant-linear
  (implies (and (syntaxp (quotep j))
                (< i k) ; k is a free var
                (syntaxp (quotep k))
                (integerp k)
                (integerp i)
                (rationalp j)
                (< 0 j))
           ;; The term (ceiling (+ -1 k) j) should get computed:
           (<= (ceiling i j) (ceiling (+ -1 k) j)))
  :rule-classes ((:linear :trigger-terms ((ceiling i j))))
  :hints (("Goal" :use (:instance ceiling-monotone
                                  (i1 i) (i2 (+ -1 k)))
           :in-theory (disable ceiling-monotone))))

(defthm ceiling-of-*-and-*-cancel-arg2-arg2
  (equal (ceiling (* x z) (* y z))
         (if (equal (fix z) 0)
             0
           (ceiling x y)))
  :hints (("Goal" :in-theory (enable ceiling))))

(defthm <-of-ceiling-and-0
  (implies (and (rationalp i)
                (rationalp j))
           (equal (< (ceiling i j) 0)
                  (if (< 0 j)
                      (<= i (- j))
                    (and (< j 0)
                         (<= (- j) i)))))
  :hints (("Goal" :in-theory (enable ceiling))))
