; A lightweight book about the built-in function ceiling.
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "integerp"))
(local (include-book "times"))
(local (include-book "times-and-divides"))
(local (include-book "floor"))
(local (include-book "numerator"))
(local (include-book "denominator"))
(local (include-book "minus"))

(in-theory (disable ceiling))

(local (in-theory (disable floor)))

;move
(local
 (defthm integerp-of-*-of---arg2
   (equal (integerp (* x (- y)))
          (integerp (* x y)))
   :hints (("Goal" :use (:instance integerp-of-- (x (* x y)))
            :in-theory (disable integerp-of--)))))

(defthmd ceiling-of-0
  (equal (ceiling 0 j)
         0)
  :hints (("Goal" :in-theory (enable ceiling floor))))

(defthmd ceiling-in-terms-of-floor
  (equal (ceiling i j)
         (- (floor (- i) j)))
  :hints (("Goal" :cases ((and (rationalp i) (rationalp j)))
           :in-theory (enable ceiling floor))))

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

(defthm ceiling-upper-bound
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (< (ceiling i j) (+ 1 (/ i j))))
  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor))))

(defthm ceiling-lower-bound
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (<= (/ i j) (ceiling i j)))
  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor))))

(defthm ceiling-lower-bound-linear
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (<= (/ i j) (ceiling i j)))
  :rule-classes ((:linear :trigger-terms ((ceiling i j)))))

;gen?
(defthm <-of-ceiling-arg1
  (implies (and (rationalp i)
                (integerp k)
                (rationalp j)
                (< 0 j))
           (equal (< k (ceiling i j))
                  (< (* j k) i)))
  :hints (("Goal" :use ((:instance my-floor-lower-bound)
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
                            <-*-/-left-with-addend)))))

;; k is bigger than the ceiling if it at least the quotient plus 1
(defthm <-of-ceiling-arg2
  (implies (and (<= (+ 1 (/ i j)) k)
                (rationalp i)
                (integerp k)
                (rationalp j)
                (< 0 j))
           (< (ceiling i j) k))
  :hints (("Goal" :use (:instance ceiling-upper-bound)
           :in-theory (disable ceiling-upper-bound
                               <-*-/-left-with-addend-alt))))

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
