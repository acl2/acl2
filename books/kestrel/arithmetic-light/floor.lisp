; A lightweight book about the built-in function floor.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
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
(local (include-book "../../meta/meta-plus-lessp"))

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
  (implies (syntaxp (not (equal j ''1)))
           (equal (floor i j)
                  (floor (/ i j) 1)))
  :hints (("Goal" :in-theory (enable floor))))

;rename params
(defthm floor-weak-monotone
  (implies (and (<= x1 x2)
                (rationalp x1)
                (rationalp x2)
                (rationalp y)
                (< 0 y) ;gen?
                )
           (<= (floor x1 y) (floor x2 y)))
  :hints (("Goal" :in-theory (e/d (floor <=-of-*-and-*-same-linear)
                                  (nonnegative-integer-quotient-lower-bound-linear2))
           :use ((:instance nonnegative-integer-quotient-lower-bound-linear2
                            (i (numerator (* x2 (/ y))))
                            (j (denominator (* x2 (/ y)))))
                 (:instance nonnegative-integer-quotient-lower-bound-linear2
                            (i (- (numerator (* x1 (/ y)))))
                            (j (denominator (* x1 (/ y)))))))))

(defthmd floor-when-multiple
  (implies (integerp (* i (/ j)))
           (equal (floor i j)
                  (/ i j))) :hints (("Goal" :in-theory (enable floor))))

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
  (implies (and (integerp n) ;move to conclusion
                (<= n (/ i j))
                (< (+ -1 (/ i j)) n)
                (< 0 j)
                (rationalp i)
                (rationalp j))
           (equal (equal (floor i j) n)
                  t))
  :hints (("Goal" :use (:instance floor-unique)
           :in-theory (disable floor-unique))))

;strengthen as we did for nniq?
;enable?
(defthmd my-floor-lower-bound ;floor-lower-bound is a theorem in rtl
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (< (+ -1 (/ i j)) (floor i j)))
  :hints (("Goal" :in-theory (enable floor))))

;; In this version, we have multiplied through by j.
(defthmd my-floor-lower-bound-alt
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (< (+ (- j) i) (* j (floor i j))))
  :rule-classes (:rewrite (:linear :trigger-terms ((* j (floor i j)))))
  :hints (("Goal"
           :use ((:instance my-floor-lower-bound)
                 (:instance <-of-*-and-*-cancel
                            (x1 (+ -1 (* i (/ j))))
                            (x2 (floor i j))
                            (y j)))
           :in-theory (disable my-floor-lower-bound
                               <-of-*-and-*-cancel))))

(defthmd my-floor-upper-bound ;floor-upper-bound is a theorem in rtl
  (implies (and (rationalp i)
                (rationalp j))
           (<= (floor i j) (/ i j)))
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-upper-bound-linear
  (implies (and (rationalp i)
                (rationalp j))
           ;; the phrasing of the * term matches our normal form
           (<= (floor i j) (* i (/ j))))
  :rule-classes ((:linear :trigger-terms ((floor i j))))
  :hints (("Goal" :in-theory (enable floor))))

;; In this version, we have multiplied through by j.
(defthmd my-floor-upper-bound-alt
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (<= (* j (floor i j)) i))
  :rule-classes (:rewrite (:linear :trigger-terms ((* j (floor i j)))))
  :hints (("Goal" :use ((:instance my-floor-upper-bound)
                        (:instance <-of-*-and-*-cancel
                                   (x2 (floor i j))
                                   (x1 (* i (/ j)))
                                   (y j)))
           :in-theory (disable my-floor-upper-bound
                               <-of-*-and-*-cancel))))

;; generalizing this is hard since even if j is not rational, the quotient may be.
(defthm floor-when-not-rationalp-arg1
  (implies (and (not (rationalp i))
                (rationalp j))
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
              :in-theory (e/d (mod) (FLOOR-UPPER-BOUND-LINEAR  <-of-*-and-*-cancel))
              :use ((:instance <-of-*-and-*-cancel (x1 (+ -1 (* I1 (/ J)) (* I2 (/ J)))) (x2 (+ (FLOOR I1 J) (FLOOR I2 J))) (y j))
                    (:instance FLOOR-upper-bound-linear (i i1) (j j))
                    (:instance FLOOR-upper-bound-linear (i i2) (j j))
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

;;compare to floor-of-+-when-mult-arg1 etc
(defthm cancel-floor-+-part-1
  (implies (and (equal i (/ x z))
                (integerp i)
                (rationalp y)
                (rationalp z))
           (equal (floor (+ x y) z)
                  (+ i (floor y z))))
  :hints (("Goal" :cases ((and (acl2-numberp y) (acl2-numberp x))
                          (and (acl2-numberp y) (not (acl2-numberp x)))
                          (and (not (acl2-numberp y)) (not (acl2-numberp x))))
           :in-theory (enable floor))))

(defthm cancel-floor-+-part-1-alt
  (implies (and (equal i (/ x z))
                (integerp i)
                (rationalp y)
                (rationalp z))
           (equal (floor (+ y x) z)
                  (+ i (floor y z))))
  :hints (("Goal" :use (:instance cancel-floor-+-part-1)
           :in-theory (disable cancel-floor-+-part-1))))
