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

;see floor-proofs for all proofs (and todos?)

(local (include-book "floor-proofs"))

;;
;; Behavior of floor when its guards are violated
;;

;this looks like it might loop! add syntaxp hyp that j isn't 1?
(defthm floor-with-i-not-rational
  (implies (not (rationalp i))
           (equal (floor i j)
                  (if (and (complex-rationalp i) (complex-rationalp j) (rationalp (/ i j)))
                      (floor (/ i j) 1) ;yuck, defines floor in terms of itself
                    0))))

(defthm floor-with-j-not-rational
  (implies (not (rationalp j))
           (equal (floor i j)
                  (if (and (complex-rationalp i) (complex-rationalp j) (rationalp (/ i j)))
                      (floor (/ i j) 1) ;yuck, defines floor in terms of itself
                    0))))

;special case of floor-with-i-not-rational but contains no if
(defthm floor-with-i-not-rational-but-j-rational
  (implies (and (not (rationalp i))
                (rationalp j)
                )
           (equal (floor i j)
                  0)))

;special case of floor-with-j-not-rational but contains no if
(defthm floor-with-j-not-rational-but-i-rational
  (implies (and (not (rationalp i))
                (rationalp j)
                )
           (equal (floor i j)
                  0)))

;;
;; type prescriptions
;;

; (thm (integerp (floor i j)))) goes through

;to gen this, prove that the quotient of 2 positive complexes is either complex or positive. (that's a type!)
;I have a marvelous proof of that fact, but this buffer is too small to contain it.
;(Actually, it's in my green notebook.)

(defthm floor-non-negative-integerp-type-prescription
  (implies (and (<= 0 i)
                (<= 0 j)
                (case-split (not (complex-rationalp j))) ;I think I can drop this hyp, but it will take some work.
                )
           (and (<= 0 (floor i j))
                (integerp (floor i j))))
  :rule-classes (:type-prescription))



;(floor #C(-4 -3) #C(4 3))= -1

(defthm floor-non-negative
  (implies (and (<= 0 i)
                (<= 0 j)
                (case-split (not (complex-rationalp i)));(case-split (rationalp i));drop?
                )
           (<= 0 (floor i j))))





(defthm floor-compare-to-zero
  (implies (and (case-split (rationalp i))
                (case-split (rationalp j)))
           (equal (< (floor i j) 0)
                  (or (and (< i 0) (< 0 j))
                      (and (< 0 i) (< j 0))
                      ))))

(defthm floor-of-non-acl2-number
  (implies (not (acl2-numberp i))
           (and (equal (floor i j)
                       0)
                (equal (floor j i)
                       0))))

;linear? how should it be phrased?
(defthm floor-upper-bound
  (implies (and (case-split (rationalp i))
                (case-split (rationalp j))
                )
           (<= (floor i j) (/ i j)))
  :rule-classes (:rewrite (:linear :trigger-terms ((floor i j)))))



(defthm floor-equal-i-over-j-rewrite
  (implies (and (case-split (not (equal j 0)))
                (case-split (rationalp i))
                (case-split (rationalp j))
                )
           (equal (equal (* j (floor i j)) i)
                  (integerp (* i (/ j))))))
;move
(defthm dumb
  (equal (< x x)
         nil))

(defthm floor-with-j-zero
  (equal (floor i 0)
         0))

(defthm floor-with-i-zero
  (equal (floor 0 j)
         0))


;(defthm floor-greater-than-zero-rewrite
 ; (equal (< 0 (floor i j))
  ;       (

(defthm floor-upper-bound-2
  (implies (and (<= 0 j)
                (case-split (rationalp i))
                (case-split (rationalp j))
                (case-split (not (equal j 0)))
                )
           (<= (* j (floor i j)) i))
  :rule-classes (:rewrite (:linear :trigger-terms ((floor i j)))))


(defthm floor-upper-bound-3
  (implies (and (<= j 0) ;rarely true
                (case-split (rationalp i))
                (case-split (rationalp j))
                (case-split (not (equal j 0)))
                )
           (<= i (* j (floor i j))))
  :rule-classes (:rewrite (:linear :trigger-terms ((floor i j)))))


(defthm floor-lower-bound
  (implies (and (case-split (rationalp i))
                (case-split (rationalp j))
                )
           (< (+ -1 (* i (/ j))) (floor i j)))
  :rule-classes (:rewrite (:linear :trigger-terms ((floor i j)))))

;a bit odd
(defthm floor-when-arg-quotient-isnt-rational
  (implies (not (rationalp (* i (/ j))))
           (equal (floor i j) 0)))

(defthm floor-of-non-rational-by-one
  (implies (not (rationalp i))
           (equal (floor i 1)
                  0)))

(defthm floor-of-rational-and-complex
  (implies (and (rationalp i)
                (not (rationalp j))
                (case-split (acl2-numberp j)))
           (and (equal (floor i j)
                       0)
                (equal (floor j i)
                       0))))

#|
(defthm floor-of-two-complexes
  (implies (and (complex-rationalp i)
                (complex-rationalp j))
           (equal (floor i j)
                  (if (rationalp (/ i j))
                      (floor (/ i j) 1)
                    0)))
  :hints (("Goal" :in-theory (enable floor))))
|#




#|
(local
 (defthm floor*2
   (implies (integerp x)
            (equal (floor (* 2 x) 2) x))
   :hints (("Goal" :in-theory (enable floor)))
   ))
|#

(defthm floor-of-integer-by-1
  (implies (integerp i)
           (equal (floor i 1)
                  i))
  :hints (("Goal" :in-theory (enable  floor))))
