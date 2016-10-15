; Copyright (C) 2015 Harsh Raju Chamarthi and Northeastern University
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; The following proof shows that the cantor pairing function, hl-nat-combine,
;; is bijective. The crux of the proof is an explicit definition of the inverse
;; of the cantor pairing function.
;; - harshrc [2014-12-27 Sat] -- adapted from proof dating May 2010.
;; [2015-1-3] Added sum-inverse bounds to fill gap in given proof (pointed by Grant Passmore).

(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

; The cantor pairing function uses n*(n+1)/2, which is the sum of numbers upto n.
; Rather than working with *,/ arith ops, I prefer +, 1- and recursion.
(defun sum (n)
  "find sum of first n numbers"
  (if (zp n)
      0
    (+ (nfix n) (sum (- n 1)))))

(defthm sum-natp
  (implies (natp n)
           (and (integerp (sum n))
                (>= (sum n) 0)))
  :rule-classes (:type-prescription :rewrite))

(defthm sum-bound
  (implies (natp n)
           (>= (sum n) n))
  :rule-classes (:linear :rewrite))

; If (sum n) = M, then (sum-inverse M M) = n
(defun sum-inverse (M x)
  "return greatest number n <= x such that (sum n) <= M"
  (if (zp x)
      0
    (if (>= M (sum x))
        x
      (sum-inverse M (1- x)))))


;(encapsulate ;
; nil
 (local (include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system))

;explicit induction hint used below
 (local
  (defun sum-inverse-ind-hint (n y i)
    (declare (xargs :measure (llist n y)
                    :well-founded-relation l<))
    (if (or (zp n) (zp y))
        i
      (if (< n (sum y))
          (sum-inverse-ind-hint n (1- y) i)
        (if (equal n (sum y))
            y
          (sum-inverse-ind-hint (1- n) y (1- i))))))
  )

 (local
  (defthm sum-inverse-is-inverse-of-sum-helper
    (implies (and (natp y)
                  (natp p)
                  (< (sum y) (sum (+ 1 p)))
                  (<= p y))
             (equal (equal y p) t)))
  )

 (local
  (defthm sum-inverse-is-inverse-of-sum
    (implies (and (natp i)
                  (natp y)
                  (natp p)
                  (<= p y)
                  (<= i p)
                  (equal n (+ i (sum p))))
             (equal (sum-inverse n y) p))
    :hints (("Goal" :induct (sum-inverse-ind-hint n y i))))
  )

 (defthm sum-inverse-sum-corollary
   (implies (and (natp i)
                 (natp p)
                 (<= i p))
            (equal (sum-inverse (+ i (sum p)) (+ i (sum p)))
                   p)))



 (defthm sum-sum-inverse-bound1
  (implies (and (natp n)
                (natp y)
                (>= y n))
           (<= (sum (sum-inverse n y)) n))
  :hints (("Goal" :induct (sum-inverse-ind-hint n y i)))
  :rule-classes (:linear :rewrite))

 (defthm sum-sum-inverse-bound2
  (implies (and (natp n)
                (natp y)
                (>= (sum y) n)
                )
           (>= (sum (sum-inverse n y)) (- n (sum-inverse n y))))
  :hints (("Goal" :induct (sum-inverse n y))
          ("Subgoal *1/3" :cases ((> (sum (- y 1)) n))))
  :rule-classes (:linear :rewrite))

 ;)


; Main Proof

; (cantor-pairing a b) = (+ b (/ (* (+ a b) (+ a b 1)) 2))
(defun cantor-pairing (a b)
    (+ b (sum (+ a b))))

; the inverse of above -- this is the crux of the proof
(defun cantor-pairing-inverse (n)
  (if (equal 0 n)
    (list 0 0)
    (let* ((j (- n (sum (sum-inverse n n))))
           (i  (- (sum-inverse n n) j)))
      (list i j))))



; Cantor pairing is surjective
; To show: \forall n \exists a,b \in N s.t. (cantor-pairing a b) = n
; = { Skolemization }
; \forall n (cantor-pairing (f1 n) (f2 n)) = n
; Since ACL2 is first-order, we manually find such f1 and f2.
(defthm cantor-pairing-onto
  (let ((a (car (cantor-pairing-inverse n)))
        (b (cadr (cantor-pairing-inverse n))))
    (implies (natp n)
             (and (natp a)
                  (natp b)
                  (equal (cantor-pairing a b) n))))
  :rule-classes nil)


(defthm cantor-pairing-inverse-is-an-inverse
  (implies (and (natp a)
                (natp b))
           (equal (cantor-pairing-inverse (cantor-pairing a b))
                  (list a b))))

; Cantor pairing is injective
(defthm cantor-pairing-one-one
  (implies (and (natp a1)
                (natp b1)
                (natp a2)
                (natp b2)
                (equal (cantor-pairing a1 b1) (cantor-pairing a2 b2)))
           (equal (list a1 b1) (list a2 b2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable cantor-pairing cantor-pairing-inverse)
                  :use ((:instance cantor-pairing-inverse-is-an-inverse (a a1) (b b1))
                        (:instance cantor-pairing-inverse-is-an-inverse (a a2) (b b2))))))#|ACL2s-ToDo-Line|#







#|
; The following just shows that cantor-pairing is the same function as hl-nat-combine
(local (include-book "system/hl-addr-combine" :dir :system))

(local
 (defthm sum-closed-form
   (implies (natp n)
            (equal (sum n)
                   (/ (* n (+ n 1)) 2))))
;:hints (("Goal" :in-theory (disable FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))))
 )

(local
 (defthm hl-nat-combine-is-same-as-cantor-pairing
   (implies (and (natp a)
                 (natp b))
            (equal (hl-nat-combine a b)
                   (cantor-pairing a b)))
   :hints (("Goal" :in-theory (e/d (hl-nat-combine) (sum)))))
 )
|#

