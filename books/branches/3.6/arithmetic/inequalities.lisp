; ACL2 books on arithmetic
; Copyright (C) 1997  Computational Logic, Inc.

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:
; Matt Kaufmann, Bishop Brock, and John Cowles, with help from Art Flatau
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

;; Extended by Ruben Gamboa to include the reals when ACL2(r) is used.  This is
;; nothing more than a trivial change of rationalp to realp.

(in-package "ACL2")

(include-book "equalities")

; ??? I'm not convinced we should be apply FC to REAL/RATIONALP hypotheses,
; but for now I'll go ahead and do so at times.

(local
 (defthm iff-equal
   (implies (and (iff x y)
                 (booleanp x)
                 (booleanp y))
            (equal x y))
   :rule-classes nil))

(defthm /-preserves-positive
  (implies (real/rationalp x)
	   (iff (< 0 (/ x))
                (< 0 x)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (fc (real/rationalp x))
                           (equal (< 0 (/ x))
                                  (< 0 x))))))

(defthm /-preserves-negative
  (implies (real/rationalp x)
	   (iff (< (/ x) 0)
                (< x 0)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (fc (real/rationalp x))
                           (equal (< (/ x) 0)
                                  (< x 0))))))

; The following two lemmas could be extended by adding two more such
; lemmas, i.e. for (< (* x z) (* z y)) and (< (* z x) (* y z)), but
; rather than incur that overhead here and in any other such cases
; (and besides, how about for example (< (* x z a) (* z a y))?), I'll
; wait for metalemmas to handle such things.

(defthm <-*-right-cancel
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y))
                (fc (real/rationalp z)))
           (iff (< (* x z) (* y z))
                (cond
                 ((< 0 z)
                  (< x y))
                 ((equal z 0)
                  nil)
                 (t (< y x)))))
  :hints (("Goal" :use
           ((:instance (:theorem
                        (implies (and (real/rationalp a)
                                      (< 0 a)
                                      (real/rationalp b)
                                      (< 0 b))
                                 (< 0 (* a b))))
                       (a (abs (- y x)))
                       (b (abs z)))))))

(defthm <-*-left-cancel
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y))
                (fc (real/rationalp z)))
           (iff (< (* z x) (* z y))
                (cond
                 ((< 0 z)
                  (< x y))
                 ((equal z 0)
                  nil)
                 (t (< y x))))))

(defthm /-inverts-order-1
  (implies (and (< 0 x)
                (< x y)
		(fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (< (/ y) (/ x)))
  :hints (("Goal" :use
           ((:instance <-*-right-cancel
                       (z (/ (* x y))))))))

; ??? Interestingly, the prover fails to prove the following corollary.

#|
(defthm <-0-minus
  (iff (< 0 (- x))
       (< x 0))
  :rule-classes
  ((:rewrite :corollary
             (equal (< 0 (- x))
                    (< x 0)))))
|#

(defthm <-0-minus
  (equal (< 0 (- x))
         (< x 0))
  :hints (("Goal" :use
           ((:instance
             iff-equal
             (x (< 0 (- x)))
             (y (< x 0)))))))

(defthm <-*-0
  (implies (and (real/rationalp x)
                (real/rationalp y))
           (iff (< (* x y) 0)
                (and (not (equal x 0))
                     (not (equal y 0))
                     (iff (< x 0)
                          (< 0 y)))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (fc (real/rationalp x))
                           (fc (real/rationalp y)))
                      (equal (< (* x y) 0)
                             (and (not (equal x 0))
                                  (not (equal y 0))
                                  (iff (< x 0)
                                       (< 0 y))))))))

(defthm 0-<-*
  (implies (and (real/rationalp x)
                (real/rationalp y))
           (iff (< 0 (* x y))
                (and (not (equal x 0))
                     (not (equal y 0))
                     (iff (< 0 x)
                          (< 0 y)))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (fc (real/rationalp x))
                           (fc (real/rationalp y)))
                      (equal (< 0 (* x y))
                             (and (not (equal x 0))
                                  (not (equal y 0))
                                  (iff (< 0 x)
                                       (< 0 y))))))))

(defthm /-inverts-order-2
  (implies (and (< y 0)
		(< x y)
		(fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (< (/ y) (/ x)))
  :hints (("Goal" :use
           ((:instance <-*-right-cancel
                       (z (/ (* x y)))))
           :in-theory (disable <-*-right-cancel))))

(defthm /-inverts-weak-order
  (implies (and (< 0 x)
		(<= x y)
		(fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (not (< (/ x) (/ y))))
  :hints (("Goal" :use /-inverts-order-1
           :in-theory (disable /-inverts-order-1))))

(defthm <-unary-/-negative-left
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0))
	   (iff (< (/ x) y)
                (< (* x y) 1)))
  :hints (("Goal" :use
           ((:instance <-*-left-cancel
                       (z x)
                       (x (/ x))
                       (y y)))
           :in-theory (set-difference-theories
                       (enable Uniqueness-of-*-inverses)
                       '(equal-/))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (< x 0)
                           (fc (real/rationalp x))
                           (fc (real/rationalp y)))
                      (equal (< (/ x) y)
                             (< (* x y) 1))))))

(defthm <-unary-/-negative-right
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0))
	   (iff (< y (/ x))
                (< 1 (* x y))))
  :hints (("Goal" :use
           ((:instance <-*-right-cancel
                       (z x)
                       (x (/ x))
                       (y y)))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (< x 0)
                           (fc (real/rationalp x))
                           (fc (real/rationalp y)))
                      (equal (< y (/ x))
                             (< 1 (* x y)))))))

(defthm <-unary-/-positive-left
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x))
	   (iff (< (/ x) y)
                (< 1 (* x y))))
  :hints (("Goal" :use
           ((:instance <-*-left-cancel
                       (z x)
                       (x (/ x))
                       (y y)))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (< 0 x)
                           (fc (real/rationalp x))
                           (fc (real/rationalp y)))
                      (equal (< (/ x) y)
                             (< 1 (* x y)))))))

(defthm <-unary-/-positive-right
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x))
	   (iff (< y (/ x))
                (< (* x y) 1)))
  :hints (("Goal" :use
           ((:instance <-*-left-cancel
                       (z x)
                       (x (/ x))
                       (y y)))
           :in-theory (union-theories
                       '(Uniqueness-of-*-inverses)
                       (disable <-unary-/-positive-left
                                equal-/
                                <-*-left-cancel))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (< 0 x)
                           (fc (real/rationalp x))
                           (fc (real/rationalp y)))
                      (equal (< y (/ x))
                             (< (* x y) 1))))))

(defthm <-minus-zero
  (equal (< (- x) 0)
         (< 0 x))
  :hints (("Goal" :use
           ((:instance iff-equal
                       (x (< (- x) 0))
                       (y (< 0 x)))))))

(defthm <-*-/-right
  (implies (and (< 0 y)
                (fc (real/rationalp a))
                (fc (real/rationalp x))
                (fc (real/rationalp y)))
           (equal (< a (* x (/ y)))
                  (< (* a y) x)))
  :hints (("Goal" :use
           ((:instance
             <-*-right-cancel
             (x a)
             (y (* x (/ y)))
             (z y))))))

(defthm <-*-/-right-commuted
  (implies (and (< 0 y)
                (fc (real/rationalp x))
                (fc (real/rationalp y))
                (fc (real/rationalp a)))
           (equal (< x (* (/ y) a))
                  (< (* x y) a))))

(defthm <-*-/-left
  (implies (and (< 0 y)
                (fc (real/rationalp x))
                (fc (real/rationalp y))
                (fc (real/rationalp a)))
           (equal (< (* x (/ y)) a)
                  (< x (* a y))))
  :hints (("Goal" :use
           ((:instance
             <-*-right-cancel
             (y a)
             (x (* x (/ y)))
             (z y))))))

(defthm <-*-/-left-commuted
  (implies (and (< 0 y)
                (fc (real/rationalp x))
                (fc (real/rationalp y))
                (fc (real/rationalp a)))
           (equal (< (* (/ y) x) a)
                  (< x (* y a)))))

(encapsulate
 ()

 (local
  (defthm *-preserves->=-1
    (implies (and (real/rationalp x1)
                  (real/rationalp x2)
                  (real/rationalp y1)
                  (>= x1 x2)
                  (>= x2 0)
                  (>= y1 0))
             (>= (* x1 y1) (* x2 y1)))
    :rule-classes nil))

 (local
  (defthm *-preserves->=-2
    (implies (and (real/rationalp x2)
                  (real/rationalp y1)
                  (real/rationalp y2)
                  (>= y1 y2)
                  (>= x2 0)
                  (>= y2 0))
             (>= (* x2 y1) (* x2 y2)))
    :rule-classes nil))

 (defthm *-preserves->=-for-nonnegatives
   (implies (and (>= x1 x2)
                 (>= y1 y2)
                 (>= x2 0)
                 (>= y2 0)
                 (fc (real/rationalp x1))
                 (fc (real/rationalp x2))
                 (fc (real/rationalp y1))
                 (fc (real/rationalp y2)))
            (>= (* x1 y1) (* x2 y2)))
   :hints (("Goal" :use
            (*-preserves->=-1 *-preserves->=-2)
            :in-theory (disable <-*-left-cancel <-*-right-cancel))))

 )

#| Already covered by EQUAL-*-/-2 from rationals-equalities.lisp
(defthm equal-binary-quotient
  (implies (and (fc (real/rationalp x))
                (fc (real/rationalp y))
                (fc (real/rationalp z))
                (fc (not (equal z 0))))
           (equal (equal x (/ y z))
                  (equal (* x z) y)))
  :hints (("Goal" :use
           ((:instance
             (:theorem
              (implies (and (real/rationalp x)
                            (real/rationalp y)
                            (real/rationalp z)
                            (not (equal z 0))
                            (equal x y))
                       (equal (* x z) (* y z))))
             (x (* x z))
             (y y)
             (z (/ z)))))))
|#

(encapsulate
 ()

 (local
  (defthm *-preserves->-1
    (implies (and (real/rationalp x1)
                  (real/rationalp x2)
                  (real/rationalp y1)
                  (> x1 x2)
                  (>= x2 0)
                  (> y1 0))
             (>= (* x1 y1) (* x2 y1)))
    :rule-classes nil))

 (local
  (defthm *-preserves->-2
    (implies (and (real/rationalp x2)
                  (real/rationalp y1)
                  (real/rationalp y2)
                  (>= y1 y2)
                  (>= x2 0)
                  (>= y2 0))
             (>= (* x2 y1) (* x2 y2)))
    :rule-classes nil))


 (defthm *-preserves->-for-nonnegatives-1
   (implies (and (> x1 x2)
                 (>= y1 y2)
                 (>= x2 0)
                 (> y2 0)
                 (fc (real/rationalp x1))
                 (fc (real/rationalp x2))
                 (fc (real/rationalp y1))
                 (fc (real/rationalp y2)))
            (> (* x1 y1) (* x2 y2)))
   :hints (("Goal" :use
            (*-preserves->-1 *-preserves->-2)
            :in-theory (disable <-*-left-cancel <-*-right-cancel
                                *-preserves->=-for-nonnegatives))))

 )

(encapsulate
 ()

 (defthm x*y>1-positive-lemma
   (implies
    (and (> x i)
         (> y j)
         (real/rationalp i)
         (real/rationalp j)
         (< 0 i)
         (< 0 j)
         (fc (real/rationalp x))
         (fc (real/rationalp y)))
    (> (* x y) (* i j)))
   :hints
   (("Goal"
     :use ((:instance
            0-<-*
            (x (- x i))
            (y (- y j)))))))

 (defthm x*y>1-positive
   (implies
    (and (> x 1)
         (> y 1)
         (fc (real/rationalp x))
         (fc (real/rationalp y)))
    (> (* x y) 1))
   :rule-classes (:linear :rewrite)
   :hints
   (("Goal" :use
     ((:instance x*y>1-positive-lemma
                 (i 1) (j 1))))))
 )

(defthm <-*-x-y-y
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (equal (< (* x y) y)
		  (cond
                   ((equal y 0)
                    nil)
                   ((< 0 y)
                    (< x 1))
                   (t
                    (< 1 x)))))
  :hints (("Goal" :use
           ((:instance <-*-right-cancel
                       (z y)
                       (x x)
                       (y 1))))))

(defthm <-*-y-x-y
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (equal (< (* y x) y)
		  (cond
                   ((equal y 0)
                    nil)
                   ((< 0 y)
                    (< x 1))
                   (t
                    (< 1 x))))))

(defthm <-y-*-x-y
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (equal (< y (* x y))
		  (cond
                   ((equal y 0)
                    nil)
                   ((< 0 y)
                    (< 1 x))
                   (t
                    (< x 1)))))
  :hints (("Goal" :use
           ((:instance <-*-right-cancel
                       (z y)
                       (x 1)
                       (y x))))))

(defthm <-y-*-y-x
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (equal (< y (* y x))
		  (cond
                   ((equal y 0)
                    nil)
                   ((< 0 y)
                    (< 1 x))
                   (t
                    (< x 1))))))

(defthm <-0-+-negative-1
  (equal (< 0 (+ (- y) x))
         (< y x))
  :hints (("Goal" :use
           (:instance iff-equal
                      (x (< 0 (+ (- y) x)))
                      (y (< y x))))))

(defthm <-0-+-negative-2
  (equal (< 0 (+ x (- y)))
         (< y x))
  :hints (("Goal" :use
           (:instance iff-equal
                      (x (< 0 (+ x (- y))))
                      (y (< y x))))))

(defthm <-+-negative-0-1
  (equal (< (+ (- y) x) 0)
         (< x y))
  :hints (("Goal" :use
           (:instance iff-equal
                      (x (< (+ (- y) x) 0))
                      (y (< x y))))))

(defthm <-+-negative-0-2
  (equal (< (+ x (- y)) 0)
         (< x y))
  :hints (("Goal" :use
           (:instance iff-equal
                      (x (< (+ x (- y)) 0))
                      (y (< x y))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Expt
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm expt->-1
  (implies
   (and (< 1 r)
        (< 0 i)
	(fc (real/rationalp r))
	(fc (integerp i)))
   (< 1 (expt r i)))
  :rule-classes :linear)

(encapsulate
 ()

 (local
  (defun
    Math-induction-start-at-k ( k n )
    (declare (xargs :guard (and (integerp k)
                                (integerp n)
                                (not (< n k)))
                    :measure (if (and (integerp k)
                                      (integerp n)
                                      (< k n))
                                 (- n k)
                               0)))
    (if (and (integerp k)
             (integerp n)
             (< k n))
        (Math-induction-start-at-k k (+ -1 n))
      t)))

 (local
  (defthm hack
    (implies (and (< (* x y) z)
                  (real/rationalp x)
                  (real/rationalp y)
                  (real/rationalp z)
                  (< 1 x)
                  (< 0 y))
             (< y z))
    :hints
    (("Goal"
      :use
      ((:instance
        (:theorem
         (implies (and (real/rationalp x)
                       (real/rationalp y)
                       (real/rationalp z)
                       (< 0 y)
                       ;; w = (* x1 y)
                       (real/rationalp w)
                       (< 0 w)
                       (< (+ y w) z))
                  (< y z)))
        (w (* (- x 1) y))))))))
        
 (defthm expt-is-increasing-for-base>1
   (implies (and (< 1 r)
                 (< i j)
                 (fc (real/rationalp r))
                 (fc (integerp i))
                 (fc (integerp j)))
            (< (expt r i)
               (expt r j)))
   :rule-classes (:rewrite :linear)
   :hints (("Goal"
            :in-theory (enable Exponents-add-unrestricted)
            :induct (Math-induction-start-at-k (+ 1 i) j))))
 )

(defthm Expt-is-decreasing-for-pos-base<1
  (implies (and (< 0 r)
                (< r 1)
                (< i j)
                (fc (real/rationalp r))
                (fc (integerp i))
                (fc (integerp j)))
           (< (expt r j)
              (expt r i)))
  :hints (("Goal" :use
           ((:instance
             expt-is-increasing-for-base>1
             (r (/ r)))))))

(defthm Expt-is-weakly-increasing-for-base>1
  (implies (and (< 1 r)
                (<= i j)
                (fc (real/rationalp r))
                (fc (integerp i))
                (fc (integerp j)))
           (<= (expt r i)
               (expt r j)))
  :hints (("Goal" :use expt-is-increasing-for-base>1
           :in-theory (disable  expt-is-increasing-for-base>1))))

(defthm Expt-is-weakly-decreasing-for-pos-base<1
  (implies (and (< 0 r)
                (< r 1)
                (<= i j)
                (fc (real/rationalp r))
                (fc (integerp i))
                (fc (integerp j)))
           (<= (expt r j)
               (expt r i)))
  :hints (("Goal" :use expt-is-decreasing-for-pos-base<1
           :in-theory (disable expt-is-decreasing-for-pos-base<1))))

