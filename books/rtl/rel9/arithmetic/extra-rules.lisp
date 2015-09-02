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

;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

;this books contains rules which aren't used anywhere in lib/ or support/

(in-package "ACL2")

;(include-book "fp2")
;(local (include-book "even-odd"))
(local (include-book "basic")) ;yuck


(defthm exp+1-1
  (implies (and (integerp m)
                (integerp n)
                (<= n m))
           (<= (+ (expt 2 m) (expt 2 n))
               (expt 2 (1+ m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-weak-monotone)
			(:instance expt-split (r 2) (i 1) (j m))))))

(defthm exp+1
    (implies (and (integerp m)
		  (integerp n)
		  (<= n m))
	     (> (* (- 1 (expt 2 m)) (- 1 (expt 2 n)))
		(- 1 (expt 2 (1+ m)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable)
		  :use ((:instance exp+1-1)
                        ))))

(defthm exp+2-1
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m)
		  (<= m 0))
	     (<= (* (expt 2 m) (expt 2 n))
		 (expt 2 m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-weak-monotone (n (+ m n)))
			(:instance expt-split (r 2))))))

(defthm exp+2-2
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m)
		  (<= m 0))
	     (<= (+ (expt 2 m) (expt 2 n) (* (expt 2 m) (expt 2 n)))
		 (* 3 (expt 2 m))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable)
		  :use ((:instance expt-weak-monotone)
			(:instance exp+2-1)))))

(defthm exp+2-3
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m)
		  (<= m 0))
	     (< (+ (expt 2 m) (expt 2 n) (* (expt 2 m) (expt 2 n)))
		 (* 4 (expt 2 m))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable)
		  :use (
			(:instance exp+2-2)
			(:instance *-strongly-monotonic (x (expt 2 m)) (y 3) (y+ 4))))))

(defthm exp+2
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m)
		  (<= m 0))
	     (< (* (1+ (expt 2 m)) (1+ (expt 2 n)))
		(1+ (expt 2 (+ m 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exp+2-3)
			(:instance expt-split (r 2) (i 2) (j m))))))


(defthm exp-invert-1
    (implies (and (integerp n)
		  (<= n -1))
	     (<= (* (expt 2 n) (expt 2 (1+ n)))
		 (expt 2 n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-weak-monotone (n (1+ n)) (m 0))
			(:instance *-weakly-monotonic (x (expt 2 n)) (y (expt 2 (1+ n))) (y+ 1))))))

(defthm exp-invert-2
    (implies (and (integerp n)
		  (<= n -1))
	     (>= (* (- 1 (expt 2 n))
		    (1+ (expt 2 (1+ n))))
		 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-split (r 2) (i n) (j 1))
			(:instance exp-invert-1)))))

(defthm cancel-x
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (<= 1 (* x y)))
	     (<= (/ x) y))
  :rule-classes ())

(defthm exp-invert
    (implies (and (integerp n)
		  (<= n -1))
	     (<= (/ (- 1 (expt 2 n)))
		 (1+ (expt 2 (1+ n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance cancel-x (x (- 1 (expt 2 n))) (y (1+ (expt 2 (1+ n)))))
			(:instance exp-invert-1)
			(:instance expt-weak-monotone (m -1))))))


(local
 (defthm sq-sq-1
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (<= (* (* a b) (* a b))
		 (* (expt 2 (- (* 2 n) 2)) (* p p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-doubly-monotonic
				   (x (* a a)) (a (* b b))
				   (y p) (b (* (expt 2 (- (* 2 n) 2)) p))))))))
;not exported anywhere!
;rephrase?
(defthm sqrt<=
    (implies (and (rationalp x)
		  (rationalp a)
		  (>= a 0)
		  (<= (* x x) (* a a)))
	     (<= x a))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-strongly-monotonic (y a) (y+ x))
			(:instance *-strongly-monotonic (x a) (y a) (y+ x))))))
(local
 (defthm sq-sq-2
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (<= (* (* (expt 2 (1- n)) p) (* (expt 2 (1- n)) p))
		 (* (expt 2 (- (* 2 n) 2)) (* p p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-split (r 2) (i (1- n)) (j (1- n))))))))


(local
 (defthm sq-sq-3
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (>= (* (expt 2 (1- n)) p) 0))
  :rule-classes ()))

(local
 (defthm sq-sq-4
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (<= (* a b)
		 (* (expt 2 (1- n)) p)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable a15)
           :use ((:instance sq-sq-1)
			(:instance sq-sq-3)
			(:instance sqrt<= (x (* a b)) (a (* (expt 2 (1- n)) p)))
			(:instance sq-sq-2))))))

(local
 (defthm sq-sq-5
    (implies (and (rationalp x)
		  (rationalp p)
		  (integerp n)
		  (<= x (* (expt 2 (1- n)) p)))
	     (<= (* 2 x) (* (expt 2 n) p)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable *-weakly-monotonic)
		  :use ((:instance expt-split (r 2) (i (1- n)) (j 1))
			(:instance *-weakly-monotonic (x 2) (y x) (y+ (* (expt 2 (1- n)) p))))))))


(local
 (defthm sq-sq-6
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (<= (* 2 a b)
		 (* (expt 2 n) p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sq-sq-4)
			(:instance sq-sq-5 (x (* a b))))))))

(local
 (defthm sq-sq-7
    (implies (and (rationalp a)
		  (rationalp b))
	     (>= (* (- a b) (- a b))
		 (- (* a a) (* 2 a b))))
  :rule-classes ()))

(local
 (defthm sq-sq-8
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (>= (* (- a b) (- a b))
		 (- (* (- 1 (expt 2 n)) p)
		    (* (expt 2 n) p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sq-sq-6)
			(:instance sq-sq-7))))))

(local
 (defthm sq-sq-9
    (implies (and (rationalp p)
		  (integerp n))
	     (= (- (* (- 1 (expt 2 n)) p)
		   (* (expt 2 n) p))
		(* (- 1 (expt 2 (1+ n))) p)))
  :rule-classes ()))

;where is this used?
;doesn't seem to be used anywhere or exported in lib?
(defthm sq-sq
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (>= (* (- a b) (- a b))
		 (* (- 1 (expt 2 (1+ n))) p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sq-sq-8)
			(:instance sq-sq-9)))))

;kill some of these 4 abs lemmas (they are from divsqrt and don't seem to be
;needed in support/ or exported in lib/) ?

(defthm abs-+
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z))
           (<= (abs (- x y))
               (+ (abs (- x z))
                  (abs (- y z)))))
  :rule-classes ())

(defthm abs->=
  (implies (and (rationalp x)
                (rationalp y))
           (>= (abs (- y x)) (- (abs x) (abs y))))
  :rule-classes ())

;kill?
(local
 (defthm abs+
   (implies (and (rationalp x)
                 (rationalp y))
            (<= (abs (+ x y))
                (+ (abs x) (abs y))))
   :rule-classes ()
   :hints (("goal" :in-theory (enable abs)))))

(defthm abs-
  (implies (and (rationalp x)
                (rationalp y))
           (<= (abs (- x y))
               (+ (abs x) (abs y))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable abs))))
