; Reflexive Tail Recursive book
; Copyright (C) 2004 John R. Cowles, University of Wyoming

; This program is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public License as
; published by the Free Software Foundation; either version 2 of
; the License, or (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free
; Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139,
; USA.

; Written by: John R. Cowles
; email:      cowles@uwyo.edu
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071 U.S.A.

#|
(certify-book "knuth")
|#
(in-package "ACL2")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Develop a small, but useful, theory of iterated applications
;   of a function with a single input argument.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Introduce a new function f1 of one argument with no constraints.

(defstub
  f1 (*) => *)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Recursively define what it means to iterate applications of f1.

(defun
  f1^n (x n)
  (if (zp n)
      x
      (f1^n (f1 x)(- n 1))))

(defthm
  f1^n=f1
  (equal (f1^n x 1)
	 (f1 x))
  :hints (("Goal"
	   :expand (f1^n x 1))))

(defthm
  compose-f1^n
  (equal (f1^n (f1^n x i) j)
	 (f1^n x (+ (nfix i)
		    (nfix j)))))

(defthm
  f1-f1^n
  (equal (f1 (f1^n x i))
	 (f1^n (f1 x) i)))

(defthm
  +1-1
  (equal (+ -1 +1 x) (fix x)))

(defthm
  f1-f1^n-a
  (implies (and (integerp i)
		(>= i 0))
	   (equal (f1 (f1^n x i))
		  (f1^n x (+ 1 i)))))

; End theory of iterated applications of a function
; with a single input argument.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Develop a theory of iterated applications of a function
; defined by tail recursion. Make three additional assumtions.

(encapsulate
 (((test1 *) => *)
  ((base1 *) => *)
  ((step1 *) => *)
  ((step1^n * *) => *)
  ((nbr-step1s-to-test1 *) => *))

 (local
  (defun test1 (x)
    (<= (ifix x) 0)))

 (local
  (defun base1 (x)
    (+ (ifix x) 1)))

 (local
  (defun step1 (x)
    (- (ifix x) 1)))

 (local
  (defun step1^n (x n)
    (if (zp n)
	x
        (step1^n (step1 x)(- n 1)))))

 (local
  (defun
    nbr-step1s-to-test1 (x)
    (nfix x)))

 (defthm
   test1-base1=>test1
   (implies (test1 (base1 x))
	    (test1 x)))

 (defthm
   base1-step1=step1-base1
   (equal (base1 (step1 x))
	  (step1 (base1 x))))

 (defthm
   step1^n-def
   (equal (step1^n x n)
	  (if (zp n)
	      x
	      (step1^n (step1 x)(- n 1))))
   :rule-classes :definition)

 ;;  The recursion is said to halt for x iff there is an n such that
 ;;  (test1 (step1^n x n)).
 ;;  If the recursions halts for x, then (nbr-step1s-to-test1 x) is
 ;;  a witness showing that the recursion halts.
 (defthm
   test1-step1^n
   (implies (test1 (step1^n x n))
	    (test1 (step1^n x (nbr-step1s-to-test1 x)))))

 ;;  If there is an x such that the recursion does not halt, then the
 ;;  only y's for which the recursion halts are the y's satisfying
 ;;  (test1 y).
 (defthm
   not-test1-step1^n
   (implies (and (not (test1 (step1^n x (nbr-step1s-to-test1 x))))
		 (test1 (step1^n y (nbr-step1s-to-test1 y))))
	    (test1 y)))
 ) ;; end encapuslate

;; This part of the proof closely follows Pete and J's DEFPUN proof.

(defun
  gn (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n)(test1 x))
      (base1 x)
      (gn (step1 x)(- n 1))))

;; Choose a ``special'' constant if one exists.
(defchoose
  not-test1-step1^n-witness (x)()
  (not (test1 (step1^n x (nbr-step1s-to-test1 x)))))

(defun
  g (x)
  (if (test1 (step1^n x (nbr-step1s-to-test1 x)))
      (gn x (nbr-step1s-to-test1 x))
      (not-test1-step1^n-witness)))

;; This encapsulate merely hides some tedious details of the proof.
(encapsulate
 nil

 (local (defthm
	  test1-nbr-steps1-to-test1
          (implies (test1 x)
                   (test1 (step1^n x (nbr-step1s-to-test1 x))))
          :hints (("goal"
		   :use ((:instance
			  test1-step1^n
			  (n 0)))))))

 (local (defthm
	  test1-g-def
          (implies (test1 x)
                   (equal (g x)
			  (base1 x)))))

 (local (defthm
	  open-step1^n
          (implies (and (integerp n)
			(< 0 n))
                   (equal (step1^n x n)
			  (step1^n (step1 x)(- n 1))))))

 (local (defthm
	  step1-step1^n-nbr-step1s-to-test1
          (implies (test1 (step1^n (step1 x) (nbr-step1s-to-test1 (step1 x))))
                   (test1 (step1^n x (nbr-step1s-to-test1 x))))
          :hints (("goal"
		   :use ((:instance
			  test1-step1^n
			  (n (+ 1 (nfix (nbr-step1s-to-test1 (step1 x))))))
			 (:instance
			  test1-step1^n (n 1)))))
          :rule-classes :forward-chaining))

 (local (defthm
	  test1-nil-nbr-step1s-to-test1
          (implies (not (test1 x))
                   (iff (test1 (step1^n (step1 x)
					(nbr-step1s-to-test1 (step1 x))))
                        (test1 (step1^n x
					(nbr-step1s-to-test1 x)))))
          :hints (("subgoal 2"
		   :use ((:instance
			  test1-step1^n
			  (x (step1 x))
			  (n (+ -1 (nbr-step1s-to-test1 x)))))))))

 (local (defthm
	  gn-step1
          (implies (and (test1 (step1^n x n))
			(test1 (step1^n x m)))
                   (equal (gn x n) (gn x m)))
          :rule-classes nil))

 (defthm
   g-def
   (equal (g x)
          (if (test1 x)
	      (base1 x)
	      (g (step1 x))))
   :hints (("subgoal 1"
	    :expand (gn x (nbr-step1s-to-test1 x)))
	   ("subgoal 1.2'"
	    :use ((:instance gn-step1
			     (x (step1 x))
			     (n (+ -1 (nbr-step1s-to-test1 x)))
			     (m (nbr-step1s-to-test1 (step1 x)))))))
   :rule-classes :definition)
 ) ;; end encapsulate

(defun
  g^n (x n)
  (if (zp n)
      x
      (g^n (g x)(- n 1))))

(defthm
  g^n=g
  (equal (g^n x 1)
	 (g x))
  :hints (("Goal"
	   :by (:functional-instance
		f1^n=f1
		(f1 g)
		(f1^n g^n)))))

;; For those x for which the recursion does not halt the following
;; holds

;;   (implies (and (integerp i)
;;                 (> i 1)
;;                 (not (test1 (step1^n x (nbr-step1s-to-test1 x)))))
;;            (equal (g^n (base1 x)(+ -1 i))
;;                   (g^n x i))))

(defthm
  g=not-test1-step1^n-a
  (implies (not (test1 (step1^n x (nbr-step1s-to-test1 x))))
	   (equal (g (not-test1-step1^n-witness))
		  (not-test1-step1^n-witness)))
  :hints (("Goal"
	   :use not-test1-step1^n-witness)))

(defthm
  g^n=not-test1-step1^n-a
  (implies (not (test1 (step1^n x (nbr-step1s-to-test1 x))))
	   (equal (g^n (not-test1-step1^n-witness) i)
		  (not-test1-step1^n-witness))))

(defthm
  g^n=not-test1-step1^n
  (implies (and (integerp i)
		(> i 0)
		(not (test1 (step1^n x (nbr-step1s-to-test1 x)))))
	  (equal (g^n x i)
		 (not-test1-step1^n-witness))))

(defun
  step1^n-induct (x n)
  (if (zp n)
      x
      (step1^n-induct (step1 x)(- n 1))))

(defthm
  test1-step1^n-base1=>test1-step1^n
  (implies (test1 (step1^n (base1 x) i))
	   (test1 (step1^n x i)))
  :hints (("Goal"
	   :induct (step1^n-induct x i))))

(defthm
  test1-step1^n-base1=>test1-step1^n-a
  (implies (test1 (step1^n (base1 x)
			   (nbr-step1s-to-test1 (base1 x))))
	   (test1 (step1^n x
			   (nbr-step1s-to-test1 x))))
  :hints (("Goal"
	   :use (:instance
		 test1-step1^n
		 (n (nbr-step1s-to-test1 (base1 x)))))))

(defthm
  g^n-base1=not-test1-step1^n
  (implies (and (integerp i)
		(> i 0)
		(not (test1 (step1^n x (nbr-step1s-to-test1 x)))))
	  (equal (g^n (base1 x) i)
		 (not-test1-step1^n-witness))))

(defthm
  g^n-base1-g^n
  (implies (and (integerp i)
		(> i 1)
		(not (test1 (step1^n x (nbr-step1s-to-test1 x)))))
	   (equal (g^n (base1 x)(+ -1 i))
		  (g^n x i))))

(in-theory (disable g=not-test1-step1^n-a
		    g^n=not-test1-step1^n-a
		    g^n=not-test1-step1^n))

;; For those x for which the recursion does halt the following
;; holds

;;   (implies (and (integerp i)
;;                 (> i 1)
;;                 (test1 (step1^n x (nbr-step1s-to-test1 x))))
;;            (equal (g^n (base1 x)(+ -1 i))
;;                   (g^n x i))))

(defthm
  g^n-step1=g^n
  (implies (and (integerp i)
		(> i 0)
		(not (test1 x)))
	   (equal (g^n (step1 x) i)
		  (g^n x i))))

(defthm
  step1-step1^n-a
  (implies (and (integerp i)
		(>= i 0))
	   (equal (step1 (step1^n x i))
		  (step1^n x (+ 1 i))))
  :hints (("Goal"
	   :by (:functional-instance
		f1-f1^n-a
		(f1 step1)
		(f1^n step1^n)))))

(defthm
  g^n-step1^n=g^n-a
  (implies (and (integerp i)
		(> i 0)
		(integerp j)
		(>= j 0)
		(not (test1 (step1^n x j)))
		(equal (g^n (step1^n x j) i)
		       (g^n x i)))
	   (equal (g^n (step1^n x (+ 1 j)) i)
		  (g^n x i)))
  :hints (("Goal"
	   :use (:instance
		 g^n-step1=g^n
		 (x (step1^n x j))))))

(defun
  least-nbr-step1s-loop (x k)
  (declare (xargs :measure (let ((k (nfix k)))
			     (cond ((>= k (nfix (nbr-step1s-to-test1 x)))
				    0)
				   ((test1 (step1^n x k))
				    0)
				   (t (- (nfix (nbr-step1s-to-test1 x)) k))))))
  (let ((k (nfix k)))
    (cond ((>= k (nfix (nbr-step1s-to-test1 x)))
	   (nfix (nbr-step1s-to-test1 x)))
	  ((test1 (step1^n x k))
	   k)
	  (t (least-nbr-step1s-loop x (+ 1 k))))))

(defthm
  test1-step1^n-least-nbr-step1s-loop
  (implies (test1 (step1^n x n))
	   (test1 (step1^n x (least-nbr-step1s-loop x k))))
  :hints (("Subgoal *1/1"
	   :in-theory (disable test1-step1^n)
	   :use test1-step1^n)))

(defthm
  least-nbr-step1s-loop-is-least
  (implies (and (integerp k)
		(>= k 0)
		(integerp i)
		(<= k i)
		(< i (least-nbr-step1s-loop x k)))
	   (not (test1 (step1^n x i)))))

(defthm
  least-nbr-step1s-loop-is-least-a
  (implies (and (test1 (step1^n x n))
		(integerp n)
		(>= n k)
		(>= k 0))
	   (>= n (least-nbr-step1s-loop x k)))
  :rule-classes (:linear :rewrite))

(defun
  least-nbr-step1s (x)
  (least-nbr-step1s-loop x 0))

(defthm
  test1-step1^n-least-nbr-step1s
  (implies (test1 (step1^n x n))
	   (test1 (step1^n x (least-nbr-step1s x)))))

(defthm
  least-nbr-step1s-is-least
  (implies (and (integerp i)
		(<= 0 i)
		(< i (least-nbr-step1s x)))
	   (not (test1 (step1^n x i))))
  :hints (("Goal"
	   :in-theory (disable least-nbr-step1s-loop-is-least)
	   :use (:instance
		 least-nbr-step1s-loop-is-least
		 (k 0)))))

(defthm
  least-nbr-step1s-is-least-a
  (implies (and (test1 (step1^n x n))
		(integerp n)
		(<= 0 n))
	   (>= n (least-nbr-step1s x)))
  :rule-classes (:linear :rewrite))

(in-theory (disable least-nbr-step1s))

(defun
  induct-natp-hint (n)
  (if (zp n)
      t
      (induct-natp-hint (- n 1))))

(defthm
  g^n-step1^n=g^n
  (implies (and (integerp i)
		(> i 0)
		(<= j (least-nbr-step1s x)))
	   (equal (g^n (step1^n x j) i)
		  (g^n x i)))
  :hints (("Goal"
	   :induct (induct-natp-hint j))
	  ("Subgoal *1/2"
	   :in-theory (disable g^n-step1^n=g^n-a)
	   :use ((:instance
		  g^n-step1^n=g^n-a
		  (j (- j 1)))))))

(defthm
  g^n-g-step1^n-a
  (implies (and (integerp i)
		(> i 0))
	   (equal (g^n (g (step1^n x (least-nbr-step1s x)))(+ -1 i))
		  (g^n (step1^n x (least-nbr-step1s x)) i)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable g g^n-step1^n=g^n))))

(defthm
  g^n-base1-step1^n-a
  (implies (and (integerp i)
		(> i 0)
		(test1 (step1^n x (least-nbr-step1s x))))
	   (equal (g^n (base1 (step1^n x (least-nbr-step1s x)))
		       (+ -1 i))
		  (g^n (step1^n x (least-nbr-step1s x)) i)))
  :rule-classes nil
  :hints (("Goal"
	   :use (g^n-g-step1^n-a))))

(defthm
  g^n-base1-step1^n-b
  (implies (and (integerp i)
		(> i 0)
		(test1 (step1^n x (least-nbr-step1s x))))
	   (equal (g^n (base1 (step1^n x (least-nbr-step1s x)))
		       (+ -1 i))
		  (g^n x i)))
  :rule-classes nil
  :hints (("Goal"
	   :use (g^n-base1-step1^n-a))))

(defthm
  base1-step1^n=step1^n-base1
  (equal (base1 (step1^n x i))
	 (step1^n (base1 x) i))
  :hints (("Goal"
	   :induct (step1^n-induct x i))))

(defthm
  g^n-step1^n-base1
  (implies (and (integerp i)
		(> i 0)
		(test1 (step1^n x (least-nbr-step1s x))))
	   (equal (g^n (step1^n (base1 x)(least-nbr-step1s x))
		       (+ -1 i))
		  (g^n x i)))
  :hints (("Goal"
	   :use (g^n-base1-step1^n-b))))

(defthm
  test1-step1^n-base1
  (implies (and (not (test1 x))
		(test1 (step1^n x (least-nbr-step1s x))))
	   (test1 (step1^n (base1 x)
			   (least-nbr-step1s (base1 x)))))
  :hints (("Goal"
	   :use (:instance
		 not-test1-step1^n
		 (y x)
		 (x (base1 x))))))

(defthm
  test1-step1^n-least-nbr-step1s-base1
  (implies (and (not (test1 x))
		(test1 (step1^n x (least-nbr-step1s x))))
	   (test1 (step1^n x
			   (least-nbr-step1s (base1 x))))))

(defthm
  least-nbr-step1s<=least-nbr-step1s-base1
  (implies (and (not (test1 x))
		(test1 (step1^n x (least-nbr-step1s x))))
	    (<= (least-nbr-step1s x)
		(least-nbr-step1s (base1 x))))
  :rule-classes (:linear :rewrite))

(defthm
  g^n-step1^n-base1=g^n-base1
  (implies (and (not (test1 x))
		(test1 (step1^n x (least-nbr-step1s x)))
		(integerp i)
		(> i 0))
	   (equal (g^n (step1^n (base1 x)(least-nbr-step1s x)) i)
		  (g^n (base1 x) i)))
  :rule-classes nil)

(defthm
  g^n-base1-g^n-a
  (implies (and (integerp i)
		(> i 1)
		(test1 (step1^n x (least-nbr-step1s x)))
		(not (test1 x)))
	   (equal (g^n (base1 x)(+ -1 i))
		  (g^n x i)))
  :hints (("Goal"
	   :use (:instance
		 g^n-step1^n-base1=g^n-base1
		 (i (+ -1 i))))))

(defthm
  g^n-base1-g^n-b
  (implies (and (integerp i)
		(> i 1)
		(test1 (step1^n x (least-nbr-step1s x))))
	   (equal (g^n (base1 x)(+ -1 i))
		  (g^n x i)))
  :hints (("Goal"
	   :cases ((test1 x)))))

(defthm
  g^n-base1=g^n
  (implies (and (integerp i)
		(> i 1))
	   (equal (g^n (base1 x)(+ -1 i))
		  (g^n x i)))
  :hints (("Goal"
	   :cases ((test1 (step1^n x (nbr-step1s-to-test1 x)))))))

(defun
  base1^n (x n)
  (if (zp n)
      x
      (base1^n (base1 x)(- n 1))))

(defthm
  base1-base1^n-a
  (implies (and (integerp i)
		(>= i 0))
	   (equal (base1 (base1^n x i))
		  (base1^n x (+ 1 i))))
  :hints (("Goal"
	   :by (:functional-instance
		f1-f1^n-a
		(f1 base1)
		(f1^n base1^n)))))

(defthm
  g^n-base1^n-base1
  (implies (not (zp j))
	   (equal (g^n (base1^n (base1 x) (+ -1 j))
		       (+ -1 i (- (+ -1 j))))
		  (g^n (base1^n x j) (+ i (- j)))))
  :hints (("goal"
	  :use ((:theorem
		 (equal (+ -1 i (- (+ -1 j)))
			(+ i (- j))))))))

(defthm
  g^n-base1
  (implies (and (not (zp j))
		(integerp i)
		(< j i))
	   (equal (g^n (base1^n x (+ -1 j))
		       (+ i (- (+ -1 j))))
		  (g^n (base1^n x j) (+ i (- j)))))
  :hints (("goal"
	   :use (:instance
		 g^n-base1=g^n
		 (x (base1^n x (+ -1 j)))
		 (i (+ i (- (+ -1 j))))))))

(defthm
  g^n-base1^n=g^n
  (implies (and (integerp i)
		(integerp j)
		(<= 0 j)
		(< j i))
	   (equal (g^n (base1^n x j)(+ i (- j)))
		  (g^n x i)))
  :hints (("Goal"
           ;; [Jared] building this into ACL2 broke this theorem
           :in-theory (disable distributivity-of-minus-over-+)
	   :induct (induct-natp-hint j))))

(defthm
  g-base1^n=g^n
  (implies (and (integerp i)
		(> i 0))
	   (equal (g (base1^n x (+ -1 i)))
		  (g^n x i)))
  :hints (("Goal"
	   :in-theory (disable g^n-base1^n=g^n)
	   :use ((:instance
		  g^n-base1^n=g^n
		  (j (+ -1 i)))
		 (:theorem
		  (equal (+ I (- (+ -1 I)))
			 1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Develop a theory showing the existence of ``reflexive tail
; recursive'' functions.

(encapsulate
 (((test *) => *)
  ((base *) => *)
  ((stp *)  => *)
  ((c) => *)
  ((base^n * *)  => *)
  ((step2 *)=> *)
  ((step2^n * *) => *)
  ((nbr-step2s-to-test *) => *))

 (local
  (defun test (x)
    (<= (ifix x) 0)))

 (local
  (defun base (x)
    (+ (ifix x) 1)))

 (local
  (defun stp (x)
    (- (ifix x) 1)))

 (local
  (defun c ()
    1))

 (local
  (defun base^n (x n)
    (if (zp n)
	x
        (base^n (base x)(- n 1)))))

 (local
  (defun step2 (x)
    (base^n (stp x)(- (c) 1))))

 (local
  (defun step2^n (x n)
    (if (zp n)
	x
        (step2^n (step2 x)(- n 1)))))

 (local
  (defun
    nbr-step2s-to-test (x)
    (nfix x)))

 (defthm
   posp-c
   (and (integerp (c))
	(> (c) 0))
   :rule-classes :type-prescription)

 (defthm
   base^n-def
   (equal (base^n x n)
	  (if (zp n)
	      x
	      (base^n (base x)(- n 1))))
   :rule-classes :definition)

 (defthm
   step2-def
   (equal (step2 x)
	  (base^n (stp x)(- (c) 1)))
   :rule-classes :definition)

 (defthm
   step2^n-def
   (equal (step2^n x n)
	  (if (zp n)
	      x
	      (step2^n (step2 x)(- n 1))))
   :rule-classes :definition)

 (defthm
   test-base=>test
   (implies (test (base x))
	    (test x)))

 (defthm
   base-stp=stp-base
   (equal (base (stp x))
	  (stp (base x))))

 ;;  The recursion is said to halt for x iff there is an n such that
 ;;  (test (step2^n x n)).
 ;;  If the recursions halts for x, then (nbr-step2s-to-test x) is
 ;;  a witness showing that the recursion halts.
 (defthm
   test-step2^n
   (implies (test (step2^n x n))
	    (test (step2^n x (nbr-step2s-to-test x)))))

 ;;  If there is an x such that the recursion does not halt, then the
 ;;  only y's for which the recursion halts are the y's satisfying
 ;;  (test1 y).
 (defthm
   not-test-step2^n
   (implies (and (not (test (step2^n x (nbr-step2s-to-test x))))
		 (test (step2^n y (nbr-step2s-to-test y))))
	    (test y)))
 ) ;; end encapuslate

(defthm
  base-base^n
  (equal (base (base^n x i))
	 (base^n (base x) i))
  :hints (("Goal"
	   :by (:functional-instance
		f1-f1^n
		(f1 base)
		(f1^n base^n)))))

(defun
  fn (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n)(test x))
      (base x)
      (fn (step2 x)(- n 1))))

;; Choose a ``special'' constant if one exists.
(defchoose
  not-test-step2^n-witness (x)()
  (not (test (step2^n x (nbr-step2s-to-test x)))))

(defun
  f (x)
  (if (test (step2^n x (nbr-step2s-to-test x)))
      (fn x (nbr-step2s-to-test x))
      (not-test-step2^n-witness)))

(defun
  f^n (x n)
  (if (zp n)
      x
      (f^n (f x)(- n 1))))

(defthm
  f-base^n=f^n
  (implies (and (integerp i)
		(> i 0))
	   (equal (f (base^n x (+ -1 i)))
		  (f^n x i)))
  :hints (("Goal"
	   :by (:functional-instance
		g-base1^n=g^n
		(g f)
		(base1 base)
		(base1^n base^n)
		(g^n f^n)
		(test1 test)
		(step1 step2)
		(step1^n step2^n)
		(nbr-step1s-to-test1 nbr-step2s-to-test)
		(gn fn)
		(not-test1-step1^n-witness not-test-step2^n-witness)))
	  ("Subgoal 7"
	   :use not-test-step2^n-witness)))

(defthm
  f-def
  (equal (f x)
	 (if (test x)
	     (base x)
	     (f (step2 x))))
  :rule-classes :definition
  :hints (("Goal"
	   :by (:functional-instance
		g-def
		(g f)
		(base1 base)
		(test1 test)
		(step1 step2)
		(step1^n step2^n)
		(nbr-step1s-to-test1 nbr-step2s-to-test)
		(gn fn)
		(not-test1-step1^n-witness not-test-step2^n-witness)
		))))

(defthm
  f-def-a
  (equal (f x)
	 (if (test x)
	     (base x)
	     (f^n (stp x)(c))))
  :rule-classes :definition)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Develop a theory assuming the existence of a ``reflexive tail
; recursive'' function.

(include-book "../../../../arithmetic/top")

(encapsulate
 (((c1)     => *)
  ((tst1 *) => *)
  ((bse1 *) => *)
  ((stp1 *) => *)
  ((stp1^n * *) => *)
  ((nbr-stp1s-to-tst1 *) => *)
  ((f2 *)   => *)
  ((f2^n * *)   => *))

 (local
  (defun c1 ()
    1))

 (local
  (defun tst1 (x)
    (<= (ifix x) 0)))

 (local
  (defun bse1 (x)
    (+ (ifix x) 1)))

 (local
  (defun stp1 (x)
    (- (ifix x) 1)))

 (local
  (defun stp1^n (x n)
    (if (zp n)
	x
        (stp1^n (stp1 x)(- n 1)))))

 (local
  (defun
    nbr-stp1s-to-tst1 (x)
    (nfix x)))

 (local
  (defun
    f2 (x)
    (if (tst1 x)
	(bse1 x)
        (f2 (stp1 x)))))

 (local
  (defun
    f2^n (x n)
    (if (zp n)
	x
        (f2^n (f2 x)(- n 1)))))

 (defthm
   posp-c1
   (and (integerp (c1))
	(> (c1) 0))
   :rule-classes :type-prescription)

 (defthm
   tst1-bse1=>tst1
   (implies (tst1 (bse1 x))
	    (tst1 x)))

 (defthm
   bse1-stp1=stp1-bse1
   (equal (bse1 (stp1 x))
	  (stp1 (bse1 x))))

 (defthm
   stp1^n-def
   (equal (stp1^n x n)
	  (if (zp n)
	      x
	      (stp1^n (stp1 x)(- n 1))))
   :rule-classes :definition)

 ;;  The recursion is said to halt for x iff there is an n such that
 ;;  (tst1 (stp1^n x n)).
 ;;  If the recursions halts for x, then (nbr-stp1s-to-tst1 x) is
 ;;  a witness showing that the recursion halts.

 (defthm
   tst1-stp1^n
   (tst1 (stp1^n x (nbr-stp1s-to-tst1 x))))

 (defthm
   f2-def-a
   (equal (f2 x)
	  (if (tst1 x)
	      (bse1 x)
	      (f2^n (stp1 x)(c1))))
   :rule-classes :definition)

 (defthm
   f2^n-def
   (equal (f2^n x n)
	  (if (zp n)
	      x
	      (f2^n (f2 x)(- n 1))))
   :rule-classes :definition)
 ) ;; end encapsulate

(defun
  least-nbr-stp1s-loop (x k)
  (declare (xargs :measure (let ((k (nfix k)))
			     (cond ((>= k (nfix (nbr-stp1s-to-tst1 x)))
				    0)
				   ((tst1 (stp1^n x k))
				    0)
				   (t (- (nfix (nbr-stp1s-to-tst1 x)) k))))))
  (let ((k (nfix k)))
    (cond ((>= k (nfix (nbr-stp1s-to-tst1 x)))
	   (nfix (nbr-stp1s-to-tst1 x)))
	  ((tst1 (stp1^n x k))
	   k)
	  (t (least-nbr-stp1s-loop x (+ 1 k))))))

(defthm
  tst1-stp1^n-least-nbr-stp1s-loop
  (tst1 (stp1^n x (least-nbr-stp1s-loop x k)))
  :hints (("Subgoal *1/1"
	   :in-theory (disable tst1-stp1^n)
	   :use tst1-stp1^n)))

(defthm
  least-nbr-stp1s-loop-is-least
  (implies (and (integerp k)
		(>= k 0)
		(integerp i)
		(<= k i)
		(< i (least-nbr-stp1s-loop x k)))
	   (not (tst1 (stp1^n x i)))))

(defthm
  least-nbr-stp1s-loop-is-least-a
  (implies (and (tst1 (stp1^n x n))
		(integerp n)
		(>= n k)
		(>= k 0))
	   (>= n (least-nbr-stp1s-loop x k)))
  :rule-classes (:linear :rewrite))

(defun
  least-nbr-stp1s (x)
  (least-nbr-stp1s-loop x 0))

(defthm
  tst1-stp1^n-least-nbr-stp1s
  (tst1 (stp1^n x (least-nbr-stp1s x))))

(defthm
  least-nbr-stp1s-is-least
  (implies (and (integerp i)
		(<= 0 i)
		(< i (least-nbr-stp1s x)))
	   (not (tst1 (stp1^n x i)))))

(defthm
  least-nbr-stp1s-is-least-a
  (implies (and (tst1 (stp1^n x n))
		(integerp n)
		(<= 0 n))
	   (>= n (least-nbr-stp1s x)))
  :rule-classes (:linear :rewrite))

(in-theory (disable least-nbr-stp1s))

(defthm
  f2^n=f2
  (equal (f2^n x 1)
	 (f2 x))
  :hints (("Goal"
	   :by (:functional-instance
		f1^n=f1
		(f1 f2)
		(f1^n f2^n)))))

(defthm
  compose-f2^n
  (equal (f2^n (f2^n x i) j)
	 (f2^n x (+ (nfix i)
		    (nfix j))))
  :hints (("Goal"
	   :by (:functional-instance
		compose-f1^n
		(f1 f2)
		(f1^n f2^n)))))

(defthm
  f2^n-f2=f2^n
  (implies (and (integerp i)
		(> i 0))
	   (equal (f2^n (f2 x)(+ -1 i))
		  (f2^n x i)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable f2-def-a))))

(defthm
  f2^n-stp1=f2^n
  (implies (and (integerp i)
		(> i 0)
		(not (tst1 x)))
	   (equal (f2^n (stp1 x)(+ -1 (c1) i))
		  (f2^n x i)))
  :hints (("Goal"
	   :use f2^n-f2=f2^n)))

(defthm
  stp1-stp1^n-a
  (implies (and (integerp i)
		(>= i 0))
	   (equal (stp1 (stp1^n x i))
		  (stp1^n x (+ 1 i))))
  :hints (("Goal"
	   :by (:functional-instance
		f1-f1^n-a
		(f1 stp1)
		(f1^n stp1^n)))))

(defthm
  f2^n-stp1=f2^n-a
  (implies (and (integerp i)
		(> i 0)
		(integerp j)
		(>= j 0)
		(not (tst1 (stp1^n x j)))
		(equal (f2^n (stp1^n x j)(+ i (* j (+ -1 (c1)))))
		       (f2^n x i)))
	   (equal (f2^n (stp1^n x (+ 1 j))(+ i (* (+ 1 j)(+ -1 (c1)))))
		  (f2^n x i)))
  :hints (("Goal"
	   :use ((:instance
		  f2^n-stp1=f2^n
		  (x (stp1^n x j))
		  (i (+ i (* j (+ -1 (c1))))))
		 (:theorem
		   (implies (and (> i 0)
				 (integerp j)
				 (>= j 0))
			    (> (+ I (* j (+ -1 (c1)))) 0)))))))

(defthm
  f2^n-stp1^n=f2^n
  (implies (and (integerp i)
		(> i 0)
		(integerp j)
		(<= 0 j)
		(<= j (least-nbr-stp1s x)))
	   (equal (f2^n (stp1^n x j)(+ i (* j (+ -1 (c1)))))
		  (f2^n x i)))
  :hints (("Goal"
	   :induct (induct-natp-hint j))
	  ("Subgoal *1/2"
	   :in-theory (disable f2^n-stp1=f2^n-a)
	   :use (:instance
		 f2^n-stp1=f2^n-a
		 (j (- j 1))))))

(defthm
  f2^n-f2-stp1^n-a
  (implies (and (integerp i)
		(> i 0))
	   (equal (f2^n (f2 (stp1^n x (least-nbr-stp1s x)))(+ -1 i))
		  (f2^n (stp1^n x (least-nbr-stp1s x)) i)))
  :rule-classes nil)

(defthm
  f2^n-f2-stp1^n-a-1
  (implies (and (integerp i)
		(> i 0))
	   (equal (f2^n (f2 (stp1^n x (least-nbr-stp1s x)))
			(+ -1 i (* (least-nbr-stp1s x)(+ -1 (c1)))))
		  (f2^n (stp1^n x (least-nbr-stp1s x))
			(+ i (* (least-nbr-stp1s x)(+ -1 (c1)))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 f2^n-f2-stp1^n-a
		 (i (+ i (* (least-nbr-stp1s x)(+ -1 (c1)))))))))

(defthm
  f2^n-bse1-stp1^n-a
  (implies (and (integerp i)
		(> i 0))
	   (equal (f2^n (bse1 (stp1^n x (least-nbr-stp1s x)))
			(+ -1 i (* (least-nbr-stp1s x)(+ -1 (c1)))))
		  (f2^n (stp1^n x (least-nbr-stp1s x))
			(+ i (* (least-nbr-stp1s x)(+ -1 (c1)))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (f2^n-f2-stp1^n-a-1))))

(defthm
  f2^n-bse1-stp1^n-b
  (implies (and (integerp i)
		(> i 0))
	   (equal (f2^n (bse1 (stp1^n x (least-nbr-stp1s x)))
			(+ -1 i (* (least-nbr-stp1s x)(+ -1 (c1)))))
		  (f2^n x i)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable f2^n-stp1^n=f2^n)
	   :use (f2^n-bse1-stp1^n-a
		 (:instance
		  f2^n-stp1^n=f2^n
		  (j (least-nbr-stp1s x)))))))

(defun
  stp1^n-induct (x n)
  (if (zp n)
      x
      (stp1^n-induct (stp1 x)(- n 1))))

(defthm
  bse1-stp1^n=stp1^n-bse1
  (equal (bse1 (stp1^n x i))
	 (stp1^n (bse1 x) i))
  :hints (("Goal"
	   :induct (stp1^n-induct x i))))

(defthm
  f2^n-stp1^n-bse1
  (implies (and (integerp i)
		(> i 0))
	   (equal (f2^n (stp1^n (bse1 x)(least-nbr-stp1s x))
			(+ -1 i (* (least-nbr-stp1s x)(+ -1 (c1)))))
		  (f2^n x i)))
  :hints (("Goal"
	   :use (f2^n-bse1-stp1^n-b))))

(defthm
  tst1-stp1^n-least-nbr-stp1s-bse1
  (tst1 (stp1^n x (least-nbr-stp1s (bse1 x)))))

(defthm
  least-nbr-stp1s<=least-nbr-stp1s-bse1
  (<= (least-nbr-stp1s x)
      (least-nbr-stp1s (bse1 x)))
  :rule-classes (:linear :rewrite))

(defthm
  f2^n-stp1^n-bse1=f2^n-bse1
  (implies (and (integerp i)
		(> i 0))
	   (equal (f2^n (stp1^n (bse1 x)(least-nbr-stp1s x))
			(+ i (* (least-nbr-stp1s x)(+ -1 (c1)))))
		  (f2^n (bse1 x) i)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable f2^n-stp1^n=f2^n)
	   :use (:instance
		 f2^n-stp1^n=f2^n
		 (x (bse1 x))
		 (j (least-nbr-stp1s x))))))

(defthm
  f2^n-bse1=f2^n
  (implies (and (integerp i)
		(> i 1))
	   (equal (f2^n (bse1 x)(+ -1 i))
		  (f2^n x i)))
  :hints (("Goal"
	   :use (f2^n-stp1^n-bse1
		 (:instance
		  f2^n-stp1^n-bse1=f2^n-bse1
		  (i (+ -1 i)))))))

(defun
  bse1^n (x n)
  (if (zp n)
      x
      (bse1^n (bse1 x)(- n 1))))

(defthm
  bse1-bse1^n-a
  (implies (and (integerp i)
		(>= i 0))
	   (equal (bse1 (bse1^n x i))
		  (bse1^n x (+ 1 i))))
  :hints (("Goal"
	   :by (:functional-instance
		f1-f1^n-a
		(f1 bse1)
		(f1^n bse1^n)))))

(defthm
  f2^n-bse1^n-bse1
  (implies (not (zp j))
	   (equal (f2^n (bse1^n (bse1 x)(+ -1 j))
			(+ -1 i (- (+ -1 j))))
		  (f2^n (bse1^n x j) (+ i (- j))))))

(defthm
  f2^n-bse1
  (implies (and (not (zp j))
		(integerp i)
		(< j i))
	   (equal (f2^n (bse1^n x (+ -1 j))
		       (+ i (- (+ -1 j))))
		  (f2^n (bse1^n x j) (+ i (- j)))))
  :hints (("goal"
	   :use (:instance
		 f2^n-bse1=f2^n
		 (x (bse1^n x (+ -1 j)))
		 (i (+ i (- (+ -1 j))))))))

(defthm
  f2^n-bse1^n=f2^n
  (implies (and (integerp i)
		(integerp j)
		(<= 0 j)
		(< j i))
	   (equal (f2^n (bse1^n x j)(+ i (- j)))
		  (f2^n x i)))
  :hints (("Goal"
	   :induct (induct-natp-hint j))
	  ("Subgoal *1/2"
	   :use f2^n-bse1)))

(defthm
  f2-bse1^n=f2^n
  (implies (and (integerp i)
		(> i 0))
	   (equal (f2 (bse1^n x (+ -1 i)))
		  (f2^n x i)))
  :hints (("Goal"
	   :in-theory (disable f2^n-bse1^n=f2^n)
	   :use ((:instance
		  f2^n-bse1^n=f2^n
		  (j (+ -1 i)))))))

(defthm
  f2-def-b
  (equal (f2 x)
	 (if (tst1 x)
	     (bse1 x)
	     (f2 (bse1^n (stp1 x)(- (c1) 1)))))
  :rule-classes :definition)
