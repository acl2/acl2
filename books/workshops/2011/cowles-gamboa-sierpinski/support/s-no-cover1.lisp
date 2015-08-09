;;Show k = 734110615000775^4
;;         = (expt 734110615000775 4)
;;         = 290433036530614504024730081259407069229771426966923250390625
;; is a Sierpinski number,
;; but no (complete) cover is known.

;; A Sierpinski number is an odd positive integer, k, such that no
;; positive integer in this infinite list is prime:

;;    k 2^1 + 1, k  2^2 + 1, k 2^3 + 1, ..., k 2^n + 1, ... .

;; A cover, for such a k, is a finite list of positive integers such that
;; each integer, j, in the above infinite list, has a factor, d, in
;; the cover, with 1 < d < j.

;;                      by
;;   John R.Cowles          Ruben Gamboa
;;   cowles@cs.uwyo.edu     ruben@cs.uwyo.edu
;;        Department of Computer Science
;;        University of Wyoming
;;        Laramie, Wyoming, USA

;; Copyright (C) 2011  University of Wyoming, Laramie, Wyoming

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
;; 02110-1301, USA.

;; A partial cover = (3 17 257 641 65537 6700417)
;; Covers all n except (mod n 4) = 2
;; For all positve integer n, if (mod n 4) does NOT equal 2,
;; then  k*2^n + 1 is divible by a member of (3 17 257 641 65537 6700417).

;; To show that k is a Sierpinski number,
;;  a divisor for k*2^n + 1 must be found for all positive
;;  integer n such that (mod n 4) = 2.

;; Such a divisor is constructed using these facts:

;;       k is a fourth power

;;       4*x^4 + 1 = (2*x^2 + 2*x + 1) * (2*x^2 - 2*x + 1)

;; Let i = 44745755, so k = i^4.

;; Then k * 2^(4n+2) + 1 = 2^2*(i*2^n)^4 + 1
;;                       = 4*(i*2^n)^4 + 1
;;                       = (2*(i*2^n)^2 + 2*(i*2^n) + 1)
;;                          * (2*(i*2^n)^2 - 2*(i*2^n) + 1)

#| To certify
  (certify-book "s-no-cover1")
|#

(in-package "ACL2")

(local (include-book "arithmetic-3/top" :dir :system))

(defun
divides (x y)
(cond ((equal x 0)
	 (equal y 0))
	((and (integerp x)
	      (integerp y))
	 (integerp (* y (/ x))))
	(t nil)))

(defthm
divides-+
(implies (and (divides x y)
		(divides x z))
	   (divides x (+ y z)))
:rule-classes nil)

(defthm
divides-*
(implies (and (divides x y)
		(integerp z))
	   (divides x (* y z)))
:rule-classes nil)

#|============================
(defun find-sierpinski-b (i d)
 (declare (xargs :measure (nfix (- d i))))
 (if (and (integerp i)
	   (integerp d)
	   (< i d))
     (if (divides d (1- (expt 2 i)))
	  i
	(find-sierpinski-b (1+ i) d))
   0))

(defun find-sierpinski-c (i b d number)
 (declare (xargs :measure (nfix (- b i))))
 (if (and (integerp i)
	   (integerp b)
	   (< i b))
     (if (divides d (1+ (* number (expt 2 i))))
	  i
	(find-sierpinski-c (1+ i) b d number))
   0))

(defun generate-sierpinski-triplets (number cover)
 (if (consp cover)
     (let* ((a number)
	     (d (car cover))
	     (b (find-sierpinski-b 1 d))
	     (c (find-sierpinski-c 0 b d a))
	     )
	(cons (list b c d)
	      (generate-sierpinski-triplets number (cdr cover))))
   nil))

(defun s-gcd (a b)
 (if (or (zp b)
	  (not (integerp a))
	  (< a 0))
     a
   (s-gcd b (mod a b))))

(defun s-lcm (a b)
 (/ (abs (* a b))
    (s-gcd a b)))

(defun s-lcm-list (l)
 (if (consp l)
     (if (consp (cdr l))
	  (s-lcm (car l)
		 (s-lcm-list (cdr l)))
	(car l))
   0))

(defun map-first (triplets)
 (if (consp triplets)
     (cons (first (car triplets))
	    (map-first (cdr triplets)))
     nil))

Partial cover triplets
for those n such that
 (mod n 4) does NOT equal 2,
(generate-sierpinski-triplets (expt 734110615000775 4)
			      '(3 17 257 641 65537 6700417))
==>((2 1 3)
   (8 4 17)
   (16 8 257)
   (64 32 641)
   (32 16 65537)
   (64 0 6700417))

Cover triplets for all n
==>((2 1 3)
   (8 4 17)
   (16 8 257)
   (64 32 641)
   (32 16 65537)
   (64 0 6700417)
   (4 2 'expression))

Least common multiple of the moduli
(s-lcm-list (map-first '((2 1 3)
			 (8 4 17)
			 (16 8 257)
			 (64 32 641)
			 (32 16 65537)
			 (64 0 6700417)
			 (4 2 'expression))))
==> 64

(defun generate-sierpinski-equalities (triplets)
 (if (consp triplets)
     (let* ((triplet (car triplets))
	     (b (first triplet))
	     (c (second triplet))
	     )
	(cons `(EQUAL (MOD N ,b) ,c)
	      (generate-sierpinski-equalities (cdr triplets))))
     nil))

(defun generate-sierpinski-cover-one ()
 (let ((triplets '((2 1 3)
		    (8 4 17)
		    (16 8 257)
		    (64 32 641)
		    (32 16 65537)
		    (64 0 6700417)
		    (4 2 'expression))))
   `(DEFUN COVER-ONE (N)
      (IF (INTEGERP N)
	   (OR ,@(generate-sierpinski-equalities triplets))
	   NIL))))

(generate-sierpinski-cover-one)
============================|#
;;==>
(DEFUN COVER-ONE (N)
      (IF (INTEGERP N)
          (OR (EQUAL (MOD N 2) 1)
              (EQUAL (MOD N 8) 4)
              (EQUAL (MOD N 16) 8)
              (EQUAL (MOD N 64) 32)
              (EQUAL (MOD N 32) 16)
              (EQUAL (MOD N 64) 0)
              (EQUAL (MOD N 4) 2))
          NIL))

(DEFUN cover (L U)
 (DECLARE (XARGS :MEASURE (IF (AND (INTEGERP L)(INTEGERP U)(< L U))
			       (- U L)
			       0)))
 (IF (AND (INTEGERP L)
	   (INTEGERP U))
     (IF (< L U)
	  (AND (cover-one L)(cover (1+ L) U))
	  T)
     NIL))

(DEFTHM cover=>cover-one
 (IMPLIES (AND (INTEGERP N)(<= L N)(< N U)(cover L U))
	   (cover-one N))
 :RULE-CLASSES NIL
 :HINTS (("GOAL" :IN-THEORY (DISABLE (:DEFINITION cover-one)))))

#|============================
(defun generate-sierpinski-cover-cases-< ()
 (let* ((triplets '((2 1 3)
		     (8 4 17)
		     (16 8 257)
		     (64 32 641)
		     (32 16 65537)
		     (64 0 6700417)
		     (4 2 'expression)))
	 (l (s-lcm-list (map-first triplets)))
	 )
   `(DEFTHM cover-<
      (IMPLIES (AND (INTEGERP N)(<= 0 N)(< N ,l))
		(OR ,@(generate-sierpinski-equalities triplets)))
      :RULE-CLASSES NIL
      :HINTS (("GOAL" :USE ((:INSTANCE cover=>cover-one (L 0)(U ,l))))))))

(generate-sierpinski-cover-cases-<)
============================|#
;;==>
(DEFTHM COVER-<
       (IMPLIES (AND (INTEGERP N) (<= 0 N) (< N 64))
                (OR (EQUAL (MOD N 2) 1)
                    (EQUAL (MOD N 8) 4)
                    (EQUAL (MOD N 16) 8)
                    (EQUAL (MOD N 64) 32)
                    (EQUAL (MOD N 32) 16)
                    (EQUAL (MOD N 64) 0)
                    (EQUAL (MOD N 4) 2)))
       :RULE-CLASSES NIL
       :HINTS (("GOAL" :USE ((:INSTANCE COVER=>COVER-ONE (L 0)
                                        (U 64))))))
#|============================
(defun generate-sierpinski-equalities-mod (triplets l)
 (if (consp triplets)
     (let* ((triplet (car triplets))
	     (b (first triplet))
	     (c (second triplet))
	     )
	(cons `(EQUAL (MOD (MOD N ,l) ,b) ,c)
	      (generate-sierpinski-equalities-mod (cdr triplets) l)))
     nil))

(defun generate-sierpinski-cover-cases-mod ()
 (let* ((triplets '((2 1 3)
		     (8 4 17)
		     (16 8 257)
		     (64 32 641)
		     (32 16 65537)
		     (64 0 6700417)
		     (4 2 'expression)))
	 (l (s-lcm-list (map-first triplets)))
	 )
   `(DEFTHM cover-mod
      (IMPLIES (INTEGERP N)
		(OR ,@(generate-sierpinski-equalities-mod triplets l)))
      :RULE-CLASSES NIL
      :HINTS (("GOAL" :USE ((:INSTANCE cover-< (N (MOD N ,l)))))))))

(generate-sierpinski-cover-cases-mod)
============================|#
;;==>
(DEFTHM COVER-MOD
       (IMPLIES (INTEGERP N)
                (OR (EQUAL (MOD (MOD N 64) 2) 1)
                    (EQUAL (MOD (MOD N 64) 8) 4)
                    (EQUAL (MOD (MOD N 64) 16) 8)
                    (EQUAL (MOD (MOD N 64) 64) 32)
                    (EQUAL (MOD (MOD N 64) 32) 16)
                    (EQUAL (MOD (MOD N 64) 64) 0)
                    (EQUAL (MOD (MOD N 64) 4) 2)))
       :RULE-CLASSES NIL
       :HINTS (("GOAL" :USE ((:INSTANCE COVER-< (N (MOD N 64)))))))

#|============================
(defun generate-sierpinski-cover-cases ()
 (let ((triplets '((2 1 3)
		    (8 4 17)
		    (16 8 257)
		    (64 32 641)
		    (32 16 65537)
		    (64 0 6700417)
		    (4 2 'expression)))
	)
   `(DEFTHM cover-thm
      (IMPLIES (INTEGERP N)
		(OR ,@(generate-sierpinski-equalities triplets)))
      :RULE-CLASSES NIL
      :HINTS (("GOAL" :USE ((:INSTANCE cover-mod)))))))

(generate-sierpinski-cover-cases)
============================|#
;;==>
(DEFTHM COVER-THM
       (IMPLIES (INTEGERP N)
                (OR (EQUAL (MOD N 2) 1)
                    (EQUAL (MOD N 8) 4)
                    (EQUAL (MOD N 16) 8)
                    (EQUAL (MOD N 64) 32)
                    (EQUAL (MOD N 32) 16)
                    (EQUAL (MOD N 64) 0)
                    (EQUAL (MOD N 4) 2)))
       :RULE-CLASSES NIL
       :HINTS (("GOAL" :USE ((:INSTANCE COVER-MOD)))))

;;Exceptional case is required:
(defthm
 Not-covered-by-part-cover
 (implies (or (equal n 2)
	       (equal n 6)
	       (equal n 10)
	       (equal n 14)
	       (equal n 18)
	       (equal n 22)
	       (equal n 26)
	       (equal n 30)
	       (equal n 34)
	       (equal n 38)
	       (equal n 42)
	       (equal n 46))
	   (and (equal (mod n 4)
		       2)
		(not (or (equal (mod n 2)  ;;Partial cover cases
				1)
			 (equal (mod n 8)
				4)
			 (equal (mod n 16)
				8)
			 (equal (mod n 64)
				32)
			 (equal (mod n 32)
				16)
			 (equal (mod n 64)
				0)))))
 :rule-classes nil)

(defun
natp-induction (n)
(if (zp n)
    t
    (natp-induction (- n 1))))

(encapsulate
(((aS) => *)
 ((bS) => *)
 ((cS) => *)
 ((dS) => *))

(local
 (defun
     aS ( )
   2))

(local
 (defun
     bS ( )
   2))

(local
 (defun
     cS ( )
   0))

(local
 (defun
     dS ( )
   3))

(defthm
    pos-int-aS
    (and (integerp (aS))
	  (> (aS) 0))
  :rule-classes
  :type-prescription)

(defthm
    pos-int-bS
    (and (integerp (bS))
	  (> (bS) 0))
  :rule-classes
  :type-prescription)

(defthm
    nat-int-cS
    (and (integerp (cS))
	  (>= (cS) 0))
  :rule-classes
  :type-prescription)

(defthm
    pos-int-dS
    (and (integerp (dS))
	  (> (dS) 0))
  :rule-classes
  :type-prescription)

(defthm
    Basis-condition-Sierpinski
    (divides (dS)
	      (+ 1
		 (* (aS)
		    (expt 2
			  (cS))))))

(defthm
    Induction-condition-Sierpinski
    (divides (dS)
	      (+ -1
		 (expt 2
		       (bS)))))
)

(defthm
   Key-lemma-Sierpinski
   (implies (and (integerp n)
		  (>= n 0))
	     (divides (dS)
		      (+ 1
			 (* (aS)
			    (expt 2
				  (+ (cS)
				     (* (bS)
					n)))))))
 :rule-classes nil
 :hints (("Goal"
	   :induct (natp-induction n))
	  ("Subgoal *1/2"
	   :use ((:instance
		  divides-+
		  (x (dS))
		  (y (+ 1 (* (aS)
			     (expt 2 (+ (- (bS))
					(cS)
					(* (bS)
					   n))))))
		  (z (* (aS)
			(expt 2 (+ (- (bS))
				   (cS)
				   (* (bS) n)))
			(+ -1 (expt 2 (bS))))))
		 (:instance
		  divides-*
		  (x (dS))
		  (y (+ -1 (expt 2 (bS))))
		  (z (* (aS)
			(expt 2
			      (+ (- (bS))
				 (cS)
				 (* (bS) n))))))))))

(in-theory (disable (:definition divides)))

#|============================
(defun generate-sierpinski-lemmas (number cover)
 (if (consp cover)
     (let* ((a number)
	     (d (car cover))
	     (b (find-sierpinski-b 1 d))
	     (c (find-sierpinski-c 0 b d a))
	     )
	(cons
	 `(DEFTHM divisor-lemma- ,d
	    (IMPLIES (AND (INTEGERP N)
			  (>= N 0))
		     (DIVIDES ,d (+ 1 (* ,a (EXPT 2 (+ ,c (* ,b N)))))))
	    :RULE-CLASSES NIL
	    :HINTS (("GOAL"
		     :USE ((:FUNCTIONAL-INSTANCE Key-Lemma-Sierpinski
						 (AS (LAMBDA () ,a))
						 (BS (LAMBDA () ,b))
						 (CS (LAMBDA () ,c))
						 (DS (LAMBDA () ,d)))))))
	 (generate-sierpinski-lemmas number (cdr cover))))
   nil))

(generate-sierpinski-lemmas (expt 734110615000775 4)
			    '(3 17 257 641 65537 6700417))
==>
((DEFTHM
 DIVISOR-LEMMA- 3
 (IMPLIES
     (AND (INTEGERP N) (>= N 0))
     (DIVIDES
          3
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 (+ 1 (* 2 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-SIERPINSKI
     (AS
      (LAMBDA NIL
              290433036530614504024730081259407069229771426966923250390625))
     (BS (LAMBDA NIL 2))
     (CS (LAMBDA NIL 1))
     (DS (LAMBDA NIL 3)))))))
  etc)

Theorems in list submitted to ACL2 by hand after modifying name of theorem:
(DEFTHM
 DIVISOR-LEMMA-3
 (IMPLIES
     (AND (INTEGERP N) (>= N 0))
     (DIVIDES
          3
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 (+ 1 (* 2 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-SIERPINSKI
     (AS
      (LAMBDA NIL
              290433036530614504024730081259407069229771426966923250390625))
     (BS (LAMBDA NIL 2))
     (CS (LAMBDA NIL 1))
     (DS (LAMBDA NIL 3)))))))
============================|#
(DEFTHM
 DIVISOR-LEMMA-3
 (IMPLIES
     (AND (INTEGERP N) (>= N 0))
     (DIVIDES
          3
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 (+ 1 (* 2 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-SIERPINSKI
     (AS
      (LAMBDA NIL
              290433036530614504024730081259407069229771426966923250390625))
     (BS (LAMBDA NIL 2))
     (CS (LAMBDA NIL 1))
     (DS (LAMBDA NIL 3)))))))
(DEFTHM
 DIVISOR-LEMMA-17
 (IMPLIES
     (AND (INTEGERP N) (>= N 0))
     (DIVIDES
          17
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 (+ 4 (* 8 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-SIERPINSKI
     (AS
      (LAMBDA NIL
              290433036530614504024730081259407069229771426966923250390625))
     (BS (LAMBDA NIL 8))
     (CS (LAMBDA NIL 4))
     (DS (LAMBDA NIL 17)))))))
(DEFTHM
 DIVISOR-LEMMA-257
 (IMPLIES
     (AND (INTEGERP N) (>= N 0))
     (DIVIDES
          257
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 (+ 8 (* 16 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-SIERPINSKI
     (AS
      (LAMBDA NIL
              290433036530614504024730081259407069229771426966923250390625))
     (BS (LAMBDA NIL 16))
     (CS (LAMBDA NIL 8))
     (DS (LAMBDA NIL 257)))))))
(DEFTHM
 DIVISOR-LEMMA-641
 (IMPLIES
     (AND (INTEGERP N) (>= N 0))
     (DIVIDES
          641
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 (+ 32 (* 64 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-SIERPINSKI
     (AS
      (LAMBDA NIL
              290433036530614504024730081259407069229771426966923250390625))
     (BS (LAMBDA NIL 64))
     (CS (LAMBDA NIL 32))
     (DS (LAMBDA NIL 641)))))))
(DEFTHM
 DIVISOR-LEMMA-65537
 (IMPLIES
     (AND (INTEGERP N) (>= N 0))
     (DIVIDES
          65537
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 (+ 16 (* 32 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-SIERPINSKI
     (AS
      (LAMBDA NIL
              290433036530614504024730081259407069229771426966923250390625))
     (BS (LAMBDA NIL 32))
     (CS (LAMBDA NIL 16))
     (DS (LAMBDA NIL 65537)))))))
(DEFTHM
 DIVISOR-LEMMA-6700417
 (IMPLIES
     (AND (INTEGERP N) (>= N 0))
     (DIVIDES
          6700417
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 (+ 0 (* 64 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-SIERPINSKI
     (AS
      (LAMBDA NIL
              290433036530614504024730081259407069229771426966923250390625))
     (BS (LAMBDA NIL 64))
     (CS (LAMBDA NIL 0))
     (DS (LAMBDA NIL 6700417)))))))

#|============================
(defun generate-sierpinski-lemmas-a (number cover)
 (if (consp cover)
     (let* ((a number)
	     (d (car cover))
	     (b (find-sierpinski-b 1 d))
	     (c (find-sierpinski-c 0 b d a))
	     )
	(cons
	 `(DEFTHM divisor-lemma-a- ,d
	    (IMPLIES (AND (INTEGERP N)
			  (>= N 0)
			  (EQUAL (MOD N ,b) ,c))
		     (DIVIDES ,d (+ 1 (* ,a (EXPT 2 N)))))
	    :HINTS (("GOAL"
		     :USE ((:INSTANCE divisor-lemma- ,d (N (FLOOR N ,b)))))))
	 (generate-sierpinski-lemmas-a number (cdr cover))))
   nil))

(generate-sierpinski-lemmas-a  (expt 734110615000775 4)
			       '(3 17 257 641 65537 6700417))
==>
((DEFTHM
 DIVISOR-LEMMA-A- 3
 (IMPLIES
     (AND (INTEGERP N)
          (>= N 0)
          (EQUAL (MOD N 2) 1))
     (DIVIDES
          3
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA- 3 (N (FLOOR N 2)))))))

  etc)

Theorems in list submitted to ACL2 by hand after modifying name of theorem
and name in hint:
(DEFTHM
 DIVISOR-LEMMA-A-3
 (IMPLIES
     (AND (INTEGERP N)
          (>= N 0)
          (EQUAL (MOD N 2) 1))
     (DIVIDES
          3
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-3 (N (FLOOR N 2)))))))
============================|#
(DEFTHM
 DIVISOR-LEMMA-A-3
 (IMPLIES
     (AND (INTEGERP N)
          (>= N 0)
          (EQUAL (MOD N 2) 1))
     (DIVIDES
          3
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-3 (N (FLOOR N 2)))))))
(DEFTHM
 DIVISOR-LEMMA-A-17
 (IMPLIES
     (AND (INTEGERP N)
          (>= N 0)
          (EQUAL (MOD N 8) 4))
     (DIVIDES
          17
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-17 (N (FLOOR N 8)))))))
(DEFTHM
 DIVISOR-LEMMA-A-257
 (IMPLIES
     (AND (INTEGERP N)
          (>= N 0)
          (EQUAL (MOD N 16) 8))
     (DIVIDES
          257
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-257 (N (FLOOR N 16)))))))
(DEFTHM
 DIVISOR-LEMMA-A-641
 (IMPLIES
     (AND (INTEGERP N)
          (>= N 0)
          (EQUAL (MOD N 64) 32))
     (DIVIDES
          641
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-641 (N (FLOOR N 64)))))))
(DEFTHM
 DIVISOR-LEMMA-A-65537
 (IMPLIES
     (AND (INTEGERP N)
          (>= N 0)
          (EQUAL (MOD N 32) 16))
     (DIVIDES
          65537
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-65537 (N (FLOOR N 32)))))))
(DEFTHM
 DIVISOR-LEMMA-A-6700417
 (IMPLIES
     (AND (INTEGERP N)
          (>= N 0)
          (EQUAL (MOD N 64) 0))
     (DIVIDES
          6700417
          (+ 1
             (* 290433036530614504024730081259407069229771426966923250390625
                (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-6700417 (N (FLOOR N 64)))))))

;; Let i = 734110615000775, so k = i^4.

;; Then k * 2^(4n+2) + 1 = 2^2*(i*2^n)^4 + 1
;;                       = 4*(i*2^n)^4 + 1
;;                       = (2*(i*2^n)^2 + 2*(i*2^n) + 1)
;;                          * (2*(i*2^n)^2 - 2*(i*2^n) + 1)

;;k * 2^(4n+2) + 1 = 4 * k * 2^(4n) + 1
(defthm
 Algebra-lemma-1
 (implies (integerp n)
	   (equal (+ 1
		     (* k
			(expt 2
			      (+ 2
				 (* 4 n)))))
		  (+ 1
		     (* 4
			k
			(expt 2
			      (* 4 n))))))
 :hints (("Goal"
	   :use (:instance
		 (:theorem
		  (implies (equal x y)
			   (equal (+ 1 x)(+ 1 y))))
		 (x (* k
		       (expt 2
			     (+ 2
				(* 4 n)))))
		 (y (* 4
		       k
		       (expt 2
			     (* 4 n))))))))

;;i^4 * 2^(4n+2) + 1 = 4 * (i * (2^n))^4 + 1
(defthm
 Algebra-lemma-2
 (implies (integerp n)
	   (equal (+ 1
		     (* (expt i 4)
			(expt 2
			      (+ 2
				 (* 4 n)))))
		  (+ 1
		     (* 4
			(expt (* i
				 (expt 2
				       n))
			      4))))))

(defthm
 Algebra-lemma-3
 (equal (+ 1
	    (* 4
	       (expt (* i
			(expt 2
			      n))
		     4)))
	 (* (+ 1
	       (* 2
		  (* i
		     (expt 2
			   n)))
	       (* 2
		  (expt (* i
			   (expt 2
				 n))
			2)))
	    (+ 1
	       (* -2
		  (* i
		     (expt 2
			   n)))
	       (* 2
		  (expt (* i
			   (expt 2
				 n))
			2)))))
 :rule-classes nil
 :hints (("Goal"
	   :by (:instance
		(:theorem
		 (equal (+ 1
			   (* 4
			      (expt x 4)))
			(* (+ 1
			      (* 2
				 x)
			      (* 2
				 (expt x
				       2)))
			   (+ 1
			      (* -2
				 x)
			      (* 2
				 (expt x
				       2))))))
		(x (* i (expt 2 n)))))))

(defthm
 Algebra-lemma-4
 (implies (integerp n)
	   (equal (+ 1
		     (* (expt i 4)
			(expt 2
			      (+ 2
				 (* 4 n)))))
		  (* (+ 1
			(* 2
			   (* i
			      (expt 2
				    n)))
			(* 2
			   (expt (* i
				    (expt 2
					  n))
				 2)))
		     (+ 1
			(* -2
			   (* i
			      (expt 2
				    n)))
			(* 2
			   (expt (* i
				    (expt 2
					  n))
				 2))))))
 :hints (("Goal"
	   :in-theory (disable PREFER-POSITIVE-ADDENDS-EQUAL)
	   :use Algebra-lemma-3)))

(defthm
 factor-divides
 (implies (and (integerp x)
		(integerp y))
	   (divides x (* x y)))
 :rule-classes nil
 :hints (("Goal"
	   :in-theory (enable (:definition divides)))))

(defthm
 Algebra-lemma-5
 (implies (and (integerp i)
		(integerp n)
		(>= n 0))
	   (divides (+ 1
		       (* 2
			  (* i
			     (expt 2
				   n)))
		       (* 2
			  (expt (* i
				   (expt 2
					 n))
				2)))
		    (+ 1
		       (* (expt i 4)
			  (expt 2
				(+ 2
				   (* 4 n)))))))
 :rule-classes nil
 :hints (("Goal"
	   :use (:instance
		 factor-divides
		 (x (+ 1
		       (* 2
			  (* i
			     (expt 2
				   n)))
		       (* 2
			  (expt (* i
				   (expt 2
					 n))
				2))))
		 (y (+ 1
		       (* -2
			  (* i
			     (expt 2
				   n)))
		       (* 2
			  (expt (* i
				   (expt 2
					 n))
				2))))))))

(defthm
 Lemma-exceptional-case
 (implies (and (integerp n)
		(>= n 0))
	   (divides (+ 1
		       (* 2
			  (* 734110615000775
			     (expt 2
				   n)))
		       (* 2
			  (expt (* 734110615000775
				   (expt 2
					 n))
				2)))
		    (+ 1
		       (* (expt 734110615000775 4)
			  (expt 2
				(+ 2
				   (* 4 n)))))))
 :rule-classes nil
 :hints (("Goal"
	   :use (:instance
		 Algebra-lemma-5
		 (i 734110615000775)))))

;; (thm
;;   (equal (+ 1
;;             (* 2 (* 734110615000775 (expt 2 (floor n 4))))
;;             (* 2 (expt (* 734110615000775 (expt 2 (floor n 4)))
;;                        2)))
;;          (+ 1
;;             (* 1468221230001550 (expt 2 (floor n 4)))
;;             (* 1077836790113632192906501201250 (expt 2 (* 2 (floor n 4)))))))

(defthm
 Lemma-exceptional-case-a
 (implies (and (integerp n)
		(>= n 0)
		(equal (mod n 4) 2))
	   (divides (+ 1
		       (* 1468221230001550
			  (expt 2
				(floor n 4)))
		       (* 1077836790113632192906501201250
			  (expt 2
				(* 2
				   (floor n 4)))))
		    (+ 1
		       (* (expt 734110615000775 4)
			  (expt 2
				n)))))
 :rule-classes
 ((:rewrite
   :corollary
   (implies (and (integerp n)
		  (>= n 0)
		  (equal (mod n 4) 2))
	     (divides (+ 1
			 (* 1468221230001550
			    (expt 2
				  (floor n 4)))
			 (* 1077836790113632192906501201250
			    (expt 2
				  (* 2
				     (floor n 4)))))
		      (+ 1
			 (* 290433036530614504024730081259407069229771426966923250390625
			    (expt 2
				  n)))))))
 :hints (("Goal"
	   :use (:instance
		 Lemma-exceptional-case
		 (n (floor n 4))))))

(defthm
 integerp-exceptional-divisor
 (implies (and (integerp n)
		(>= n 0))
	   (integerp (+ 1
			(* 1468221230001550
			   (expt 2
				 (floor n 4)))
			(* 1077836790113632192906501201250
			   (expt 2
				 (* 2
				    (floor n 4)))))))
 :rule-classes :type-prescription)

;; x>1 => 2x^2 + 2x + 1 < 2x^4 + 2x^4 + 1
;;                      = 4x^4 + 1

(defthm
 Algebra-lemma-6
 (implies (and (integerp x)
		(> x 1))
	   (< (+ 1 (* 2 x)(* 2 (expt x 2)))
	      (+ 1 (* 4 (expt x 4)))))
 :rule-classes nil
 :hints (("Goal"
	   :use (:instance
		 (:theorem
		  (implies (< a b)
			   (< (+ 1 a)(+ 1 b))))
		 (a (+ (* 2 x)(* 2 (expt x 2))))
		 (b (* 4 (expt x 4)))))))

(defthm
 Exceptional-divisor<k*2^n+1
 (implies (and (integerp n)
		(>= n 0)
		(equal (mod n 4) 2))
	   (< (+ 1
		 (* 1468221230001550
		    (expt 2
			  (floor n 4)))
		 (* 1077836790113632192906501201250
		    (expt 2
			  (* 2
			     (floor n 4)))))
	      (+ 1
		 (* 290433036530614504024730081259407069229771426966923250390625
		    (expt 2
			  n)))))
 :rule-classes :linear
 :hints (("Goal"
	   :use (:instance
		 Algebra-lemma-6
		 (x (* 734110615000775
		       (expt 2 (floor n 4))))))))

#|============================
(defun generate-sierpinski-divisor-cases (triplets)
 (if (consp triplets)
     (let* ((triplet (car triplets))
	     (b (first triplet))
	     (c (second triplet))
	     (d (third triplet))
	     )
	(cons `((EQUAL (MOD N ,b) ,c) ,d)
	      (generate-sierpinski-divisor-cases (cdr triplets))))
     nil))

(defun generate-sierpinski-divisor-definition (triplets)
   `(DEFUN proper-divisor (N)
      (IF (INTEGERP N)
	   (COND ,@(generate-sierpinski-divisor-cases triplets))
	   0)))

(generate-sierpinski-divisor-definition '((2 1 3)
					  (8 4 17)
					  (16 8 257)
					  (64 32 641)
					  (32 16 65537)
					  (64 0 6700417)))
==>(DEFUN PROPER-DIVISOR (N)
    (IF (INTEGERP N)
	 (COND ((EQUAL (MOD N 2) 1) 3)
	       ((EQUAL (MOD N 8) 4) 17)
	       ((EQUAL (MOD N 16) 8) 257)
	       ((EQUAL (MOD N 64) 32) 641)
	       ((EQUAL (MOD N 32) 16) 65537)
	       ((EQUAL (MOD N 64) 0) 6700417))
	 0))
This defun must be modified for exceptional case.
============================|#
(DEFUN PROPER-DIVISOR (N)
    (IF (INTEGERP N)
	 (COND ((EQUAL (MOD N 2) 1) 3)
	       ((EQUAL (MOD N 8) 4) 17)
	       ((EQUAL (MOD N 16) 8) 257)
	       ((EQUAL (MOD N 64) 32) 641)
	       ((EQUAL (MOD N 32) 16) 65537)
	       ((EQUAL (MOD N 64) 0) 6700417)
	       ((equal (mod n 4) 2)
		(+ 1
		   (* 1468221230001550
		      (expt 2
			    (floor n 4)))
		   (* 1077836790113632192906501201250
		      (expt 2
			    (* 2
			       (floor n 4)))))))
	 0))

(defthm
 Integerp-proper-divisor
 (implies (and (integerp n)
		(>= n 0))
	   (integerp (proper-divisor n)))
 :rule-classes :type-prescription
 :hints (("Goal"
	   :use cover-thm)))

(defthm
 Proper-divisor>1
 (implies (and (integerp n)
		(>= n 0))
	   (< 1 (proper-divisor n)))
 :rule-classes nil
 :hints (("Goal"
	   :use Cover-thm)))

(defthm
 Proper-divisor<k*2^n+1
 (implies (and (integerp n)
		(>= n 0))
	   (< (proper-divisor n)
	      (+ 1
		 (* (expt 734110615000775 4)
		    (expt 2
			  n))))))

(defthm
 Proper-divisor-divides-k*2^n+1
 (implies (and (integerp n)
		(>= n 0))
	   (divides (proper-divisor n)
		    (+ 1
		       (* (expt 734110615000775 4)
			  (expt 2
				n)))))
 :hints (("Goal"
	   :use Cover-thm)))