;; Show k = 3896845303873881175159314620808887046066972469809^2
;;          = (expt 3896845303873881175159314620808887046066972469809 2)
;; is a Riesel number,
;; but no (complete) cover is known.

;; A Riesel number is an odd positive integer, k, such that no
;; positive integer in this infinite list is prime:

;;    k 2^1 - 1, k  2^2 - 1, k 2^3 - 1, ..., k 2^n - 1, ... .

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

;; A partial cover = (7 17 31 41 71 97 113 127 151 241 257 281 337
;;                      641 673 1321 14449 29191 65537 6700417)
;; Covers all n except (mod n 2) = 0.
;; For all positve integer n, if (mod n 2) = 1, then  k*2^n - 1 is divible
;; by a member of (7 17 31 41 71 97 113 127 151 241 257 281 337
;;                   641 673 1321 14449 29191 65537 6700417).

;; To show that k is a Riesel number,
;;  a divisor for k*2^n - 1 must be found for all positive
;;  integer n such that (mod n 2) = 0.

;; Such a divisor is constructed using these facts:

;;       k is a square

;;       a^2*x^2 - 1 = (a*x + 1) * (a*x - 1)

;; Let a = 3896845303873881175159314620808887046066972469809, so k = a^2.

;; Then k * 2^(2n) - 1 = (a*2^n + 1) * (a*2^n - 1)

#| To certify
  (certify-book "r-no-cover")
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
(defun find-riesel-b (i d)
 (declare (xargs :measure (nfix (- d i))))
 (if (and (integerp i)
	   (integerp d)
	   (< i d))
     (if (divides d (1- (expt 2 i)))
	  i
	  (find-riesel-b (1+ i) d))
     0))

(defun find-riesel-c (i b d number)
 (declare (xargs :measure (nfix (- b i))))
 (if (and (integerp i)
	   (integerp b)
	   (< i b))
     (if (divides d (1- (* number (expt 2 i))))
	  i
	  (find-riesel-c (1+ i) b d number))
     0))

(defun generate-riesel-triplets (number cover)
 (if (consp cover)
     (let* ((a number)
	     (d (car cover))
	     (b (find-riesel-b 1 d))
	     (c (find-riesel-c 0 b d a))
	     )
	(cons (list b c d)
	      (generate-riesel-triplets number (cdr cover))))
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
 (mod n 2) = 1,
(generate-riesel-triplets
(expt 3896845303873881175159314620808887046066972469809 2)
'(7 17 31 41 71 97 113 127 151 241 257 281 337 641 673 1321
  14449 29191 65537 6700417))
==>((3 2 7)
   (8 5 17)
   (5 0 31)
   (20 11 41)
   (35 14 71)
   (48 7 97)
   (28 15 113)
   (7 2 127)
   (15 12 151)
   (24 19 241)
   (16 9 257)
   (70 59 281)
   (21 18 337)
   (64 33 641)
   (48 31 673)
   (60 3 1321)
   (84 75 14449)
   (105 69 29191)
   (32 17 65537)
   (64 1 6700417))

Cover triplets for all n
==>((3 2 7)
   (8 5 17)
   (5 0 31)
   (20 11 41)
   (35 14 71)
   (48 7 97)
   (28 15 113)
   (7 2 127)
   (15 12 151)
   (24 19 241)
   (16 9 257)
   (70 59 281)
   (21 18 337)
   (64 33 641)
   (48 31 673)
   (60 3 1321)
   (84 75 14449)
   (105 69 29191)
   (32 17 65537)
   (64 1 6700417)
   (2 0 'expression))

Least common multiple of the moduli
(s-lcm-list (map-first '((3 2 7)
			 (8 5 17)
			 (5 0 31)
			 (20 11 41)
			 (35 14 71)
			 (48 7 97)
			 (28 15 113)
			 (7 2 127)
			 (15 12 151)
			 (24 19 241)
			 (16 9 257)
			 (70 59 281)
			 (21 18 337)
			 (64 33 641)
			 (48 31 673)
			 (60 3 1321)
			 (84 75 14449)
			 (105 69 29191)
			 (32 17 65537)
			 (64 1 6700417)
			 (2 0 'expression))))
==> 6720

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
 (let ((triplets '((3 2 7)
		    (8 5 17)
		    (5 0 31)
		    (20 11 41)
		    (35 14 71)
		    (48 7 97)
		    (28 15 113)
		    (7 2 127)
		    (15 12 151)
		    (24 19 241)
		    (16 9 257)
		    (70 59 281)
		    (21 18 337)
		    (64 33 641)
		    (48 31 673)
		    (60 3 1321)
		    (84 75 14449)
		    (105 69 29191)
		    (32 17 65537)
		    (64 1 6700417)
		    (2 0 'expression))))
   `(DEFUN COVER-ONE (N)
      (IF (INTEGERP N)
	   (OR ,@(generate-sierpinski-equalities triplets))
	   NIL))))

(generate-sierpinski-cover-one)
============================|#
;;==>
(DEFUN COVER-ONE (N)
      (IF (INTEGERP N)
          (OR (EQUAL (MOD N 3) 2)
              (EQUAL (MOD N 8) 5)
              (EQUAL (MOD N 5) 0)
              (EQUAL (MOD N 20) 11)
              (EQUAL (MOD N 35) 14)
              (EQUAL (MOD N 48) 7)
              (EQUAL (MOD N 28) 15)
              (EQUAL (MOD N 7) 2)
              (EQUAL (MOD N 15) 12)
              (EQUAL (MOD N 24) 19)
              (EQUAL (MOD N 16) 9)
              (EQUAL (MOD N 70) 59)
              (EQUAL (MOD N 21) 18)
              (EQUAL (MOD N 64) 33)
              (EQUAL (MOD N 48) 31)
              (EQUAL (MOD N 60) 3)
              (EQUAL (MOD N 84) 75)
              (EQUAL (MOD N 105) 69)
              (EQUAL (MOD N 32) 17)
              (EQUAL (MOD N 64) 1)
              (EQUAL (MOD N 2) 0))
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

; The following is needed for Lispworks 6.0.1 and maybe some other host Lisps,
; in order to avoid a stack overflow.
(comp 'cover)

(DEFTHM cover=>cover-one
 (IMPLIES (AND (INTEGERP N)(<= L N)(< N U)(cover L U))
	   (cover-one N))
 :RULE-CLASSES NIL
 :HINTS (("GOAL" :IN-THEORY (DISABLE (:DEFINITION cover-one)))))

#|============================
(defun generate-sierpinski-cover-cases-< ()
 (let* ((triplets '((3 2 7)
		     (8 5 17)
		     (5 0 31)
		     (20 11 41)
		     (35 14 71)
		     (48 7 97)
		     (28 15 113)
		     (7 2 127)
		     (15 12 151)
		     (24 19 241)
		     (16 9 257)
		     (70 59 281)
		     (21 18 337)
		     (64 33 641)
		     (48 31 673)
		     (60 3 1321)
		     (84 75 14449)
		     (105 69 29191)
		     (32 17 65537)
		     (64 1 6700417)
		     (2 0 'expression)))
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
       (IMPLIES (AND (INTEGERP N) (<= 0 N) (< N 6720))
                (OR (EQUAL (MOD N 3) 2)
                    (EQUAL (MOD N 8) 5)
                    (EQUAL (MOD N 5) 0)
                    (EQUAL (MOD N 20) 11)
                    (EQUAL (MOD N 35) 14)
                    (EQUAL (MOD N 48) 7)
                    (EQUAL (MOD N 28) 15)
                    (EQUAL (MOD N 7) 2)
                    (EQUAL (MOD N 15) 12)
                    (EQUAL (MOD N 24) 19)
                    (EQUAL (MOD N 16) 9)
                    (EQUAL (MOD N 70) 59)
                    (EQUAL (MOD N 21) 18)
                    (EQUAL (MOD N 64) 33)
                    (EQUAL (MOD N 48) 31)
                    (EQUAL (MOD N 60) 3)
                    (EQUAL (MOD N 84) 75)
                    (EQUAL (MOD N 105) 69)
                    (EQUAL (MOD N 32) 17)
                    (EQUAL (MOD N 64) 1)
                    (EQUAL (MOD N 2) 0)))
       :RULE-CLASSES NIL
       :HINTS (("GOAL" :USE ((:INSTANCE COVER=>COVER-ONE (L 0)
                                        (U 6720))))))
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
 (let* ((triplets '((3 2 7)
		     (8 5 17)
		     (5 0 31)
		     (20 11 41)
		     (35 14 71)
		     (48 7 97)
		     (28 15 113)
		     (7 2 127)
		     (15 12 151)
		     (24 19 241)
		     (16 9 257)
		     (70 59 281)
		     (21 18 337)
		     (64 33 641)
		     (48 31 673)
		     (60 3 1321)
		     (84 75 14449)
		     (105 69 29191)
		     (32 17 65537)
		     (64 1 6700417)
		     (2 0 'expression)))
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
                (OR (EQUAL (MOD (MOD N 6720) 3) 2)
                    (EQUAL (MOD (MOD N 6720) 8) 5)
                    (EQUAL (MOD (MOD N 6720) 5) 0)
                    (EQUAL (MOD (MOD N 6720) 20) 11)
                    (EQUAL (MOD (MOD N 6720) 35) 14)
                    (EQUAL (MOD (MOD N 6720) 48) 7)
                    (EQUAL (MOD (MOD N 6720) 28) 15)
                    (EQUAL (MOD (MOD N 6720) 7) 2)
                    (EQUAL (MOD (MOD N 6720) 15) 12)
                    (EQUAL (MOD (MOD N 6720) 24) 19)
                    (EQUAL (MOD (MOD N 6720) 16) 9)
                    (EQUAL (MOD (MOD N 6720) 70) 59)
                    (EQUAL (MOD (MOD N 6720) 21) 18)
                    (EQUAL (MOD (MOD N 6720) 64) 33)
                    (EQUAL (MOD (MOD N 6720) 48) 31)
                    (EQUAL (MOD (MOD N 6720) 60) 3)
                    (EQUAL (MOD (MOD N 6720) 84) 75)
                    (EQUAL (MOD (MOD N 6720) 105) 69)
                    (EQUAL (MOD (MOD N 6720) 32) 17)
                    (EQUAL (MOD (MOD N 6720) 64) 1)
                    (EQUAL (MOD (MOD N 6720) 2) 0)))
       :RULE-CLASSES NIL
       :HINTS (("GOAL" :USE ((:INSTANCE COVER-< (N (MOD N 6720)))))))

#|============================
(defun generate-sierpinski-cover-cases ()
 (let ((triplets '((3 2 7)
		    (8 5 17)
		    (5 0 31)
		    (20 11 41)
		    (35 14 71)
		    (48 7 97)
		    (28 15 113)
		    (7 2 127)
		    (15 12 151)
		    (24 19 241)
		    (16 9 257)
		    (70 59 281)
		    (21 18 337)
		    (64 33 641)
		    (48 31 673)
		    (60 3 1321)
		    (84 75 14449)
		    (105 69 29191)
		    (32 17 65537)
		    (64 1 6700417)
		    (2 0 'expression)))
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
                (OR (EQUAL (MOD N 3) 2)
                    (EQUAL (MOD N 8) 5)
                    (EQUAL (MOD N 5) 0)
                    (EQUAL (MOD N 20) 11)
                    (EQUAL (MOD N 35) 14)
                    (EQUAL (MOD N 48) 7)
                    (EQUAL (MOD N 28) 15)
                    (EQUAL (MOD N 7) 2)
                    (EQUAL (MOD N 15) 12)
                    (EQUAL (MOD N 24) 19)
                    (EQUAL (MOD N 16) 9)
                    (EQUAL (MOD N 70) 59)
                    (EQUAL (MOD N 21) 18)
                    (EQUAL (MOD N 64) 33)
                    (EQUAL (MOD N 48) 31)
                    (EQUAL (MOD N 60) 3)
                    (EQUAL (MOD N 84) 75)
                    (EQUAL (MOD N 105) 69)
                    (EQUAL (MOD N 32) 17)
                    (EQUAL (MOD N 64) 1)
                    (EQUAL (MOD N 2) 0)))
       :RULE-CLASSES NIL
       :HINTS (("GOAL" :USE ((:INSTANCE COVER-MOD)))))

;;Exceptional case is required:
(defthm
 Not-covered-by-part-cover
 (implies (or (equal n 4)
	       (equal n 6)
	       (equal n 22)
	       (equal n 34)
	       (equal n 46))
	   (and (equal (mod n 2)
		       0)
		(not (or (equal (mod n 3)  ;;Partial cover cases
				2)
			 (equal (mod n 8)
				5)
			 (equal (mod n 5)
				0)
			 (equal (mod n 20)
				11)
			 (equal (mod n 35)
				14)
			 (equal (mod n 48)
				7)
			 (equal (mod n 28)
				15)
			 (equal (mod n 7)
				2)
			 (equal (mod n 15)
				12)
			 (equal (mod n 24)
				19)
			 (equal (mod n 16)
				9)
			 (equal (mod n 70)
				59)
			 (equal (mod n 21)
				18)
			 (equal (mod n 64)
				33)
			 (equal (mod n 48)
				31)
			 (equal (mod n 60)
				3)
			 (equal (mod n 84)
				75)
			 (equal (mod n 105)
				69)
			 (equal (mod n 32)
				17)
			 (equal (mod n 64)
				1)))))
 :rule-classes nil)

(defun
natp-induction (n)
(if (zp n)
    t
    (natp-induction (- n 1))))

(encapsulate
(((aR) => *)
 ((bR) => *)
 ((cR) => *)
 ((dR) => *))

(local
 (defun
   aR ( )
   2))

(local
 (defun
   bR ( )
   2))

(local
 (defun
   cR ( )
   1))

(local
 (defun
   dR ( )
   3))

(defthm
  pos-int-aR
  (and (integerp (aR))
	(> (aR) 0))
  :rule-classes
  :type-prescription)

(defthm
  pos-int-bR
  (and (integerp (bR))
	(> (bR) 0))
  :rule-classes
  :type-prescription)

(defthm
  nat-int-cR
  (and (integerp (cR))
	(>= (cR) 0))
  :rule-classes
  :type-prescription)

(defthm
  pos-int-dR
  (and (integerp (dR))
	(> (dR) 0))
  :rule-classes
  :type-prescription)

(defthm
  Basis-condition-Riesel
  (divides (dR)
	    (+ -1
	       (* (aR)
		  (expt 2
			(cR))))))

(defthm
  Induction-condition-Riesel
  (divides (dR)
	    (+ -1
	       (expt 2
		     (bR)))))
) ;;end encapsulate

;; For integer n>=0, d | a*2^(b*n+cR)-1
(defthm
 Key-lemma-Riesel
 (implies (and (integerp n)
		(>= n 0))
	   (divides (dR)
		    (+ -1
		       (* (aR)
			  (expt 2
				(+ (cR)
				   (* (bR)
				      n)))))))
 :rule-classes nil
 :hints (("Goal"
	   :induct (natp-induction n))
	  ("Subgoal *1/2"
	   :use ((:instance
		  divides-+
		  (x (dR))
		  (y (+ -1 (* (aR)
			      (expt 2 (+ (- (bR))
					 (cR)
					 (* (bR)
					    n))))))
		  (z (* (aR)
			(expt 2 (+ (- (bR))
				   (cR)
				   (* (bR) n)))
			(+ -1 (expt 2 (bR))))))
		 (:instance
		  divides-*
		  (x (dR))
		  (y (+ -1 (expt 2 (bR))))
		  (z (* (aR)
			(expt 2
			      (+ (- (bR))
				 (cR)
				 (* (bR) n))))))))))

(in-theory (disable (:definition divides)))

#|============================
(defun generate-riesel-lemmas (number cover)
 (if (consp cover)
     (let* ((a number)
	     (d (car cover))
	     (b (find-riesel-b 1 d))
	     (c (find-riesel-c 0 b d a))
	     )
	(cons
	 `(DEFTHM divisor-lemma- ,d
	    (IMPLIES (AND (INTEGERP N)
			  (>= N 0))
		     (DIVIDES ,d (+ -1 (* ,a (EXPT 2 (+ ,c (* ,b N)))))))
	    :RULE-CLASSES NIL
	    :HINTS (("GOAL"
		     :USE ((:FUNCTIONAL-INSTANCE Key-Lemma-Riesel
						 (AR (LAMBDA () ,a))
						 (BR (LAMBDA () ,b))
						 (CR (LAMBDA () ,c))
						 (DR (LAMBDA () ,d)))))))
	 (generate-riesel-lemmas number (cdr cover))))
   nil))

(generate-riesel-lemmas
(expt 3896845303873881175159314620808887046066972469809 2)
'(7 17 31 41 71 97 113 127 151 241 257 281 337 641 673 1321
  14449 29191 65537 6700417))
==>
((DEFTHM
 DIVISOR-LEMMA- 7
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   7
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 2 (* 3 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 3))
     (CR (LAMBDA NIL 2))
     (DR (LAMBDA NIL 7)))))))

      etc)

Theorems in list submitted to ACL2 by hand after modifying name of theorem:
(DEFTHM
 DIVISOR-LEMMA-7
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   7
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 2 (* 3 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 3))
     (CR (LAMBDA NIL 2))
     (DR (LAMBDA NIL 7)))))))
============================|#
(DEFTHM
 DIVISOR-LEMMA-7
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   7
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 2 (* 3 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 3))
     (CR (LAMBDA NIL 2))
     (DR (LAMBDA NIL 7)))))))
(DEFTHM
 DIVISOR-LEMMA-17
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   17
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 5 (* 8 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 8))
     (CR (LAMBDA NIL 5))
     (DR (LAMBDA NIL 17)))))))
(DEFTHM
 DIVISOR-LEMMA-31
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   31
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 0 (* 5 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 5))
     (CR (LAMBDA NIL 0))
     (DR (LAMBDA NIL 31)))))))
(DEFTHM
 DIVISOR-LEMMA-41
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   41
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 11 (* 20 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 20))
     (CR (LAMBDA NIL 11))
     (DR (LAMBDA NIL 41)))))))
(DEFTHM
 DIVISOR-LEMMA-71
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   71
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 14 (* 35 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 35))
     (CR (LAMBDA NIL 14))
     (DR (LAMBDA NIL 71)))))))
(DEFTHM
 DIVISOR-LEMMA-97
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   97
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 7 (* 48 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 48))
     (CR (LAMBDA NIL 7))
     (DR (LAMBDA NIL 97)))))))
(DEFTHM
 DIVISOR-LEMMA-113
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   113
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 15 (* 28 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 28))
     (CR (LAMBDA NIL 15))
     (DR (LAMBDA NIL 113)))))))
(DEFTHM
 DIVISOR-LEMMA-127
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   127
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 2 (* 7 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 7))
     (CR (LAMBDA NIL 2))
     (DR (LAMBDA NIL 127)))))))
(DEFTHM
 DIVISOR-LEMMA-151
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   151
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 12 (* 15 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 15))
     (CR (LAMBDA NIL 12))
     (DR (LAMBDA NIL 151)))))))
(DEFTHM
 DIVISOR-LEMMA-241
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   241
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 19 (* 24 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 24))
     (CR (LAMBDA NIL 19))
     (DR (LAMBDA NIL 241)))))))
(DEFTHM
 DIVISOR-LEMMA-257
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   257
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 9 (* 16 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 16))
     (CR (LAMBDA NIL 9))
     (DR (LAMBDA NIL 257)))))))
(DEFTHM
 DIVISOR-LEMMA-281
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   281
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 59 (* 70 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 70))
     (CR (LAMBDA NIL 59))
     (DR (LAMBDA NIL 281)))))))
(DEFTHM
 DIVISOR-LEMMA-337
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   337
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 18 (* 21 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 21))
     (CR (LAMBDA NIL 18))
     (DR (LAMBDA NIL 337)))))))
(DEFTHM
 DIVISOR-LEMMA-641
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   641
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 33 (* 64 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 64))
     (CR (LAMBDA NIL 33))
     (DR (LAMBDA NIL 641)))))))
(DEFTHM
 DIVISOR-LEMMA-673
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   673
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 31 (* 48 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 48))
     (CR (LAMBDA NIL 31))
     (DR (LAMBDA NIL 673)))))))
(DEFTHM
 DIVISOR-LEMMA-1321
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   1321
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 3 (* 60 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 60))
     (CR (LAMBDA NIL 3))
     (DR (LAMBDA NIL 1321)))))))
(DEFTHM
 DIVISOR-LEMMA-14449
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   14449
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 75 (* 84 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 84))
     (CR (LAMBDA NIL 75))
     (DR (LAMBDA NIL 14449)))))))
(DEFTHM
 DIVISOR-LEMMA-29191
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   29191
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 69 (* 105 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 105))
     (CR (LAMBDA NIL 69))
     (DR (LAMBDA NIL 29191)))))))
(DEFTHM
 DIVISOR-LEMMA-65537
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   65537
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 17 (* 32 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 32))
     (CR (LAMBDA NIL 17))
     (DR (LAMBDA NIL 65537)))))))
(DEFTHM
 DIVISOR-LEMMA-6700417
 (IMPLIES
  (AND (INTEGERP N) (>= N 0))
  (DIVIDES
   6700417
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 (+ 1 (* 64 N)))))))
 :RULE-CLASSES NIL
 :HINTS
 (("GOAL"
   :USE
   ((:FUNCTIONAL-INSTANCE
     KEY-LEMMA-RIESEL
     (AR
      (LAMBDA
       NIL
       15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481))
     (BR (LAMBDA NIL 64))
     (CR (LAMBDA NIL 1))
     (DR (LAMBDA NIL 6700417)))))))

#|============================
(defun generate-riesel-lemmas-a (number cover)
 (if (consp cover)
     (let* ((a number)
	     (d (car cover))
	     (b (find-riesel-b 1 d))
	     (c (find-riesel-c 0 b d a))
	     )
	(cons
	 `(DEFTHM divisor-lemma-a- ,d
	    (IMPLIES (AND (INTEGERP N)
			  (>= N 0)
			  (EQUAL (MOD N ,b) ,c))
		     (DIVIDES ,d (+ -1 (* ,a (EXPT 2 N)))))
	    :HINTS (("GOAL"
		     :USE ((:INSTANCE divisor-lemma- ,d (N (FLOOR N ,b)))))))
	 (generate-riesel-lemmas-a number (cdr cover))))
   nil))

(generate-riesel-lemmas-a
(expt 3896845303873881175159314620808887046066972469809 2)
'(7 17 31 41 71 97 113 127 151 241 257 281 337 641 673 1321
  14449 29191 65537 6700417))
==>
((DEFTHM
 DIVISOR-LEMMA-A- 7
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 3) 2))
  (DIVIDES
   7
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA- 7 (N (FLOOR N 3)))))))

                etc)

Theorems in list submitted to ACL2 by hand after modifying name of theorem
and name in hint:
(DEFTHM
 DIVISOR-LEMMA-A-7
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 3) 2))
  (DIVIDES
   7
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-7 (N (FLOOR N 3)))))))
============================|#
(DEFTHM
 DIVISOR-LEMMA-A-7
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 3) 2))
  (DIVIDES
   7
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-7 (N (FLOOR N 3)))))))
(DEFTHM
 DIVISOR-LEMMA-A-17
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 8) 5))
  (DIVIDES
   17
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-17 (N (FLOOR N 8)))))))
(DEFTHM
 DIVISOR-LEMMA-A-31
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 5) 0))
  (DIVIDES
   31
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-31 (N (FLOOR N 5)))))))
(DEFTHM
 DIVISOR-LEMMA-A-41
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 20) 11))
  (DIVIDES
   41
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-41 (N (FLOOR N 20)))))))
(DEFTHM
 DIVISOR-LEMMA-A-71
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 35) 14))
  (DIVIDES
   71
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-71 (N (FLOOR N 35)))))))
(DEFTHM
 DIVISOR-LEMMA-A-97
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 48) 7))
  (DIVIDES
   97
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-97 (N (FLOOR N 48)))))))
(DEFTHM
 DIVISOR-LEMMA-A-113
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 28) 15))
  (DIVIDES
   113
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-113 (N (FLOOR N 28)))))))
(DEFTHM
 DIVISOR-LEMMA-A-127
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 7) 2))
  (DIVIDES
   127
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-127 (N (FLOOR N 7)))))))
(DEFTHM
 DIVISOR-LEMMA-A-151
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 15) 12))
  (DIVIDES
   151
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-151 (N (FLOOR N 15)))))))
(DEFTHM
 DIVISOR-LEMMA-A-241
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 24) 19))
  (DIVIDES
   241
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-241 (N (FLOOR N 24)))))))
(DEFTHM
 DIVISOR-LEMMA-A-257
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 16) 9))
  (DIVIDES
   257
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-257 (N (FLOOR N 16)))))))
(DEFTHM
 DIVISOR-LEMMA-A-281
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 70) 59))
  (DIVIDES
   281
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-281 (N (FLOOR N 70)))))))
(DEFTHM
 DIVISOR-LEMMA-A-337
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 21) 18))
  (DIVIDES
   337
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-337 (N (FLOOR N 21)))))))
(DEFTHM
 DIVISOR-LEMMA-A-641
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 64) 33))
  (DIVIDES
   641
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-641 (N (FLOOR N 64)))))))
(DEFTHM
 DIVISOR-LEMMA-A-673
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 48) 31))
  (DIVIDES
   673
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-673 (N (FLOOR N 48)))))))
(DEFTHM
 DIVISOR-LEMMA-A-1321
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 60) 3))
  (DIVIDES
   1321
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-1321 (N (FLOOR N 60)))))))
(DEFTHM
 DIVISOR-LEMMA-A-14449
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 84) 75))
  (DIVIDES
   14449
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-14449 (N (FLOOR N 84)))))))
(DEFTHM
 DIVISOR-LEMMA-A-29191
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 105) 69))
  (DIVIDES
   29191
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-29191 (N (FLOOR N 105)))))))
(DEFTHM
 DIVISOR-LEMMA-A-65537
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 32) 17))
  (DIVIDES
   65537
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-65537 (N (FLOOR N 32)))))))
(DEFTHM
 DIVISOR-LEMMA-A-6700417
 (IMPLIES
  (AND (INTEGERP N)
       (>= N 0)
       (EQUAL (MOD N 64) 1))
  (DIVIDES
   6700417
   (+
    -1
    (*
     15185403322323921315363059221894499813326933057733071440861144571601117057698737700140317416496481
     (EXPT 2 N)))))
 :HINTS (("GOAL" :USE ((:INSTANCE DIVISOR-LEMMA-6700417 (N (FLOOR N 64)))))))

;; Let a = 3896845303873881175159314620808887046066972469809, so k = a^2.

;; Then k * 2^(2n) - 1 = (a*2^n + 1) * (a*2^n - 1)

(defthm
 Algebra-lemma-1
 (implies (integerp n)
	   (equal (+ -1
		     (* (expt a 2)
			(expt 2 (* 2 n))))
		  (* (+ 1
			(* a
			   (expt 2 n)))
		     (+ -1
			(* a
			   (expt 2 n))))))
 :rule-classes nil)

(defthm
 factor-divides
 (implies (and (integerp x)
		(integerp y))
	   (divides x (* x y)))
 :rule-classes nil
 :hints (("Goal"
	   :in-theory (enable (:definition divides)))))

(defthm
 Algebra-lemma-2
 (implies (and (integerp a)
		(integerp n)
		(>= n 0))
	   (divides (+ 1
		       (* a
			  (expt 2 n)))
		    (+ -1
		       (* (expt a 2)
			  (expt 2 (* 2 n))))))
 :rule-classes nil
 :hints (("Goal"
	   :use ((:instance
		  factor-divides
		  (x (+ 1
			(* a
			   (expt 2 n))))
		  (y (+ -1
			(* a
			  (expt 2 n)))))
		 Algebra-lemma-1))))

(defthm
 Lemma-exceptional-case
 (implies (and (integerp n)
		(>= n 0)
		(equal (mod n 2) 0))
	   (divides (+ 1
		       (* 3896845303873881175159314620808887046066972469809
			  (expt 2 (floor n 2))))
		    (+ -1
		       (* (expt 3896845303873881175159314620808887046066972469809 2)
			  (expt 2 n)))))
 :rule-classes nil
 :hints (("Goal"
	   :use (:instance
		 Algebra-lemma-2
		 (a 3896845303873881175159314620808887046066972469809)
		 (n (floor n 2))))))

(defthm
 Algebra-lemma-3
 (implies (and (integerp x)
		(< 2 x))
	   (< (+ 1 x)
	      (+ -1 (expt x 2))))
 :rule-classes nil
 :hints (("Goal"
	   :use (:instance
		 (:theorem
		  (implies (and (integerp a)
				(< 0 a)
				(< b c))
			   (< (* a b)(* a c))))
		 (a (+ 1 x))
		 (b 1)
		 (c (+ -1 x))))))

(defthm
 Algebra-lemma-4
 (implies (and (integerp w)
		(< 0 w)
		(<= w x)
		(integerp z)
		(< 0 z)
		(< y z))
	   (< (* w y)(* x z)))
 :rule-classes nil
 :hints (("Goal"
	   :use ((:instance
		  (:theorem
		   (implies (and (integerp a)
				 (< 0 a)
				 (< b c))
			    (< (* a b)(* a c))))
		  (a w)
		  (b y)
		  (c z))
		 (:instance
		  (:theorem
		   (implies (and (integerp a)
				 (< 0 a)
				 (<= b c))
			    (<= (* a b)(* a c))))
		  (a z)
		  (b w)
		  (c x))
		 (:instance
		  (:theorem
		   (implies (and (< a b)
				 (<= b c))
			    (< a c)))
		  (a (* w y))
		  (b (* w z))
		  (c (* x z)))))))

(defthm
 Algebra-lemma-5
 (implies (and (integerp n)
		(>= n 0)
		(integerp a)
		(< 2 a))
	   (< (+ 1 (* a (expt 2 n)))
	      (+ -1 (* (expt a 2)
		       (expt 2 (* 2 n))))))
 :rule-classes nil
 :hints (("Goal"
	   :use ((:instance
		  Algebra-lemma-3
		  (x (* a (expt 2 n))))
		 (:instance
		  Algebra-lemma-4
		  (w 1)
		  (x (expt 2 n))
		  (y 2)
		  (z a))))))

(defthm
 Exceptional-divisor<k*2^n-1
 (implies (and (integerp n)
		(>= n 0)
		(equal (mod n 2) 0))
	   (< (+ 1
		 (* 3896845303873881175159314620808887046066972469809
		    (expt 2 (floor n 2))))
	      (+ -1
		 (* (expt 3896845303873881175159314620808887046066972469809 2)
		    (expt 2 n)))))
 :rule-classes nil
 :hints (("Goal"
	   :in-theory (disable SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<)
	   :use ((:instance
		  Algebra-lemma-5
		  (a 3896845303873881175159314620808887046066972469809)
		  (n (floor n 2)))))))

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

(generate-sierpinski-divisor-definition '((3 2 7)
					  (8 5 17)
					  (5 0 31)
					  (20 11 41)
					  (35 14 71)
					  (48 7 97)
					  (28 15 113)
					  (7 2 127)
					  (15 12 151)
					  (24 19 241)
					  (16 9 257)
					  (70 59 281)
					  (21 18 337)
					  (64 33 641)
					  (48 31 673)
					  (60 3 1321)
					  (84 75 14449)
					  (105 69 29191)
					  (32 17 65537)
					  (64 1 6700417)))
==>(DEFUN PROPER-DIVISOR (N)
    (IF (INTEGERP N)
	 (COND ((EQUAL (MOD N 3) 2) 7)
	       ((EQUAL (MOD N 8) 5) 17)
	       ((EQUAL (MOD N 5) 0) 31)
	       ((EQUAL (MOD N 20) 11) 41)
	       ((EQUAL (MOD N 35) 14) 71)
	       ((EQUAL (MOD N 48) 7) 97)
	       ((EQUAL (MOD N 28) 15) 113)
	       ((EQUAL (MOD N 7) 2) 127)
	       ((EQUAL (MOD N 15) 12) 151)
	       ((EQUAL (MOD N 24) 19) 241)
	       ((EQUAL (MOD N 16) 9) 257)
	       ((EQUAL (MOD N 70) 59) 281)
	       ((EQUAL (MOD N 21) 18) 337)
	       ((EQUAL (MOD N 64) 33) 641)
	       ((EQUAL (MOD N 48) 31) 673)
	       ((EQUAL (MOD N 60) 3) 1321)
	       ((EQUAL (MOD N 84) 75) 14449)
	       ((EQUAL (MOD N 105) 69) 29191)
	       ((EQUAL (MOD N 32) 17) 65537)
	       ((EQUAL (MOD N 64) 1) 6700417))
	 0))
This defun must be modified for exceptional case.
============================|#
(DEFUN PROPER-DIVISOR (N)
      (IF (INTEGERP N)
          (COND ((EQUAL (MOD N 3) 2) 7)
                ((EQUAL (MOD N 8) 5) 17)
                ((EQUAL (MOD N 5) 0) 31)
                ((EQUAL (MOD N 20) 11) 41)
                ((EQUAL (MOD N 35) 14) 71)
                ((EQUAL (MOD N 48) 7) 97)
                ((EQUAL (MOD N 28) 15) 113)
                ((EQUAL (MOD N 7) 2) 127)
                ((EQUAL (MOD N 15) 12) 151)
                ((EQUAL (MOD N 24) 19) 241)
                ((EQUAL (MOD N 16) 9) 257)
                ((EQUAL (MOD N 70) 59) 281)
                ((EQUAL (MOD N 21) 18) 337)
                ((EQUAL (MOD N 64) 33) 641)
                ((EQUAL (MOD N 48) 31) 673)
                ((EQUAL (MOD N 60) 3) 1321)
                ((EQUAL (MOD N 84) 75) 14449)
                ((EQUAL (MOD N 105) 69) 29191)
                ((EQUAL (MOD N 32) 17) 65537)
                ((EQUAL (MOD N 64) 1) 6700417)
		 ((equal (mod n 2) 0)    ;; Exceptional case
		  (+ 1
		     (* 3896845303873881175159314620808887046066972469809
			(expt 2 (floor n 2))))))
          0))

(defthm
 Integerp-proper-divisor
 (implies (and (integerp n)
		(>= n 0))
	   (integerp (proper-divisor n)))
 :rule-classes nil
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
 Proper-divisor<k*2^n-1
 (implies (and (integerp n)
		(>= n 0))
	   (< (proper-divisor n)
	      (+ -1
		 (* (expt 3896845303873881175159314620808887046066972469809 2)
		    (expt 2 n)))))
 :rule-classes nil
 :hints (("Subgoal 4"
	   :use Exceptional-divisor<k*2^n-1)))

(defthm
 Proper-divisor-divides-k*2^n-1
 (implies (and (integerp n)
		(>= n 0))
	   (divides (proper-divisor n)
		    (+ -1
		       (* (expt 3896845303873881175159314620808887046066972469809 2)
			  (expt 2 n)))))
 :rule-classes nil
 :hints (("Subgoal 5"
	   :use cover-thm)
	  ("Subgoal 4"
	   :use Lemma-exceptional-case)))