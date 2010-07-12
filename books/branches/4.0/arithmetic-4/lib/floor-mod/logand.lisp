; Arithmetic-4 Library
; Copyright (C) 2008 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; logand.lisp
;;;
;;; A crude start on a book about logand and friends.
;;; One should look through the RTL and IHS books to get an
;;; idea of what others have found useful.
;;;
;;; What other logxxx ops should be here?
;;; logandc1, logandc2, logbitp, logcount, logeqv, logior, lognand,
;;; lognor, lognot, logorc1, logorc2, logtest, logxor are defined
;;; in ACL2.
;;;
;;; For the moment, we only treat lognot, logand, and logior.  I
;;; should look again, but I believe that lognot and logand (or,
;;; rather binary-logand) are the ``primitive'' definitions, and that
;;; the others are defined in terms of those two. 
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "../basic-ops/building-blocks")

(local
 (include-book "../basic-ops/top"))

(local
 (include-book "more-floor-mod"))

(local
 (include-book "floor-mod"))

(local
 (include-book "floor-mod-basic"))

(local
 (include-book "truncate-rem"))

(local
 (include-book "logand-helper"))

(local
 (set-default-hints '((nonlinearp-default-hint
		       stable-under-simplificationp hist pspv))))

(local
 (in-theory (e/d (ash-to-floor) (ash))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; logand associativity and commutativity:

(defthm |(logand y x)|
  (equal (logand y x)
	 (logand x y)))

(defthm |(logand (logand x y) z)|
  (equal (logand (logand x y) z)
	 (logand x y z)))

(defthm |(logand y x z)|
  (equal (logand y x z)
	 (logand x y z))
  :hints (("Goal" :use (:instance logand-y-x-z))))

(defthm |(logand c d x)|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (logand c d x)
		  (logand (logand c d) x))))

;;; ``Base'' theorems:

(defthm logand-0-x
  (equal (logand 0 x)
	 0))

(defthm logand-1-x
  (implies (integerp x)
	   (equal (logand 1 x)
		  (if (evenp x)
		      0
		    1)))
  :hints (("Goal" :expand ((logand 1 x)
			   (LOGAND 0 (FLOOR X 2))))))

(defthm logand--1-x
  (implies (integerp x)
	   (equal (logand -1 x)
		  x)))

(defthm logand-x-x
  (implies (integerp x)
	   (equal (logand x x)
		  x)))

;;; Misc:

(defthm |(equal (logand x y) -1)|
  (equal (equal (logand x y) -1)
	 (and (equal x -1)
	      (equal y -1))))

(defthm |(< (logand x y) 0)|
  (equal (< (logand x y) 0)
	 (and (integerp x)
	      (< x 0)
	      (integerp y)
	      (< y 0)))
  :rule-classes ((:rewrite)

;;; Make these linear also?

		 (:type-prescription
		  :corollary
		   (implies (and (integerp x)
				 (< x 0)
				 (integerp y)
				 (< y 0))
			    (and (integerp (logand x y))
				 (< (logand x y) 0))))
		 (:type-prescription
		  :corollary
		   (implies (and (integerp x)
				 (integerp y)
				 (<= 0 y))
			    (and (integerp (logand x y))
				 (<= 0 (logand x y)))))
		 (:type-prescription
		  :corollary
		   (implies (and (integerp x)
				 (<= 0 x)
				 (integerp y))
			    (and (integerp (logand x y))
				 (<= 0 (logand x y)))))))

;;; These next two should be generalized to any power of 2

(defthm |(floor (logand x y) 2)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (floor (logand x y) 2)
		  (logand (floor x 2) (floor y 2)))))

(defthm |(mod (logand x y) 2)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (mod (logand x y) 2)
		  (if (and (not (integerp (* 1/2 x)))
			   (not (integerp (* 1/2 y))))
		      1
		    0))))

(defthm |(integerp (* 1/2 (logand x y)))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (integerp (* 1/2 (logand x y)))
		  (or (integerp (* 1/2 x))
		      (integerp (* 1/2 y))))))

;;; Masks:

(local
 (defun ind-hint (x n)
   (declare (xargs :measure (nfix n)))
   (if (or (zip x) (zp n))
       t
     (ind-hint (floor x 2) (+ -1 n)))))

(defthm logand-mask
  (implies (and (integerp x) 
		(integerp n)
		(<= 0 n))
	   (equal (logand x (+ -1 (expt 2 n)))
		  (mod x (expt 2 n))))
  :hints (("Goal" :do-not '(generalize)
	   :in-theory (enable mod)
	   :cases ((equal n 0)))
	  ("Subgoal 2" :induct (ind-hint x n))))

(defun l-c-m-fn (c)  
  ;; logand-constant-mask, not least-common-multiple.  We need fewer
  ;; collisions among TLAs.
  (let ((n (power-of-2-minus-1 c)))
    (if n
	(list (cons 'n (kwote n)))
      nil)))

(defthm logand-constant-mask
 (implies (and (bind-free (l-c-m-fn c) (n))
	       (integerp n)
	       (<= 0 n)
	       (equal (+ -1 (expt 2 n)) c)
	       (integerp x) )
	  (equal (logand x c)
		 (mod x (+ 1 c)))))

(defthm logand-mask-shifted
  (implies (and (integerp x) 
		(integerp n1)
		(integerp n2)
		(<= 0 n1)
		(<= 0 n2))
	   (equal (logand x (* (expt 2 n1)
			       (+ -1 (expt 2 n2))))
		  (* (expt 2 n1)
		     (mod (floor x (expt 2 n1))
			  (expt 2 n2)))))
  :hints (("Goal" :do-not '(generalize)
	   :induct (ind-hint x n1))))

(in-theory (disable logand))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; logior associativity and commutativity:

(defthm |(logior y x)|
  (equal (logior y x)
	 (logior x y)))

(defthm |(logior (logior x y) z)|
  (equal (logior (logior x y) z)
	 (logior x y z)))

(defthm |(logior y x z)|
  (equal (logior y x z)
	 (logior x y z)))

(defthm |(logior c d x)|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (logior c d x)
		  (logior (logior c d) x))))

;;; ``Base'' theorems:

(defthm logior-0-x
  (implies (integerp x)
	   (equal (logior 0 x)
		  x)))

(defthm logior-1-x
  (implies (integerp x)
	   (equal (logior 1 x)
		  (if (evenp x)
		      (+ 1 x)
		    x)))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logior--1-x
  (implies (integerp x)
	   (equal (logior -1 x)
		  -1)))

(defthm logior-x-x
  (implies (integerp x)
	   (equal (logior x x)
		  x)))

;;; Misc:

(defthm |(equal (logior x y) 0)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (equal (logior x y) 0)
		  (and (equal x 0)
		       (equal y 0)))))

(defthm |(< (logior x y) 0)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (< (logior x y) 0)
		  (or (< x 0)
		      (< y 0))))
  :rule-classes ((:rewrite)
		 (:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< x 0))
			   (< (logior x y) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< y 0))
			   (< (logior x y) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< 0 x)
				(< 0 y))
			   (< 0 (logior x y))))))

;;; These next two should be generalized to any power of 2

(defthm |(floor (logior x y) 2)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (floor (logior x y) 2)
		  (logior (floor x 2) (floor y 2))))
  :hints (("Goal" :in-theory (enable logand))))

(defthm |(mod (logior x y) 2)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (mod (logior x y) 2)
		  (if (and (integerp (* 1/2 x))
			   (integerp (* 1/2 y)))
		      0
		    1))))

(defthm |(integerp (* 1/2 (logior x y)))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (integerp (* 1/2 (logior x y)))
		  (and (integerp (* 1/2 x))
		       (integerp (* 1/2 y))))))

(in-theory (disable logior))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; logxor associativity and commutativity:

(defthm |(logxor y x)|
  (equal (logxor y x)
	 (logxor x y)))
#|
(defthm |(logxor (logxor x y) z)|
  (equal (logxor (logxor x y) z)
	 (logxor x y z)))

(defthm |(logxor y x z)|
  (equal (logxor y x z)
	 (logxor x y z)))

(defthm |(logxor c d x)|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (logxor c d x)
		  (logxor (logxor c d) x))))
|#
;;; ``Base'' theorems:

(defthm logxor-0-x
  (implies (integerp x)
	   (equal (logxor 0 x)
		  x)))

(defthm logxor-1-x
  (implies (integerp x)
	   (equal (logxor 1 x)
		  (if (evenp x)
		      (+ 1 x)
		    (+ -1 x))))
  :hints (("Goal" :in-theory (enable logior 
				     logand))))

(defthm logxor--1-x
  (implies (integerp x)
	   (equal (logxor -1 x)
		  (lognot x))))

(defthm logxor-x-x
  (implies (integerp x)
	   (equal (logxor x x)
		  0))
  :hints (("Goal" :in-theory (enable logior 
				     logand))))

;;; Misc:



;;; These next two should be generalized to any power of 2

(defthm |(floor (logxor x y) 2)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (floor (logxor x y) 2)
		  (logxor (floor x 2) (floor y 2))))
  :hints (("Goal" :in-theory (enable logand
				     logior))))

(defthm |(mod (logxor x y) 2)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (mod (logxor x y) 2)
		  (logxor (mod x 2) (mod y 2)))))

(defthm |(integerp (* 1/2 (logxor x y)))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (integerp (* 1/2 (logxor x y)))
		  (iff (integerp (* 1/2 x))
		       (integerp (* 1/2 y))))))

(in-theory (disable logxor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; lognot

(defthm |(equal (lognot x) (lognot y))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (equal (lognot x) (lognot y))
		  (equal x y))))

(defthm |(equal (lognot x) -1)|
  (implies (integerp x)
	   (equal (equal (lognot x) -1)
		  (equal x 0))))

(defthm |(equal (lognot x) 0)|
  (equal (equal (lognot x) 0)
         (equal x -1)))

(defthm |(floor (lognot x) 2)|
  (implies (integerp x)
	   (equal (floor (lognot x) 2)
		  (lognot (floor x 2)))))

(defthm |(mod (lognot x) 2)|
  (implies (integerp x)
	   (equal (mod (lognot x) 2)
		  (if (integerp (* 1/2 x))
		      1
		    0))))

(defthm |(integerp (* 1/2 (lognot x)))|
  (implies (integerp x)
	   (equal (integerp (* 1/2 (lognot x)))
		  (not (integerp (* 1/2 x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm lognot-logand
  (implies (and (integerp x)
		(integerp y))
	   (equal (lognot (logand x y))
		  (logior (lognot x) (lognot y))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm lognot-logior
  (implies (and (integerp x)
		(integerp y))
	   (equal (lognot (logior x y))
		  (logand (lognot x) (lognot y))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm lognot-lognot
  (implies (integerp x)
	   (equal (lognot (lognot x))
		  x)))

(in-theory (disable lognot))
