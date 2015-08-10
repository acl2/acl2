; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; floor-mod-basic-helper.lisp
;;;
;; This book contains some messy proofs which I want to hide.
;; There is probably nothing to be gained by looking at it.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(IN-PACKAGE "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(table acl2-defaults-table :state-ok t)

(include-book "../basic-ops/building-blocks")

(local
 (include-book "forcing-types"))

(local
 (include-book "../basic-ops/top"))

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Floor (and hence mod) are built on to pf
;;; nonnegative-integer-quotient.  Here is what we need to know about
;;; it.

(local
 (defthm niq-bounds
   (implies (and (integerp i)
		 (<= 0 i)
		 (integerp j)
		 (< 0 j))
	    (and (<= (nonnegative-integer-quotient i j)
		     (/ i j))
		 (< (+ (/ i j) -1)
		    (nonnegative-integer-quotient i j))))
   :rule-classes ((:linear
		   :trigger-terms ((nonnegative-integer-quotient i j))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Basic theorems about floor and mod

;;(defthm floor-integerp
;;  (integerp (floor x y)))

(defthm integerp-mod
  (implies (and (integerp x)
		(integerp y))
	   (integerp (mod x y)))
  :rule-classes (:rewrite :type-prescription))

#-non-standard-analysis
(defthm rationalp-mod
  (implies (rationalp x)
           (rationalp (mod x y)))
  :hints (("Goal" :cases ((rationalp y))))
  :rule-classes (:rewrite :type-prescription))

#+non-standard-analysis
(defthm rationalp-mod
  (implies (and (rationalp x)
		(rationalp y))
           (rationalp (mod x y)))
  :rule-classes (:rewrite :type-prescription))

#+non-standard-analysis
(defthm realp-mod
  (implies (real/rationalp x)
           (real/rationalp (mod x y)))
  :hints (("Goal" :cases ((real/rationalp y))))
  :rule-classes (:rewrite :type-prescription))

(defthm floor-mod-elim
  (implies (acl2-numberp x)
	   (equal (+ (mod x y)
		     (* y (floor x y)))
		  x))
  :hints (("Goal" :in-theory (disable floor)))
  :rule-classes ((:rewrite)
		 (:elim)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm linear-floor-bounds-1
  (implies (real/rationalp (/ x y))
	   (and (< (+ (/ x y) -1)
		   (floor x y))
		(<= (floor x y)
		    (/ x y))))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))))

(defthm linear-floor-bounds-2
  (implies (integerp (/ x y))
	   (equal (floor x y)
		  (/ x y)))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))))

(defthm linear-floor-bounds-3
  (implies (and (real/rationalp (/ x y))
		(not (integerp (/ x y))))
	   (< (floor x y)
	      (/ x y)))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))))

(encapsulate
 ()

 (local
  (defthm hack0
    (implies (and (real/rationalp x)
		  (real/rationalp y)
		  (real/rationalp z))
	     (equal (* z (complex x y))
		    (complex (* x z) (* y z))))
    :hints (("Goal" :use ((:instance complex-definition)
			  (:instance complex-definition
				     (x (* x z))
				     (y (* y z)))))
	    ("Goal'4'" :use ((:instance distributivity
					(x z)
					(y x)
					(z (* #c(0 1) y))))))))

 (local
  (defthm hack1
    (implies (and (real/rationalp x)
		  (real/rationalp y))
	     (equal (real/rationalp (complex x y))
		    (equal y 0)))))

 (local
  (defthm hack2
    (implies (and (acl2-numberp x)
		  (real/rationalp y))
	     (and (equal (realpart (* x y))
			 (* y (realpart x)))
		  (equal (imagpart (* x y))
			 (* y (imagpart x)))))))

 (local
  (defthm hack3
    (implies (and (acl2-numberp x)
		  (real/rationalp y)
		  (not (equal y 0)))
	     (equal (real/rationalp (* x y))
		    (equal (imagpart x) 0)))
    :hints (("Goal" :cases ((real/rationalp x)
			    (complex-rationalp x))))))

 (local
  (defthm foo-1
    (implies (and (acl2-numberp x)
		  (< 0 x)
		  (real/rationalp y)
		  (real/rationalp z)
		  (< y z))
	     (< (* x y) (* x z)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x y))
				     (y (* x z)))
			  (:instance completion-of-<
				     (x 0)
				     (y x))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0))))
    :otf-flg t))

 (local
  (defthm foo-2
    (implies (and (acl2-numberp x)
		  (< 0 x)
		  (real/rationalp y)
		  (real/rationalp z)
		  (<= y z))
	     (<= (* x y) (* x z)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x z))
				     (y (* x y)))
			  (:instance completion-of-<
				     (x x)
				     (y 0))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0))))))

 (local
  (defthm foo-3
    (implies (and (acl2-numberp x)
		  (< x 0)
		  (real/rationalp y)
		  (real/rationalp z)
		  (< y z))
	     (< (* x z) (* x y)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x z))
				     (y (* x y)))
			  (:instance completion-of-<
				     (x x)
				     (y 0))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0))))))

 (local
  (defthm foo-4
    (implies (and (acl2-numberp x)
		  (< x 0)
		  (real/rationalp y)
		  (real/rationalp z)
		  (<= y z))
	     (<= (* x z) (* x y)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x y))
				     (y (* x z)))
			  (:instance completion-of-<
				     (x 0)
				     (y x))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0))))))

 (defthm mod-bounds-1
   (implies (and (real/rationalp (/ x y))
		 (< 0 y))
	    (and (<= 0 (mod x y))
		 (< (mod x y) y)))
   :rule-classes ((:generalize)
		  (:linear))
   :hints (("Goal" :use (:instance linear-floor-bounds-1)
	    :in-theory (disable floor))
	   ("Subgoal 1'" :use (:instance foo-1
					 (x y)
					 (y (* x (/ y)))
					 (z (+ 1 (floor x y))))
	    :in-theory (disable foo-1 floor))
	   ("Subgoal 2'" :use (:instance foo-2
					 (x y)
					 (y (floor x y))
					 (z (* x (/ y))))
	    :in-theory (disable foo-2 floor)))
   :otf-flg t)

 (defthm mod-bounds-2
   (implies (and (real/rationalp (/ x y))
		 (< y 0))
	    (and (<= (mod x y) 0)
		 (< y (mod x y))))
   :rule-classes ((:generalize)
		  (:linear))
  :hints (("Goal" :use (:instance linear-floor-bounds-1)
				       :in-theory (disable floor))
		  ("Subgoal 1'" :use (:instance foo-3
						(x y)
						(y (* x (/ y)))
						(z (+ 1 (floor x y))))
		   :in-theory (disable foo-1 floor))
		  ("Subgoal 2'" :use (:instance foo-4
						(x y)
						(y (floor x y))
						(z (* x (/ y))))
		   :in-theory (disable foo-2 floor)))
   :otf-flg t)

 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable floor mod))

(encapsulate
 ()

 (local
  (defthm hack0
    (implies (and (real/rationalp x)
		  (real/rationalp y)
		  (real/rationalp z))
	     (equal (* z (complex x y))
		    (complex (* x z) (* y z))))
    :hints (("Goal" :use ((:instance complex-definition)
			  (:instance complex-definition
				     (x (* x z))
				     (y (* y z)))))
	    ("Goal'4'" :use ((:instance distributivity
					(x z)
					(y x)
					(z (* #c(0 1) y))))))))

 (local
  (defthm hack1
    (implies (and (real/rationalp x)
		  (real/rationalp y))
	     (equal (real/rationalp (complex x y))
		    (equal y 0)))))

 (local
  (defthm hack2
    (implies (and (acl2-numberp x)
		  (real/rationalp y))
	     (and (equal (realpart (* x y))
			 (* y (realpart x)))
		  (equal (imagpart (* x y))
			 (* y (imagpart x)))))))

 (local
  (defthm hack3
    (implies (and (acl2-numberp x)
		  (real/rationalp y)
		  (not (equal y 0)))
	     (equal (real/rationalp (* x y))
		    (equal (imagpart x) 0)))
    :hints (("Goal" :cases ((real/rationalp x)
			    (complex-rationalp x))))))

 (local
  (defthm foo-1
    (implies (and (acl2-numberp x)
		  (< 0 x)
		  (real/rationalp y)
		  (real/rationalp z)
		  (< y z))
	     (< (* x y) (* x z)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x y))
				     (y (* x z)))
			  (:instance completion-of-<
				     (x 0)
				     (y x))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0))))
    :otf-flg t))

 (local
  (defthm foo-2
    (implies (and (acl2-numberp x)
		  (<= 0 x)
		  (real/rationalp y)
		  (real/rationalp z)
		  (<= y z))
	     (<= (* x y) (* x z)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x z))
				     (y (* x y)))
			  (:instance completion-of-<
				     (x x)
				     (y 0))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0))))))

 (local
  (defthm foo-3
    (implies (and (acl2-numberp x)
		  (< x 0)
		  (real/rationalp y)
		  (real/rationalp z)
		  (< y z))
	     (< (* x z) (* x y)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x z))
				     (y (* x y)))
			  (:instance completion-of-<
				     (x x)
				     (y 0))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0))))))

 (local
  (defthm foo-4
    (implies (and (acl2-numberp x)
		  (<= x 0)
		  (real/rationalp y)
		  (real/rationalp z)
		  (<= y z))
	     (<= (* x z) (* x y)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x y))
				     (y (* x z)))
			  (:instance completion-of-<
				     (x 0)
				     (y x))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0))))))

 (local
  (defthm floor-rule-1
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		  (real/rationalp (/ x y)))
	     (equal (< 0 (floor x y))
		    (<= 1 (/ x y))))))

 (local
  (defthm bar-1
    (implies (real/rationalp (/ x y))
	     (equal (< (/ x y) 1)
		    (not (or (and (< 0 y)
				  (<= y x))
			     (and (< y 0)
				  (<= x y))))))
    :hints (("Subgoal 7" :use (:instance foo-1
					 (x y)
					 (y (* x (/ y)))
					 (z 1)))
	    ("Subgoal 6" :use (:instance foo-3
					 (x y)
					 (y (* x (/ y)))
					 (z 1)))
	    ("Subgoal 4" :use (:instance foo-4
					 (x y)
					 (y 1)
					 (z (* x (/ y)))))
	    ("Subgoal 3" :use (:instance foo-3
					 (x y)
					 (y (* x (/ y)))
					 (z 1)))
	    ("Subgoal 1" :use (:instance foo-2
					 (x y)
					 (z (* x (/ y)))
					 (y 1))))
    :otf-flg t))

 (local
  (defthm floor-rule-2
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		  (acl2-numberp x)
		  (acl2-numberp y)
		  (real/rationalp (/ x y)))
	     (equal (< (floor x y) 0)
		    (< (/ x y) 0)))
    :otf-flg t))

 (local
  (defthm bar-2
    (implies (real/rationalp (/ x y))
	     (equal (< (/ x y) 0)
		    (or (and (< 0 y)
			     (< x 0))
			(and (< y 0)
			     (< 0 x)))))
    :hints (("Subgoal 6'" :use (:instance foo-2
					  (x y)
					  (y 0)
					  (z (* x (/ y)))))
	    ("Subgoal 5" :use (:instance foo-3
					 (x y)
					 (y (* x (/ y)))
					 (z 0)))
	    ("Subgoal 2" :use (:instance foo-1
					 (x y)
					 (y (* x (/ y)))
					 (z 0)))
	    ("Subgoal 1'" :use (:instance foo-4
					  (x y)
					  (y 0)
					  (z (* x (/ y))))))
    :otf-flg t))

 (local
  (prefer-positive-exponents))

 (defthm floor-positive
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                (real/rationalp (/ x y)))
           (equal (< 0 (floor x y))
                  (or (and (< 0 y)
                           (<= y x))
                      (and (< y 0)
                           (<= x y)))))
  :rule-classes ((:rewrite)
		 (:rewrite
                  :backchain-limit-lst (nil 3 1)
		  :corollary
		  (implies (and (syntaxp
                                 (not (rewriting-goal-literal x mfc state)))
                                (real/rationalp (/ x y))
				(<= 1 (/ x y)))
                           (< 0 (floor x y))))
		 (:rewrite
                  :backchain-limit-lst (nil 3 1 1)
		  :corollary
		  (implies (and (syntaxp
                                 (not (rewriting-goal-literal x mfc state)))
                                (real/rationalp (/ x y))
                                (< 0 y)
                                (<= y x))
                           (< 0 (floor x y))))
		 (:rewrite
                  :backchain-limit-lst (nil 3 1 1)
		  :corollary
		  (implies (and (syntaxp
                                 (not (rewriting-goal-literal x mfc state)))
                                (real/rationalp (/ x y))
                                (< y 0)
                                (<= x y))
			   (< 0 (floor x y))))
		 (:type-prescription
		  :corollary
		  (implies (and (real/rationalp (/ x y))
				(<= 1 (/ x y)))
			   (and (integerp (floor x y))
				(< 0 (floor x y)))))
		 (:type-prescription
		  :corollary
		  (implies (and (real/rationalp (/ x y))
                                (< 0 y)
                                (<= y x))
			   (and (integerp (floor x y))
				(< 0 (floor x y)))))
		 (:type-prescription
		  :corollary
		  (implies (and (real/rationalp (/ x y))
                                (< y 0)
                                (<= x y))
			   (and (integerp (floor x y))
				(< 0 (floor x y))))))
  :otf-flg t)

 (defthm floor-negative
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(real/rationalp (/ x y)))
	   (equal (< (floor x y) 0)
		  (or (and (< 0 x)
			   (< y 0))
		      (and (< x 0)
			   (< 0 y)))))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :backchain-limit-lst (nil 3 1)
		  :corollary
		  (implies (and (syntaxp
				 (not (rewriting-goal-literal x mfc state)))
				(real/rationalp (/ x y))
				(< (/ x y) 0))
			   (< (floor x y) 0)))
		 (:rewrite
		  :backchain-limit-lst (nil 3 1 1)
		  :corollary
		  (implies (and (syntaxp
				 (not (rewriting-goal-literal x mfc state)))
				(real/rationalp (/ x y))
				(< 0 x)
				(< y 0))
			   (< (floor x y) 0)))
		 (:rewrite
		  :backchain-limit-lst (nil 3 1 1)
		  :corollary
		  (implies (and (syntaxp
				 (not (rewriting-goal-literal x mfc state)))
				(real/rationalp (/ x y))
				(< x 0)
				(< 0 y))
			   (< (floor x y) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (real/rationalp (/ x y))
				(< (/ x y) 0))
			   (and (integerp (floor x y))
				(< (floor x y) 0))))
		 (:type-prescription
		  :corollary
		  (implies (and (real/rationalp (/ x y))
				(< 0 x)
				(< y 0))
			   (and (integerp (floor x y))
				(< (floor x y) 0))))
		 (:type-prescription
		  :corollary
		  (implies (and (real/rationalp (/ x y))
				(< x 0)
				(< 0 y))
			   (and (integerp (floor x y))
				(< (floor x y) 0)))))
  :otf-flg t)

 (defthm floor-zero
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(acl2-numberp y)
                (real/rationalp (/ x y)))
           (equal (equal (floor x y) 0)
                  (or (equal y 0)
                      (and (<= 0 x)
                           (< x y))
                      (and (<= x 0)
                           (< y x)))))
  :rule-classes ((:rewrite)
		 (:rewrite
                  :backchain-limit-lst (3 1)
		  :corollary
		  (implies (and (real/rationalp (/ x y))
                                (equal y 0))
			   (equal (floor x y) 0)))
		 (:rewrite
                  :backchain-limit-lst (3 1 1)
		  :corollary
		  (implies (and (real/rationalp (/ x y))
                                (<= 0 (/ x y))
				(< (/ x y) 1))
			   (equal (floor x y) 0)))
		 (:rewrite
                  :backchain-limit-lst (3 1 1)
		  :corollary
		  (implies (and (real/rationalp (/ x y))
                                (<= 0 x)
				(< x y))
			   (equal (floor x y) 0)))
		 (:rewrite
		  :backchain-limit-lst (3 1 1)
		  :corollary
		  (implies (and (real/rationalp (/ x y))
                                (<= x 0)
				(< y x))
			   (equal (floor x y) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (real/rationalp (/ x y))
                                (equal y 0))
			   (equal (floor x y) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (real/rationalp (/ x y))
                                (<= 0 (/ x y))
				(< (/ x y) 1))
			   (equal (floor x y) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (real/rationalp (/ x y))
                                (<= 0 x)
				(< x y))
			   (equal (floor x y) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (real/rationalp (/ x y))
                                (<= x 0)
				(< y x))
			   (equal (floor x y) 0))))
  :hints (("Goal" :cases ((< 0 (floor x y))
			  (< (floor x y) 0)))))

 )
