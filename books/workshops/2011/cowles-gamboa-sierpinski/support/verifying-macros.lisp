
;; Verifying Macros for Sierpinski and Riesel Numbers
;;                      by
;;   John R.Cowles          Ruben Gamboa
;;   cowles@cs.uwyo.edu     ruben@cs.uwyo.edu
;;        Department of Computer Science
;;        University of Wyoming
;;        Laramie, Wyoming, USA

;; Copyright (C) 2011  University of Wyoming, Laramie, Wyoming

;; A Sierpinski number is an odd positive integer, k, such that no
;; positive integer in this infinite list is prime:

;;    k 2^1 + 1, k  2^2 + 1, k 2^3 + 1, ..., k 2^n + 1, ... .

;; A Riesel number is similar to a Sierpinski number, with -1 replacing
;; +1 in the above infinite list. Such a number is an odd positive
;; integer, k, so that no positive integer in this infinite list is
;; prime:

;;    k 2^1 - 1, k 2^2 - 1, k 2^3 - 1, ..., k 2^n - 1, ... .

;; A cover, for such a k, is a finite list of positive integers such that
;; each integer, j, in the appropriate infinite list, has a factor, d, in
;; the cover, with 1 < d < j.

;; Given a k and its cover, ACL2 is used to systematically verify that
;; each integer, in the appropriate infinite list, has a smaller factor
;; in the cover.

;; For each individual k and cover, ACL2 events are generated that would
;; prove k is a Sierpinski or Riesel number, if all the events
;; succeed. If some of the events fail, then, as usual when using ACL2,
;; further study of the failure is required, in the hope of taking
;; corrective action.

;; The generation of these events is controlled by the macros
;; verify-sierpinski and verify-riesel.  These macros take three
;; arguments: the name of a witness function that will find a factor for
;; a given k 2^n +or- 1, the number k that is a Sierpinski or Riesel
;; number, and the cover for k.  The macros then generate an ACL2 proof.

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

#|
To certify:
 (defpkg "U" (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*))
 (certify-book "verifying-macros" 1)
|#

(in-package "ACL2")

(local (include-book "arithmetic-3/top" :dir :system))
(include-book "data-structures/utilities" :dir :system)

(defun nat-to-string (number)
 (if (zp number)
     "0"
     (if (< number 10)
	  (string (char "0123456789" number))
	  (string-append (nat-to-string (floor number 10))
			 (string (char "0123456789" (mod number 10)))))))

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

(defun
natp-induction (n)
(if (zp n)
    t
    (natp-induction (- n 1))))

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
)

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

(defun generate-sierpinski-lemmas (divisor number cover)
 (if (consp cover)
     (let* ((a number)
	     (d (car cover))
	     (b (find-sierpinski-b 1 d))
	     (c (find-sierpinski-c 0 b d a))
	     (lemma (u::pack-intern divisor divisor '-lemma- (nat-to-string d)))
	     )
	(cons
	 `(LOCAL (DEFTHM ,lemma
		     (IMPLIES (AND (INTEGERP N)
				   (>= N 0))
			      (DIVIDES ,d (+ 1 (* ,a (EXPT 2 (+ ,c (* ,b N)))))))
		   :HINTS (("GOAL"
			    :USE ((:FUNCTIONAL-INSTANCE Key-Lemma-Sierpinski
							(AS (LAMBDA () ,a))
							(BS (LAMBDA () ,b))
							(CS (LAMBDA () ,c))
							(DS (LAMBDA () ,d))))))))
	 (generate-sierpinski-lemmas divisor number (cdr cover))))
     nil
     ))

(defun generate-sierpinski-lemmas-a (divisor number cover)
 (if (consp cover)
     (let* ((a number)
	     (d (car cover))
	     (b (find-sierpinski-b 1 d))
	     (c (find-sierpinski-c 0 b d a))
	     (Lemma (u::pack-intern divisor divisor '-lemma- (nat-to-string d)))
	     (lemma-a (u::pack-intern divisor divisor '-lemma-a- (nat-to-string d)))
	     )
	(cons
	 `(LOCAL (DEFTHM ,lemma-a
		     (IMPLIES (AND (INTEGERP N)
				   (>= N 0)
				   (EQUAL (MOD N ,b) ,c))
			      (DIVIDES ,d (+ 1 (* ,a (EXPT 2 N)))))
		   :HINTS (("GOAL"
			    :USE ((:INSTANCE ,lemma (N (FLOOR N ,b))))
			    :IN-THEORY (DISABLE ,lemma)))))
	 (generate-sierpinski-lemmas-a divisor number (cdr cover))))
     nil
     ))

(defun generate-riesel-lemmas (divisor number cover)
 (if (consp cover)
     (let* ((a number)
	     (d (car cover))
	     (b (find-riesel-b 1 d))
	     (c (find-riesel-c 0 b d a))
	     (lemma (u::pack-intern divisor divisor '-lemma- (nat-to-string d)))
	     )
	(cons
	 `(LOCAL (DEFTHM ,lemma
		     (IMPLIES (AND (INTEGERP N)
				   (>= N 0))
			      (DIVIDES ,d (+ -1 (* ,a (EXPT 2 (+ ,c (* ,b N)))))))
		   :HINTS (("GOAL"
			    :USE ((:FUNCTIONAL-INSTANCE Key-Lemma-Riesel
							(AR (LAMBDA () ,a))
							(BR (LAMBDA () ,b))
							(CR (LAMBDA () ,c))
							(DR (LAMBDA () ,d))))))))
	 (generate-riesel-lemmas divisor number (cdr cover))))
     nil
     ))

(defun generate-riesel-lemmas-a (divisor number cover)
 (if (consp cover)
     (let* ((a number)
	     (d (car cover))
	     (b (find-riesel-b 1 d))
	     (c (find-riesel-c 0 b d a))
	     (Lemma (u::pack-intern divisor divisor '-lemma- (nat-to-string d)))
	     (lemma-a (u::pack-intern divisor divisor '-lemma-a- (nat-to-string d)))
	     )
	(cons
	 `(LOCAL (DEFTHM ,lemma-a
		     (IMPLIES (AND (INTEGERP N)
				   (>= N 0)
				   (EQUAL (MOD N ,b) ,c))
			      (DIVIDES ,d (+ -1 (* ,a (EXPT 2 N)))))
		   :HINTS (("GOAL"
			    :USE ((:INSTANCE ,lemma (N (FLOOR N ,b))))
			    :IN-THEORY (DISABLE ,lemma)))))
	 (generate-riesel-lemmas-a divisor number (cdr cover))))
     nil
     ))

(defun generate-sierpinski-equalities-mod (triplets l)
 (if (consp triplets)
     (let* ((triplet (car triplets))
	     (b (first triplet))
	     (c (second triplet))
	     ;(d (third triplet))
	     )
	(cons `(EQUAL (MOD (MOD N ,l) ,b) ,c)
	      (generate-sierpinski-equalities-mod (cdr triplets) l)))
     nil))

(defun generate-sierpinski-equalities (triplets)
 (if (consp triplets)
     (let* ((triplet (car triplets))
	     (b (first triplet))
	     (c (second triplet))
	     ;(d (third triplet))
	     )
	(cons `(EQUAL (MOD N ,b) ,c)
	      (generate-sierpinski-equalities (cdr triplets))))
     nil))

(defun map-first (triplets)
 (if (consp triplets)
     (cons (first (car triplets))
	    (map-first (cdr triplets)))
     nil))

(defun generate-sierpinski-cover-one (divisor number cover)
 (let ((triplets (generate-sierpinski-triplets number cover))
	(cover-one (u::pack-intern divisor divisor '-check-cover-one))
	)
   `(LOCAL (DEFUN ,cover-one (N)
	      (IF (INTEGERP N)
		  (OR ,@(generate-sierpinski-equalities triplets))
		  NIL)))))

(defun generate-riesel-cover-one (divisor number cover)
 (let ((triplets (generate-riesel-triplets number cover))
	(cover-one (u::pack-intern divisor divisor '-check-cover-one))
	)
   `(LOCAL (DEFUN ,cover-one (N)
	      (IF (INTEGERP N)
		  (OR ,@(generate-sierpinski-equalities triplets))
		  NIL)))))

(defun generate-sierpinski-riesel-cover (divisor)
 (let ((cover (u::pack-intern divisor divisor '-check-cover))
	(cover-one (u::pack-intern divisor divisor '-check-cover-one))
	)
   `(LOCAL (DEFUN ,cover (L U)
	      (DECLARE (XARGS :MEASURE (IF (AND (INTEGERP L)(INTEGERP U)(< L U))
					   (- U L)
					   0)))
	      (IF (AND (INTEGERP L)
		       (INTEGERP U))
		  (IF (< L U)
		      (AND (,cover-one L)(,cover (1+ L) U))
		      T)
		  NIL)))))

(defun generate-sierpinski-riesel-cover=>cover-one (divisor)
 (let ((cover (u::pack-intern divisor divisor '-check-cover))
	(cover-one (u::pack-intern divisor divisor '-check-cover-one))
	(cover=> (u::pack-intern divisor divisor '-check-cover=>check-cover-one))
	)
   `(LOCAL (DEFTHM ,cover=>
	      (IMPLIES (AND (INTEGERP N)(<= L N)(< N U)(,cover L U))
		       (,cover-one N))
	      :RULE-CLASSES NIL
	      :HINTS (("GOAL" :IN-THEORY (DISABLE (:DEFINITION ,cover-one))))))))

(defun generate-sierpinski-cover-cases-< (divisor number cover)
 (let* ((triplets (generate-sierpinski-triplets number cover))
	 (l (s-lcm-list (map-first triplets)))
        (cover=> (u::pack-intern divisor divisor '-check-cover=>check-cover-one))
        (cover-< (u::pack-intern divisor divisor '-cover-all-cases-<- (nat-to-string l)))
	 )
   `(LOCAL (DEFTHM ,cover-<
		(IMPLIES (AND (INTEGERP N)(<= 0 N)(< N ,l))
			 (OR ,@(generate-sierpinski-equalities triplets)))
		:RULE-CLASSES NIL
		:HINTS (("GOAL" :USE ((:INSTANCE ,cover=> (L 0)(U ,l)))))))))

(defun generate-riesel-cover-cases-< (divisor number cover)
 (let* ((triplets (generate-riesel-triplets number cover))
	 (l (s-lcm-list (map-first triplets)))
        (cover=> (u::pack-intern divisor divisor '-check-cover=>check-cover-one))
        (cover-< (u::pack-intern divisor divisor '-cover-all-cases-<- (nat-to-string l)))
	 )
   `(LOCAL (DEFTHM ,cover-<
		(IMPLIES (AND (INTEGERP N)(<= 0 N)(< N ,l))
			 (OR ,@(generate-sierpinski-equalities triplets)))
		:RULE-CLASSES NIL
		:HINTS (("GOAL" :USE ((:INSTANCE ,cover=> (L 0)(U ,l)))))))))

(defun generate-sierpinski-cover-cases-mod (divisor number cover)
 (let* ((triplets (generate-sierpinski-triplets number cover))
	 (l (s-lcm-list (map-first triplets)))
        (cover-< (u::pack-intern divisor divisor '-cover-all-cases-<- (nat-to-string l)))
	 (cover-mod (u::pack-intern divisor divisor '-cover-all-cases-mod- (nat-to-string l)))
	 )
   `(LOCAL (DEFTHM ,cover-mod
		(IMPLIES (INTEGERP N)
			 (OR ,@(generate-sierpinski-equalities-mod triplets l)))
	      :RULE-CLASSES NIL
	      :HINTS (("GOAL" :USE ((:INSTANCE ,cover-< (N (MOD N ,l))))))))))

(defun generate-riesel-cover-cases-mod (divisor number cover)
 (let* ((triplets (generate-riesel-triplets number cover))
	 (l (s-lcm-list (map-first triplets)))
        (cover-< (u::pack-intern divisor divisor '-cover-all-cases-<- (nat-to-string l)))
	 (cover-mod (u::pack-intern divisor divisor '-cover-all-cases-mod- (nat-to-string l)))
	 )
   `(LOCAL (DEFTHM ,cover-mod
		(IMPLIES (INTEGERP N)
			 (OR ,@(generate-sierpinski-equalities-mod triplets l)))
	      :RULE-CLASSES NIL
	      :HINTS (("GOAL" :USE ((:INSTANCE ,cover-< (N (MOD N ,l))))))))))

(defun generate-sierpinski-cover-cases (divisor number cover)
 (let* ((triplets (generate-sierpinski-triplets number cover))
	 (l (s-lcm-list (map-first triplets)))
	 (cover-mod (u::pack-intern divisor divisor '-cover-all-cases-mod- (nat-to-string l)))
	 (cover-thm (u::pack-intern divisor divisor '-cover-all-cases))
	 )
   `(LOCAL (DEFTHM ,cover-thm
		(IMPLIES (INTEGERP N)
			 (OR ,@(generate-sierpinski-equalities triplets)))
	      :RULE-CLASSES NIL
	      :HINTS (("GOAL" :USE ((:INSTANCE ,cover-mod))))))))

(defun generate-riesel-cover-cases (divisor number cover)
 (let* ((triplets (generate-riesel-triplets number cover))
	 (l (s-lcm-list (map-first triplets)))
	 (cover-mod (u::pack-intern divisor divisor '-cover-all-cases-mod- (nat-to-string l)))
	 (cover-thm (u::pack-intern divisor divisor '-cover-all-cases))
	 )
   `(LOCAL (DEFTHM ,cover-thm
		(IMPLIES (INTEGERP N)
			 (OR ,@(generate-sierpinski-equalities triplets)))
	      :RULE-CLASSES NIL
	      :HINTS (("GOAL" :USE ((:INSTANCE ,cover-mod))))))))

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

(defun generate-sierpinski-divisor-definition (divisor number cover)
 (let* ((triplets (generate-sierpinski-triplets number cover))
	 ;(l (s-lcm-list (map-first triplets)))
	 )
   `(LOCAL (DEFUN ,divisor (N)
      (IF (INTEGERP N)
	   (COND ,@(generate-sierpinski-divisor-cases triplets))
	   0)))))

(defun generate-riesel-divisor-definition (divisor number cover)
 (let* ((triplets (generate-riesel-triplets number cover))
	 ;(l (s-lcm-list (map-first triplets)))
	 )
   `(LOCAL (DEFUN ,divisor (N)
      (IF (INTEGERP N)
	   (COND ,@(generate-sierpinski-divisor-cases triplets))
	   0)))))

(defun generate-sierpinski-divisor-constraint-natp (divisor)
 (let* ((divisor-natp (u::pack-intern divisor divisor '-natp))
	 (cover-thm (u::pack-intern divisor divisor '-cover-all-cases))
	 )
   `(DEFTHM ,divisor-natp
	 (AND (INTEGERP (,divisor N))
	      (<= 0 (,divisor N)))
      :HINTS (("GOAL"
	   :USE ((:INSTANCE ,cover-thm))
	   )))))

(defun generate-sierpinski-divisor-constraint-gt-1 (divisor)
 (let* ((divisor-gt-1 (u::pack-intern divisor divisor '-gt-1))
	 (cover-thm (u::pack-intern divisor divisor '-cover-all-cases))
	 )
   `(DEFTHM ,divisor-gt-1
	 (IMPLIES (INTEGERP N)
		  (< 1 (,divisor N)))
      :HINTS (("GOAL"
	   :USE ((:INSTANCE ,cover-thm))
	   )))))

(defun generate-sierpinski-divisor-constraint-lt-sierpinski (divisor number)
 (let* ((divisor-lt-sierpinski (u::pack-intern divisor divisor '-lt-sierpinski))
	 )
   `(DEFTHM ,divisor-lt-sierpinski
      (IMPLIES (AND (INTEGERP N)
		     (<= 0 N))
		(< (,divisor N)
		   (+ 1 (* ,number (EXPT 2 N))))))))

(defun generate-riesel-divisor-constraint-lt-riesel (divisor number)
 (let* ((divisor-lt-riesel (u::pack-intern divisor divisor '-lt-sierpinski))
	 )
   `(DEFTHM ,divisor-lt-riesel
      (IMPLIES (AND (INTEGERP N)
		     (<= 0 N))
		(< (,divisor N)
		   (+ -1 (* ,number (EXPT 2 N))))))))

(defun generate-sierpinski-divisor-constraint-divisor-divides (divisor number)
 (let* ((divisor-divides (u::pack-intern divisor divisor '-divides-sierpinski-sequence))
	 (cover-thm (u::pack-intern divisor divisor '-cover-all-cases))
	 )
   `(DEFTHM ,divisor-divides
	 (IMPLIES (AND (INTEGERP N)
		       (<= 0 N))
		  (DIVIDES (,divisor N)
			   (+ 1 (* ,number (EXPT 2 N)))))
      :HINTS (("GOAL"
		:IN-THEORY (DISABLE (:DEFINITION DIVIDES))
		:USE ,cover-thm)))))

(defun generate-riesel-divisor-constraint-divisor-divides (divisor number)
 (let* ((divisor-divides (u::pack-intern divisor divisor '-divides-riesel-sequence))
	 (cover-thm (u::pack-intern divisor divisor '-cover-all-cases))
	 )
   `(DEFTHM ,divisor-divides
	 (IMPLIES (AND (INTEGERP N)
		       (<= 0 N))
		  (DIVIDES (,divisor N)
			   (+ -1 (* ,number (EXPT 2 N)))))
      :HINTS (("GOAL"
		:IN-THEORY (DISABLE (:DEFINITION DIVIDES))
		:USE ,cover-thm)))))

(defmacro verify-sierpinski (divisor number cover)
 `(ENCAPSULATE (((,divisor *) => *))
		,@(generate-sierpinski-lemmas   divisor number cover)
		,@(generate-sierpinski-lemmas-a divisor number cover)
               ,(generate-sierpinski-cover-one divisor number cover)
               ,(generate-sierpinski-riesel-cover divisor)
               ,(generate-sierpinski-riesel-cover=>cover-one divisor)
               ,(generate-sierpinski-cover-cases-< divisor number cover)
		,(generate-sierpinski-cover-cases-mod divisor number cover)
		,(generate-sierpinski-cover-cases divisor number cover)
		,(generate-sierpinski-divisor-definition divisor number cover)
		,(generate-sierpinski-divisor-constraint-natp divisor)
		,(generate-sierpinski-divisor-constraint-gt-1 divisor)
		,(generate-sierpinski-divisor-constraint-lt-sierpinski divisor number)
		,(generate-sierpinski-divisor-constraint-divisor-divides divisor number)
		))

(defmacro verify-riesel (divisor number cover)
 `(ENCAPSULATE (((,divisor *) => *))
		,@(generate-riesel-lemmas   divisor number cover)
		,@(generate-riesel-lemmas-a divisor number cover)
               ,(generate-riesel-cover-one divisor number cover)
               ,(generate-sierpinski-riesel-cover divisor)
               ,(generate-sierpinski-riesel-cover=>cover-one divisor)
               ,(generate-riesel-cover-cases-< divisor number cover)
		,(generate-riesel-cover-cases-mod divisor number cover)
		,(generate-riesel-cover-cases divisor number cover)
		,(generate-riesel-divisor-definition divisor number cover)
		,(generate-sierpinski-divisor-constraint-natp divisor)
		,(generate-sierpinski-divisor-constraint-gt-1 divisor)
		,(generate-riesel-divisor-constraint-lt-riesel divisor number)
		,(generate-riesel-divisor-constraint-divisor-divides divisor number)
		))

;;Smallest known Sierpinski number
(verify-sierpinski sierpinski-witness-78557 78557 (3 5 7 13 19 37 73))

;;Smallest known prime Sierpinski number
(verify-sierpinski sierpinski-witness-271129 271129 (3 5 7 13 17 241))

;;More Sierpinski numbers
(verify-sierpinski sierpinski-witness-271577 271577 (3 5 7 13 17 241))

(verify-sierpinski sierpinski-witness-322523 322523 (3 5 7 13 37 73 109))

(verify-sierpinski sierpinski-witness-327739 327739 (3 5 7 13 17 97 257))

(verify-sierpinski sierpinski-witness-482719 482719 (3 5 7 13 17 241))

(verify-sierpinski sierpinski-witness-575041 575041 (3 5 7 13 17 241))

(verify-sierpinski sierpinski-witness-603713 603713 (3 5 7 13 17 241))

(verify-sierpinski sierpinski-witness-903983 903983 (3 5 7 13 17 241))

(verify-sierpinski sierpinski-witness-934909 934909 (3 5 7 13 19 73 109))

(verify-sierpinski sierpinski-witness-965431 965431 (3 5 7 13 17 241))

(verify-sierpinski sierpinski-witness-1259779 1259779 (3 5 7 13 19 73 109))

(verify-sierpinski sierpinski-witness-1290677 1290677 (3 5 7 13 19 37 109))

(verify-sierpinski sierpinski-witness-1518781 1518781 (3 5 7 13 17 241))

(verify-sierpinski sierpinski-witness-1624097 1624097 (3 5 7 13 17 241))

(verify-sierpinski sierpinski-witness-1639459 1639459 (3 5 7 13 17 241))

(verify-sierpinski sierpinski-witness-1777613 1777613 (3 5 7 13 17 19 109 433))

(verify-sierpinski sierpinski-witness-2131043 2131043 (3 5 7 13 17 241))

;;Smallest Sierpinski number found by Sierpinski
(verify-sierpinski sierpinski-witness-15511380746462593381 15511380746462593381 (3 5 17 257 641 65537 6700417))

;;Smallest known Riesel number
(verify-riesel riesel-witness-509203 509203 (3 5 7 13 17 241))

;;More Riesel numbers
(verify-riesel riesel-witness-762701 762701 (3 5 7 13 17 241))

(verify-riesel riesel-witness-777149 777149 (3 5 7 13 19 37 73))

(verify-riesel riesel-witness-790841 790841 (3 5 7 13 19 37 73))

(verify-riesel riesel-witness-992077 992077 (3 5 7 13 17 241))

;;Numbers both Sierpinski and Riesel
(verify-sierpinski sierpinski-witness-143665583045350793098657 143665583045350793098657 (3 7 11 19 31 37 61 73 109 151 331 1321))
(verify-riesel         riesel-witness-143665583045350793098657 143665583045350793098657 (3 5 13 17 97 241 257))

(verify-sierpinski sierpinski-witness-47867742232066880047611079 47867742232066880047611079 (3 5 13 17 97 241 257))
(verify-riesel         riesel-witness-47867742232066880047611079 47867742232066880047611079 (3 7 11 19 31 37 41 61 73 109 151 331))

(verify-sierpinski sierpinski-witness-878503122374924101526292469 878503122374924101526292469 (3 5 11 17 31 41 61 151 331 61681))
(verify-riesel         riesel-witness-878503122374924101526292469 878503122374924101526292469 (3 7 13 19 37 73 97 109 241 257))

(verify-sierpinski sierpinski-witness-3872639446526560168555701047 3872639446526560168555701047 (3 5 11 17 31 41 61 151 331 61681))
(verify-riesel         riesel-witness-3872639446526560168555701047 3872639446526560168555701047 (3 7 13 19 37 73 97 109 241 673))

(verify-sierpinski sierpinski-witness-623506356601958507977841221247 623506356601958507977841221247 (3 5 17 257 641 65537 6700417))
(verify-riesel         riesel-witness-623506356601958507977841221247 623506356601958507977841221247 (3 7 13 19 37 73 97 109 241 673))