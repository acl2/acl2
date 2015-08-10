; An ACL2 Tarai Function book.
; Copyright (C) 2000  John R. Cowles, University of Wyoming

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
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

;; Any total function on integer lists that satisfies the
;;  restricted tarai recursion must equal the function
;;  Fb for lists of lengths 2-7:

;; (certify-book "C:/acl2/tak/rTarai8")

(in-package "ACL2")

(include-book "rTarai7")

;; The book rTarai7, included above, in turn, includes the
;;  the book rTarai6, in turn, includes the book tarai5,
;;  which includes all the definitions required to define
;;  Bailey's version (called Fb) of the f function for
;;  Knuth's Theorem 4. The included book also contains a
;;  theorem showing that the function Fb satisfies the
;;  restricted tarai recursion for lists of lengths between
;;  2 and 7.

;; The book rTarai7 contains the theorem showing that any
;;  total function on integer lists that satisfies the
;;  restricted tarai recursion must equal the function Fb
;;  for lists of lengths 2-6.

;; The book rTarai6 contains the constrained axioms for
;;  the restricted tarai recursion and theorems showing that
;;  any total function on integer lists that satisfies the
;;  restricted tarai recursion must equal the function Fb
;;  for lists of lengths 2-5.

;; Fb satisfies the RESTRICTED tarai recursion
;;  (rule-classes nil) (from the book tarai5):
#|  (defthm
      Fb-sat-tarai-def-a
      (implies (and
		(integer-listp lst)
		(consp (rest lst))        ;; (len lst) > 1
		(not
		 (consp (nthcdr 7 lst)))) ;; (len lst) <= 7
	       (equal (Fb lst)
		      (if (<= (first lst)
			      (second lst))
			  (second lst)
			(Fb (Fb-lst
			     (lst-rotates-with-minus-1
			      (- (DEC-FRONT-LEN lst) 1)
			      lst)))))))
|#

;; (rTarai lst) = (Fb lst) when lst is a list of length 7:

(local
 (defthm
     lst-rotates-with-minus-1-7a
     (let ((lst (list first second third forth fifth sixth seventh)))
       (equal (lst-rotates-with-minus-1 1 lst)
	      (list (list (- first 1) second third forth fifth sixth seventh)
		    (list (- second 1) third forth fifth sixth seventh first))
	      ))
     :hints (("Goal"
	      :expand ((lst-rotates-with-minus-1
			1
			(list first second third forth fifth sixth seventh))))
	     )))

(local
 (defthm
     lst-rotates-with-minus-1-7b
     (let ((lst (list first second third forth fifth sixth seventh)))
       (equal (lst-rotates-with-minus-1 2 lst)
	      (list (list (- first 1) second third forth fifth sixth seventh)
		    (list (- second 1) third forth fifth sixth seventh first)
		    (list (- third 1) forth fifth sixth seventh first second))
	      ))))

(local
 (defthm
     lst-rotates-with-minus-1-7c
     (let ((lst (list first second third forth fifth sixth seventh)))
       (equal (lst-rotates-with-minus-1 3 lst)
	      (list (list (- first 1) second third forth fifth sixth seventh)
		    (list (- second 1) third forth fifth sixth seventh first)
		    (list (- third 1) forth fifth sixth seventh first second)
		    (list (- forth 1) fifth sixth seventh first second third))
	      ))))

(local
 (defthm
     lst-rotates-with-minus-1-7d
     (let ((lst (list first second third forth fifth sixth seventh)))
       (equal (lst-rotates-with-minus-1 4 lst)
	      (list (list (- first 1) second third forth fifth sixth seventh)
		    (list (- second 1) third forth fifth sixth seventh first)
		    (list (- third 1) forth fifth sixth seventh first second)
		    (list (- forth 1) fifth sixth seventh first second third)
		    (list (- fifth 1) sixth seventh first second third forth)
		    )))))

(local
 (defthm
     lst-rotates-with-minus-1-7e
     (let ((lst (list first second third forth fifth sixth seventh)))
       (equal
	(lst-rotates-with-minus-1 5 lst)
	(list (list (- first 1) second third forth fifth sixth seventh)
	      (list (- second 1) third forth fifth sixth seventh first)
	      (list (- third 1) forth fifth sixth seventh first second)
	      (list (- forth 1) fifth sixth seventh first second third)
	      (list (- fifth 1) sixth seventh first second third forth)
	      (list (- sixth 1) seventh first second third forth fifth)
	      )))))

(local
 (defthm
     lst-rotates-with-minus-1-7f
     (let ((lst (list first second third forth
		      fifth sixth seventh)))
       (equal
	(lst-rotates-with-minus-1 6 lst)
	(list (list (- first 1) second third forth
		    fifth sixth seventh)
	      (list (- second 1) third forth fifth
		    sixth seventh first)
	      (list (- third 1) forth fifth sixth
		    seventh first second)
	      (list (- forth 1) fifth sixth seventh
		    first second third)
	      (list (- fifth 1) sixth seventh first
		    second third forth)
	      (list (- sixth 1) seventh first second
		    third forth fifth)
	      (list (- seventh 1) first second third
		    forth fifth sixth)
	      )))))

(defthm
    rTarai=Fb-7a
    (implies (and (integer-listp lst)
		  (consp (nthcdr 6 lst))    ;; (len lst) > 6
		  (not
		   (consp (nthcdr 7 lst)))) ;; (len lst) <= 7
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst))
		   (fifth (fifth lst))
		   (sixth (sixth lst))
		   (seventh (seventh lst)))
	       (implies (and
			 (> first second)
			 (<= second third)
			 (equal
			  (rTarai
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh))
			  (Fb
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh)))
			 (equal
			  (rTarai
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first))
			  (Fb
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-7b
    (implies (and (integer-listp lst)
		  (consp (nthcdr 6 lst))    ;; (len lst) > 6
		  (not
		   (consp (nthcdr 7 lst)))) ;; (len lst) <= 7
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst))
		   (fifth (fifth lst))
		   (sixth (sixth lst))
		   (seventh (seventh lst)))
	       (implies (and
			 (> first second)
			 (> second third)
			 (<= third fourth)
			 (equal
			  (rTarai
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh))
			  (Fb
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh)))
			 (equal
			  (rTarai
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first))
			  (Fb
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first)))
			 (equal
			  (rTarai
			   (list
			    (- third 1) fourth fifth
			    sixth seventh first second))
			  (Fb
			   (list
			    (- third 1) fourth fifth
			    sixth seventh first second)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    (Fb
			     (list
			      (- third 1) fourth fifth
			      sixth seventh first second))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    (Fb
			     (list
			      (- third 1) fourth fifth
			      sixth seventh first second))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-7c
    (implies (and (integer-listp lst)
		  (consp (nthcdr 6 lst))    ;; (len lst) > 6
		  (not
		   (consp (nthcdr 7 lst)))) ;; (len lst) <= 7
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst))
		   (fifth (fifth lst))
		   (sixth (sixth lst))
		   (seventh (seventh lst)))
	       (implies (and
			 (> first second)
			 (> second third)
			 (> third fourth)
			 (<= fourth fifth)
			 (equal
			  (rTarai
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh))
			  (Fb
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh)))
			 (equal
			  (rTarai
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first))
			  (Fb
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first)))
			 (equal
			  (rTarai
			   (list
			    (- third 1) fourth fifth
			    sixth seventh first second))
			  (Fb
			   (list
			    (- third 1) fourth fifth
			    sixth seventh first second)))
			 (equal
			  (rTarai
			   (list
			    (- fourth 1) fifth sixth
			    seventh first second third))
			  (Fb
			   (list
			    (- fourth 1) fifth sixth
			    seventh first second third)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    (Fb
			     (list
			      (- third 1) fourth fifth
			      sixth seventh first second))
			    (Fb
			     (list
			      (- fourth 1) fifth sixth
			      seventh first second third))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    (Fb
			     (list
			      (- third 1) fourth fifth
			      sixth seventh first second))
			    (Fb
			     (list
			      (- fourth 1) fifth sixth
			      seventh first second third))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-7d
    (implies (and (integer-listp lst)
		  (consp (nthcdr 6 lst))    ;; (len lst) > 6
		  (not
		   (consp (nthcdr 7 lst)))) ;; (len lst) <= 7
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst))
		   (fifth (fifth lst))
		   (sixth (sixth lst))
		   (seventh (seventh lst)))
	       (implies (and
			 (> first second)
			 (> second third)
			 (> third fourth)
			 (> fourth fifth)
			 (<= fifth sixth)
			 (equal
			  (rTarai
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh))
			  (Fb
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh)))
			 (equal
			  (rTarai
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first))
			  (Fb
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first)))
			 (equal
			  (rTarai
			   (list
			    (- third 1) fourth fifth
			    sixth seventh first second))
			  (Fb
			   (list
			    (- third 1) fourth fifth
			    sixth seventh first second)))
			 (equal
			  (rTarai
			   (list
			    (- fourth 1) fifth sixth
			    seventh first second third))
			  (Fb
			   (list
			    (- fourth 1) fifth sixth
			    seventh first second third)))
			 (equal
			  (rTarai
			   (list
			    (- fifth 1) sixth seventh
			    first second third fourth))
			  (Fb
			   (list
			    (- fifth 1) sixth seventh
			    first second third fourth)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    (Fb
			     (list
			      (- third 1) fourth fifth
			      sixth seventh first second))
			    (Fb
			     (list
			      (- fourth 1) fifth sixth
			      seventh first second third))
			    (Fb
			     (list
			      (- fifth 1) sixth seventh
			      first second third fourth))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    (Fb
			     (list
			      (- third 1) fourth fifth
			      sixth seventh first second))
			    (Fb
			     (list
			      (- fourth 1) fifth sixth
			      seventh first second third))
			    (Fb
			     (list
			      (- fifth 1) sixth seventh
			      first second third fourth))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-7e
    (implies (and (integer-listp lst)
		  (consp (nthcdr 6 lst))    ;; (len lst) > 6
		  (not
		   (consp (nthcdr 7 lst)))) ;; (len lst) <= 7
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst))
		   (fifth (fifth lst))
		   (sixth (sixth lst))
		   (seventh (seventh lst)))
	       (implies (and
			 (> first second)
			 (> second third)
			 (> third fourth)
			 (> fourth fifth)
			 (> fifth sixth)
			 (<= sixth seventh)
			 (equal
			  (rTarai
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh))
			  (Fb
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh)))
			 (equal
			  (rTarai
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first))
			  (Fb
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first)))
			 (equal
			  (rTarai
			   (list
			    (- third 1) fourth fifth
			    sixth seventh first second))
			  (Fb
			   (list
			    (- third 1) fourth fifth
			    sixth seventh first second)))
			 (equal
			  (rTarai
			   (list
			    (- fourth 1) fifth sixth
			    seventh first second third))
			  (Fb
			   (list
			    (- fourth 1) fifth sixth
			    seventh first second third)))
			 (equal
			  (rTarai
			   (list
			    (- fifth 1) sixth seventh
			    first second third fourth))
			  (Fb
			   (list
			    (- fifth 1) sixth seventh
			    first second third fourth)))
			 (equal
			  (rTarai
			   (list
			    (- sixth 1) seventh first
			    second third fourth fifth))
			  (Fb
			   (list
			    (- sixth 1) seventh first
			    second third fourth fifth)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    (Fb
			     (list
			      (- third 1) fourth fifth
			      sixth seventh first second))
			    (Fb
			     (list
			      (- fourth 1) fifth sixth
			      seventh first second third))
			    (Fb
			     (list
			      (- fifth 1) sixth seventh
			      first second third fourth))
			    (Fb
			     (list
			      (- sixth 1) seventh first
			      second third fourth fifth))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    (Fb
			     (list
			      (- third 1) fourth fifth
			      sixth seventh first second))
			    (Fb
			     (list
			      (- fourth 1) fifth sixth
			      seventh first second third))
			    (Fb
			     (list
			      (- fifth 1) sixth seventh
			      first second third fourth))
			    (Fb
			     (list
			      (- sixth 1) seventh first
			      second third fourth fifth))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-7f
    (implies (and (integer-listp lst)
		  (consp (nthcdr 6 lst))    ;; (len lst) > 6
		  (not
		   (consp (nthcdr 7 lst)))) ;; (len lst) <= 7
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst))
		   (fifth (fifth lst))
		   (sixth (sixth lst))
		   (seventh (seventh lst)))
	       (implies (and
			 (> first second)
			 (> second third)
			 (> third fourth)
			 (> fourth fifth)
			 (> fifth sixth)
			 (> sixth seventh)
			 (equal
			  (rTarai
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh))
			  (Fb
			   (list
			    (- first 1) second third
			    fourth fifth sixth seventh)))
			 (equal
			  (rTarai
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first))
			  (Fb
			   (list
			    (- second 1) third fourth
			    fifth sixth seventh first)))
			 (equal
			  (rTarai
			   (list
			    (- third 1) fourth fifth
			    sixth seventh first second))
			  (Fb
			   (list
			    (- third 1) fourth fifth
			    sixth seventh first second)))
			 (equal
			  (rTarai
			   (list
			    (- fourth 1) fifth sixth
			    seventh first second third))
			  (Fb
			   (list
			    (- fourth 1) fifth sixth
			    seventh first second third)))
			 (equal
			  (rTarai
			   (list
			    (- fifth 1) sixth seventh
			    first second third fourth))
			  (Fb
			   (list
			    (- fifth 1) sixth seventh
			    first second third fourth)))
			 (equal
			  (rTarai
			   (list
			    (- sixth 1) seventh first
			    second third fourth fifth))
			  (Fb
			   (list
			    (- sixth 1) seventh first
			    second third fourth fifth)))
			 (equal
			  (rTarai
			   (list
			    (- seventh 1) first second
			    third fourth fifth sixth))
			  (Fb
			   (list
			    (- seventh 1) first second
			    third fourth fifth sixth)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    (Fb
			     (list
			      (- third 1) fourth fifth
			      sixth seventh first second))
			    (Fb
			     (list
			      (- fourth 1) fifth sixth
			      seventh first second third))
			    (Fb
			     (list
			      (- fifth 1) sixth seventh
			      first second third fourth))
			    (Fb
			     (list
			      (- sixth 1) seventh first
			      second third fourth fifth))
			    (Fb
			     (list
			      (- seventh 1) first second
			      third fourth fifth sixth))
			   ))
			  (Fb
			   (list
			    (Fb
			     (list
			      (- first 1) second third
			      fourth fifth sixth seventh))
			    (Fb
			     (list
			      (- second 1) third fourth
			      fifth sixth seventh first))
			    (Fb
			     (list
			      (- third 1) fourth fifth
			      sixth seventh first second))
			    (Fb
			     (list
			      (- fourth 1) fifth sixth
			      seventh first second third))
			    (Fb
			     (list
			      (- fifth 1) sixth seventh
			      first second third fourth))
			    (Fb
			     (list
			      (- sixth 1) seventh first
			      second third fourth fifth))
			    (Fb
			     (list
			      (- seventh 1) first second
			      third fourth fifth sixth))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defun
    Induct-hint-7r (lst)
    "Time:  3800.13 seconds (prove: 2126.90, print: 1673.01, other: 0.22)"
    (declare (xargs :measure (measure lst)))
    (if (and (integer-listp lst)
	     (consp (nthcdr 1 lst)))        ;; (len lst) > 1
	(cond ((not (consp (nthcdr 2 lst))) ;; (len lst) <= 2
	       0)
	      ((not (consp (nthcdr 3 lst))) ;; (len lst) <= 3
	       0)
	      ((not (consp (nthcdr 4 lst))) ;; (len lst) <= 4
	       0)
	      ((not (consp (nthcdr 5 lst))) ;; (len lst) <= 5
	       0)
	      ((not (consp (nthcdr 6 lst))) ;; (len lst) <= 6
	       0)
	      ((not (consp (nthcdr 7 lst))) ;; (len lst) <= 7
	       (let ((first (first lst))
		     (second (second lst))
		     (third (third lst))
		     (fourth (fourth lst))
		     (fifth (fifth lst))
		     (sixth (sixth lst))
		     (seventh (seventh lst)))
		 (cond ((<= first second) 0)
		       ((<= second third)
			(+ (Induct-hint-7r
			    (list
			     (- first 1) second third
			     fourth fifth sixth seventh))
			   (Induct-hint-7r
			    (list
			     (- second 1) third fourth
			     fifth sixth seventh first))
			   (Induct-hint-7r
			    (list
			     (Fb
			      (list
			       (- first 1) second third
			       fourth fifth sixth seventh))
			     (Fb
			      (list
			       (- second 1) third fourth
			       fifth sixth seventh first))
			     ))))
		       ((<= third fourth)
			(+ (Induct-hint-7r
			    (list
			     (- first 1) second third
			     fourth fifth sixth seventh))
			   (Induct-hint-7r
			    (list
			     (- second 1) third fourth
			     fifth sixth seventh first))
			   (Induct-hint-7r
			    (list
			     (- third 1) fourth fifth
			     sixth seventh first second))
			   (Induct-hint-7r
			    (list
			     (Fb
			      (list
			       (- first 1) second third
			       fourth fifth sixth seventh))
			     (Fb
			      (list
			       (- second 1) third fourth
			       fifth sixth seventh first))
			     (Fb
			      (list
			       (- third 1) fourth fifth
			       sixth seventh first second))
			     ))))
		       ((<= fourth fifth)
			(+ (Induct-hint-7r
			    (list
			     (- first 1) second third
			     fourth fifth sixth seventh))
			   (Induct-hint-7r
			    (list
			     (- second 1) third fourth
			     fifth sixth seventh first))
			   (Induct-hint-7r
			    (list
			     (- third 1) fourth fifth
			     sixth seventh first second))
			   (Induct-hint-7r
			    (list
			     (- fourth 1) fifth sixth
			     seventh first second third))
			   (Induct-hint-7r
			    (list
			     (Fb
			      (list
			       (- first 1) second third
			       fourth fifth sixth seventh))
			     (Fb
			      (list
			       (- second 1) third fourth
			       fifth sixth seventh first))
			     (Fb
			      (list
			       (- third 1) fourth fifth
			       sixth seventh first second))
			     (Fb
			      (list
			       (- fourth 1) fifth sixth
			       seventh first second third))
			     ))))
		       ((<= fifth sixth)
			(+ (Induct-hint-7r
			    (list
			     (- first 1) second third
			     fourth fifth sixth seventh))
			   (Induct-hint-7r
			    (list
			     (- second 1) third fourth
			     fifth sixth seventh first))
			   (Induct-hint-7r
			    (list
			     (- third 1) fourth fifth
			     sixth seventh first second))
			   (Induct-hint-7r
			    (list
			     (- fourth 1) fifth sixth
			     seventh first second third))
			   (Induct-hint-7r
			    (list
			     (- fifth 1) sixth seventh first
			     second third fourth))
			   (Induct-hint-7r
			    (list
			     (Fb
			      (list
			       (- first 1) second third
			       fourth fifth sixth seventh))
			     (Fb
			      (list
			       (- second 1) third fourth
			       fifth sixth seventh first))
			     (Fb
			      (list
			       (- third 1) fourth fifth
			       sixth seventh first second))
			     (Fb
			      (list
			       (- fourth 1) fifth sixth
			       seventh first second third))
			     (Fb
			      (list
			       (- fifth 1) sixth seventh
			       first second third fourth))
			     ))))
		       ((<= sixth seventh)
			(+ (Induct-hint-7r
			    (list
			     (- first 1) second third
			     fourth fifth sixth seventh))
			   (Induct-hint-7r
			    (list
			     (- second 1) third fourth
			     fifth sixth seventh first))
			   (Induct-hint-7r
			    (list
			     (- third 1) fourth fifth
			     sixth seventh first second))
			   (Induct-hint-7r
			    (list
			     (- fourth 1) fifth sixth
			     seventh first second third))
			   (Induct-hint-7r
			    (list
			     (- fifth 1) sixth seventh
			     first second third fourth))
			   (Induct-hint-7r
			    (list
			     (- sixth 1) seventh first
			     second third fourth fifth))
			   (Induct-hint-7r
			    (list
			     (Fb
			      (list
			       (- first 1) second third
			       fourth fifth sixth seventh))
			     (Fb
			      (list
			       (- second 1) third fourth
			       fifth sixth seventh first))
			     (Fb
			      (list
			       (- third 1) fourth fifth
			       sixth seventh first second))
			     (Fb
			      (list
			       (- fourth 1) fifth sixth
			       seventh first second third))
			     (Fb
			      (list
			       (- fifth 1) sixth seventh
			       first second third fourth))
			     (Fb
			      (list
			       (- sixth 1) seventh first
			       second third fourth fifth))
			     ))))
		       (t
			(+ (Induct-hint-7r
			    (list
			     (- first 1) second third
			     fourth fifth sixth seventh))
			   (Induct-hint-7r
			    (list
			     (- second 1) third fourth
			     fifth sixth seventh first))
			   (Induct-hint-7r
			    (list
			     (- third 1) fourth fifth
			     sixth seventh first second))
			   (Induct-hint-7r
			    (list
			     (- fourth 1) fifth sixth
			     seventh first second third))
			   (Induct-hint-7r
			    (list
			     (- fifth 1) sixth seventh
			     first second third fourth))
			   (Induct-hint-7r
			    (list
			     (- sixth 1) seventh first
			     second third fourth fifth))
			   (Induct-hint-7r
			    (list
			     (- seventh 1) first second
			     third fourth fifth sixth))
			   (Induct-hint-7r
			    (list
			     (Fb
			      (list
			       (- first 1) second third
			       fourth fifth sixth seventh))
			     (Fb
			      (list
			       (- second 1) third fourth
			       fifth sixth seventh first))
			     (Fb
			      (list
			       (- third 1) fourth fifth
			       sixth seventh first second))
			     (Fb
			      (list
			       (- fourth 1) fifth sixth
			       seventh first second third))
			     (Fb
			      (list
			       (- fifth 1) sixth seventh
			       first second third fourth))
			     (Fb
			      (list
			       (- sixth 1) seventh first
			       second third fourth fifth))
			     (Fb
			      (list
			       (- seventh 1) first second
			       third fourth fifth sixth))
			     )))))))
	      (t 0))
        0))

(defthm
    rTarai=Fb-7
    (implies (and (integer-listp lst)
		  (consp (nthcdr 1 lst))    ;; (len lst) > 1
		  (not
		   (consp (nthcdr 7 lst)))) ;; (len lst) <= 7
	     (equal (rTarai lst)(Fb lst)))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :induct (Induct-hint-7r lst))))
