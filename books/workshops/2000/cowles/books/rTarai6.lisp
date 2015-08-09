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
;;  Fb for lists of lengths 2-5:

;; (certify-book "C:/acl2/tak/rTarai6")

(in-package "ACL2")

(include-book "tarai5")

;; The book tarai5, included above, includes all the
;;  definitions required to define Bailey's version (called
;;  Fb) of the f function for Knuth's Theorem 4. The included
;;  book also contains a theorem showing that the function Fb
;;  satisfies the restricted tarai recursion for lists of
;;  lengths between 2 and 7.

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

(defthm
    integerp-last-el
    (implies (and (integer-listp lst)
		  (consp lst))
	     (integerp (last-el lst)))
    :rule-classes :type-prescription)

(defthm
    integerp-Gb
    (implies (and (integer-listp lst)
		  (consp lst))
	     (integerp (Gb lst)))
    :rule-classes (:type-prescription
		   :rewrite))

(defthm
    integerp-listp-first-non-decrease
    (implies (integer-listp lst)
	     (integer-listp (first-non-decrease lst))))

(defthm
    integerp-Fb
    (implies (and (integer-listp lst)
		  (consp lst))
	     (integerp (Fb lst)))
    :rule-classes (:type-prescription
		   :rewrite))

(encapsulate
 (((rTarai *) => *)
  ((rTarai-lst *) => *))

 (local (defun
	    rTarai (lst)
	    (Fb lst)))

 (local (defun
	    rTarai-lst (lst)
	    (Fb-lst lst)))

 (defthm
     rTarai-def
     (implies (and
	       (integer-listp lst)
	       (consp (rest lst))        ;; (len lst) > 1
	       (not
		(consp (nthcdr 7 lst)))) ;; (len lst) <= 7
	      (equal (rTarai lst)
		     (if (<= (first lst)
			     (second lst))
			 (second lst)
		         (rTarai (rTarai-lst
				  (lst-rotates-with-minus-1
				   (- (DEC-FRONT-LEN lst) 1)
				   lst))))))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory (disable Fb Fb-lst dec-front-len
				  lst-rotates-with-minus-1)
	    :use Fb-sat-tarai-def-a)))

 (defthm
     rTarai-lst-def
     (equal (rTarai-lst lst)
	    (if (consp lst)
		(cons (rTarai (first lst))
		      (rTarai-lst (rest lst)))
	        nil))
     :rule-classes :definition)
 ) ;; end encapsulate

(defthm
    true-lisp-rTarai-lst
    (true-listp (rTarai-lst lst))
    :rule-classes :type-prescription
    :hints (("Goal"
	     :induct (Fb-lst lst))))

(defun
    measure (lst)
    "Return e0-ordinal based on the number of strictly
     decreasing elements at the front of the list and on
     the difference between the first and second elements
     (when such elements exist."
    (declare (xargs :guard (integer-listp lst)))
    (cond ((consp (rest lst))    ;; (len lst) > 1
	   (cons (dec-front-len lst)
		 (nfix (- (first lst)(second lst)))))
	  ((consp lst) 1)        ;; (len lst) = 1
	  (t 0)))                ;; (len lst) = 0

(defthm
    rTarai=Fb-1
    (implies (and (integer-listp lst)
		  (consp (rest lst))        ;; (len lst) > 1
		  (not
		   (consp (nthcdr 7 lst))) ;; (len lst) <= 7
		  (<= (first lst)(second lst)))
	     (equal (rTarai lst)(Fb lst)))
    :hints (("Goal"
	     :use rTarai-def)))

;; (rTarai lst) = (Fb lst) when lst is a list of length 2:

(local
 (defthm
     lst-rotates-with-minus-1-2a
     (let ((lst (list first second)))
       (equal (lst-rotates-with-minus-1 1 lst)
	      (list (list (- first 1) second)
		    (list (- second 1) first))))
     :hints (("Goal"
	      :expand (lst-rotates-with-minus-1
		       1
		       (list first second))))))

(defthm
    rTarai=Fb-2a
    (implies (and (integer-listp lst)
		  (consp (nthcdr 1 lst))    ;; (len lst) > 1
		  (not
		   (consp (nthcdr 2 lst)))) ;; (len lst) <= 2
	     (let ((first (first lst))
		   (second (second lst)))
	       (implies (and
			 (> first second)
			 (equal (rTarai
				 (list
				  (- first 1) second))
				(Fb
				 (list
				  (- first 1) second)))
			 (equal (rTarai
				 (list
				  (- second 1) first))
				(Fb
				 (list
				  (- second 1) first)))
			 (equal (rTarai
				 (list
				  (Fb
				   (list
				    (- first 1) second))
				  (Fb
				   (list
				    (- second 1) first))))
				(Fb
				 (list
				  (Fb
				   (list
				    (- first 1) second))
				  (Fb
				   (list
				    (- second 1) first))))))
	       (equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defun
    Induct-hint-2r (lst)
    (declare (xargs :measure (measure lst)))
    (if (and (integer-listp lst)
	     (consp (nthcdr 1 lst))        ;; (len lst) > 1
	     (not (consp (nthcdr 2 lst)))) ;; (len lst) <= 2
	(let ((first (first lst))
	      (second (second lst)))
	  (cond ((<= first second) 0)
		(t (+ (Induct-hint-2r
		       (list (- first 1) second))
		      (Induct-hint-2r
		       (list (- second 1) first))
		      (Induct-hint-2r
		       (list
			(Fb (list (- first 1) second))
			(Fb (list (- second 1) first))))))))
      0))

(defthm
    rTarai=Fb-2
    (implies (and (integer-listp lst)
		  (consp (nthcdr 1 lst))    ;; (len lst) > 1
		  (not
		   (consp (nthcdr 2 lst)))) ;; (len lst) <= 2
	     (equal (rTarai lst)(Fb lst)))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :induct (Induct-hint-2r lst))))

;; (rTarai lst) = (Fb lst) when lst is a list of length 2 or 3:

(local
 (defthm
     lst-rotates-with-minus-1-3a
     (let ((lst (list first second third)))
       (equal (lst-rotates-with-minus-1 1 lst)
	      (list (list (- first 1) second third)
		    (list (- second 1) third first))))
     :hints (("Goal"
	      :expand ((lst-rotates-with-minus-1
			1
			(list first second third)))))))

(local
 (defthm
     lst-rotates-with-minus-1-3b
     (let ((lst (list first second third)))
       (equal (lst-rotates-with-minus-1 2 lst)
	      (list (list (- first 1) second third)
		    (list (- second 1) third first)
		    (list (- third 1) first second))))))

(defthm
    rTarai=Fb-3a
    (implies (and (integer-listp lst)
		  (consp (nthcdr 2 lst))    ;; (len lst) > 2
		  (not
		   (consp (nthcdr 3 lst)))) ;; (len lst) <= 3
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst)))
	       (implies (and
			 (> first second)
			 (<= second third)
			 (equal (rTarai
				 (list
				  (- first 1) second third))
				(Fb
				 (list
				  (- first 1) second third)))
			 (equal (rTarai
				 (list
				  (- second 1) third first))
				(Fb
				 (list
				  (- second 1) third first)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list (- first 1) second third))
			    (Fb
			     (list (- second 1) third first))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list (- first 1) second third))
			    (Fb
			     (list (- second 1) third first))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-3b
    (implies (and (integer-listp lst)
		  (consp (nthcdr 2 lst))    ;; (len lst) > 2
		  (not
		   (consp (nthcdr 3 lst)))) ;; (len lst) <= 3
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst)))
	       (implies (and (> first second)
			     (> second third)
			     (equal
			      (rTarai
			       (list
				(- first 1) second third))
			      (Fb
			       (list
				(- first 1) second third)))
			     (equal
			      (rTarai
			       (list
				(- second 1) third first))
			      (Fb
			       (list
				(- second 1) third first)))
			     (equal
			      (rTarai
			       (list
				(- third 1) first second))
			      (Fb
			       (list
				(- third 1) first second)))
			     (equal
			      (rTarai
			       (list
				(Fb
				 (list
				  (- first 1) second third))
				(Fb
				 (list
				  (- second 1) third first))
				(Fb
				 (list
				  (- third 1) first second))
				))
			      (Fb
			       (list
				(Fb
				 (list
				  (- first 1) second third))
				(Fb
				 (list
				  (- second 1) third first))
				(Fb
				 (list
				  (- third 1) first second))
				))))
			(equal (rTarai lst)(Fb lst)))))
      :hints (("Goal"
	       :in-theory (disable Fb rTarai=Fb-3a)
	       :use (rTarai-def
		     Fb-sat-tarai-def-a))))

(defun
    Induct-hint-3r (lst)
    (declare (xargs :measure (measure lst)))
    (if (and (integer-listp lst)
	     (consp (nthcdr 1 lst)))        ;; (len lst) > 1
	(cond ((not (consp (nthcdr 2 lst))) ;; (len lst) <= 2
	       0)
	      ((not (consp (nthcdr 3 lst))) ;; (len lst) <= 3
	       (let ((first (first lst))
		     (second (second lst))
		     (third (third lst)))
		 (cond ((<= first second) 0)
		       ((<= second third)
			(+ (Induct-hint-3r
			    (list (- first 1) second third))
			   (Induct-hint-3r
			    (list (- second 1) third first))
			   (Induct-hint-3r
			    (list
			     (Fb (list (- first 1) second third))
			     (Fb (list (- second 1) third first))
			     ))))
		       (t (+ (Induct-hint-3r
			      (list (- first 1) second third))
			     (Induct-hint-3r
			      (list (- second 1) third first))
			     (Induct-hint-3r
			      (list (- third 1) first second))
			     (Induct-hint-3r
			      (list
			       (Fb (list (- first 1) second third))
			       (Fb (list (- second 1) third first))
			       (Fb (list (- third 1) first second))
			       )))))))
	      (t 0))
        0))

(defthm
    rTarai=Fb-3
    (implies (and (integer-listp lst)
		  (consp (nthcdr 1 lst))    ;; (len lst) > 1
		  (not
		   (consp (nthcdr 3 lst)))) ;; (len lst) <= 3
	     (equal (rTarai lst)(Fb lst)))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :induct (Induct-hint-3r lst))))

;; (rTarai lst) = (Fb lst) when lst is a list of length 2, 3, or 4:

(local
 (defthm
     lst-rotates-with-minus-1-4a
     (let ((lst (list first second third forth)))
       (equal (lst-rotates-with-minus-1 1 lst)
	      (list (list (- first 1) second third forth)
		    (list (- second 1) third forth first))))
     :hints (("Goal"
	      :expand ((lst-rotates-with-minus-1
			1
			(list first second third forth)))))))

(local
 (defthm
     lst-rotates-with-minus-1-4b
     (let ((lst (list first second third forth)))
       (equal (lst-rotates-with-minus-1 2 lst)
	      (list (list (- first 1) second third forth)
		    (list (- second 1) third forth first)
		    (list (- third 1) forth first second)))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-4c
     (let ((lst (list first second third forth)))
       (equal (lst-rotates-with-minus-1 3 lst)
	      (list (list (- first 1) second third forth)
		    (list (- second 1) third forth first)
		    (list (- third 1) forth first second)
		    (list (- forth 1) first second third)))))
 )

(defthm
    rTarai=Fb-4a
    (implies (and (integer-listp lst)
		  (consp (nthcdr 3 lst))    ;; (len lst) > 3
		  (not
		   (consp (nthcdr 4 lst)))) ;; (len lst) <= 4
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst)))
	       (implies (and
			 (> first second)
			 (<= second third)
			 (equal (rTarai
				 (list
				  (- first 1) second
				  third fourth))
				(Fb
				 (list
				  (- first 1) second
				  third fourth)))
			 (equal (rTarai
				 (list
				  (- second 1) third
				  fourth first))
				(Fb
				 (list
				  (- second 1) third
				  fourth first)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth))
			    (Fb
			     (list (- second 1) third
				   fourth first))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth))
			    (Fb
			     (list (- second 1) third
				   fourth first))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-4b
    (implies (and (integer-listp lst)
		  (consp (nthcdr 3 lst))    ;; (len lst) > 3
		  (not
		   (consp (nthcdr 4 lst)))) ;; (len lst) <= 4
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst)))
	       (implies (and
			 (> first second)
			 (> second third)
			 (<= third fourth)
			 (equal (rTarai
				 (list
				  (- first 1) second
				  third fourth))
				(Fb
				 (list
				  (- first 1) second
				  third fourth)))
			 (equal (rTarai
				 (list
				  (- second 1) third
				  fourth first))
				(Fb
				 (list
				  (- second 1) third
				  fourth first)))
			 (equal (rTarai
				 (list (- third 1) fourth
				       first second))
				(Fb
				 (list (- third 1) fourth
				       first second)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth))
			    (Fb
			     (list (- second 1) third
				   fourth first))
			    (Fb
			     (list (- third 1) fourth
				   first second))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth))
			    (Fb
			     (list (- second 1) third
				   fourth first))
			    (Fb
			     (list (- third 1) fourth
				   first second))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-4c
    (implies (and (integer-listp lst)
		  (consp (nthcdr 3 lst))    ;; (len lst) > 3
		  (not
		   (consp (nthcdr 4 lst)))) ;; (len lst) <= 4
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst)))
	       (implies (and
			 (> first second)
			 (> second third)
			 (> third fourth)
			 (equal (rTarai
				 (list
				  (- first 1) second
				  third fourth))
				(Fb
				 (list
				  (- first 1) second
				  third fourth)))
			 (equal (rTarai
				 (list
				  (- second 1) third
				  fourth first))
				(Fb
				 (list
				  (- second 1) third
				  fourth first)))
			 (equal (rTarai
				 (list (- third 1) fourth
				       first second))
				(Fb
				 (list (- third 1) fourth
				       first second)))
			 (equal (rTarai
				 (list (- fourth 1) first
				       second third))
				(Fb
				 (list (- fourth 1) first
				       second third)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth))
			    (Fb
			     (list (- second 1) third
				   fourth first))
			    (Fb
			     (list (- third 1) fourth
				   first second))
			    (Fb
			     (list (- fourth 1) first
				   second third))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth))
			    (Fb
			     (list (- second 1) third
				   fourth first))
			    (Fb
			     (list (- third 1) fourth
				   first second))
			    (Fb
			     (list (- fourth 1) first
				   second third))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defun
    Induct-hint-4r (lst)
    (declare (xargs :measure (measure lst)))
    (if (and (integer-listp lst)
	     (consp (nthcdr 1 lst)))        ;; (len lst) > 1
	(cond ((not (consp (nthcdr 2 lst))) ;; (len lst) <= 2
	       0)
	      ((not (consp (nthcdr 3 lst))) ;; (len lst) <= 3
	       0)
	      ((not (consp (nthcdr 4 lst))) ;; (len lst) <= 4
	       (let ((first (first lst))
		     (second (second lst))
		     (third (third lst))
		     (fourth (fourth lst)))
		 (cond ((<= first second) 0)
		       ((<= second third)
			(+ (Induct-hint-4r
			    (list (- first 1) second
				  third fourth))
			   (Induct-hint-4r
			    (list (- second 1) third
				  fourth first))
			   (Induct-hint-4r
			    (list
			     (Fb (list (- first 1) second
				       third fourth))
			     (Fb (list (- second 1) third
				       fourth first))
			     ))))
		       ((<= third fourth)
			(+ (Induct-hint-4r
			    (list (- first 1) second
				  third fourth))
			   (Induct-hint-4r
			    (list (- second 1) third
				  fourth first))
			   (Induct-hint-4r
			    (list (- third 1) fourth
				  first second))
			   (Induct-hint-4r
			    (list
			     (Fb (list (- first 1) second
				       third fourth))
			     (Fb (list (- second 1) third
				       fourth first))
			     (Fb (list (- third 1) fourth
				       first second))
			     ))))
		       (t
			(+ (Induct-hint-4r
			    (list (- first 1) second
				  third fourth))
			   (Induct-hint-4r
			    (list (- second 1) third
				  fourth first))
			   (Induct-hint-4r
			    (list (- third 1) fourth
				  first second))
			   (Induct-hint-4r
			    (list (- fourth 1) first
				  second third))
			   (Induct-hint-4r
			    (list
			     (Fb (list (- first 1) second
				       third fourth))
			     (Fb (list (- second 1) third
				       fourth first))
			     (Fb (list (- third 1) fourth
				       first second))
			     (Fb (list (- fourth 1) first
				       second third))
			     )))))))
	      (t 0))
        0))

(defthm
    rTarai=Fb-4
    (implies (and (integer-listp lst)
		  (consp (nthcdr 1 lst))    ;; (len lst) > 1
		  (not
		   (consp (nthcdr 4 lst)))) ;; (len lst) <= 4
	     (equal (rTarai lst)(Fb lst)))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :induct (Induct-hint-4r lst))))

;; (rTarai lst) = (Fb lst) when lst is a list of length 2,3,4, or 5:

(local
 (defthm
     lst-rotates-with-minus-1-5a
     (let ((lst (list first second third forth fifth)))
       (equal (lst-rotates-with-minus-1 1 lst)
	      (list (list (- first 1) second third forth fifth)
		    (list (- second 1) third forth fifth first))))
     :hints (("Goal"
	      :expand ((lst-rotates-with-minus-1
			1
			(list first second third forth fifth))))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-5b
     (let ((lst (list first second third forth fifth)))
       (equal (lst-rotates-with-minus-1 2 lst)
	      (list (list (- first 1) second third forth fifth)
		    (list (- second 1) third forth fifth first)
		    (list (- third 1) forth fifth first second)))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-5c
     (let ((lst (list first second third forth fifth)))
       (equal (lst-rotates-with-minus-1 3 lst)
	      (list (list (- first 1) second third forth fifth)
		    (list (- second 1) third forth fifth first)
		    (list (- third 1) forth fifth first second)
		    (list (- forth 1) fifth first second third)))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-5d
     (let ((lst (list first second third forth fifth)))
       (equal (lst-rotates-with-minus-1 4 lst)
	      (list (list (- first 1) second third forth fifth)
		    (list (- second 1) third forth fifth first)
		    (list (- third 1) forth fifth first second)
		    (list (- forth 1) fifth first second third)
		    (list (- fifth 1) first second third forth)
		    ))))
 )

(defthm
    rTarai=Fb-5a
    (implies (and (integer-listp lst)
		  (consp (nthcdr 4 lst))    ;; (len lst) > 4
		  (not
		   (consp (nthcdr 5 lst)))) ;; (len lst) <= 5
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst))
		   (fifth (fifth lst)))
	       (implies (and
			 (> first second)
			 (<= second third)
			 (equal (rTarai
				 (list
				  (- first 1) second
				  third fourth fifth))
				(Fb
				 (list
				  (- first 1) second
				  third fourth fifth)))
			 (equal (rTarai
				 (list
				  (- second 1) third
				  fourth fifth first))
				(Fb
				 (list
				  (- second 1) third
				  fourth fifth first)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth fifth))
			    (Fb
			     (list (- second 1) third
				   fourth fifth first))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth fifth))
			    (Fb
			     (list (- second 1) third
				   fourth fifth first))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-5b
    (implies (and (integer-listp lst)
		  (consp (nthcdr 4 lst))    ;; (len lst) > 4
		  (not
		   (consp (nthcdr 5 lst)))) ;; (len lst) <= 5
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst))
		   (fifth (fifth lst)))
	       (implies (and
			 (> first second)
			 (> second third)
			 (<= third fourth)
			 (equal (rTarai
				 (list
				  (- first 1) second
				  third fourth fifth))
				(Fb
				 (list
				  (- first 1) second
				  third fourth fifth)))
			 (equal (rTarai
				 (list
				  (- second 1) third
				  fourth fifth first))
				(Fb
				 (list
				  (- second 1) third
				  fourth fifth first)))
			 (equal (rTarai
				 (list (- third 1) fourth
				       fifth first second))
				(Fb
				 (list (- third 1) fourth
				       fifth first second)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth fifth))
			    (Fb
			     (list (- second 1) third
				   fourth fifth first))
			    (Fb
			     (list (- third 1) fourth
				   fifth first second))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth fifth))
			    (Fb
			     (list (- second 1) third
				   fourth fifth first))
			    (Fb
			     (list (- third 1) fourth
				   fifth first second))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-5c
    (implies (and (integer-listp lst)
		  (consp (nthcdr 4 lst))    ;; (len lst) > 4
		  (not
		   (consp (nthcdr 5 lst)))) ;; (len lst) <= 5
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst))
		   (fifth (fifth lst)))
	       (implies (and
			 (> first second)
			 (> second third)
			 (> third fourth)
			 (<= fourth fifth)
			 (equal (rTarai
				 (list
				  (- first 1) second
				  third fourth fifth))
				(Fb
				 (list
				  (- first 1) second
				  third fourth fifth)))
			 (equal (rTarai
				 (list
				  (- second 1) third
				  fourth fifth first))
				(Fb
				 (list
				  (- second 1) third
				  fourth fifth first)))
			 (equal (rTarai
				 (list (- third 1) fourth
				       fifth first second))
				(Fb
				 (list (- third 1) fourth
				       fifth first second)))
			 (equal (rTarai
				 (list (- fourth 1) fifth
				       first second third))
				(Fb
				 (list (- fourth 1) fifth
				       first second third)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth fifth))
			    (Fb
			     (list (- second 1) third
				   fourth fifth first))
			    (Fb
			     (list (- third 1) fourth
				   fifth first second))
			    (Fb
			     (list (- fourth 1) fifth
				   first second third))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth fifth))
			    (Fb
			     (list (- second 1) third
				   fourth fifth first))
			    (Fb
			     (list (- third 1) fourth
				   fifth first second))
			    (Fb
			     (list (- fourth 1) fifth
				   first second third))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defthm
    rTarai=Fb-5d
    (implies (and (integer-listp lst)
		  (consp (nthcdr 4 lst))    ;; (len lst) > 4
		  (not
		   (consp (nthcdr 5 lst)))) ;; (len lst) <= 5
	     (let ((first (first lst))
		   (second (second lst))
		   (third (third lst))
		   (fourth (fourth lst))
		   (fifth (fifth lst)))
	       (implies (and
			 (> first second)
			 (> second third)
			 (> third fourth)
			 (> fourth fifth)
			 (equal (rTarai
				 (list
				  (- first 1) second
				  third fourth fifth))
				(Fb
				 (list
				  (- first 1) second
				  third fourth fifth)))
			 (equal (rTarai
				 (list
				  (- second 1) third
				  fourth fifth first))
				(Fb
				 (list
				  (- second 1) third
				  fourth fifth first)))
			 (equal (rTarai
				 (list (- third 1) fourth
				       fifth first second))
				(Fb
				 (list (- third 1) fourth
				       fifth first second)))
			 (equal (rTarai
				 (list (- fourth 1) fifth
				       first second third))
				(Fb
				 (list (- fourth 1) fifth
				       first second third)))
			 (equal (rTarai
				 (list (- fifth 1) first
				       second third fourth))
				(Fb
				 (list (- fifth 1) first
				       second third fourth)))
			 (equal
			  (rTarai
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth fifth))
			    (Fb
			     (list (- second 1) third
				   fourth fifth first))
			    (Fb
			     (list (- third 1) fourth
				   fifth first second))
			    (Fb
			     (list (- fourth 1) fifth
				   first second third))
			    (Fb
			     (list (- fifth 1) first
				   second third fourth))
			    ))
			  (Fb
			   (list
			    (Fb
			     (list (- first 1) second
				   third fourth fifth))
			    (Fb
			     (list (- second 1) third
				   fourth fifth first))
			    (Fb
			     (list (- third 1) fourth
				   fifth first second))
			    (Fb
			     (list (- fourth 1) fifth
				   first second third))
			    (Fb
			     (list (- fifth 1) first
				   second third fourth))
			    ))))
			(equal (rTarai lst)(Fb lst)))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (rTarai-def
		   Fb-sat-tarai-def-a))))

(defun
    Induct-hint-5r (lst)
    "Time:  203.55 seconds (prove: 54.76, print: 148.73, other: 0.06)"
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
	       (let ((first (first lst))
		     (second (second lst))
		     (third (third lst))
		     (fourth (fourth lst))
		     (fifth (fifth lst)))
		 (cond ((<= first second) 0)
		       ((<= second third)
			(+ (Induct-hint-5r
			    (list (- first 1) second
				  third fourth fifth))
			   (Induct-hint-5r
			    (list (- second 1) third
				  fourth fifth first))
			   (Induct-hint-5r
			    (list
			     (Fb (list (- first 1) second
				       third fourth fifth))
			     (Fb (list (- second 1) third
				       fourth fifth first))
			     ))))
		       ((<= third fourth)
			(+ (Induct-hint-5r
			    (list (- first 1) second
				  third fourth fifth))
			   (Induct-hint-5r
			    (list (- second 1) third
				  fourth fifth first))
			   (Induct-hint-5r
			    (list (- third 1) fourth
				  fifth first second))
			   (Induct-hint-5r
			    (list
			     (Fb (list (- first 1) second
				       third fourth fifth))
			     (Fb (list (- second 1) third
				       fourth fifth first))
			     (Fb (list (- third 1) fourth
				       fifth first second))
			     ))))
		       ((<= fourth fifth)
			(+ (Induct-hint-5r
			    (list (- first 1) second
				  third fourth fifth))
			   (Induct-hint-5r
			    (list (- second 1) third
				  fourth fifth first))
			   (Induct-hint-5r
			    (list (- third 1) fourth
				  fifth first second))
			   (Induct-hint-5r
			    (list (- fourth 1) fifth
				  first second third))
			   (Induct-hint-5r
			    (list
			     (Fb (list (- first 1) second
				       third fourth fifth))
			     (Fb (list (- second 1) third
				       fourth fifth first))
			     (Fb (list (- third 1) fourth
				       fifth first second))
			     (Fb (list (- fourth 1) fifth
				       first second third))
			     ))))
		       (t
			(+ (Induct-hint-5r
			    (list (- first 1) second
				  third fourth fifth))
			   (Induct-hint-5r
			    (list (- second 1) third
				  fourth fifth first))
			   (Induct-hint-5r
			    (list (- third 1) fourth
				  fifth first second))
			   (Induct-hint-5r
			    (list (- fourth 1) fifth
				  first second third))
			   (Induct-hint-5r
			    (list (- fifth 1) first
				  second third fourth))
			   (Induct-hint-5r
			    (list
			     (Fb (list (- first 1) second
				       third fourth fifth))
			     (Fb (list (- second 1) third
				       fourth fifth first))
			     (Fb (list (- third 1) fourth
				       fifth first second))
			     (Fb (list (- fourth 1) fifth
				       first second third))
			     (Fb (list (- fifth 1) first
				       second third fourth))
			     )))))))
	      (t 0))
        0))

(defthm
    rTarai=Fb-5
    (implies (and (integer-listp lst)
		  (consp (nthcdr 1 lst))    ;; (len lst) > 1
		  (not
		   (consp (nthcdr 5 lst)))) ;; (len lst) <= 5
	     (equal (rTarai lst)(Fb lst)))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :induct (Induct-hint-5r lst))))
