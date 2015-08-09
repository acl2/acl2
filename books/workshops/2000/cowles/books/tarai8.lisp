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

;; Any total function from integer lists to integers that
;;  satisfies the tarai recursion must equal the function
;;  Fb for lists of length 7:

;; (certify-book "C:/acl2/tak/tarai8")

(in-package "ACL2")

(include-book "tarai5")

;; The book tarai5, included above, includes all the
;;  definitions required to define Bailey's version (called
;;  Fb) of the f function for Knuth's Theorem 4. The included
;;  book also contains a theorem showing that the function Fb
;;  satisfies the tarai recursion for lists of lengths between
;;  2 and 7.

;; Fb satisfies the tarai recursion (rule-classes nil)
;;    (from the book tarai5):
#|  (defthm
      Fb-sat-tarai-def
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
			      (- (LEN lst) 1)
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
 (((tarai *)  => *)
  ((tarai-lst *)  => *))

 (local (defun
	    tarai (lst)
	    (Fb lst)))

 (local (defun
	    tarai-lst (lst)
	    (Fb-lst lst)))

 (defthm
     tarai-def
     (implies (and
	       (integer-listp lst)
	       (consp (rest lst))        ;; (len lst) > 1
	       (not
		(consp (nthcdr 7 lst)))) ;; (len lst) <= 7
	      (equal (tarai lst)
		     (if (<= (first lst)
			     (second lst))
			 (second lst)
		         (tarai (tarai-lst
				 (lst-rotates-with-minus-1
				  (- (LEN lst) 1)
				  lst))))))
     :rule-classes nil
     :hints (("Goal"
	      :in-theory (disable Fb Fb-lst len
				  lst-rotates-with-minus-1)
	      :use Fb-sat-tarai-def)))

 (defthm
     tarai-lst-def
     (equal (tarai-lst lst)
	    (if (consp lst)
		(cons (tarai (first lst))
		      (tarai-lst (rest lst)))
	        nil))
     :rule-classes :definition)

 (defthm
    Integerp-tarai
    (implies (and (integer-listp lst)
		  (consp (rest lst)))
	     (integerp (tarai lst)))
    :rule-classes (:rewrite :type-prescription))
 ) ;; end encapsulate

(defthm
    true-lisp-tarai-lst
    (true-listp (tarai-lst lst))
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
    tarai=Fb-1
    (implies (and (integer-listp lst)
		  (consp (rest lst))        ;; (len lst) > 1
		  (not
		   (consp (nthcdr 7 lst))) ;; (len lst) <= 7
		  (<= (first lst)(second lst)))
	     (equal (tarai lst)(Fb lst)))
    :hints (("Goal"
	     :use tarai-def)))

;; (tarai lst) = (Fb lst) when lst is a list of length 7:

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
    tarai=Fb-7a
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (<= second third)
		    (equal (tarai
			    (list (- first 1) second third
				  fourth fifth sixth seventh))
			   (Fb
			    (list (- first 1) second third
				  fourth fifth sixth seventh)))
		    (equal (tarai
			    (list (- second 1) third fourth
				  fifth sixth seventh first))
			   (Fb
			    (list (- second 1) third fourth
				  fifth sixth seventh first)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (tarai
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (tarai
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (tarai
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (tarai
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (tarai
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (tarai
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (tarai
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (tarai
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (tarai
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (tarai
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :use (:instance
		   tarai-def
		   (lst (list first second third
			      fourth fifth sixth seventh))))))

(defthm
    tarai=Fb-7b
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (<= third fourth)
		    (equal (tarai
			    (list (- first 1) second third
				  fourth fifth sixth seventh))
			   (Fb
			    (list (- first 1) second third
				  fourth fifth sixth seventh)))
		    (equal (tarai
			    (list (- second 1) third fourth
				  fifth sixth seventh first))
			   (Fb
			    (list (- second 1) third fourth
				  fifth sixth seventh first)))
		    (equal (tarai
			    (list (- third 1) fourth fifth
				  sixth seventh first second))
			   (Fb
			    (list (- third 1) fourth fifth
				  sixth seventh first second)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (Fb
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (tarai
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (tarai
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (tarai
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (tarai
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (Fb
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (tarai
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (tarai
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (tarai
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (tarai
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :use (:instance
		   tarai-def
		   (lst (list first second third
			      fourth fifth sixth seventh))))))

(defthm
    Fb-sat-tarai-def-7c
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (> third fourth)
		    (<= fourth fifth))
	       (equal (Fb
		       (list
			(Fb
			 (list (- first 1) second third
			       fourth fifth sixth seventh))
			(Fb
			 (list (- second 1) third fourth
			       fifth sixth seventh first))
			(Fb
			 (list (- third 1) fourth fifth
			       sixth seventh first second))
			(Fb
			 (list (- fourth 1) fifth sixth
			       seventh first second third))
			(tarai
			 (list (- fifth 1) sixth seventh first
			       second third fourth))
			(tarai
			 (list (- sixth 1) seventh first second
			       third fourth fifth))
			(tarai
			 (list (- seventh 1) first second
			       third fourth fifth sixth))))
		      (Fb lst)))))

(defthm
    tarai=Fb-7c
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (> third fourth)
		    (<= fourth fifth)
		    (equal (tarai
			    (list (- first 1) second third
				  fourth fifth sixth seventh))
			   (Fb
			    (list (- first 1) second third
				  fourth fifth sixth seventh)))
		    (equal (tarai
			    (list (- second 1) third fourth
				  fifth sixth seventh first))
			   (Fb
			    (list (- second 1) third fourth
				  fifth sixth seventh first)))
		    (equal (tarai
			    (list (- third 1) fourth fifth
				  sixth seventh first second))
			   (Fb
			    (list (- third 1) fourth fifth
				  sixth seventh first second)))
		    (equal (tarai
			    (list (- fourth 1) fifth sixth
				  seventh first second third))
			   (Fb
			    (list (- fourth 1) fifth sixth
				  seventh first second third)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (Fb
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (Fb
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (tarai
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (tarai
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (tarai
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (Fb
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (Fb
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (tarai
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (tarai
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (tarai
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (:instance
		    tarai-def
		    (lst (list first second third
			       fourth fifth sixth seventh))))))

(defthm
    Fb-sat-tarai-def-7d
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (> third fourth)
		    (> fourth fifth)
		    (<= fifth sixth))
	       (equal (Fb
		       (list
			(Fb
			 (list (- first 1) second third
			       fourth fifth sixth seventh))
			(Fb
			 (list (- second 1) third fourth
			       fifth sixth seventh first))
			(Fb
			 (list (- third 1) fourth fifth
			       sixth seventh first second))
			(Fb
			 (list (- fourth 1) fifth sixth
			       seventh first second third))
			(Fb
			 (list (- fifth 1) sixth seventh first
			       second third fourth))
			(tarai
			 (list (- sixth 1) seventh first second
			       third fourth fifth))
			(tarai
			 (list (- seventh 1) first second
			       third fourth fifth sixth))))
		      (Fb lst)))))

(defthm
    tarai=Fb-7d
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (> third fourth)
		    (> fourth fifth)
		    (<= fifth sixth)
		    (equal (tarai
			    (list (- first 1) second third
				  fourth fifth sixth seventh))
			   (Fb
			    (list (- first 1) second third
				  fourth fifth sixth seventh)))
		    (equal (tarai
			    (list (- second 1) third fourth
				  fifth sixth seventh first))
			   (Fb
			    (list (- second 1) third fourth
				  fifth sixth seventh first)))
		    (equal (tarai
			    (list (- third 1) fourth fifth
				  sixth seventh first second))
			   (Fb
			    (list (- third 1) fourth fifth
				  sixth seventh first second)))
		    (equal (tarai
			    (list (- fourth 1) fifth sixth
				  seventh first second third))
			   (Fb
			    (list (- fourth 1) fifth sixth
				  seventh first second third)))
		    (equal (tarai
			    (list (- fifth 1) sixth seventh first
				  second third fourth))
			   (Fb
			    (list (- fifth 1) sixth seventh first
				  second third fourth)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (Fb
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (Fb
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (Fb
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (tarai
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (tarai
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (Fb
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (Fb
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (Fb
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (tarai
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (tarai
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (:instance
		   tarai-def
		   (lst (list first second third
			      fourth fifth sixth seventh))))))

(defthm
    Fb-sat-tarai-def-7e
    ;;Time:  2160.88 seconds (prove: 1123.98, print: 1036.73, other: 0.17)
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (> third fourth)
		    (> fourth fifth)
		    (> fifth sixth)
		    (<= sixth seventh))
	       (equal (Fb
		       (list
			(Fb
			 (list (- first 1) second third
			       fourth fifth sixth seventh))
			(Fb
			 (list (- second 1) third fourth
			       fifth sixth seventh first))
			(Fb
			 (list (- third 1) fourth fifth
			       sixth seventh first second))
			(Fb
			 (list (- fourth 1) fifth sixth
			       seventh first second third))
			(Fb
			 (list (- fifth 1) sixth seventh first
			       second third fourth))
			(Fb
			 (list (- sixth 1) seventh first second
			       third fourth fifth))
			(tarai
			 (list (- seventh 1) first second
			       third fourth fifth sixth))))
		      (Fb lst)))))

(defthm
    tarai=Fb-7e
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (> third fourth)
		    (> fourth fifth)
		    (> fifth sixth)
		    (<= sixth seventh)
		    (equal (tarai
			    (list (- first 1) second third
				  fourth fifth sixth seventh))
			   (Fb
			    (list (- first 1) second third
				  fourth fifth sixth seventh)))
		    (equal (tarai
			    (list (- second 1) third fourth
				  fifth sixth seventh first))
			   (Fb
			    (list (- second 1) third fourth
				  fifth sixth seventh first)))
		    (equal (tarai
			    (list (- third 1) fourth fifth
				  sixth seventh first second))
			   (Fb
			    (list (- third 1) fourth fifth
				  sixth seventh first second)))
		    (equal (tarai
			    (list (- fourth 1) fifth sixth
				  seventh first second third))
			   (Fb
			    (list (- fourth 1) fifth sixth
				  seventh first second third)))
		    (equal (tarai
			    (list (- fifth 1) sixth seventh first
				  second third fourth))
			   (Fb
			    (list (- fifth 1) sixth seventh first
				  second third fourth)))
		    (equal (tarai
			    (list (- sixth 1) seventh first second
				  third fourth fifth))
			   (Fb
			    (list (- sixth 1) seventh first second
				  third fourth fifth)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (Fb
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (Fb
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (Fb
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (Fb
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (tarai
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (Fb
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (Fb
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (Fb
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (Fb
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (tarai
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use (:instance
		   tarai-def
		   (lst (list first second third
			      fourth fifth sixth seventh))))))

(defthm
    tarai=Fb-7f
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (> third fourth)
		    (> fourth fifth)
		    (> fifth sixth)
		    (> sixth seventh)
		    (equal (tarai
			    (list (- first 1) second third
				  fourth fifth sixth seventh))
			   (Fb
			    (list (- first 1) second third
				  fourth fifth sixth seventh)))
		    (equal (tarai
			    (list (- second 1) third fourth
				  fifth sixth seventh first))
			   (Fb
			    (list (- second 1) third fourth
				  fifth sixth seventh first)))
		    (equal (tarai
			    (list (- third 1) fourth fifth
				  sixth seventh first second))
			   (Fb
			    (list (- third 1) fourth fifth
				  sixth seventh first second)))
		    (equal (tarai
			    (list (- fourth 1) fifth sixth
				  seventh first second third))
			   (Fb
			    (list (- fourth 1) fifth sixth
				  seventh first second third)))
		    (equal (tarai
			    (list (- fifth 1) sixth seventh first
				  second third fourth))
			   (Fb
			    (list (- fifth 1) sixth seventh first
				  second third fourth)))
		    (equal (tarai
			    (list (- sixth 1) seventh first second
				  third fourth fifth))
			   (Fb
			    (list (- sixth 1) seventh first second
				  third fourth fifth)))
		    (equal (tarai
			    (list (- seventh 1) first second
				  third fourth fifth sixth))
			   (Fb
			    (list (- seventh 1) first second
				  third fourth fifth sixth)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (Fb
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (Fb
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (Fb
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (Fb
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (Fb
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second third
				    fourth fifth sixth seventh))
			     (Fb
			      (list (- second 1) third fourth
				    fifth sixth seventh first))
			     (Fb
			      (list (- third 1) fourth fifth
				    sixth seventh first second))
			     (Fb
			      (list (- fourth 1) fifth sixth
				    seventh first second third))
			     (Fb
			      (list (- fifth 1) sixth seventh first
				    second third fourth))
			     (Fb
			      (list (- sixth 1) seventh first second
				    third fourth fifth))
			     (Fb
			      (list (- seventh 1) first second
				    third fourth fifth sixth))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :use ((:instance
		    tarai-def
		    (lst (list first second third
			       fourth fifth sixth seventh)))
		   (:instance
		    Fb-sat-tarai-def
		    (lst (list first second third
			       fourth fifth sixth seventh)))))))

(defun
    Induct-hint-7 (first second third fourth fifth sixth seventh)
    "Time:  1205.95 seconds (prove: 575.73, print: 630.05, other: 0.17)"
    (declare (xargs :measure
		    (measure (list first second third
				   fourth fifth sixth seventh))))
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (if (integer-listp lst)
	  (cond ((<= first second) 0)
		((<= second third)
		 (+ (Induct-hint-7 (- first 1) second third
				   fourth fifth sixth seventh)
		    (Induct-hint-7 (- second 1)third fourth
				   fifth sixth seventh first)
		    (Induct-hint-7
		     (Fb (list (- first 1) second
			       third fourth fifth sixth seventh))
		     (Fb (list (- second 1) third
			       fourth fifth sixth seventh first))
		     (tarai (list (- third 1) fourth
				  fifth sixth seventh first second))
		     (tarai (list (- fourth 1) fifth
				  sixth seventh first second third))
		     (tarai (list (- fifth 1) sixth seventh first
				  second third fourth))
		     (tarai (list (- sixth 1) seventh first second
				  third fourth fifth))
		     (tarai (list (- seventh 1) first second
				  third fourth fifth sixth)))))
		((<= third fourth)
		 (+ (Induct-hint-7 (- first 1) second third
				   fourth fifth sixth seventh)
		    (Induct-hint-7 (- second 1)third fourth
				   fifth sixth seventh first)
		    (Induct-hint-7 (- third 1) fourth
				   fifth sixth seventh first second)
		    (Induct-hint-7
		     (Fb (list (- first 1) second
			       third fourth fifth sixth seventh))
		     (Fb (list (- second 1) third
			       fourth fifth sixth seventh first))
		     (Fb (list (- third 1) fourth
			       fifth sixth seventh first second))
		     (tarai (list (- fourth 1) fifth
				  sixth seventh first second third))
		     (tarai (list (- fifth 1) sixth seventh first
				  second third fourth))
		     (tarai (list (- sixth 1) seventh first second
				  third fourth fifth))
		     (tarai (list (- seventh 1) first second
				  third fourth fifth sixth)))))
		((<= fourth fifth)
		 (+ (Induct-hint-7 (- first 1) second third
				   fourth fifth sixth seventh)
		    (Induct-hint-7 (- second 1)third fourth
				   fifth sixth seventh first)
		    (Induct-hint-7 (- third 1) fourth
				   fifth sixth seventh first second)
		    (Induct-hint-7 (- fourth 1) fifth
				   sixth seventh first second third)
		    (Induct-hint-7
		     (Fb (list (- first 1) second
			       third fourth fifth sixth seventh))
		     (Fb (list (- second 1) third
			       fourth fifth sixth seventh first))
		     (Fb (list (- third 1) fourth
			       fifth sixth seventh first second))
		     (Fb (list (- fourth 1) fifth
			       sixth seventh first second third))
		     (tarai (list (- fifth 1) sixth seventh first
				  second third fourth))
		     (tarai (list (- sixth 1) seventh first second
				  third fourth fifth))
		     (tarai (list (- seventh 1) first second
				  third fourth fifth sixth)))))
		((<= fifth sixth)
		 (+ (Induct-hint-7 (- first 1) second third
				   fourth fifth sixth seventh)
		    (Induct-hint-7 (- second 1)third fourth
				   fifth sixth seventh first)
		    (Induct-hint-7 (- third 1) fourth
				   fifth sixth seventh first second)
		    (Induct-hint-7 (- fourth 1) fifth
				   sixth seventh first second third)
		    (Induct-hint-7 (- fifth 1) sixth seventh first
				   second third fourth)
		    (Induct-hint-7
		     (Fb (list (- first 1) second
			       third fourth fifth sixth seventh))
		     (Fb (list (- second 1) third
			       fourth fifth sixth seventh first))
		     (Fb (list (- third 1) fourth
			       fifth sixth seventh first second))
		     (Fb (list (- fourth 1) fifth
			       sixth seventh first second third))
		     (Fb (list (- fifth 1) sixth seventh first
			       second third fourth))
		     (tarai (list (- sixth 1) seventh first second
				  third fourth fifth))
		     (tarai (list (- seventh 1) first second
				  third fourth fifth sixth)))))
		((<= sixth seventh)
		 (+ (Induct-hint-7 (- first 1) second third
				   fourth fifth sixth seventh)
		    (Induct-hint-7 (- second 1)third fourth
				   fifth sixth seventh first)
		    (Induct-hint-7 (- third 1) fourth
				   fifth sixth seventh first second)
		    (Induct-hint-7 (- fourth 1) fifth
				   sixth seventh first second third)
		    (Induct-hint-7 (- fifth 1) sixth seventh first
				   second third fourth)
		    (Induct-hint-7 (- sixth 1) seventh first second
				   third fourth fifth)
		    (Induct-hint-7
		     (Fb (list (- first 1) second
			       third fourth fifth sixth seventh))
		     (Fb (list (- second 1) third
			       fourth fifth sixth seventh first))
		     (Fb (list (- third 1) fourth
			       fifth sixth seventh first second))
		     (Fb (list (- fourth 1) fifth
			       sixth seventh first second third))
		     (Fb (list (- fifth 1) sixth seventh first
			       second third fourth))
		     (Fb (list (- sixth 1) seventh first second
			       third fourth fifth))
		     (tarai (list (- seventh 1) first second
				  third fourth fifth sixth)))))
		(t
		 (+ (Induct-hint-7 (- first 1) second third
				   fourth fifth sixth seventh)
		    (Induct-hint-7 (- second 1)third fourth
				   fifth sixth seventh first)
		    (Induct-hint-7 (- third 1) fourth
				   fifth sixth seventh first second)
		    (Induct-hint-7 (- fourth 1) fifth
				   sixth seventh first second third)
		    (Induct-hint-7 (- fifth 1) sixth seventh first
				   second third fourth)
		    (Induct-hint-7 (- sixth 1) seventh first second
				   third fourth fifth)
		    (Induct-hint-7 (- seventh 1) first second
				   third fourth fifth sixth)
		    (Induct-hint-7
		     (Fb (list (- first 1) second
			       third fourth fifth sixth seventh))
		     (Fb (list (- second 1) third
			       fourth fifth sixth seventh first))
		     (Fb (list (- third 1) fourth
			       fifth sixth seventh first second))
		     (Fb (list (- fourth 1) fifth
			       sixth seventh first second third))
		     (Fb (list (- fifth 1) sixth seventh first
			       second third fourth))
		     (Fb (list (- sixth 1) seventh first second
			       third fourth fifth))
		     (Fb (list (- seventh 1) first second
			       third fourth fifth sixth))))))
	  0)))

(defthm
    tarai=Fb-7
    (let ((lst (list first second third fourth fifth sixth seventh)))
      (implies (integer-listp lst)
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :induct (Induct-hint-7 first second third
				    fourth fifth sixth seventh))))
