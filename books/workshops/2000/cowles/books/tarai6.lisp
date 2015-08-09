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
;;  Fb for lists of length 2-5:

;; (certify-book "C:/acl2/tak/tarai6")

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

;; (tarai lst) = (Fb lst) when lst is a list of length 2:

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
    tarai=Fb-2a
    (let ((lst (list first second)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (equal (tarai
			    (list (- first 1) second))
			   (Fb
			   (list (- first 1) second)))
		    (equal (tarai
			    (list (- second 1) first))
			   (Fb
			    (list (- second 1) first)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second))
			     (Fb
			      (list (- second 1) first))))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second))
			     (Fb
			      (list (- second 1) first))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :use (:instance
		   tarai-def
		   (lst (list first second))))))

(defun
    Induct-hint-2 (first second)
    (declare (xargs :measure
		    (measure (list first second))))
    (let ((lst (list first second)))
      (if (integer-listp lst)
	  (cond ((<= first second) 0)
		(t (+ (Induct-hint-2 (- first 1) second)
		      (Induct-hint-2 (- second 1) first)
		      (Induct-hint-2
		       (Fb (list (- first 1) second))
		       (Fb (list (- second 1) first))))))
	  0)))

(defthm
    tarai=Fb-2
    (let ((lst (list first second)))
      (implies (integer-listp lst)
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :induct (Induct-hint-2 first second))))

;; (tarai lst) = (Fb lst) when lst is a list of length 3:

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
    tarai=Fb-3a
    (let ((lst (list first second third)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (equal (tarai
			    (list (- first 1) second third))
			   (Fb
			   (list (- first 1) second third)))
		    (equal (tarai
			    (list (- second 1) third first))
			   (Fb
			    (list (- second 1) third first)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second third))
			     (Fb
			      (list (- second 1) third first))
			     (tarai
			      (list (- third 1) first second))
			     ))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second third))
			     (Fb
			      (list (- second 1) third first))
			     (tarai
			      (list (- third 1) first second))
			     ))))
	       (equal (tarai lst)(Fb lst))))
  :hints (("Goal"
	   :use (:instance
		 tarai-def
		 (lst (list first second third))))))

(defthm
    tarai=Fb-3b
    (let ((lst (list first second third)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (equal (tarai
			    (list (- first 1) second third))
			   (Fb
			   (list (- first 1) second third)))
		    (equal (tarai
			    (list (- second 1) third first))
			   (Fb
			    (list (- second 1) third first)))
		    (equal (tarai
			    (list (- third 1) first second))
			   (Fb
			    (list (- third 1) first second)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second third))
			     (Fb
			      (list (- second 1) third first))
			     (Fb
			      (list (- third 1) first second))
			     ))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second third))
			     (Fb
			      (list (- second 1) third first))
			     (Fb
			      (list (- third 1) first second))
			     ))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :in-theory (disable tarai=Fb-3a)
	     :use (:instance
		   tarai-def
		   (lst (list first second third))))))

(defun
    Induct-hint-3 (first second third)
    (declare (xargs :measure
		    (measure (list first second third))))
    (let ((lst (list first second third)))
      (if (integer-listp lst)
	  (cond ((<= first second) 0)
		((<= second third)
		 (+ (Induct-hint-3 (- first 1) second third)
		    (Induct-hint-3 (- second 1)third first)
		    (Induct-hint-3
		     (Fb (list (- first 1) second third))
		     (Fb (list (- second 1) third first))
		     (tarai (list (- third 1) first second)))))
		(t (+ (Induct-hint-3 (- first 1) second third)
		      (Induct-hint-3 (- second 1) third first)
		      (Induct-hint-3 (- third 1) first second)
		      (Induct-hint-3
		       (Fb (list (- first 1) second third))
		       (Fb (list (- second 1) third first))
		       (Fb (list (- third 1) first second))))))
          0)))

(defthm
    tarai=Fb-3
    (let ((lst (list first second third)))
      (implies (integer-listp lst)
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :induct (Induct-hint-3 first second third))))

;; (tarai lst) = (Fb lst) when lst is a list of length 4:

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
    tarai=Fb-4a
    (let ((lst (list first second third fourth)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (<= second third)
		    (equal (tarai
			    (list (- first 1) second
				  third fourth))
			   (Fb
			    (list (- first 1) second
				  third fourth)))
		    (equal (tarai
			    (list (- second 1) third
				  fourth first))
			   (Fb
			    (list (- second 1) third
				  fourth first)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second
				    third fourth))
			     (Fb
			      (list (- second 1) third
				    fourth first))
			     (tarai
			      (list (- third 1) fourth
				    first second))
			     (tarai
			      (list (- fourth 1) first
				    second third))))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second
				    third fourth))
			     (Fb
			      (list (- second 1) third
				    fourth first))
			     (tarai
			      (list (- third 1) fourth
				    first second))
			     (tarai
			      (list (- fourth 1) first
				    second third))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :use (:instance
		   tarai-def
		   (lst (list first second third fourth))))))

(defthm
    tarai=Fb-4b
    (let ((lst (list first second third fourth)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (<= third fourth)
		    (equal (tarai
			    (list (- first 1) second
				  third fourth))
			   (Fb
			    (list (- first 1) second
				  third fourth)))
		    (equal (tarai
			    (list (- second 1) third
				  fourth first))
			   (Fb
			    (list (- second 1) third
				  fourth first)))
		    (equal (tarai
			    (list (- third 1) fourth
				  first second))
			   (Fb
			    (list (- third 1) fourth
				  first second)))
		    (equal (tarai
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
			     (tarai
			      (list (- fourth 1) first
				    second third))))
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
			     (tarai
			      (list (- fourth 1) first
				    second third))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :use (:instance
		   tarai-def
		   (lst (list first second third fourth))))))


(defthm
    tarai=Fb-4c
    (let ((lst (list first second third fourth)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (> third fourth)
		    (equal (tarai
			    (list (- first 1) second
				  third fourth))
			   (Fb
			    (list (- first 1) second
				  third fourth)))
		    (equal (tarai
			    (list (- second 1) third
				  fourth first))
			   (Fb
			    (list (- second 1) third
				  fourth first)))
		    (equal (tarai
			    (list (- third 1) fourth
				  first second))
			   (Fb
			    (list (- third 1) fourth
				  first second)))
		    (equal (tarai
			    (list (- fourth 1) first
				  second third))
			   (Fb
			    (list (- fourth 1) first
				  second third)))
		    (equal (tarai
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
				    second third))))
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
				    second third))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :use (:instance
		   tarai-def
		   (lst (list first second third fourth))))))

(defun
    Induct-hint-4 (first second third fourth)
    (declare (xargs :measure
		    (measure (list first second
				   third fourth))))
    (let ((lst (list first second third fourth)))
      (if (integer-listp lst)
	  (cond ((<= first second) 0)
		((<= second third)
		 (+ (Induct-hint-4 (- first 1) second
				   third fourth)
		    (Induct-hint-4 (- second 1)third
				   fourth first)
		    (Induct-hint-4
		     (Fb (list (- first 1) second
			       third fourth))
		     (Fb (list (- second 1) third
			       fourth first))
		     (tarai (list (- third 1) fourth
				  first second))
		     (tarai (list (- fourth 1) first
				  second third)))))
		((<= third fourth)
		 (+ (Induct-hint-4 (- first 1) second
				   third fourth)
		    (Induct-hint-4 (- second 1) third
				   fourth first)
		    (Induct-hint-4 (- third 1) fourth
				   first second)
		    (Induct-hint-4
		     (Fb (list (- first 1) second
			       third fourth))
		     (Fb (list (- second 1) third
			       fourth first))
		     (Fb (list (- third 1) fourth
			       first second))
		     (tarai (list (- fourth 1) first
				  second third)))))
		(t (+ (Induct-hint-4 (- first 1) second
				     third fourth)
		      (Induct-hint-4 (- second 1) third
				     fourth first)
		      (Induct-hint-4 (- third 1) fourth
				     first second)
		      (Induct-hint-4 (- fourth 1) first
				     second third)
		      (Induct-hint-4
		       (Fb (list (- first 1) second
				 third fourth))
		       (Fb (list (- second 1) third
				 fourth first))
		       (Fb (list (- third 1) fourth
				 first second))
		       (Fb (list (- fourth 1) first
				  second third))))))
	  0)))

(defthm
    tarai=Fb-4
    (let ((lst (list first second third fourth)))
      (implies (integer-listp lst)
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :in-theory (disable Fb)
	     :induct (Induct-hint-4 first second
				    third fourth))))

;; (tarai lst) = (Fb lst) when lst is a list of length 5:

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
    tarai=Fb-5a
    (let ((lst (list first second third fourth fifth)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (<= second third)
		    (equal (tarai
			    (list (- first 1) second
				  third fourth fifth))
			   (Fb
			    (list (- first 1) second
				  third fourth fifth)))
		    (equal (tarai
			    (list (- second 1) third
				  fourth fifth first))
			   (Fb
			    (list (- second 1) third
				  fourth fifth first)))
		    (equal (tarai
			    (list
			     (Fb
			      (list (- first 1) second
				    third fourth fifth))
			     (Fb
			      (list (- second 1) third
				    fourth fifth first))
			     (tarai
			      (list (- third 1) fourth
				    fifth first second))
			     (tarai
			      (list (- fourth 1) fifth
				    first second third))
			     (tarai
			      (list (- fifth 1) first
				    second third fourth))))
			   (Fb
			    (list
			     (Fb
			      (list (- first 1) second
				    third fourth fifth))
			     (Fb
			      (list (- second 1) third
				    fourth fifth first))
			     (tarai
			      (list (- third 1) fourth
				    fifth first second))
			     (tarai
			      (list (- fourth 1) fifth
				    first second third))
			     (tarai
			      (list (- fifth 1) first
				    second third fourth))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :use (:instance
		   tarai-def
		   (lst (list first second third
			      fourth fifth))))))

(defthm
    tarai=Fb-5b
    (let ((lst (list first second third fourth fifth)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (<= third fourth)
		    (equal (tarai
			    (list (- first 1) second
				  third fourth fifth))
			   (Fb
			    (list (- first 1) second
				  third fourth fifth)))
		    (equal (tarai
			    (list (- second 1) third
				  fourth fifth first))
			   (Fb
			    (list (- second 1) third
				  fourth fifth first)))
		    (equal (tarai
			    (list (- third 1) fourth
				  fifth first second))
			   (Fb
			    (list (- third 1) fourth
				  fifth first second)))
		    (equal (tarai
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
			     (tarai
			      (list (- fourth 1) fifth
				    first second third))
			     (tarai
			      (list (- fifth 1) first
				    second third fourth))))
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
			     (tarai
			      (list (- fourth 1) fifth
				    first second third))
			     (tarai
			      (list (- fifth 1) first
				    second third fourth))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :use (:instance
		   tarai-def
		   (lst (list first second third
			      fourth fifth))))))

(defthm
    tarai=Fb-5c
    (let ((lst (list first second third fourth fifth)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (> third fourth)
		    (<= fourth fifth)
		    (equal (tarai
			    (list (- first 1) second
				  third fourth fifth))
			   (Fb
			    (list (- first 1) second
				  third fourth fifth)))
		    (equal (tarai
			    (list (- second 1) third
				  fourth fifth first))
			   (Fb
			    (list (- second 1) third
				  fourth fifth first)))
		    (equal (tarai
			    (list (- third 1) fourth
				  fifth first second))
			   (Fb
			    (list (- third 1) fourth
				  fifth first second)))
		    (equal (tarai
			    (list (- fourth 1) fifth
				  first second third))
			   (Fb
			    (list (- fourth 1) fifth
				  first second third)))
		    (equal (tarai
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
			     (tarai
			      (list (- fifth 1) first
				    second third fourth))))
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
			     (tarai
			      (list (- fifth 1) first
				    second third fourth))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :use (:instance
		   tarai-def
		   (lst (list first second third
			      fourth fifth))))))

(defthm
    tarai=Fb-5d
    (let ((lst (list first second third fourth fifth)))
      (implies (and (integer-listp lst)
		    (> first second)
		    (> second third)
		    (> third fourth)
		    (> fourth fifth)
		    (equal (tarai
			    (list (- first 1) second
				  third fourth fifth))
			   (Fb
			    (list (- first 1) second
				  third fourth fifth)))
		    (equal (tarai
			    (list (- second 1) third
				  fourth fifth first))
			   (Fb
			    (list (- second 1) third
				  fourth fifth first)))
		    (equal (tarai
			    (list (- third 1) fourth
				  fifth first second))
			   (Fb
			    (list (- third 1) fourth
				  fifth first second)))
		    (equal (tarai
			    (list (- fourth 1) fifth
				  first second third))
			   (Fb
			    (list (- fourth 1) fifth
				  first second third)))
		    (equal (tarai
			    (list (- fifth 1) first
				  second third fourth))
			   (Fb
			    (list (- fifth 1) first
				  second third fourth)))
		    (equal (tarai
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
				    second third fourth))))
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
				    second third fourth))))))
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
	     :in-theory (disable tarai=Fb-5a
				 tarai=Fb-5b
				 tarai=Fb-5c)
	     :use (:instance
		   tarai-def
		   (lst (list first second third
			      fourth fifth))))))

(defun
    Induct-hint-5 (first second third fourth fifth)
    (declare (xargs :measure
		    (measure (list first second
				   third fourth fifth))))
    (let ((lst (list first second third fourth fifth)))
      (if (integer-listp lst)
	  (cond ((<= first second) 0)
		((<= second third)
		 (+ (Induct-hint-5 (- first 1) second
				   third fourth fifth)
		    (Induct-hint-5 (- second 1)third
				   fourth fifth first)
		    (Induct-hint-5
		     (Fb (list (- first 1) second
			       third fourth fifth))
		     (Fb (list (- second 1) third
			       fourth fifth first))
		     (tarai (list (- third 1) fourth
				  fifth first second))
		     (tarai (list (- fourth 1) fifth
				  first second third))
		     (tarai (list (- fifth 1) first
				  second third fourth)))))
		((<= third fourth)
		 (+ (Induct-hint-5 (- first 1) second
				   third fourth fifth)
		    (Induct-hint-5 (- second 1) third
				   fourth fifth first)
		    (Induct-hint-5 (- third 1) fourth
				   fifth first second)
		    (Induct-hint-5
		     (Fb (list (- first 1) second
			       third fourth fifth))
		     (Fb (list (- second 1) third
			       fourth fifth first))
		     (Fb (list (- third 1) fourth
			       fifth first second))
		     (tarai (list (- fourth 1) fifth
				  first second third))
		     (tarai (list (- fifth 1) first
				  second third fourth)))))
		((<= fourth fifth)
		 (+ (Induct-hint-5 (- first 1) second
				   third fourth fifth)
		    (Induct-hint-5 (- second 1) third
				   fourth fifth first)
		    (Induct-hint-5 (- third 1) fourth
				   fifth first second)
		    (Induct-hint-5 (- fourth 1) fifth
				   first second third)
		    (Induct-hint-5
		     (Fb (list (- first 1) second
			       third fourth fifth))
		     (Fb (list (- second 1) third
			       fourth fifth first))
		     (Fb (list (- third 1) fourth
			       fifth first second))
		     (Fb (list (- fourth 1) fifth
			       first second third))
		     (tarai (list (- fifth 1) first
				  second third fourth)))))
		(t (+ (Induct-hint-5 (- first 1) second
				     third fourth fifth)
		      (Induct-hint-5 (- second 1) third
				     fourth fifth first)
		      (Induct-hint-5 (- third 1) fourth
				     fifth first second)
		      (Induct-hint-5 (- fourth 1) fifth
				     first second third)
		      (Induct-hint-5 (- fifth 1) first
				     second third fourth)
		      (Induct-hint-5
		       (Fb (list (- first 1) second
				 third fourth fifth))
		       (Fb (list (- second 1) third
				 fourth fifth first))
		       (Fb (list (- third 1) fourth
				 fifth first second))
		       (Fb (list (- fourth 1) fifth
				 first second third))
		       (Fb (list (- fifth 1) first
				 second third fourth))))))
	  0)))

(defthm
    tarai=Fb-5
    (let ((lst (list first second third fourth fifth)))
      (implies (integer-listp lst)
	       (equal (tarai lst)(Fb lst))))
    :hints (("Goal"
					:in-theory (disable Fb)
	     :induct (Induct-hint-5 first second third
				    fourth fifth))))

