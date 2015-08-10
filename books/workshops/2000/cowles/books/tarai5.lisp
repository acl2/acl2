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

;; The function Fb satisfies the tarai recursion and the
;;  restricted tarai recursion for lists of lengths between
;;  2 and 7. This book summarizes books tarai1-tarai4.

;; Times using 600 MHz pentium:
;;  The book in tarai3.lisp requires over 46 min. to certify.
;;  The book in tarai4.lisp requires over 3.85 hours to
;;   certify.

;; Many of the books tarai2-tarai4 require ACL2 Version 2.5
;;  or later to certify. A feature, of the implementation of
;;  linear arithmetic in Version 2.4, that prevented the
;;  straightforward proofs of some theorems in these books,
;;  has been eliminated in Version 2.5. (Essentially, the
;;  2.4 version of linear arithmetic sometimes dealt with
;;  equations of the form  VAR = Term by substituting Term
;;  for SOME, but NOT ALL, occurrences of VAR.)

;; (certify-book "C:/acl2/tak/tarai5")

(in-package "ACL2")

(local (include-book "tarai1"))

(local (include-book "tarai2"))

(local (include-book "tarai3"))

(local (include-book "tarai4"))

(defmacro
    last-el (lst)
    "Return the last element in the list lst."
    (list 'car (list 'last lst)))

(defun
    Gb (lst)
    "Bailey's g function for Knuth's Theorem 4.
     The input lst is intended to be a nonempty
     list of integers."
    (declare (xargs :guard (and (integer-listp lst)
				(consp lst))))
    (cond ((consp (nthcdr 3 lst))    ;; (len lst) > 3
	   (if (or (equal (first lst)
			  (+ (second lst) 1))
		   (> (second lst)
		      (+ (third lst) 1)))
	       (Gb (rest lst))
	       (max (third lst)
		    (last-el lst))))
	  (t (last-el lst))))       ;; (len lst) <= 3

(defun
    decreasing-p (lst)
    "Determine if the elements in lst are strictly decreasing."
    (declare (xargs :guard (rational-listp lst)))
    (if (consp (rest lst))         ;; (len lst) > 1
	(and (> (first lst)(second lst))
	     (decreasing-p (rest lst)))
        t))

(defun
    first-non-decrease (lst)
    "Return the front of lst up to and including the first
     element that does not strictly decrease."
    (declare (xargs :guard (and (rational-listp lst)
				(not (decreasing-p lst)))))
    (if (consp (rest lst))        ;; (len lst) > 1
	(if (<= (first lst)(second lst))
	    (list (first lst)(second lst))
 	    (cons (first lst)
		  (first-non-decrease (rest lst))))
        lst))

(defun
    Fb (lst)
    "Bailey's f function for Knuth's theorem 4.
     The input lst is intended to be a nonempty
     list of integers."
    (declare (xargs :guard (and (integer-listp lst)
				(consp lst))))
    (if (decreasing-p lst)
	(first lst)
        (Gb (first-non-decrease lst))))

(defun
    rotate (lst)
    "Return the result of shifting the first element
     of the list lst onto the tail end of lst."
    (declare (xargs :guard (true-listp lst)))
    (if (consp lst)
	(append (rest lst)(list (first lst)))
        nil))

(defun
    minus-1 (lst)
    "Return the result of replacing (first lst)
     with (first lst) - 1."
    (declare (xargs :guard (and (rational-listp lst)
				(consp lst))))
    (if (consp lst)
	(cons (- (first lst) 1)
	      (rest lst))
        lst))

(defun
    lst-rotates-with-minus-1 (n lst)
    "Return the list of n+1 successive rotates of the
     list lst with the first of each rotate replaced
     by the first minus 1."
    (declare (xargs :guard (and (rational-listp lst)
				(consp lst)
				(integerp n)
				(>= n 0))))
    (if (zp n)
	(list (minus-1 lst))
        (cons (minus-1 lst)
	      (lst-rotates-with-minus-1 (- n 1)
					(rotate lst)))))

(defun
    Fb-lst (lst)
    (if (consp lst)
	(cons (Fb (first lst))
	      (Fb-lst (rest lst)))
        nil))

(defun
    dec-front-len (lst)
    "Return the number of strictly decreasing elements
     at the front of the list lst."
    (declare (xargs :guard (rational-listp lst)))
    (cond ((consp (rest lst))  ;; (len lst) > 1
	   (if (<= (first lst)(second lst))
	       1
	       (+ 1 (dec-front-len (rest lst)))))
	  ((consp lst) 1)      ;; (len lst) = 1
	  (t 0)))              ;; (len lst) = 0

(defthm
    Fb-sat-tarai-def
    (implies (and (integer-listp lst)
		  (consp (rest lst))           ;; (len lst) > 1
		  (not (consp (nthcdr 7 lst))) ;; (len lst) <= 7
		  )
	     (equal (Fb lst)
		    (if (<= (first lst)
			    (second lst))
			(second lst)
		      (Fb (Fb-lst (lst-rotates-with-minus-1
				   (- (len lst) 1)
				   lst))))))
    :rule-classes nil
    :hints (("Goal"
	     :in-theory (disable Fb Fb-lst len
				 lst-rotates-with-minus-1)
	     :use ((:instance
		    Fb-sat-tarai-def-2
		    (first (first lst))
		    (second (second lst)))
		   (:instance
		    Fb-sat-tarai-def-3
		    (first (first lst))
		    (second (second lst))
		    (third (third lst)))
		   (:instance
		    Fb-sat-tarai-def-4
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (forth (fourth lst)))
		   (:instance
		    Fb-sat-tarai-def-5
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (forth (fourth lst))
		    (fifth (fifth lst)))
		   (:instance
		    Fb-sat-tarai-def-6
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (forth (fourth lst))
		    (fifth (fifth lst))
		    (sixth (sixth lst)))
		   (:instance
		    Fb-sat-tarai-def-7
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (forth (fourth lst))
		    (fifth (fifth lst))
		    (sixth (sixth lst))
		    (seventh (seventh lst)))
		   ))))

(defthm
    Fb-sat-tarai-def-a
    (implies (and (integer-listp lst)
		  (consp (rest lst))           ;; (len lst) > 1
		  (not (consp (nthcdr 7 lst))) ;; (len lst) <= 7
		  )
	     (equal (Fb lst)
		    (if (<= (first lst)
			    (second lst))
			(second lst)
		      (Fb (Fb-lst (lst-rotates-with-minus-1
				   (- (dec-front-len lst) 1)
				   lst))))))
    :rule-classes nil
    :hints (("Goal"
	     :in-theory (disable Fb Fb-lst dec-front-len
				 lst-rotates-with-minus-1)
	     :use ((:instance
		    Fb-sat-tarai-def-2a
		    (first (first lst))
		    (second (second lst)))
		   (:instance
		    Fb-sat-tarai-def-3a
		    (first (first lst))
		    (second (second lst))
		    (third (third lst)))
		   (:instance
		    Fb-sat-tarai-def-4a
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (forth (fourth lst)))
		   (:instance
		    Fb-sat-tarai-def-5a
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (forth (fourth lst))
		    (fifth (fifth lst)))
		   (:instance
		    Fb-sat-tarai-def-6a
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (forth (fourth lst))
		    (fifth (fifth lst))
		    (sixth (sixth lst)))
		   (:instance
		    Fb-sat-tarai-def-7a
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (forth (fourth lst))
		    (fifth (fifth lst))
		    (sixth (sixth lst))
		    (seventh (seventh lst)))
		   ))))
