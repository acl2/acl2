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

;; The function Fb satisfies the tarai recursion for
;;  lists of length 7.

;; (certify-book "C:/acl2/tak/tarai4")

(in-package "ACL2")

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
;;----------------------------------------------------------
;; Fb satisfies the tarai restricted recursion equation
;;  when lst is a true list of integers of length 7.
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
    Fb-sat-tarai-def-7
    (implies (and (integerp first)
		  (integerp second)
		  (integerp third)
		  (integerp forth)
		  (integerp fifth)
		  (integerp sixth)
		  (integerp seventh))
	     (let ((lst (list first second third forth fifth
			      sixth seventh)))
	       (equal (Fb lst)
		      (if (<= (first lst)
			      (second lst))
			  (second lst)
			(Fb (Fb-lst (lst-rotates-with-minus-1
				     (- (len lst) 1)
				     lst)))))))
    :rule-classes nil)


