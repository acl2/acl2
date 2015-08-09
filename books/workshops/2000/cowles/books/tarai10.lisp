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

;; These implementations of Knuth's and Bailey's versions of the f function
;;  for Knuth's theorem 4 compute the same results for all true lists of
;;  lengths 0-4 and for all lists of integers of length 5. An example is
;;  provided showing there are lists of integers of length 6 for which the
;;  two functions compute different results.

;; (certify-book "C:/acl2/tak/tarai10")

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
    Gk (lst)
    "Knuth's g function for Knuth's Theorem 4.
     The input lst is intended to be a nonempty
     list of integers."
    (declare (xargs :guard (and (integer-listp lst)
				(consp lst))))
    (cond ((consp (nthcdr 2 lst))    ;; (len lst) > 2
	   (cond ((equal (first lst)
		      (+ (second lst) 1))
		  (Gk (rest lst)))
		 ((equal (second lst)
			 (+ (third lst) 1))
		  (max (third lst)
		       (last-el lst)))
		 (t (last-el lst))))
	  (t (last-el lst))))       ;; (len lst) <= 2

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
    Fk (lst)
    "Knuth's f function for Knuth's theorem 4.
     The input lst is intended to be a nonempty
     list of integers."
    (declare (xargs :guard (and (integer-listp lst)
				(consp lst))))
    (if (decreasing-p lst)
	(first lst)
        (Gk (first-non-decrease lst))))

(defthm
    Fk=Fb-1
    (let ((lst (list first)))
      (equal (Fk lst)(Fb lst))))

(defthm
    Fk=Fb-2
    (let ((lst (list first second)))
      (equal (Fk lst)(Fb lst))))

(defthm
    Fk=Fb-3
    (let ((lst (list first second third)))
      (equal (Fk lst)(Fb lst))))

(defthm
    Fk=Fb-4
    (let ((lst (list first second third fourth)))
      (equal (Fk lst)(Fb lst))))

(defthm
    Fk=Fb-0-4
    (implies (and (true-listp lst)
		  (not (consp (nthcdr 4 lst)))) ;; (len lst) <= 4
	     (equal (Fk lst)(Fb lst)))
    :hints (("Goal"
	     :in-theory (disable Fk Fb))))

(defthm
    Fk=Fb-5
    (let ((lst (list first second third fourth fifth)))
      (implies (integer-listp lst)
	       (equal (Fk lst)(Fb lst)))))

(defthm
    Fk=Fb-0-5
    (implies (and (integer-listp lst)
		  (not (consp (nthcdr 5 lst)))) ;; (len lst) <= 5
	     (equal (Fk lst)(Fb lst)))
    :hints (("Goal"
	     :in-theory (disable Fk Fb))))

(defthm
    Fk<>Fb-6-example
    (let ((lst '(8 6 4 3 1 2)))
      (and (equal (Fk lst) 2)
	   (equal (Fb lst) 3)
	   (not (equal (Fk lst)(Fb lst))))))
