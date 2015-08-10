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

;; 25 July 00
;; These are implementations of Knuth's (original and revised)
;;  and Bailey's versions of the f function for Knuth's theorem 4.
;; For lists of integers, the revised Knuth and Bailey versions
;;  compute the same values.

;; (certify-book "C:/acl2/tak/tarai11")

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
    Gko (lst)
    "Knuth's original g function for Knuth's Theorem 4.
     The input lst is intended to be a nonempty
     list of integers."
    (declare (xargs :guard (and (integer-listp lst)
				(consp lst))))
    (cond ((consp (nthcdr 2 lst))    ;; (len lst) > 2
	   (cond ((equal (first lst)
			 (+ (second lst) 1))
		  (Gko (rest lst)))
		 ((equal (second lst)
			 (+ (third lst) 1))
		  (max (third lst)
		       (last-el lst)))
		 (t (last-el lst))))
	  (t (last-el lst))))       ;; (len lst) <= 2

(defun
    Gkr (lst)
    "Knuth's revised g function for Knuth's Theorem 4.
     The input lst is intended to be a nonempty
     list of integers."
    (declare (xargs :guard (and (integer-listp lst)
				(consp lst))))
    (cond ((consp (nthcdr 2 lst))    ;; (len lst) > 2
	   (cond ((and (> (first lst)
			  (+ (second lst) 1))
		       (equal (+ (second lst) 1)
			      (+ (third lst) 2)))
		  (max (third lst)
		       (last-el lst)))
		 (t (Gkr (rest lst)))))
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
    Fko (lst)
    "Knuth's original f function for Knuth's theorem 4.
     The input lst is intended to be a nonempty
     list of integers."
    (declare (xargs :guard (and (integer-listp lst)
				(consp lst))))
    (if (decreasing-p lst)
	(first lst)
        (Gko (first-non-decrease lst))))

(defun
    Fkr (lst)
    "Knuth's revised f function for Knuth's theorem 4.
     The input lst is intended to be a nonempty
     list of integers."
    (declare (xargs :guard (and (integer-listp lst)
				(consp lst))))
    (if (decreasing-p lst)
	(first lst)
        (Gkr (first-non-decrease lst))))

(defun
    front (lst)
    "Return lst with (last-el lst) removed."
    (declare (xargs :guard (listp lst)))
    (if (consp (rest lst))  ;; (len lst) > 1
	(cons (first lst) (front (rest lst)))
        nil))

(defthm
    Gb=Gkr-1
    (let ((lst (list first)))
      (equal (Gb lst)(Gkr lst))))

(defthm
    Gb=Gkr-2
    (let ((lst (list first second)))
      (equal (Gb lst)(Gkr lst))))

(defthm
    Gb=Gkr<=2
    (implies (and (true-listp lst)
		  (not (consp (nthcdr 2 lst)))) ;; (len lst) <= 2
	     (equal (Gb lst)(Gkr lst)))
    :hints (("Goal"
	     :in-theory (disable Gb Gkr))))

(defthm
    Gb=Gkr
    (implies (and (integer-listp lst)
		  (decreasing-p (front lst)))
	     (equal (Gb lst)(Gkr lst))))

(defthm
    integer-listp-first-non-decrease
    (implies (integer-listp lst)
	     (integer-listp (first-non-decrease lst))))

(defthm
    decreasing-p-front-first-non-decrease
    (decreasing-p (front (first-non-decrease lst))))

(defthm
    Fb=Fkr
    (implies (integer-listp lst)
	     (equal (Fb lst)(Fkr lst))))
