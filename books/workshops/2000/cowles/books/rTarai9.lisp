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

;; The recursive calls, specified in the definition of the
;;  restricted tarai recursion, terminate for lists of
;;  integers of lengths 2-7.

;; (certify-book "C:/acl2/tak/rTarai9")

(in-package "ACL2")

(include-book "rTarai8")

;; The RESTRICTED tarai recursion:
#|(defthm
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
				   lst)))))))
|#
#|
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
|#

(defthm
    e0-ordinalp-measure
    (e0-ordinalp (measure lst)))

;; The recursion in (rTarai lst) halts when lst is a list
;;  of length 2:

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
    e0-ord-<-measure-rotates-2
    (let ((lst (list first second)))
      (implies
       (and (integer-listp lst)
	    (> first second)
	    (member-equal rlst (lst-rotates-with-minus-1
				(- (DEC-FRONT-LEN lst) 1)
				lst)))
       (e0-ord-< (measure rlst)
		 (measure lst)))))

(defthm
    e0-ord-<-measure-rTarai-lst-2
    (let ((lst (list first second)))
      (implies
       (and (integer-listp lst)
	  (> first second))
       (e0-ord-< (measure (rTarai-lst
			   (lst-rotates-with-minus-1
			    (- (DEC-FRONT-LEN lst) 1)
			    lst)))
		 (measure lst)))))

;; The recursion in (rTarai lst) halts when lst is a list
;;  of length 3:

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
    e0-ord-<-measure-rotates-3
    (let ((lst (list first second third)))
      (implies
       (and (integer-listp lst)
	    (> first second)
	    (member-equal rlst (lst-rotates-with-minus-1
				(- (DEC-FRONT-LEN lst) 1)
				lst)))
       (e0-ord-< (measure rlst)
		 (measure lst)))))

(defthm
    e0-ord-<-measure-rTarai-lst-3
    (let ((lst (list first second third)))
      (implies
       (and (integer-listp lst)
	    (> first second))
       (e0-ord-< (measure (rTarai-lst
			   (lst-rotates-with-minus-1
			    (- (DEC-FRONT-LEN lst) 1)
			    lst)))
		 (measure lst)))))

;; The recursion in (rTarai lst) halts when lst is a list
;;  of length 4:

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
    e0-ord-<-measure-rotates-4
    (let ((lst (list first second third fourth)))
      (implies
       (and (integer-listp lst)
	    (> first second)
	    (member-equal rlst (lst-rotates-with-minus-1
				(- (DEC-FRONT-LEN lst) 1)
				lst)))
       (e0-ord-< (measure rlst)
		 (measure lst)))))

(defthm
    e0-ord-<-measure-rTarai-lst-4
    (let ((lst (list first second third fourth)))
      (implies
       (and (integer-listp lst)
	    (> first second))
       (e0-ord-< (measure (rTarai-lst
			   (lst-rotates-with-minus-1
			    (- (DEC-FRONT-LEN lst) 1)
			    lst)))
		 (measure lst)))))

;; The recursion in (rTarai lst) halts when lst is a list
;;  of length 5:

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
    e0-ord-<-measure-rotates-5
    (let ((lst (list first second third fourth fifth)))
      (implies
       (and (integer-listp lst)
	    (> first second)
	    (member-equal rlst (lst-rotates-with-minus-1
				(- (DEC-FRONT-LEN lst) 1)
				lst)))
       (e0-ord-< (measure rlst)
		 (measure lst)))))

(defthm
    e0-ord-<-measure-rTarai-lst-5
    (let ((lst (list first second third fourth fifth)))
      (implies
       (and (integer-listp lst)
	    (> first second))
       (e0-ord-< (measure (rTarai-lst
			   (lst-rotates-with-minus-1
			    (- (DEC-FRONT-LEN lst) 1)
			    lst)))
		 (measure lst)))))

;; The recursion in (rTarai lst) halts when lst is a list
;;  of length 6:

(local
 (defthm
     lst-rotates-with-minus-1-6a
     (let ((lst (list first second third forth fifth sixth)))
       (equal (lst-rotates-with-minus-1 1 lst)
	      (list (list (- first 1) second third forth fifth sixth)
		    (list (- second 1) third forth fifth sixth first))))
     :hints (("Goal"
	      :expand ((lst-rotates-with-minus-1
			1
			(list first second third forth fifth sixth))))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-6b
     (let ((lst (list first second third forth fifth sixth)))
       (equal (lst-rotates-with-minus-1 2 lst)
	      (list (list (- first 1) second third forth fifth sixth)
		    (list (- second 1) third forth fifth sixth first)
		    (list (- third 1) forth fifth sixth first second)))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-6c
     (let ((lst (list first second third forth fifth sixth)))
       (equal (lst-rotates-with-minus-1 3 lst)
	      (list (list (- first 1) second third forth fifth sixth)
		    (list (- second 1) third forth fifth sixth first)
		    (list (- third 1) forth fifth sixth first second)
		    (list (- forth 1) fifth sixth first second third)))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-6d
     (let ((lst (list first second third forth fifth sixth)))
       (equal (lst-rotates-with-minus-1 4 lst)
	      (list (list (- first 1) second third forth fifth sixth)
		    (list (- second 1) third forth fifth sixth first)
		    (list (- third 1) forth fifth sixth first second)
		    (list (- forth 1) fifth sixth first second third)
		    (list (- fifth 1) sixth first second third forth)
		    ))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-6e
     (let ((lst (list first second third forth fifth sixth)))
       (equal
	(lst-rotates-with-minus-1 5 lst)
	(list (list (- first 1) second third forth fifth sixth)
	      (list (- second 1) third forth fifth sixth first)
	      (list (- third 1) forth fifth sixth first second)
	      (list (- forth 1) fifth sixth first second third)
	      (list (- fifth 1) sixth first second third forth)
	      (list (- sixth 1) first second third forth fifth)
	      ))))
 )

(defthm
    e0-ord-<-measure-rotates-6
    (let ((lst (list first second third fourth fifth sixth)))
      (implies
       (and (integer-listp lst)
	    (> first second)
	    (member-equal rlst (lst-rotates-with-minus-1
				(- (DEC-FRONT-LEN lst) 1)
				lst)))
       (e0-ord-< (measure rlst)
		 (measure lst)))))

(defthm
    e0-ord-<-measure-rTarai-lst-6
    (let ((lst (list first second third fourth fifth sixth)))
      (implies
       (and (integer-listp lst)
	    (> first second))
       (e0-ord-< (measure (rTarai-lst
			   (lst-rotates-with-minus-1
			    (- (DEC-FRONT-LEN lst) 1)
			    lst)))
		 (measure lst)))))

;; The recursion in (rTarai lst) halts when lst is a list
;;  of length 7:

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
    e0-ord-<-measure-rotates-7
    (let ((lst (list first second third fourth
		     fifth sixth seventh)))
      (implies
       (and (integer-listp lst)
	    (> first second)
	    (member-equal rlst (lst-rotates-with-minus-1
				(- (DEC-FRONT-LEN lst) 1)
				lst)))
       (e0-ord-< (measure rlst)
		 (measure lst)))))

(defthm
    e0-ord-<-measure-rTarai-lst-7
    (let ((lst (list first second third fourth
		     fifth sixth seventh)))
      (implies
       (and (integer-listp lst)
	    (> first second))
       (e0-ord-< (measure (rTarai-lst
			   (lst-rotates-with-minus-1
			    (- (DEC-FRONT-LEN lst) 1)
			    lst)))
		 (measure lst)))))

;; The recursion in (rTarai lst) halts when lst is a list
;;  of any length 2-7:

(defthm
    e0-ord-<-measure-rotates
    (implies
     (and (integer-listp lst)
	  (consp (nthcdr 1 lst))       ;; (len lst) > 1
	  (not (consp (nthcdr 7 lst))) ;; (len lst) <= 7
	  (> (first lst)(second lst))
	  (member-equal rlst (lst-rotates-with-minus-1
			      (- (DEC-FRONT-LEN lst) 1)
			      lst)))
     (e0-ord-< (measure rlst)
	       (measure lst)))
    :hints (("Goal"
	     :in-theory (disable Fb measure dec-front-len
				 member-equal
				 e0-ord-<-measure-rotates-2
				 e0-ord-<-measure-rotates-3
				 e0-ord-<-measure-rotates-4
				 e0-ord-<-measure-rotates-5
				 e0-ord-<-measure-rotates-6
				 e0-ord-<-measure-rotates-7)
	     :use ((:instance
		    e0-ord-<-measure-rotates-2
		    (first (first lst))
		    (second (second lst)))
		   (:instance
		    e0-ord-<-measure-rotates-3
		    (first (first lst))
		    (second (second lst))
		    (third (third lst)))
		   (:instance
		    e0-ord-<-measure-rotates-4
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst)))
		   (:instance
		    e0-ord-<-measure-rotates-5
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst))
		    (fifth (fifth lst)))
		   (:instance
		    e0-ord-<-measure-rotates-6
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst))
		    (fifth (fifth lst))
		    (sixth (sixth lst)))
		   (:instance
		    e0-ord-<-measure-rotates-7
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst))
		    (fifth (fifth lst))
		    (sixth (sixth lst))
		    (seventh (seventh lst)))))))

(defthm
    e0-ord-<-measure-rTarai-lst
      (implies
       (and (integer-listp lst)
	    (consp (nthcdr 1 lst))       ;; (len lst) > 1
	    (not (consp (nthcdr 7 lst))) ;; (len lst) <= 7
	    (> (first lst)(second lst)))
       (e0-ord-< (measure (rTarai-lst
			   (lst-rotates-with-minus-1
			    (- (DEC-FRONT-LEN lst) 1)
			    lst)))
		 (measure lst)))
    :hints (("Goal"
	     :in-theory (disable
			 Fb measure dec-front-len
			 e0-ord-<-measure-rTarai-lst-2
			 e0-ord-<-measure-rTarai-lst-3
			 e0-ord-<-measure-rTarai-lst-4
			 e0-ord-<-measure-rTarai-lst-5
			 e0-ord-<-measure-rTarai-lst-6
			 e0-ord-<-measure-rTarai-lst-7
			 )
	     :use ((:instance
		     e0-ord-<-measure-rTarai-lst-2
		    (first (first lst))
		    (second (second lst)))
		   (:instance
		    e0-ord-<-measure-rTarai-lst-3
		    (first (first lst))
		    (second (second lst))
		    (third (third lst)))
		   (:instance
		    e0-ord-<-measure-rTarai-lst-4
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst)))
		   (:instance
		    e0-ord-<-measure-rTarai-lst-5
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst))
		    (fifth (fifth lst)))
		   (:instance
		    e0-ord-<-measure-rTarai-lst-6
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst))
		    (fifth (fifth lst))
		    (sixth (sixth lst)))
		   (:instance
		    e0-ord-<-measure-rTarai-lst-7
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst))
		    (fifth (fifth lst))
		    (sixth (sixth lst))
		    (seventh (seventh lst)))))))

