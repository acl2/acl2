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
;;  Fb for lists of lengths 2-7. This book summarizes
;;  books tarai6-tarai8.

;; (certify-book "C:/acl2/tak/tarai9")

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

(local (include-book "tarai6"))
(local (include-book "tarai7"))
(local (include-book "tarai8"))

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
    tarai=Fb
    (implies (and (integer-listp lst)
		  (consp (rest lst))           ;; (len lst) > 1
		  (not (consp (nthcdr 7 lst))) ;; (len lst) <= 7
		  )
	     (equal (tarai lst)(Fb lst)))
    :hints (("Goal"
	     :in-theory (disable Fb tarai=Fb-2 tarai=Fb-3
				 tarai=Fb-4 tarai=Fb-5
				 tarai=Fb-6 tarai=Fb-7)
	     :use ((:instance
		    tarai=Fb-2
		    (first (first lst))
		    (second (second lst)))
		   (:instance
		    tarai=Fb-3
		    (first (first lst))
		    (second (second lst))
		    (third (third lst)))
		   (:instance
		    tarai=Fb-4
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst)))
		   (:instance
		    tarai=Fb-5
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst))
		    (fifth (fifth lst)))
		   (:instance
		    tarai=Fb-6
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst))
		    (fifth (fifth lst))
		    (sixth (sixth lst)))
		   (:instance
		    tarai=Fb-7
		    (first (first lst))
		    (second (second lst))
		    (third (third lst))
		    (fourth (fourth lst))
		    (fifth (fifth lst))
		    (sixth (sixth lst))
		    (seventh (seventh lst)))
		   ))))
