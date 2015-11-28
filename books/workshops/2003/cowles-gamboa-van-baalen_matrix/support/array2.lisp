; The ACL2 two-dimensional Arrays Book.
; Copyright (C) 2003 John R. Cowles, University of Wyoming

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

; Summer and Fall 2002.
;  Last modified 19 May 2003

; This book is based on a similar book about one-dimensional arrays
; Written by:  Bishop Brock
; Computational Logic, Inc.

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
To certify at UW:

:set-cbd "/home/faculty/cowles/acl2/matrix/" ;;pyramid

:set-cbd "/home/cowles/matrix/" ;;turing

(certify-book "array2"
	      0
	      nil ;;compile-flg
	      )
|#
#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
To use at UW:

:set-cbd "/home/faculty/cowles/acl2/matrix/" ;;pyramid

:set-cbd "/home/cowles/matrix/" ;;turing

(include-book
 "array2")
|#
(in-package "ACL2")

(local
 (defthm
   assoc-eq-properties
   (implies
    (and (alistp l)
	 (assoc-eq x l))
    (and (consp (assoc-eq x l))
	 (equal (car (assoc-eq x l)) x)))))

(local
 (defthm
   assoc2-properties
   (implies
    (and (alistp l)
	 (assoc2 i j l))
    (and (consp (assoc2 i j l))
	 (consp (car (assoc2 i j l)))
	 (equal (car (car (assoc2 i j l))) i)
	 (equal (cdr (car (assoc2 i j l))) j)))))

(local
 (defthm
   assoc-keyword-properties
   (implies
    (and (alistp l)
	 (assoc-keyword x l))
    (and (consp (assoc-keyword x l))
	 (equal (car (assoc-keyword x l)) x)))))

(local
 (defthm
   bounded-integer-alistp2-car-assoc2-properties
   (implies
    (and (bounded-integer-alistp2 l m n)
	 (assoc2 i j l))
    (and (integerp (car (car (assoc2 i j l))))
	 (integerp (cdr (car (assoc2 i j l))))
	 (>= (car (car (assoc2 i j l))) 0)
	 (>= (cdr (car (assoc2 i j l))) 0)
	 (< (car (car (assoc2 i j l))) m)
	 (< (cdr (car (assoc2 i j l))) n)))))

(local
 (defthm array2p-forward-local
   (implies
    (array2p name l)
    (and
     (symbolp name)
     (alistp l)
     (keyword-value-listp (cdr (assoc-eq :header l)))
     (true-listp
      (cadr (assoc-keyword :dimensions
			   (cdr (assoc-eq :header l)))))
     (equal
      (length (cadr (assoc-keyword :dimensions
				   (cdr (assoc-eq
					 :header l)))))
      2)
     (integerp
      (car (cadr (assoc-keyword :dimensions
				(cdr (assoc-eq
				      :header l))))))
     (integerp
      (cadr (cadr (assoc-keyword :dimensions
				 (cdr (assoc-eq
				       :header l))))))
     (integerp
      (cadr (assoc-keyword :maximum-length
			   (cdr (assoc-eq :header l)))))
     (< 0
	(car (cadr (assoc-keyword
		    :dimensions
		    (cdr (assoc-eq :header l))))))
     (< 0
	(cadr (cadr (assoc-keyword
		     :dimensions
		     (cdr (assoc-eq :header l))))))
     (< (* (car (cadr (assoc-keyword
		       :dimensions
		       (cdr (assoc-eq :header l)))))
	   (cadr (cadr (assoc-keyword
			:dimensions
			(cdr (assoc-eq :header l))))))
	(cadr (assoc-keyword
	       :maximum-length
	       (cdr (assoc-eq :header l)))))
     (<= (cadr (assoc-keyword
		:maximum-length
		(cdr (assoc-eq :header l))))
	 *maximum-positive-32-bit-integer*)
     (bounded-integer-alistp2
      l
      (car (cadr (assoc-keyword
		  :dimensions
		  (cdr (assoc-eq :header l)))))
      (cadr (cadr (assoc-keyword
		   :dimensions
		   (cdr (assoc-eq :header l))))))))
   :rule-classes :forward-chaining))

(local
 (defthm array2p-header-exists
   (implies
    (array2p name l)
    (assoc-eq :header l))))

(local
 (defthm array2p-cons-1
   (implies
    (and (array2p name l)
	 (integerp i)
	 (>= i 0)
	 (< i (car (dimensions name l)))
	 (integerp j)
	 (>= j 0)
	 (< j (cadr (dimensions name l))))
    (array2p name (cons (cons (cons i j) val) l)))))

(local (in-theory (disable array2p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;(compress211 name L i x j default) processes array elements
;;  L(i x) . . . L(i (- j 1)).

(local
 (defthm
   alistp-compress211
   (alistp (compress211 name l i x j default))))

(local
 (defthm bounded-integer-alistp2-compress211
   (implies
    (and (array2p name l)
	 (integerp i)
	 (integerp x)
	 (integerp k)
         (>= x 0)
	 (>= i 0)
	 (> k i))
    (bounded-integer-alistp2 (compress211 name l i x j default)
			     k
			     j))))

(local
 (defthm
   compress211-assoc2-property-0
   (implies (and (alistp l)
		 (assoc2 m n l)
		 (assoc2 m n (compress211 name l i x j default)))
	    (equal (assoc2 m n (compress211 name l i x j default))
		   (assoc2 m n l)))))

(local
 (defthm
   compress211-assoc2-property-1
   (implies
    (and (not (assoc2 i n (compress211 name l i x j default)))
	 (alistp l)
         (integerp x)
	 (integerp j)
	 (integerp n)
	 (<= x n)
	 (< n j)
	 (assoc2 i n l))
    (equal (cdr (assoc2 i n l))
	   default))))

(local
 (defthm
   compress211-assoc2-property-2
   (implies
    (and (alistp l)
	 (not (assoc2 m n l)))
    (not (assoc2 m n (compress211 name l i x j default))))))

(local
 (defthm
   not-assoc2-compress211
   (implies (and (alistp l)
		 (not (equal k i)))
	    (not (assoc2 k m (compress211 name L i x j default)))
	    )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;(compress21 name L n i j default) processes array elements
;;       L(n 0) . . . L(n (- j 1))
;;       .      .         .
;;       .        .       .
;;       .          .     .
;; L((- i 1) 0) . . . L((- i 1)(- j 1))

(local
 (defthm
   alistp-append
   (implies (and (alistp l1)
		 (alistp l2))
	    (alistp (append l1 l2)))))

(local
 (defthm
   alistp-compress21
   (alistp (compress21 name l n i j default))))

(local
 (defthm
   bounded-integer-alistp2-append
   (implies (and (bounded-integer-alistp2 l1 i j)
		 (bounded-integer-alistp2 l2 i j))
	    (bounded-integer-alistp2 (append l1 l2)
				     i
				     j))))

(local
 (defthm
   bounded-integer-alistp2-compress21
   (implies
    (and (array2p name l)
	 (integerp i)
	 (integerp n)
	 (>= n 0))
    (bounded-integer-alistp2 (compress21 name l n i j default)
			     i
			     j))))

(local
 (defthm
   assoc2-append
   (equal (assoc2 i j (append l1 l2))
	  (if (assoc2 i j l1)
	      (assoc2 i j l1)
	      (assoc2 i j l2)))))

(local
 (defthm
   compress21-assoc2-property-0
   (implies
    (and (alistp l)
         (assoc2 k m l)
	 (assoc2 k m (compress21 name l n i j default)))
    (equal (assoc2 k m (compress21 name l n i j default))
	   (assoc2 k m l)))))

(local
 (defthm
   compress21-assoc2-property-1
   (implies
    (and (not (assoc2 k m (compress21 name l n i j default)))
	 (alistp l)
         (integerp i)
	 (integerp j)
	 (integerp k)
	 (integerp m)
	 (integerp n)
	 (<= n i)
	 (<= n k)
	 (< k i)
	 (<= 0 m)
	 (< m j)
	 (assoc2 k m l))
    (equal (cdr (assoc2 k m l))
	   default))
   :hints (("Subgoal *1/5"
	    :use (:instance
		  compress211-assoc2-property-1
		  (i k)
		  (n m)
		  (x 1))))))

(local
 (defthm
   compress21-assoc2-property-2
   (implies
    (and (alistp l)
	 (not (assoc2 k m l)))
    (not (assoc2 k m (compress21 name l n i j default))))))

(local
 (defthm
   compress2-assoc2-property-0
   (implies
    (and (alistp l)
	 (assoc2 k m l)
	 (assoc2 k m (compress2 name l)))
    (equal (cdr (assoc2 k m (compress2 name l)))
	   (cdr (assoc2 k m l))))))

(local
 (defthm
   compress2-assoc2-property-1
   (implies
    (and (array2p name l)
	 (integerp k)
	 (integerp m)
	 (<= 0 k)
	 (< k (car (dimensions name l)))
	 (<= 0 m)
	 (< m (cadr (dimensions name l)))
	 (assoc2 k m l)
	 (not (assoc2 k m (compress2 name l))))
    (equal (cdr (assoc2 k m l))
	   (cadr (assoc-keyword :default (cdr (assoc-eq :header l))
				))))))

(local
 (defthm
   compress2-assoc2-property-2
   (implies
    (and (alistp l)
	 (not (assoc2 k m l)))
    (not (assoc2 k m (compress2 name l))))))

(local
 (defthm
   header-compress2
   (implies
    (array2p name l)
    (equal (assoc-eq :header (compress2 name l))
	   (assoc-eq :header l)))))

(defthm
  array2p-compress2
  (implies
   (array2p name l)
   (array2p name (compress2 name l)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((compress2 name l))))
  :hints (("Goal"
	   :in-theory (enable array2p))))

(defthm
  array2p-compress2-properties
  (implies
   (array2p name l)
   (and
    (equal (header name (compress2 name l))
	   (header name l))
    (equal (dimensions name (compress2 name l))
	   (dimensions name l))
    (equal (maximum-length name (compress2 name l))
	   (maximum-length name l))
    (equal (default name (compress2 name l))
	   (default name l)))))

(local (in-theory (disable compress2)))

(defthm
  array2p-aset2
  (implies
   (and (array2p name l)
	(integerp i)
	(integerp j)
	(>= i 0)
	(>= j 0)
	(< i (car (dimensions name l)))
	(< j (cadr (dimensions name l))))
   (array2p name (aset2 name l i j val))))

(defthm
  array2p-aset2-properties
  (implies
   (and (array2p name l)
	(integerp i)
	(integerp j)
	(>= i 0)
	(>= j 0)
	(< i (car (dimensions name l)))
	(< j (cadr (dimensions name l))))
   (and
    (equal (header name (aset2 name l i j val))
	   (header name l))
    (equal (dimensions name (aset2 name l i j val))
	   (dimensions name l))
    (equal (maximum-length name (aset2 name l i j val))
	   (maximum-length name l))
    (equal (default name (aset2 name l i j val))
	   (default name l)))))

(defthm
  aref2-compress2
  (implies
   (and (array2p name l)
	(integerp i)
	(integerp j)
	(>= i 0)
	(>= j 0)
	(< i (car (dimensions name l)))
	(< j (cadr (dimensions name l))))
   (equal (aref2 name (compress2 name l) i j)
	  (aref2 name l i j))))

(defthm
  array2p-acons-properties
  (and
   (equal (header name (cons (cons (cons i j) val) l))
	  (header name l))
   (equal (dimensions name (cons (cons (cons i j) val) l))
	  (dimensions name l))
   (equal (maximum-length name (cons (cons (cons i j) val) l))
	  (maximum-length name l))
   (equal (default name (cons (cons (cons i j) val) l))
	  (default name l))))

(defthm
  array2p-consp-header
  (implies
   (array2p name l)
   (consp (header name l)))
  :rule-classes :type-prescription)

(defthm
  array2p-car-header
  (implies
   (array2p name l)
   (equal (car (header name l))
	  :header)))

;  These two theorems for the AREF2-ASET2 cases are used to prove a
;  combined result, and then exported DISABLEd:

(defthm
  aref2-aset2-equal
  (implies
   (and (array2p name l)
	(integerp i)
	(integerp j)
	(>= i 0)
	(>= j 0)
	(< i (car (dimensions name l)))
	(< j (cadr (dimensions name l))))
   (equal (aref2 name (aset2 name l i j val) i j)
	  val)))

(defthm
  aref2-aset2-not-equal
  (implies
   (and (array2p name l)
	(integerp i1)
	(integerp j1)
	(>= i1 0)
	(>= j1 0)
	(< i1 (car (dimensions name l)))
	(< j1 (cadr (dimensions name l)))
	(integerp i2)
	(integerp j2)
	(>= i2 0)
	(>= j2 0)
	(< i2 (car (dimensions name l)))
	(< j2 (cadr (dimensions name l)))
	(not (and (equal i1 i2)
		  (equal j1 j2))))
   (equal (aref2 name (aset2 name l i1 j1 val) i2 j2)
	  (aref2 name l i2 j2))))

(defthm
  aref2-aset2
  (implies
   (and (array2p name l)
	(integerp i1)
	(integerp j1)
	(>= i1 0)
	(>= j1 0)
	(< i1 (car (dimensions name l)))
	(< j1 (cadr (dimensions name l)))
	(integerp i2)
	(integerp j2)
	(>= i2 0)
	(>= j2 0)
	(< i2 (car (dimensions name l)))
	(< j2 (cadr (dimensions name l)))
	)
   (equal (aref2 name (aset2 name l i1 j1 val) i2 j2)
	  (if (and (equal i1 i2)
		   (equal j1 j2))
	      val
	      (aref2 name l i2 j2)))))

(in-theory (disable aref2-aset2-equal aref2-aset2-not-equal))

;;; The final form of the :FORWARD-CHAINING lemma for ARRAY2P.
;;;   A forward definition of (ARRAY2P name l), in terms of
;;;   HEADER, DIMENSIONS, and MAXIMUM-LENGTH.
;;;   Note that ACL2 also defines a lemma ARRAY2P-FORWARD, but
;;;   that lemma is in terms of the expansions of HEADER,
;;;   DIMENSIONS, and MAXIMUM-LENGTH.

;;;   One should normaly DISABLE ARRAY2P in favor of this
;;;   :FORWARD-CHAINING rule. If allowed to open, ARRAY2P can
;;;   cause severe performance degradation due to its large size
;;;   and many recursive functions.  This lemma is designed to be
;;;   used with the ARRAY2-FUNCTIONS theory DISABLEd.

(defthm array2p-forward-modular
  (implies
   (array2p name l)
   (and (symbolp name)
	(alistp l)
	(keyword-value-listp (cdr (header name l)))
	(true-listp (dimensions name l))
	(equal (length (dimensions name l)) 2)
	(integerp (car (dimensions name l)))
	(integerp (cadr (dimensions name l)))
	(integerp (maximum-length name l))
	(< 0 (car (dimensions name l)))
	(< 0 (cadr (dimensions name l)))
	(< (* (car (dimensions name l))
	      (cadr (dimensions name l)))
	   (maximum-length name l))
	(<= (maximum-length name l)
	    *maximum-positive-32-bit-integer*)
	(bounded-integer-alistp2 l
				 (car (dimensions name l))
				 (cadr (dimensions name l)))))
  :rule-classes :forward-chaining)

(defthm array2p-linear-modular
  (implies
   (array2p name l)
   (and (< 0 (car (dimensions name l)))
	(< 0 (cadr (dimensions name l)))
	(< (* (car (dimensions name l))
	      (cadr (dimensions name l)))
	   (maximum-length name l))
	(<= (maximum-length name l)
	    *maximum-positive-32-bit-integer*)))
  :rule-classes :linear)

(deftheory
  array2-functions
  '(array2p aset2 aref2 compress2 header dimensions maximum-length
    default)
; Matt K. mod 10/30/2015: :doc is no longer supported for deftheory.
; :doc "A theory of all functions specific to 2-dimensional arrays.
;       This theory must be DISABLEd in order for the lemmas
;       exported by the array2 book to be applicable."
  )

(deftheory
  array2-lemmas
  '(array2p-compress2
    array2p-compress2-properties
    array2p-aset2
    array2p-aset2-properties
    aref2-compress2
    array2p-acons-properties
    array2p-consp-header
    array2p-car-header
    aref2-aset2
    array2p-forward-modular
    array2p-linear-modular))

(deftheory
  array2-disabled-lemmas
  '(aref2-aset2-equal
    aref2-aset2-not-equal)
; Matt K. mod 10/30/2015: :doc is no longer supported for deftheory.
; :doc "A theory of all rules exported DISABLEd by the array2 book.
;       Note that in order for these rules to be applicable you
;       will first need to (DISABLE ARRAY2-FUNCTIONS)."
  )

