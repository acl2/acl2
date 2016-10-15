; The ACL2 two-dimensional Alist Book.
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


; Spring 2003
;  Last modified 21 May 2003

; This book is similar to the book array2.lisp.

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
To certify at UW:

:set-cbd "/home/faculty/cowles/acl2/matrix/" ;;pyramid

:set-cbd "/home/cowles/matrix/" ;;turing

(certify-book "alist2")
|#
#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
To use at UW:

:set-cbd "/home/faculty/cowles/acl2/matrix/" ;;pyramid

:set-cbd "/home/cowles/matrix/" ;;turing

(include-book
 "alist2")
|#
(in-package "ACL2")

;; Logically, an ACL2 two-dimensional array is an alist that satisfies these
;;  properties:

(defun
  alist2p (name L)
  "Determine if L satisfies the logical properties of an ACL2 array2p.
   The ignored argument, name, is there only to make life easier later
   when using such standard ACL2 array functions as aref2, aset2, header,
   default, etc., that also have such an argument."
  (declare (ignore name)(xargs :guard t))
  (and (alistp l)
       (let ((header-keyword-list (cdr (assoc-eq :header L))))
	    (and (keyword-value-listp header-keyword-list)
		 (let ((dimensions
			(cadr (assoc-keyword :dimensions header-keyword-list))))
		      (and (consp dimensions)
			   (let ((cdr-dim (cdr dimensions)))
			        (and (consp cdr-dim)
				     (let ((d1 (car dimensions))
					   (d2 (car cdr-dim)))
				          (and (integerp d1)
					       (integerp d2)
					       (< 0 d1)
					       (< 0 d2)
					       (bounded-integer-alistp2 L d1 d2)))
				     ))))))))

(defthm
  array2p-alist2p
  (implies (array2p name L)
	   (alist2p name L)))

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
 (defthm alist2p-forward-local
   (implies
    (alist2p name L)
    (and
     (alistp L)
     (keyword-value-listp (cdr (assoc-eq :header L)))
     (consp (cadr (assoc-keyword :dimensions
				 (cdr (assoc-eq :header L)))))
     (consp (cdadr (assoc-keyword :dimensions
				  (cdr (assoc-eq :header L)))))
     (integerp
      (car (cadr (assoc-keyword :dimensions
				(cdr (assoc-eq :header L))))))
     (integerp
      (cadr (cadr (assoc-keyword :dimensions
				 (cdr (assoc-eq :header L))))))
     (< 0 (car (cadr (assoc-keyword :dimensions
				    (cdr (assoc-eq :header L))))))
     (< 0 (cadr (cadr (assoc-keyword :dimensions
				     (cdr (assoc-eq :header L))))))
     (bounded-integer-alistp2 L
			      (car (cadr (assoc-keyword
					  :dimensions
					  (cdr (assoc-eq :header L)))))
			      (cadr (cadr (assoc-keyword
					   :dimensions
					   (cdr (assoc-eq :header L))))))))
   :rule-classes :forward-chaining))

(local
 (defthm alist2p-header-exists
   (implies
    (alist2p name L)
    (assoc-eq :header L))))

(local
 (defthm alist2p-cons-1
   (implies
    (and (alist2p name L)
	 (integerp i)
	 (>= i 0)
	 (< i (car (dimensions name l)))
	 (integerp j)
	 (>= j 0)
	 (< j (cadr (dimensions name l))))
    (alist2p name (cons (cons (cons i j) val) L)))))

(local (in-theory (disable alist2p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;(compress211 name L i x j default) processes array elements
;;  L(i x) . . . L(i (- j 1)).

(local
 (defthm
   alistp-compress211
   (alistp (compress211 name L i x j default))))

(local
 (defthm bounded-integer-alistp2-compress211
   (implies
    (and (alist2p name L)
	 (integerp i)
	 (integerp x)
	 (integerp k)
         (>= x 0)
	 (>= i 0)
	 (> k i))
    (bounded-integer-alistp2 (compress211 name L i x j default)
			     k
			     j))))

(local
 (defthm
   compress211-assoc2-property-0
   (implies (and (alistp L)
		 (assoc2 m n L)
		 (assoc2 m n (compress211 name L i x j default)))
	    (equal (assoc2 m n (compress211 name L i x j default))
		   (assoc2 m n L)))))

(local
 (defthm
   compress211-assoc2-property-1
   (implies
    (and (not (assoc2 i n (compress211 name L i x j default)))
	 (alistp L)
         (integerp x)
	 (integerp j)
	 (integerp n)
	 (<= x n)
	 (< n j)
	 (assoc2 i n L))
    (equal (cdr (assoc2 i n L))
	   default))))

(local
 (defthm
   compress211-assoc2-property-2
   (implies
    (and (alistp L)
	 (not (assoc2 m n L)))
    (not (assoc2 m n (compress211 name L i x j default))))))

(local
 (defthm
   not-assoc2-compress211
   (implies (and (alistp L)
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
   (implies (and (alistp L1)
		 (alistp L2))
	    (alistp (append L1 L2)))))

(local
 (defthm
   alistp-compress21
   (alistp (compress21 name L n i j default))))

(local
 (defthm
   bounded-integer-alistp2-append
   (implies (and (bounded-integer-alistp2 L1 i j)
		 (bounded-integer-alistp2 L2 i j))
	    (bounded-integer-alistp2 (append L1 L2)
				     i
				     j))))

(local
 (defthm
   bounded-integer-alistp2-compress21
   (implies
    (and (alist2p name L)
	 (integerp i)
	 (integerp n)
	 (>= n 0))
    (bounded-integer-alistp2 (compress21 name L n i j default)
			     i
			     j))))

(local
 (defthm
   assoc2-append
   (equal (assoc2 i j (append L1 L2))
	  (if (assoc2 i j L1)
	      (assoc2 i j L1)
	      (assoc2 i j L2)))))

(local
 (defthm
   compress21-assoc2-property-0
   (implies
    (and (alistp L)
         (assoc2 k m L)
	 (assoc2 k m (compress21 name L n i j default)))
    (equal (assoc2 k m (compress21 name L n i j default))
	   (assoc2 k m L)))))

(local
 (defthm
   compress21-assoc2-property-1
   (implies
    (and (not (assoc2 k m (compress21 name L n i j default)))
	 (alistp L)
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
	 (assoc2 k m L))
    (equal (cdr (assoc2 k m L))
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
    (and (alistp L)
	 (not (assoc2 k m L)))
    (not (assoc2 k m (compress21 name L n i j default))))))

(local
 (defthm
   compress2-assoc2-property-0
   (implies
    (and (alistp L)
	 (assoc2 k m L)
	 (assoc2 k m (compress2 name L)))
    (equal (cdr (assoc2 k m (compress2 name L)))
	   (cdr (assoc2 k m L))))))

(local
 (defthm
   compress2-assoc2-property-1
   (implies
    (and (alist2p name L)
	 (integerp k)
	 (integerp m)
	 (<= 0 k)
	 (< k (car (dimensions name L)))
	 (<= 0 m)
	 (< m (cadr (dimensions name L)))
	 (assoc2 k m L)
	 (not (assoc2 k m (compress2 name L))))
    (equal (cdr (assoc2 k m L))
	   (cadr (assoc-keyword :default (cdr (assoc-eq :header L))
				))))))

(local
 (defthm
   compress2-assoc2-property-2
   (implies
    (and (alistp L)
	 (not (assoc2 k m L)))
    (not (assoc2 k m (compress2 name L))))))

(local
 (defthm
   header-compress2
   (implies
    (alist2p name L)
    (equal (assoc-eq :header (compress2 name L))
	   (assoc-eq :header L)))))

(defthm
  alist2p-compress2
  (implies
   (alist2p name L)
   (alist2p name (compress2 name L)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((compress2 name L))))
  :hints (("Goal"
	   :in-theory (enable alist2p))))

(defthm
  alist2p-compress2-properties
  (implies
   (alist2p name L)
   (and
    (equal (header name (compress2 name L))
	   (header name L))
    (equal (dimensions name (compress2 name L))
	   (dimensions name L))
    (equal (maximum-length name (compress2 name L))
	   (maximum-length name L))
    (equal (default name (compress2 name L))
	   (default name L)))))

(local (in-theory (disable compress2)))

(defthm
  alist2p-aset2
  (implies
   (and (alist2p name L)
	(integerp i)
	(integerp j)
	(>= i 0)
	(>= j 0)
	(< i (car (dimensions name L)))
	(< j (cadr (dimensions name L))))
   (alist2p name (aset2 name L i j val))))

(defthm
  alist2p-aref2-compress2
  (implies
   (and (alist2p name L)
	(integerp i)
	(integerp j)
	(>= i 0)
	(>= j 0)
	(< i (car (dimensions name L)))
	(< j (cadr (dimensions name L))))
   (equal (aref2 name (compress2 name L) i j)
	  (aref2 name L i j))))

(defthm
  array2p-acons-properties
  (and
   (equal (header name (cons (cons (cons i j) val) L))
	  (header name L))
   (equal (dimensions name (cons (cons (cons i j) val) L))
	  (dimensions name L))
   (equal (maximum-length name (cons (cons (cons i j) val) L))
	  (maximum-length name L))
   (equal (default name (cons (cons (cons i j) val) L))
	  (default name L))))

(defthm
  alist2p-aset2-properties
  (implies
   (and (alist2p name L)
	(integerp i)
	(integerp j)
	(>= i 0)
	(>= j 0)
	(< i (car (dimensions name L)))
	(< j (cadr (dimensions name L))))
   (and
    (equal (header name (aset2 name L i j val))
	   (header name L))
    (equal (dimensions name (aset2 name L i j val))
	   (dimensions name L))
    (equal (maximum-length name (aset2 name L i j val))
	   (maximum-length name L))
    (equal (default name (aset2 name L i j val))
	   (default name L)))))

(defthm
  alist2p-consp-header
  (implies
   (alist2p name L)
   (consp (header name L)))
  :rule-classes :type-prescription)

(defthm
  alist2p-car-header
  (implies
   (alist2p name L)
   (equal (car (header name L))
	  :header)))

;  These two theorems for the ALISR2P-AREF2-ASET2 cases are used to prove a
;  combined result, and then exported DISABLEd:
;    NOTE: The combined result below can be proved without first proving the
;          two cases, but we'll keep these results organized as they were.

(defthm
  alist2p-aref2-aset2-equal
  (implies
   (and (alist2p name L)
	(integerp i)
	(integerp j)
	(>= i 0)
	(>= j 0)
	(< i (car (dimensions name L)))
	(< j (cadr (dimensions name L))))
   (equal (aref2 name (aset2 name L i j val) i j)
	  val)))

(defthm
  alist2p-aref2-aset2-not-equal
  (implies
   (and (alist2p name L)
	(integerp i1)
	(integerp j1)
	(>= i1 0)
	(>= j1 0)
	(< i1 (car (dimensions name L)))
	(< j1 (cadr (dimensions name L)))
	(integerp i2)
	(integerp j2)
	(>= i2 0)
	(>= j2 0)
	(< i2 (car (dimensions name L)))
	(< j2 (cadr (dimensions name L)))
	(not (and (equal i1 i2)
		  (equal j1 j2))))
   (equal (aref2 name (aset2 name L i1 j1 val) i2 j2)
	  (aref2 name L i2 j2))))

(defthm
  alist2p-aref2-aset2
  (implies
   (and (alist2p name L)
	(integerp i1)
	(integerp j1)
	(>= i1 0)
	(>= j1 0)
	(< i1 (car (dimensions name L)))
	(< j1 (cadr (dimensions name L)))
	(integerp i2)
	(integerp j2)
	(>= i2 0)
	(>= j2 0)
	(< i2 (car (dimensions name L)))
	(< j2 (cadr (dimensions name L)))
	)
   (equal (aref2 name (aset2 name L i1 j1 val) i2 j2)
	  (if (and (equal i1 i2)
		   (equal j1 j2))
	      val
	      (aref2 name l i2 j2)))))

(in-theory (disable alist2p-aref2-aset2-equal alist2p-aref2-aset2-not-equal))

;;; The final form of the :FORWARD-CHAINING lemma for ALIST2P.
;;;   A forward definition of (ALIST2P name l), in terms of
;;;   HEADER, DIMENSIONS, and MAXIMUM-LENGTH.

;;;   One should normaly DISABLE ALIST2P in favor of this
;;;   :FORWARD-CHAINING rule. If allowed to open, ALIST2P can
;;;   cause severe performance degradation due to its large size
;;;   and many recursive functions.  This lemma is designed to be
;;;   used with the ALISP2-FUNCTIONS theory DISABLEd.

;; This forward-chaining rule appears to require the ignored argument, name,
;;  in alist2p in order to avoid name as a free variable.
(defthm alist2p-forward-modular
  (implies
   (alist2p name L)
   (and (alistp L)
	(keyword-value-listp (cdr (header name L)))
	(consp (dimensions name L))
	(consp (cdr (dimensions name L)))
	(integerp (car (dimensions name L)))
	(integerp (cadr (dimensions name L)))
	(< 0 (car (dimensions name L)))
	(< 0 (cadr (dimensions name L)))
	(bounded-integer-alistp2 L
				 (car (dimensions name L))
				 (cadr (dimensions name L)))))
  :rule-classes :forward-chaining)

(defthm alist2p-linear-modular
  (implies
   (alist2p name L)
   (and (< 0 (car (dimensions name L)))
	(< 0 (cadr (dimensions name L)))))
  :rule-classes :linear)

(deftheory
  alist2-functions
  '(alist2p aset2 aref2 compress2 header dimensions maximum-length
    default)
; Matt K. mod 10/30/2015: :doc is no longer supported for deftheory.
; :doc "A theory of all functions specific to 2-dimensional alists.
;       This theory must be DISABLEd in order for the lemmas
;       exported by the alist2 book to be applicable."
  )

(deftheory
  alist2-lemmas
  '(alist2p-compress2
    alist2p-compress2-properties
    alist2p-aset2
    alist2p-aset2-properties
    alist2p-aref2-compress2
    array2p-acons-properties
    alist2p-consp-header
    alist2p-car-header
    alist2p-aref2-aset2
    alist2p-forward-modular
    alist2p-linear-modular))

(deftheory
  alist2-disabled-lemmas
  '(alist2p-aref2-aset2-equal
    alist2p-aref2-aset2-not-equal)
; Matt K. mod 10/30/2015: :doc is no longer supported for deftheory.
; :doc "A theory of all rules exported DISABLEd by the alist2 book.
;       Note that in order for these rules to be applicable you
;       will first need to (DISABLE ALIST2-FUNCTIONS)."
  )

