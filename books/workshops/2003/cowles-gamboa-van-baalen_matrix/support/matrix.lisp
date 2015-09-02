; The ACL2 Matrices (Implemented as ACL2 2-D Arrays) Book.
; Copyright (C) 2002 Ruben Gamboa and John R. Cowles, University of Wyoming

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
; Ruben Gamboa and John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

; Summer and Fall 2002.
;  Last modified 13 June 2003.

; ACL2 Version 2.8 alpha (as of May 11 03)
#|
 To certify in
      ACL2 Version 2.8 alpha (as of May 11 03)

(certify-book "matrix"
	      0
	      t ;;compile-flg
	      )
|#
#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
At UW:

:set-cbd "/home/faculty/cowles/acl2/matrix/" ;;pyramid

:set-cbd "/home/cowles/matrix/" ;; turing
|#

(in-package "ACL2")

#|
(local  ;;turing
 (include-book
 "/home/cowles/acl2-sources/books/arithmetic-2.8/top"))

(local  ;;pyramid
 (include-book
  "/home/acl2/acl2-2.8/v2-8-alpha-05-11-03/books/arithmetic/top"))
|#

(local
 (include-book "../../../../arithmetic/top"))

(include-book "array2")

(include-book "alist2")

(defthm
  compress211-$arg
  (implies (syntaxp (not (eq name ''$arg)))
	   (equal (compress211 name  l n i j default)
		  (compress211 '$arg l n i j default))))

(defthm
  compress21-$arg
  (implies (syntaxp (not (eq name ''$arg)))
	   (equal (compress21 name  l n i j default)
		  (compress21 '$arg l n i j default))))

(defthm
  array2p-$arg-equal-parts
  (implies (syntaxp (not (eq name ''$arg)))
	   (and (equal (header name  l)
		       (header '$arg l))
		(equal (dimensions name  l)
		       (dimensions '$arg l))
		(equal (maximum-length name  l)
		       (maximum-length '$arg l))
		(equal (default name  l)
		       (default '$arg l))
		(equal (compress2 name  l)
		       (compress2 '$arg l))
		(equal (aref2 name  l i j)
		       (aref2 '$arg l i j))
		(equal (aset2 name  l i j val)
		       (aset2 '$arg l i j val)))))

(defthm
  array2p-$arg
  (implies (array2p name  l)
	   (array2p '$arg l))
  :rule-classes :forward-chaining)

(defthm
  not-array2p-arg$
  (implies (and (not (array2p name l))
		(symbolp name))
	   (not (array2p '$arg l)))
  :rule-classes :forward-chaining)

(defthm
  alist2p-$arg
  (implies (alist2p name  l)
	   (alist2p '$arg l))
  :rule-classes :forward-chaining)

(defthm
  not-alist2p-arg$
  (implies (not (alist2p name l))
	   (not (alist2p '$arg l)))
  :rule-classes :forward-chaining)

(in-theory (disable alist2p array2p aset2 aref2 compress2 header
		    dimensions maximum-length default))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Boolean test for a matrix:

;;  The  need for the following constant is explained in
;;   detail later in this book:

;;   Search for
;;      ; Ensuring closure of matrix multiplication.

(defconst
  *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*
  46340)

;;  To ensure that matrix multiplication is closed, the
;;   matrix can have no more that 46,340 rows and no more
;;   46,340 columns.

(defun
  matrixp (m n X)
  "Determine if X is a m by n matrix."
  (declare (xargs :guard t))
  (and (array2p '$arg X)
       (let ((dims (dimensions '$arg X)))
	    (and (equal m (first dims))
		 (equal n (second dims))))
       (<= m *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*)
       (<= n *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*)))

(defmacro
  r (M)
  "Return the number of rows in the matrix M."
  `(car (dimensions '$arg ,M)))

(defmacro
  c (M)
  "Return the number of columns in the matrix M."
  `(cadr (dimensions '$arg ,M)))

(defthm
  array2p-matrixp
  (implies (and (array2p name M)
		(<= (r M) *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*)
		(<= (c M) *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*))
	   (matrixp (r M)(c M) M)))

;;;;;;;;;;;;;;;;;;;
;; Matrix equality:

(defun
  m-=-row (M1 M2 m n)
  "Determine if all the following equalities hold:
   M1(m 0) = M2(m 0), . . . , M1(m n) = M2(m n);
   ie. determine if the m'th row of M1 matches the
       m'th row of M2.
   All entries are treated as numbers."
  (declare (xargs :guard (and (integerp m)
			      (>= m 0)
			      (integerp n)
			      (>= n 0)
			      (array2p '$arg1 M1)
			      (array2p '$arg2 M2)
			      (let ((dims1 (dimensions '$arg1 M1)))
				   (and (< m (car dims1))
					(< n (cadr dims1))))
			      (let ((dims2 (dimensions '$arg2 M2)))
				   (and (< m (car dims2))
					(< n (cadr dims2)))))))
  (if (zp n)
      (equal (fix (aref2 '$arg1 M1 m 0))
	     (fix (aref2 '$arg2 M2 m 0)))
      (and (equal (fix (aref2 '$arg1 M1 m n))
		  (fix (aref2 '$arg2 M2 m n)))
	   (m-=-row M1 M2 m (- n 1)))))

(defthm
  reflexivity-of-m-=-row
  (m-=-row X X m n))

(defthm
  symmetry-of-m-=-row
  (implies (m-=-row M1 M2 m n)
	   (m-=-row M2 M1 m n)))

(defthm
  transitivity-of-m-=-row
  (implies (and (m-=-row M1 M2 m n)
		(m-=-row M2 M3 m n))
	   (m-=-row M1 M3 m n))
  :rule-classes (:rewrite :forward-chaining))

(defthm
  m-=-row-compress2
  (implies (and (alist2p name l)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name l)))
		(< j (cadr (dimensions name l))))
	   (m-=-row (compress2 name l) l i j)))

(defthm
  m-=-row-remove-compress2-1
  (implies (and (alist2p name l1)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name l1)))
		(< j (cadr (dimensions name l1))))
	   (equal (m-=-row (compress2 name l1) l2 i j)
		  (m-=-row l1 l2 i j))))

(defthm
  m-=-row-remove-compress2-2
  (implies (and (alist2p name l2)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name l2)))
		(< j (cadr (dimensions name l2))))
	   (equal (m-=-row l1 (compress2 name l2) i j)
		  (m-=-row l1 l2 i j))))

(defthm
  m-=-row-fix-aref2
  (implies (and (m-=-row M1 M2 m n)
		(integerp n)
		(integerp j)
		(<= 0 j)
		(<= j n))
	  (equal (fix (aref2 name M1 m j))
		 (fix (aref2 name M2 m j))))
  :rule-classes nil)

(defun
  m-=-row-1 (M1 M2 m n)
  "Determine if all the following equalities hold:
   M1(0 0) = M2(0 0), . . . , M1(0 n) = M2(0 n)
           .          .               .
           .            .             .
           .              .           .
   M1(m 0) = M2(m 0), . . . , M1(m n) = M2(m n);
   ie. determine if rows 0 thru m of M1 matches
       rows 0 thru m of M2.
   All entries are treated as numbers."
  (declare (xargs :guard (and (integerp m)
			      (>= m 0)
			      (integerp n)
			      (>= n 0)
			      (array2p '$arg1 M1)
			      (array2p '$arg2 M2)
			      (let ((dims1 (dimensions '$arg1 M1)))
				   (and (< m (car dims1))
					(< n (cadr dims1))))
			      (let ((dims2 (dimensions '$arg2 M2)))
				   (and (< m (car dims2))
					(< n (cadr dims2)))))))
  (if (zp m)
      (m-=-row M1 M2 0 n)
      (and (m-=-row M1 M2 m n)
	   (m-=-row-1 M1 M2 (- m 1) n))))

(defthm
  reflexivity-of-m-=-row-1
  (m-=-row-1 X X m n))

(defthm
  symmetry-of-m-=-row-1
  (implies (m-=-row-1 M1 M2 m n)
	   (m-=-row-1 M2 M1 m n)))

(defthm
  transitivity-of-m-=-row-1
  (implies (and (m-=-row-1 M1 M2 m n)
		(m-=-row-1 M2 M3 m n))
	   (m-=-row-1 M1 M3 m n))
  :rule-classes (:rewrite :forward-chaining))

(defthm
  m-=-row-1-compress2
  (implies (and (alist2p name l)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name l)))
		(< j (cadr (dimensions name l))))
	   (m-=-row-1 (compress2 name l) l i j)))

(defthm
  m-=-row-1-remove-compress2-1
  (implies (and (alist2p name l1)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name l1)))
		(< j (cadr (dimensions name l1))))
	   (equal (m-=-row-1 (compress2 name l1) l2 i j)
		  (m-=-row-1 l1 l2 i j))))

(defthm
  m-=-row-1-remove-compress2-2
  (implies (and (alist2p name l2)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name l2)))
		(< j (cadr (dimensions name l2))))
	   (equal (m-=-row-1 l1 (compress2 name l2) i j)
		  (m-=-row-1 l1 l2 i j))))

(defthm
  m-=-row-1-fix-aref2
  (implies (and (m-=-row-1 M1 M2 m n)
		(integerp m)
		(integerp n)
		(integerp i)
		(integerp j)
		(<= 0 i)
		(<= 0 j)
		(<= i m)
		(<= j n))
	  (equal (fix (aref2 name M1 i j))
		 (fix (aref2 name M2 i j))))
  :rule-classes nil
  :hints (("Subgoal *1/2"
	   :use (:instance
		 m-=-row-fix-aref2
		 (m i)))
	  ("Subgoal *1/1"
	   :use (:instance
		 m-=-row-fix-aref2
		 (m 0)))))

(defun
  m-= (M1 M2)
  "Determine if the matrices represented by the alists
   M1 and M2 are equal (as matrices of numbers)."
  (declare (xargs :guard (and (array2p '$arg1 M1)
			      (array2p '$arg2 M2))))
  (if (mbt (and (alist2p '$arg1 M1)
		(alist2p '$arg2 M2)))
      (let ((dim1 (dimensions '$arg1 M1))
	    (dim2 (dimensions '$arg2 M2)))
	   (if (and (= (first dim1)
		       (first dim2))
		    (= (second dim1)
			   (second dim2)))
	       (m-=-row-1 (compress2 '$arg1 M1)
			  (compress2 '$arg2 M2)
			  (- (first dim1) 1)
			  (- (second dim1) 1))
	       nil))
      (equal M1 M2)))

(defequiv
  ;; m-=-is-an-equivalence
  m-=)

(defthm
  m-=-compress2
  (implies (alist2p name l)
	   (m-= (compress2 name l) l)))

(defthm
  m-=-implies-equal-dims
  (implies (m-= M1 M2)
	   (and (equal (car (dimensions name M1))
		       (car (dimensions name M2)))
		(equal (cadr (dimensions name M1))
		       (cadr (dimensions name M2)))))
  :rule-classes nil)

(defcong
  ;; m-=-implies-equal-alist2p-2
  m-= equal (alist2p name M) 2
  :hints (("Goal"
	   :use (:theorem
		 (implies (m-= M M-equiv)
			  (iff (alist2p name M)
			       (alist2p name M-equiv)
			       ))))))

(defthm
  m-=-fix-aref2
  (implies (and (m-= M1 M2)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name M1)))
		(< j (cadr (dimensions name M1))))
	   (equal (fix (aref2 name M1 i j))
		  (fix (aref2 name M2 i j))))
  :rule-classes nil
  :hints (("Subgoal 3'"
	   :use (:instance
		 m-=-row-1-fix-aref2
		 (name '$arg)
		 (m (+ -1 (car (dimensions '$arg M1)))
		    )
		 (n (+ -1 (cadr (dimensions '$arg M1))
		       ))))
	  ("Subgoal 2'"
	   :use (:instance
		m-=-row-1-fix-aref2
		(name '$arg)
		(m (+ -1 (car (dimensions '$arg M1)))
		   )
		(n (+ -1 (cadr (dimensions '$arg M1))
		      ))))
	  ("Subgoal 1'"
	   :use (:instance
		m-=-row-1-fix-aref2
		(name '$arg)
		(m (+ -1 (car (dimensions '$arg M1)))
		   )
		(n (+ -1 (cadr (dimensions '$arg M1))
		      ))))))

;;;;;;;;;;;;;;;
;; Zero matrix:

(defun
  m-0 (m n)
  "Return an alist representing the m by n matrix whose
   elements are all equal to 0.
   To use the ACL2 efficient array mechanism to store (m-0 m n),
   (* m n)) must be stictly less than 2147483647 which is
   the *MAXIMUM-POSITIVE-32-BIT-INTEGER*."
  (declare (xargs :guard (and (integerp m)
			      (integerp n)
			      (> m 0)
			      (> n 0))))
  (list (list :HEADER
	      :DIMENSIONS (list m n)
	      :MAXIMUM-LENGTH (+ 1 (* m n))
	      :DEFAULT 0
	      :NAME 'zero-matrix)))

(defthm
  alist2p-m-0
  (implies (and (integerp m)
		(integerp n)
		(> m 0)
		(> n 0))
	   (alist2p name (m-0 m n)))
  :hints (("Goal" :in-theory (enable alist2p))))

(defthm
  array2p-m-0
  (implies (and (symbolp name)
		(integerp m)
		(integerp n)
		(> m 0)
		(> n 0)
		(< (* m n) *MAXIMUM-POSITIVE-32-BIT-INTEGER*))
	   (array2p name (m-0 m n)))
  :hints (("Goal" :in-theory (enable array2p))))

(defthm
  sqrt-*-sqrt-<-sq
  (implies (and (rationalp x)
		(rationalp y)
		(>= x 0)
		(>= y 0)
		(<= x 46340)
		(<= y 46340))
	   (< (* x y) 2147483647))
  :rule-classes (:rewrite :linear)
  :hints (("Goal"
	   :use (:instance
		 *-PRESERVES->=-FOR-NONNEGATIVES
		 (x2 x)
		 (y2 y)
		 (x1 46340)
		 (y1 46340)))))

(defthm
  matrixp-m-0
  (implies (and (integerp m)
		(integerp n)
		(> m 0)
		(> n 0)
		(<= m *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*)
		(<= n *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*))
	   (matrixp m n (m-0 m n)))
  :hints (("Goal" :in-theory (enable array2p
				     dimensions
				     header))))

(defthm
  aref2-m-0
  (equal (aref2 name (m-0 m n) i j) 0)
  :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(defthm
  dimensions-m-0
  (equal (dimensions name (m-0 m n))(list m n))
  :hints (("Goal"
	   :in-theory (enable header dimensions))))

(defthm
  default-m-0
  (equal (default name (m-0 m n))
	 0)
  :hints (("Goal"
	   :in-theory (enable header default))))

(in-theory (disable m-0))

(defthm
  alist2p-alist2p-m-0
  (implies (alist2p name1 M)
	   (alist2p name2 (m-0 (car (dimensions
				     '$arg M))
			       (cadr (dimensions
				      '$arg M))))))

(defthm
  array2p-array2p-m-0
  (implies (and (array2p name1 M)
		(symbolp name2))
	   (array2p name2 (m-0 (car (dimensions
				     '$arg M))
			       (cadr (dimensions
				      '$arg M))))))

;;;;;;;;;;;;;;;;;;;
;; Identity matrix:

(defun
  m-1a (n)
  "Return alist of length n of the form
   ( ((- n 1) . (- n 1)) . 1) . . . ((0 . 0) . 1) )."
  (declare (xargs :guard (and (integerp n)
			      (>= n 0))
		  :verify-guards nil))
  (if (zp n)
      nil
      (acons (cons (- n 1)(- n 1)) 1 (m-1a (- n 1)))))

(defthm
  alistp-m-1a
  (alistp (m-1a n)))

(verify-guards m-1a)

(defthm
  bounded-integer-alistp2->=
  (implies (and (bounded-integer-alistp2 l i j)
		(integerp m)
		(integerp n)
		(<= i m)
		(<= j n))
	   (bounded-integer-alistp2 l m n)))

(defthm
  bounded-integer-alistp2-m-1a
  (bounded-integer-alistp2 (m-1a n) n n))

(defthm
  assoc2-i-i-m-1a
  (implies (and (integerp i)
		(integerp n)
		(>= i 0)
		(< i n))
	   (and (assoc2 i i (m-1a n))
		(equal (cdr (assoc2 i i (m-1a n)))
		       1))))

(defthm
  assoc2-i-j-m-1a
  (implies (not (equal i j))
	   (not (assoc2 i j (m-1a n)))))

(defun
  m-1 (n)
  "Return an alist representing the n by n identity matrix.
   To use the ACL2 efficient array mechanism to store (m-1 n),
   (* n n)) must be stictly less than 2147483647 which is
   the *MAXIMUM-POSITIVE-32-BIT-INTEGER*."
  (declare (xargs :guard (and (integerp n)
			      (>= n 0))))
  (cons (list :HEADER
	      :DIMENSIONS (list n n)
	      :MAXIMUM-LENGTH (+ 1 (* n n))
	      :DEFAULT 0
	      :NAME 'identity-matrix)
	(m-1a n)))

(defthm
  alist2p-m-1
  (implies (and (integerp n)
		(> n 0))
	   (alist2p name (m-1 n)))
  :hints (("Goal"
	   :in-theory (enable alist2p))))

(defthm
  array2p-m-1
  (implies (and (symbolp name)
		(integerp n)
		(> n 0)
		(< (* n n) *MAXIMUM-POSITIVE-32-BIT-INTEGER*))
	   (array2p name (m-1 n)))
  :hints (("Goal"
	   :in-theory (enable array2p))))

(defthm
  matrixp-m-1
  (implies (and (integerp n)
		(> n 0)
		(<= n *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*))
	   (matrixp n n (m-1 n)))
  :hints (("Goal"
	   :in-theory (enable array2p dimensions header))))

(defthm
  aref2-m-1-i-i
  (implies (and (integerp i)
		(integerp n)
		(<= 0 i)
		(< i n))
	   (equal (aref2 name (m-1 n) i i) 1))
  :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(defthm
  aref2-m-1-i-j
  (implies (not (equal i j))
	   (equal (aref2 name (m-1 n) i j) 0))
  :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(defthm
  dimensions-m-1
  (equal (dimensions name (m-1 n))(list n n))
  :hints (("Goal"
	   :in-theory (enable header dimensions))))

(in-theory (disable m-1))

;;;;;;;;;;;;;;;;;;;;;;;;;
;; Transpose of a matrix:

(defun
  m-trans-a (M)
  (declare (xargs :guard (alistp M)))
  (if (consp M)
      (let ((key (caar M))
	    (datum (cdar M)))
	   (if (consp key)
	       (acons (cons (cdr key)
			    (car key))
		      datum
		      (m-trans-a (cdr M)))
	       (m-trans-a (cdr M))))
      nil))

(defthm
  alistp-m-trans-a
  (alistp (m-trans-a M)))

(defthm
  bounded-integer-alistp2-m-trans-a
  (implies (bounded-integer-alistp2 l m n)
	   (bounded-integer-alistp2 (m-trans-a l)
				    n
				    m)))

(defthm
  assoc2-m-trans-a
  (iff (assoc2 i j (m-trans-a M))
       (assoc2 j i M)))

(defthm
  cdr-assoc2-m-trans-a
  (equal (cdr (assoc2 i j (m-trans-a M)))
	 (cdr (assoc2 j i M))))

(defun
  m-trans (M)
  "Return an alist representing the transpose of the matrix
   represented by the alist M."
  (declare (xargs :guard (array2p '$arg M)))
  (cons (list :HEADER
	      :DIMENSIONS (let ((dims (dimensions '$arg M)))
			       (list (cadr dims)(car dims)))
	      :MAXIMUM-LENGTH (maximum-length '$arg M)
	      :DEFAULT (default '$arg M)
	      :NAME 'transpose-matrix)
	(m-trans-a M)))

(defthm
  alist2p-m-trans
  (implies (alist2p name M)
	   (alist2p name (m-trans M)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((m-trans M))))
  :hints (("Goal"
	   :in-theory (enable alist2p header
			      dimensions))))

(defthm
  array2p-m-trans
  (implies (array2p name M)
	   (array2p name (m-trans M)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((m-trans M))))
  :hints (("Goal"
	   :in-theory (enable array2p header
			      dimensions
			      maximum-length))))

(defthm
  dimensions-m-trans
  (equal (dimensions name (m-trans M))
	 (list (cadr (dimensions name M))
	       (car  (dimensions name M))))
  :hints (("Goal"
	   :in-theory (enable dimensions header))))

(defthm
  equal-list-dimensions-array2p
  (implies (array2p name M)
	   (equal (list (car (dimensions name M))
			(cadr (dimensions name M)))
		  (dimensions name M)))
  :hints (("Goal"
	   :in-theory (enable array2p dimensions header))))

(defthm
  aref2-m-trans
  (equal (aref2 name (m-trans M) i j)
	 (aref2 name M j i))
  :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(in-theory (disable m-trans))

(defthm
  matrixp-m-trans
  (implies (matrixp m n X)
	   (matrixp n m (m-trans X))))

(defthm
  m-=-row-idempotency-of-m-trans
  (m-=-row (m-trans (m-trans M)) M i j))

(defthm
  m-=-row-1-idempotency-of-m-trans
  (m-=-row-1 (m-trans (m-trans M)) M i j))

(defthm
  array2p-alist2p-$arg2
  (implies (array2p name M)
	   (alist2p '$arg2 M))
  :hints (("Goal"
	   :use (:theorem
		 (implies (array2p name M)
			  (array2p '$arg2 M))))))

(defthm
  idempotency-of-m-trans-alist2p
  (implies (alist2p name M)
	   (m-= (m-trans (m-trans M)) M)))

(defthm
  idempotency-of-m-trans-array2p
  (implies (array2p name M)
	   (m-= (m-trans (m-trans M)) M))
  :hints (("Goal'"
	   :use (:theorem
		 (implies (array2p '$arg1 M)
			  (alist2p '$arg1
				   (m-trans
				    (m-trans M))))))))

(defthm
  remove-last-col-m-=-row-1
  (implies (m-=-row-1 M1 M2 i j)
	   (m-=-row-1 M1 M2 i (- j 1))))

(local
 (defthm
   m-=-row-1-m-trans-1
   (implies (m-=-row-1 (m-trans M1)(m-trans M2) j i)
	    (m-=-row-1 M1 M2 i j))))

(local
 (defthm
   m-=-row-1-m-trans-2
   (implies (m-=-row-1 M1 M2 i j)
	    (m-=-row-1 (m-trans M1)(m-trans M2) j i))
   :hints (("Goal"
	    :in-theory (disable m-=-row-1-idempotency-of-m-trans)
	    :use ((:instance
		   m-=-row-1-m-trans-1
		   (M1 (m-trans M1))
		   (M2 (m-trans M2))
		   (j i)
		   (i j))
		  (:instance
		   m-=-row-1-idempotency-of-m-trans
		   (M M1))
		  (:instance
		   m-=-row-1-idempotency-of-m-trans
		   (M M2)))))))

(defthm
  m-=-row-1-m-trans-iff
  (iff (m-=-row-1 (m-trans M1)(m-trans M2) j i)
       (m-=-row-1 M1 M2 i j)))

(local
 (in-theory (disable m-=-row-1-m-trans-1
		     m-=-row-1-m-trans-2)))

(defcong
  ;; M-=-IMPLIES-M-=-M-TRANS-1
  m-= m-= (m-trans M) 1)

(defthm
  m-=-row-1-m-trans-m-0
  (m-=-row-1 (m-trans (m-0 m n))
	     (m-0 n m)
	     j
	     i))

(defthm
  m-=-m-trans-m-0
  (implies (and (integerp m)
		(integerp n)
		(> m 0)
		(> n 0))
	   (m-= (m-trans (m-0 m n))
		(m-0 n m))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unary minus of a matrix:

(defun
  m-unary--a (M)
  (declare (xargs :guard (alistp M)))
  (if (consp M)
      (let ((key (caar M))
	    (datum (cdar M)))
	   (if (consp key)
	       (acons key
		      (- (fix datum))
		      (m-unary--a (cdr M)))
	       (m-unary--a (cdr M))))
      nil))

(defthm
  alistp-m-unary--a
  (alistp (m-unary--a M)))

(defthm
  bounded-integer-alistp2-m-unary--a
  (implies (bounded-integer-alistp2 l m n)
	   (bounded-integer-alistp2 (m-unary--a l) m n)))

(defthm
  assoc2-m-unary--a
  (iff (assoc2 i j (m-unary--a M))
       (assoc2 i j M)))

(defthm
  cdr-assoc2-m-unary--a
  (implies (assoc2 i j M)
	   (equal (cdr (assoc2 i j (m-unary--a M)))
		  (- (cdr (assoc2 i j M))))))

(defun
  m-unary-- (M)
  "Return an alist representing the unary minus of the matrix
   represented by the alist M."
  (declare (xargs :guard (array2p '$arg M)))
  (cons (list :HEADER
	      :DIMENSIONS (dimensions '$arg M)
	      :MAXIMUM-LENGTH (maximum-length '$arg M)
	      :DEFAULT (- (fix (default '$arg M)))
	      :NAME 'unary-minus-matrix)
	(m-unary--a M)))

(defthm
  alist2p-m-unary--
  (implies (alist2p name M)
	   (alist2p name (m-unary-- M)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((m-unary-- M))))
  :hints (("Goal"
	   :in-theory (enable alist2p header
			      dimensions))))

(defthm
  array2p-m-unary--
  (implies (array2p name M)
	   (array2p name (m-unary-- M)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((m-unary-- M))))
  :hints (("Goal"
	   :in-theory (enable array2p header
			      dimensions
			      maximum-length))))

(defthm
  dimensions-m-unary--
  (equal (dimensions name (m-unary-- M))
         (dimensions name M))
  :hints (("Goal"
	   :in-theory (enable array2p dimensions header))))

(defthm
  aref2-m-unary--
  (equal (aref2 name (m-unary-- M) i j)
	 (- (aref2 name M i j)))
  :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(in-theory (disable m-unary--))

(defthm
  matrixp-m-unary--
  (implies (matrixp m n X)
	   (matrixp m n (m-unary-- X))))

(defthm
  m-=-row-idempotency-of-m-unary--
  (m-=-row (m-unary-- (m-unary-- M)) M i j))

(defthm
  m-=-row-1-idempotency-of-m-unary--
  (m-=-row-1 (m-unary-- (m-unary-- M)) M i j))

(defthm
  idempotency-of-m-unary--_alist2p
  (implies (alist2p name M)
	   (m-= (m-unary-- (m-unary-- M)) M)))

(defthm
  array2p-alist2p-$arg1-m-unaray--
  (implies (array2p name M)
	   (alist2p '$arg1 (m-unary-- (m-unary-- M)))
	   )
  :hints (("Goal"
	   :use (:theorem
		 (implies (array2p '$arg1 M)
			  (alist2p '$arg1
				   (m-unary--
				    (m-unary-- M))))
		 ))))

(defthm
  idempotency-of-m-unary--_array2p
  (implies (array2p name M)
	   (m-= (m-unary-- (m-unary-- M)) M)))

(defthm
  m-=-row-1-m-unary--
  (implies (m-=-row-1 M1 M2 i j)
	   (m-=-row-1 (m-unary-- M1)(m-unary-- M2) i j)))

(defcong
  ;; M-=-IMPLIES-M-=-M-UNARY---1
  m-= m-= (m-unary-- M) 1)

(defthm
  m-=-row-1-m-trans-m-unary--
  (m-=-row-1 (m-trans (m-unary-- M))
	     (m-unary-- (m-trans M))
	     i
	     j))

(defthm
  m-=-m-trans-m-unary--
  (implies (alist2p name M)
	   (m-= (m-trans (m-unary-- M))
		(m-unary-- (m-trans M)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Scalar multiplication of a matrix:

(defun
  s-*-a (a M)
  (declare (xargs :guard (and (acl2-numberp a)
			      (alistp M))))
  (if (consp M)
      (let ((key (caar M))
	    (datum (cdar M)))
	   (if (consp key)
	       (acons key
		      (* a (fix datum))
		      (s-*-a a (cdr M)))
	       (s-*-a a (cdr M))))
      nil))

(defthm
  alistp-s-*-a
  (alistp (s-*-a a M)))

(defthm
  bounded-integer-alistp2-s-*-a
  (implies (bounded-integer-alistp2 l m n)
	   (bounded-integer-alistp2 (s-*-a a l) m n)))

(defthm
  assoc2-s-*-a
  (iff (assoc2 i j (s-*-a a M))
       (assoc2 i j M)))

(defthm
  cdr-assoc2-s-*-a
  (implies (assoc2 i j M)
	   (equal (cdr (assoc2 i j (s-*-a a M)))
		  (* a (cdr (assoc2 i j M))))))

(defun
  s-* (a M)
  "Return an alist representing the multiplication
   of the scalar a times the matrix represented by
   the alist M."
  (declare (xargs :guard (and (acl2-numberp a)
			      (array2p '$arg M))))
  (cons (list :HEADER
	      :DIMENSIONS (dimensions '$arg M)
	      :MAXIMUM-LENGTH (maximum-length '$arg M)
	      :DEFAULT (* a (fix (default '$arg M)))
	      :NAME 'scalar-mult-matrix)
	(s-*-a a M)))

(defthm
  alist2p-s-*
  (implies (alist2p name M)
	   (alist2p name (s-* a M)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((s-* a M))))
  :hints (("Goal"
	   :in-theory (enable alist2p header
			      dimensions))))

(defthm
  array2p-s-*
  (implies (array2p name M)
	   (array2p name (s-* a M)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((s-* a M))))
  :hints (("Goal"
	   :in-theory (enable array2p header
			      dimensions
			      maximum-length))))

(defthm
  dimensions-s-*
  (equal (dimensions name (s-* a M))
         (dimensions name M))
  :hints (("Goal"
	   :in-theory (enable array2p dimensions header))))

(defthm
  aref2-s-*
  (equal (aref2 name (s-* a M) i j)
	 (* a (aref2 name M i j)))
  :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(in-theory (disable s-*))

(defthm
  matrixp-s-*
  (implies (matrixp m n X)
	   (matrixp m n (s-* a X))))

(defthm
  m-=-row-1-s-*
  (implies (m-=-row-1 M1 M2 i j)
	   (m-=-row-1 (s-* a M1)(s-* a M2) i j)))

(defcong
  ;; M-=-IMPLIES-M-=-S-*-2
  m-= m-= (s-* a M) 2)

(defthm
  m-=-row-associate-scalars-left-s-*
  (m-=-row (s-* a1 (s-* a2 M))(s-* (* a1 a2) M) i j))

(defthm
  m-=-row-1-associate-scalars-left-s-*
  (m-=-row-1 (s-* a1 (s-* a2 M))(s-* (* a1 a2) M) i j))

(defthm
  associate-scalars-left-s-*
  (implies (alist2p name M)
	   (m-= (s-* a1 (s-* a2 M))
		(s-* (* a1 a2) M))))

(defthm
  m-=-row-1-s-*-0
  (m-=-row-1 (s-* 0 M)(m-0 (r M)(c M)) i j))

(defthm
  m-=-s-*-0
  (implies (alist2p name M)
	   (m-= (s-* 0 M)(m-0 (r M)(c M)))))

(defthm
  m-=-row-1-s-*-m-0
  (m-=-row-1 (s-* a (m-0 m n))(m-0 m n) i j))

(defthm
  m-=-s-*-m-0
  (implies (and (integerp m)
		(integerp n)
		(> m 0)
		(> n 0))
	   (m-= (s-* a (m-0 m n))(m-0 m n))))

(defthm
  m-=-row-1-s-*-1
  (m-=-row-1 (s-* 1 M) M i j))

(defthm
  m-=-s-*-1
  (implies (alist2p name M)
	   (m-= (s-* 1 M) M)))

(defthm
  m-=-row-1-s-*_-1
  (m-=-row-1 (s-* -1 M)(m-unary-- M) i j))

(defthm
  m-=-s-*_-1
  (implies (alist2p name M)
	   (m-= (s-* -1 M)(m-unary-- M))))

(defthm
  m-=-row-1-m-trans-s-*
  (m-=-row-1 (m-trans (s-* s M))
	     (s-* s (m-trans M))
	     i
	     j))

(defthm
  m-=-m-trans-s-*
  (implies (alist2p name M)
	   (m-= (m-trans (s-* s M))
		(s-* s (m-trans M)))))

;;;;;;;;;;;;;;
;; Matrix sum:

(defun
  m-binary-+-row (M1 M2 m n)
  "Return an alist with the following values:
   M1(m 0)+M2(m 0), . . . , M1(m n)+M2(m n);
   ie. construct an alist of values representing
   the vector sum of the m'th row of M1 and the
   m'th row of M2."
  (declare (xargs :guard
		  (and (integerp m)
		       (>= m 0)
		       (integerp n)
		       (>= n 0)
		       (array2p '$arg1 M1)
		       (array2p '$arg2 M2)
		       (let ((dims1 (dimensions
				     '$arg1 M1)))
			    (and (< m (first dims1))
				 (< n (second dims1))))
		       (let ((dims2 (dimensions
				     '$arg2 M2)))
			    (and (< m (first dims2))
				 (< n (second dims2))))
		       )))
  (if (zp n)
      (list (cons (cons m 0)
		  (+ (fix (aref2 '$arg1 M1 m 0))
		     (fix (aref2 '$arg2 M2 m 0)))))
      (cons (cons (cons m n)
		  (+ (fix (aref2 '$arg1 M1 m n))
		     (fix (aref2 '$arg2 M2 m n))))
	    (m-binary-+-row M1 M2 m (- n 1)))))

(defthm
  m-binary-+-row-remove-compress2-1
  (implies (and (alist2p name l1)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name l1)))
		(< j (cadr (dimensions name l1))))
	   (equal (m-binary-+-row (compress2 name l1) l2 i j)
		  (m-binary-+-row l1 l2 i j))))

(defthm
  m-binary-+-row-remove-compress2-2
  (implies (and (alist2p name l2)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name l2)))
		(< j (cadr (dimensions name l2))))
	   (equal (m-binary-+-row l1 (compress2 name l2) i j)
		  (m-binary-+-row l1 l2 i j))))

(defthm
  m-=-row-implies-equal-m-binary-+-row-1
  (implies (m-=-row M1 M2 m n)
	   (equal (m-binary-+-row M1 M3 m n)
		  (m-binary-+-row M2 M3 m n))))

(defthm
  m-=-row-implies-equal-m-binary-+-row-2
  (implies (m-=-row M2 M3 m n)
	   (equal (m-binary-+-row M1 M2 m n)
		  (m-binary-+-row M1 M3 m n))))

(defthm
  assoc2-m-binary-+-row
  (implies (and (integerp n)
		(integerp j)
		(>= j 0)
		(<= j n))
	   (assoc2 m j (m-binary-+-row M1 M2 m n))))

(defthm
  assoc2=nil-m-binary-+-row
  (implies (not (equal i m))
	   (equal (assoc2 i j (m-binary-+-row M1 M2 m n))
		  nil)))

(defthm
  cdr-assoc2-m-binary-+-row
  (implies (and (integerp n)
		(integerp j)
		(>= j 0)
		(<= j n))
	   (equal (cdr (assoc2 m j (m-binary-+-row M1 M2 m n)))
		  (+ (aref2 '$arg1 M1 m j)
		     (aref2 '$arg2 M2 m j)))))

(defun
  m-binary-+-row-1 (M1 M2 m n)
  "Return an alist with all the following values:
   M1(0 0)+M2(0 0), . . . , M1(0 n)+M2(0 n)
          .         .              .
          .           .            .
          .             .          .
   M1(m 0)+M2(m 0), . . . , M1(m n)+M2(m n);
   ie. construct an alist of values representing
   the vector sum of rows 0 thru m of M1 with
   the corresponding rows 0 thru m of M2."
  (declare (xargs :guard
		  (and (integerp m)
		       (>= m 0)
		       (integerp n)
		       (>= n 0)
		       (array2p '$arg1 M1)
		       (array2p '$arg2 M2)
		       (let ((dims1 (dimensions
				     '$arg1 M1)))
			    (and (< m (first dims1))
				 (< n (second dims1))))
		       (let ((dims2 (dimensions
				     '$arg2 M2)))
			    (and (< m (first dims2))
				 (< n (second dims2))))
		       )))
  (if (zp m)
      (m-binary-+-row M1 M2 0 n)
      (append (m-binary-+-row M1 M2 m n)
	      (m-binary-+-row-1 M1 M2 (- m 1) n))))

(defthm
  alistp-m-binary-+-row-1
  (alistp (m-binary-+-row-1 M1 M2 m n)))

(defthm
  bounded-integerp-alistp2-m-binary-+-row-1
  (implies (and (integerp m)
		(integerp n)
		(>= i 0)
		(>= j 0)
		(< i m)
		(< j n))
	   (bounded-integer-alistp2 (m-binary-+-row-1 M1 M2 i j)
				    m
				    n)))

(defthm
  m-binary-+-row-1-remove-compress2-1
  (implies (and (alist2p name l1)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name l1)))
		(< j (cadr (dimensions name l1))))
	   (equal (m-binary-+-row-1 (compress2 name l1) l2 i j)
		  (m-binary-+-row-1 l1 l2 i j))))

(defthm
  m-binary-+-row-1-remove-compress2-2
  (implies (and (alist2p name l2)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name l2)))
		(< j (cadr (dimensions name l2))))
	   (equal (m-binary-+-row-1 l1 (compress2 name l2) i j)
		  (m-binary-+-row-1 l1 l2 i j))))

(defthm
  m-=-row-1-implies-equal-m-binary-+-row-1-1
  (implies (m-=-row-1 M1 M2 m n)
	   (equal (m-binary-+-row-1 M1 M3 m n)
		  (m-binary-+-row-1 M2 M3 m n))))

(defthm
  m-=-row-1-implies-equal-m-binary-+-row-1-2
  (implies (m-=-row-1 M2 M3 m n)
	   (equal (m-binary-+-row-1 M1 M2 m n)
		  (m-binary-+-row-1 M1 M3 m n))))

(defthm
  assoc2-m-binary-+-row-1
  (implies (and (integerp m)
		(integerp n)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(<= i m)
		(<= j n))
	   (assoc2 i j (m-binary-+-row-1 M1 M2 m n))))

(defthm
  assoc2=nil-m-binary-+-row-1
  (implies (and (>= m 0)
		(> i m))
	   (equal (assoc2 i j (m-binary-+-row-1 M1 M2 m n))
		  nil)))

(local
 (defthm
   assoc2-append
   (equal (assoc2 i j (append L1 L2))
	  (if (assoc2 i j L1)
	      (assoc2 i j L1)
	      (assoc2 i j L2)))))

(local
 (defthm
   cdr-assoc2-m-binary-+-row-1-lemma
   (implies (and (equal (cdr (assoc2 i j
				     (m-binary-+-row-1 M1 M2
						       (+ -1 m) n)))
			(+ (aref2 '$arg M1 i j)
			   (aref2 '$arg M2 i j)))
		 (integerp j)
		 (<= 0 j)
		 (<= j n))
	    (equal (cdr (assoc2 i j
				(append (m-binary-+-row M1 M2 m n)
					(m-binary-+-row-1 M1 M2
							  (+ -1 m) n))))
		   (+ (aref2 '$arg M1 i j)
		      (aref2 '$arg M2 i j))))))

(local (in-theory (disable assoc2-append)))

(defthm
  cdr-assoc2-m-binary-+-row-1
  (implies (and (integerp m)
		(integerp n)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(<= i m)
		(<= j n))
	   (equal (cdr (assoc2 i j (m-binary-+-row-1 M1 M2 m n)))
		  (+ (aref2 '$arg1 M1 i j)
		     (aref2 '$arg2 M2 i j)))))

(local (in-theory (disable cdr-assoc2-m-binary-+-row-1-lemma)))

(defun
  m-binary-+ (M1 M2)
  "Return an alist representing the matrix sum
   of the matrices represented by the alists M1
   and M2. This is done by adding a header to an
   alist containing the appropriate values."
  (declare (xargs :guard
		  (and (array2p '$arg1 M1)
		       (array2p '$arg2 M2)
		       (let ((dim1 (dimensions '$arg1
					       M1))
			     (dim2 (dimensions '$arg2
					       M2)))
			    (and
			     (= (first dim1)
				    (first dim2))
			     (= (second dim1)
				    (second dim2)))))
		  ))
  (let* ((dim1 (dimensions '$arg1 M1))
	 (dim2 (dimensions '$arg2 M2))
	 (dim11 (first dim1))
	 (dim12 (second dim1))
	 (dim21 (first dim2))
	 (dim22 (second dim2)))
  (if (mbt (and (alist2p '$arg1 M1)
		(alist2p '$arg2 M2)
		(= dim11 dim21)
		(= dim12 dim22)))
      (cons (list :HEADER
		  :DIMENSIONS (list dim11 dim12)
		  :MAXIMUM-LENGTH
		  (+ 1 (* dim11 dim12))
		  :DEFAULT 0
		  :NAME 'matrix-sum)
	    (m-binary-+-row-1 (compress2 '$arg1 M1)
			      (compress2 '$arg2 M2)
			      (- dim11 1)
			      (- dim12 1)))
      (+ M1 M2))))

(defmacro
  m-+ (&rest rst)
  (if rst
      (if (cdr rst)
	  (xxxjoin 'm-binary-+ rst)
	  (car rst))
      0))

(add-binop m-+ m-binary-+)

(defthm
  alist2p-m-+
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (first (dimensions name M1))
		       (first (dimensions name M2)))
		(equal (second (dimensions name M1))
		       (second (dimensions name M2))))
	   (alist2p name (m-+ M1 M2)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((m-+ M1 M2))))
  :hints (("Goal"
	   :in-theory (enable alist2p header
			      dimensions))))

(defthm
  array2p-m-+
  (implies (and (array2p name M1)
		(array2p name M2)
		(equal (dimensions name M1)
		       (dimensions name M2)))
	   (array2p name (m-+ M1 M2)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((m-+ M1 M2))))
  :hints (("Goal"
	   :in-theory (enable array2p header
			      dimensions
			      maximum-length))))

(defthm
  array2p-m-+-1
  (implies (and (array2p name M1)
		(array2p name M2)
		(equal (first (dimensions name M1))
		       (first (dimensions name M2)))
		(equal (second (dimensions name M1))
		       (second (dimensions name M2))))
	   (array2p name (m-+ M1 M2)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((m-+ M1 M2))))
  :hints (("Goal"
	   :in-theory (disable m-binary-+
			       equal-list-dimensions-array2p)
	   :use ((:instance
		  equal-list-dimensions-array2p
		  (M M1))
		 (:instance
		  equal-list-dimensions-array2p
		  (M M2))))))

(defthm
  dimensions-m-+-alist2p
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (first (dimensions name M1))
		       (first (dimensions name M2)))
		(equal (second (dimensions name M1))
		       (second (dimensions name M2))))
	   (equal (dimensions name (m-+ M1 M2))
		  (list (car (dimensions name M1))
			(cadr (dimensions name M1)))))
  :hints (("Goal"
	   :in-theory (enable alist2p dimensions
			      header))))

(defthm
  dimensions-m-+-array2p
  (implies (and (array2p name M1)
		(array2p name M2)
		(equal (dimensions name M1)
		       (dimensions name M2)))
	   (equal (dimensions name (m-+ M1 M2))
		  (dimensions name M1)))
  :hints (("Goal"
	   :in-theory (disable
		       equal-list-dimensions-array2p
		       dimensions-m-+-alist2p)
	   :use ((:instance
		  equal-list-dimensions-array2p
		  (M M1))
		 dimensions-m-+-alist2p))))

(defthm
  matrixp-m-+
  (implies (and (matrixp m n X1)
		(matrixp m n X2))
	   (matrixp m n (m-+ X1 X2)))
  :hints (("Goal"
	   :in-theory (disable m-binary-+))))

(defthm
  default-m-+-alist2p
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (first (dimensions name M1))
		       (first (dimensions name M2)))
		(equal (second (dimensions name M1))
		       (second (dimensions name M2))))
	   (equal (default name (m-+ M1 M2)) 0))
  :hints (("Goal"
	   :in-theory (enable alist2p default
			      header))))

(defthm
  default-m-+-array2p
  (implies (and (array2p name M1)
		(array2p name M2)
		(equal (dimensions name M1)
		       (dimensions name M2)))
	   (equal (default name (m-+ M1 M2)) 0))
  :hints (("Goal"
	   :in-theory (enable array2p default header))))

(defthm
  maximum-length-m-+
  (implies (and (array2p name M1)
		(array2p name M2)
		(equal (dimensions name M1)
		       (dimensions name M2)))
	   (equal (maximum-length name (m-+ M1 M2))
		  (+ 1 (* (car (dimensions name M1))
			  (cadr (dimensions name M1))))))
  :hints (("Goal"
	   :in-theory (enable array2p maximum-length header))))

(defthm
  aref2-m-+
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (first (dimensions name M1))
		       (first (dimensions name M2)))
		(equal (second (dimensions name M1))
		       (second (dimensions name M2)))
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (car (dimensions name M1)))
		(< j (cadr (dimensions name M1))))
	   (equal (aref2 name (m-+ M1 M2) i j)
		  (+ (aref2 name M1 i j)
		     (aref2 name M2 i j))))
  :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(defcong
  ;; M-=-IMPLIES-EQUAL-M-+-1
  m-= equal (M-+ M1 M2) 1)

(defcong
  ;; M-=-IMPLIES-EQUAL-M-+-2
  m-= equal (M-+ M1 M2) 2)

(defthm
  commutativity-of-m-binary-+-row
  (equal (m-binary-+-row M1 M2 m n)
	 (m-binary-+-row M2 M1 m n)))

(defthm
  commutativity-of-m-binary-+-row-1
  (equal (m-binary-+-row-1 M1 M2 m n)
	 (m-binary-+-row-1 M2 M1 m n)))

(defthm
  commutativity-of-m-+
  (equal (m-+ M1 M2)
	 (m-+ M2 M1)))

(defthm
  aref2-cons
  (equal (aref2 name (cons (cons (cons i j) val) lst) m n)
	 (if (and (equal i m)
		  (equal j n))
	     val
	     (aref2 name lst m n)))
  :hints (("Goal"
	   :in-theory (enable aref2))))

(defthm
  aref2-cons-move-header
  (equal (aref2 name
		(cons (list :HEADER
			    :DIMENSIONS dims
			    :MAXIMUM-LENGTH max-length
			    :DEFAULT default
			    :NAME name1)
		      (cons (cons (cons i j) val) lst))
		m
		n)
	 (if (and (equal i m)
		  (equal j n))
	     val
	     (aref2 name
		    (cons (list :HEADER
				:DIMENSIONS dims
				:MAXIMUM-LENGTH max-length
				:DEFAULT default
				:NAME name1)
			  lst)
		    m
		    n)))
  :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(defthm
  m-binary-+-row-remove-last
  (implies (and (>= i 0)
		(> n i))
	   (equal (m-binary-+-row
		   M1
		   (cons (cons (cons m n) val) M2)
		   m
		   i)
		  (m-binary-+-row M1
				  M2
				  m
				  i))))

(defthm
  associativity-of-m-binary-+-row
  (equal (m-binary-+-row (m-binary-+-row M1 M2 m n)
			 M3
			 m
			 n)
	 (m-binary-+-row M1
			 (m-binary-+-row M2 M3 m n)
			 m
			 n)))

(in-theory (disable commutativity-of-m-binary-+-row
		    commutativity-of-m-binary-+-row-1))

(in-theory (disable associativity-of-m-binary-+-row))

(defthm
  m-binary-+-row-append-1
  (equal (m-binary-+-row (append (m-binary-+-row M1
						 M2
						 m
						 n)
				 lst)
			 M3
			 m
			 n)
	 (m-binary-+-row (m-binary-+-row M1 M2 m n)
			 M3
			 m
			 n)))

(defthm
  m-binary-+-row-append-2
  (equal (m-binary-+-row M1
			 (append (m-binary-+-row M2
						 M3
						 m
						 n)
				 lst)
			 m
			 n)
	 (m-binary-+-row M1
			 (m-binary-+-row M2 M3 m n)
			 m
			 n)))

(defthm
  m-binary-+-row-cons-1
  (implies (> m i)
	   (equal (m-binary-+-row
		   (cons (cons (cons m n) val) lst)
		   M1
		   i
		   j)
		  (m-binary-+-row lst M1 i j))))

(defthm
  m-binary-+-row-cons-1-a
  (implies (and (>= j 0)
		(> n j))
	   (equal (m-binary-+-row
		   (cons (cons (cons m n) val) lst)
		   M1
		   i
		   j)
		  (m-binary-+-row lst M1 i j))))

(defthm
  m-binary-+-row-cons-1-a-header
  (implies (and (>= j 0)
		(> n j))
	   (equal (m-binary-+-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (cons (cons (cons m n) val) lst))
		   M3
		   i
		   j)
		  (m-binary-+-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   i
		   j))))

(defthm
  m-binary-+-row-cons-2
  (implies (> m i)
	   (equal (m-binary-+-row
		   M1
		   (cons (cons (cons m n) val) lst)
		   i
		   j)
		  (m-binary-+-row M1 lst i j))))

(defthm
  m-binary-+-row-cons-2-a-header
  (implies (and (>= j 0)
		(> n j))
	   (equal (m-binary-+-row
		   M1
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (cons (cons (cons m n) val) lst))
		   i
		   j)
		  (m-binary-+-row
		   M1
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   i
		   j))))

(defthm
  aref2-append-m-binary-+-row
  (implies (and (> m i))
	   (equal (aref2 name (append (m-binary-+-row M1 M2 m j)
				      lst)
			 i n)
		  (aref2 name lst i n))))

(defthm
  aref2-append-m-binary-+-row-header
  (implies (and (> m i))
	   (equal (aref2
		   name
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-+-row M1 M2 m j)
				 lst))
		   i
		   n)
		  (aref2
		   name
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   i
		   n))))

(defthm
  m-binary-+-row-append-3
  (implies (> m i)
	   (equal (m-binary-+-row (append (m-binary-+-row M1
							  M2
							  m
							  n)
					  lst)
				  M3
				  i
				  n)
		  (m-binary-+-row lst
				  M3
				  i
				  n))))

(defthm
  m-binary-+-row-append-3-header
  (implies (> m i)
	   (equal (m-binary-+-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-+-row M1
						 M2
						 m
						 n)
				 lst))
		   M3
		   i
		   n)
		  (m-binary-+-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   i
		   n))))

(defthm
  m-binary-+-row-append-4
  (implies (> m i)
	   (equal (m-binary-+-row M3
				  (append (m-binary-+-row M1
							  M2
							  m
							  n)
					  lst)
				  i
				  n)
		  (m-binary-+-row M3
				  lst
				  i
				  n))))

(defthm
  m-binary-+-row-append-4-header
  (implies (> m i)
	   (equal (m-binary-+-row
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-+-row M1
						 M2
						 m
						 n)
				 lst))
		   i
		   n)
		  (m-binary-+-row
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   i
		   n))))

(defthm
  m-binary-+-row-1-append-1
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-binary-+-row-1 (append (m-binary-+-row M1
							    M2
							    m
							    n)
					    lst)
				    M3
				    j
				    n)
		  (m-binary-+-row-1 lst
				    M3
				    j
				    n))))

(defthm
  m-binary-+-row-1-append-1-header
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-binary-+-row-1
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-+-row M1
						 M2
						 m
						 n)
				 lst))
		   M3
		   j
		   n)
		  (m-binary-+-row-1
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   j
		   n))))

(defthm
  m-binary-+-row-1-append-2
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-binary-+-row-1 M1
				    (append (m-binary-+-row M2
							    M3
							    m
							    n)
					    lst)
				    j
				    n)
		  (m-binary-+-row-1 M1
				    lst
				    j
				    n))))

(defthm
  m-binary-+-row-1-append-2-header
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-binary-+-row-1
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-+-row M1
						 M2
						 m
						 n)
				 lst))
		   j
		   n)
		  (m-binary-+-row-1
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   j
		   n))))

(in-theory (enable associativity-of-m-binary-+-row))

(defthm
  associativity-of-m-binary-+-row-1
  (equal (m-binary-+-row-1 (m-binary-+-row-1 M1 M2 m n) M3 m n)
	 (m-binary-+-row-1 M1 (m-binary-+-row-1 M2 M3 m n) m n)))

(defthm
  dimensions-header
  (equal (dimensions name
		     (cons (list :HEADER
				 :DIMENSIONS dims
				 :MAXIMUM-LENGTH max-length
				 :DEFAULT default
				 :NAME name1)
			   lst))
	 dims)
 :hints (("Goal"
	  :in-theory (enable header dimensions))))

(defthm
  default-header
  (equal (default name
	          (cons (list :HEADER
			      :DIMENSIONS dims
			      :MAXIMUM-LENGTH max-length
			      :DEFAULT default
			      :NAME name1)
			lst))
	 default)
 :hints (("Goal"
	  :in-theory (enable header default))))

(defthm
  alist2p-m-binary-+-header
  (implies (and (alist2p name1 M1)
		(alist2p name2 M2)
		(equal (first (dimensions '$arg M1))
		       (first (dimensions '$arg M2)))
		(equal (second (dimensions '$arg M1))
		       (second (dimensions '$arg M2))
		       ))
	   (alist2p name
		    (cons (list :HEADER
				:DIMENSIONS
				(list
				 (first
				  (DIMENSIONS '$ARG
					      M1))
				 (second
				  (dimensions '$arg
					      M1)))
				:MAXIMUM-LENGTH
				(+ 1
				   (* (CAR (DIMENSIONS '$ARG M1))
				      (CADR (DIMENSIONS '$ARG M1))))
				:DEFAULT 0
				:NAME 'MATRIX-SUM)
			  (m-binary-+-row-1 M1
					    M2
					    (+ -1
					       (car (dimensions
						     '$arg M1)))
					    (+ -1
					       (cadr (dimensions
						      '$arg M1)))
					    ))))
  :hints (("Goal"
	   :use alist2p-m-+)))

(defthm
  array2p-m-binary-+-header
  (implies (and (array2p name1 M1)
		(array2p name2 M2)
		(equal (dimensions '$arg M1)
		       (dimensions '$arg M2))
		(symbolp name))
	   (array2p name
		    (cons (list :HEADER
				:DIMENSIONS (DIMENSIONS '$ARG M1)
				:MAXIMUM-LENGTH
				(+ 1
				   (* (CAR (DIMENSIONS '$ARG M1))
				      (CADR (DIMENSIONS '$ARG M1))))
				:DEFAULT 0
				:NAME 'MATRIX-SUM)
			  (m-binary-+-row-1 M1
					    M2
					    (+ -1
					       (car (dimensions
						     '$arg M1)))
					    (+ -1
					       (cadr (dimensions
						      '$arg M1)))
					    ))))
  :hints (("Goal"
	   :use array2p-m-+)))

(defthm
  aref2-m-binary-+-row-1-remove-header-alist2p
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(integerp i)
		(integerp j)
		(<= 0 i)
		(<= 0 j)
		(< i (car (dimensions name M1)))
		(< j (cadr (dimensions name M1))))
 (equal (aref2 name
	       (cons (list :HEADER
			   :DIMENSIONS
			   (list (first
				  (DIMENSIONS '$ARG
					      M1))
				 (second
				  (dimensions '$arg
					      M1)))
			   :MAXIMUM-LENGTH max-length
			   :DEFAULT default
			   :NAME name1)
		     (m-binary-+-row-1 M1
				       M2
				       (+ -1
					  (car (dimensions
						'$arg M1)))
				       (+ -1
					  (cadr (dimensions
						 '$arg M1)))))
	       i j)
	(aref2 name (m-binary-+-row-1 M1
				      M2
				      (+ -1
					 (car (dimensions
					       name M1)))
				      (+ -1
					 (cadr (dimensions
						name M1))))
	       i
	       j)))
   :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(defthm
  aref2-m-binary-+-row-1-remove-header-array2p
  (implies (and (array2p name M1)
		(array2p name M2)
		(integerp i)
		(integerp j)
		(<= 0 i)
		(<= 0 j)
		(< i (car (dimensions name M1)))
		(< j (cadr (dimensions name M1))))
 (equal (aref2 name
	       (cons (list :HEADER
			   :DIMENSIONS (DIMENSIONS '$ARG M1)
			   :MAXIMUM-LENGTH max-length
			   :DEFAULT default
			   :NAME name1)
		     (m-binary-+-row-1 M1
				       M2
				       (+ -1
					  (car (dimensions
						'$arg M1)))
				       (+ -1
					  (cadr (dimensions
						 '$arg M1)))))
	       i j)
	(aref2 name (m-binary-+-row-1 M1
				      M2
				      (+ -1
					 (car (dimensions
					       name M1)))
				      (+ -1
					 (cadr (dimensions
						name M1))))
	       i
	       j)))
   :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(defthm
  m-binary-+-row-append-1-remove-header
  (equal (m-binary-+-row (cons (list :HEADER
				     :DIMENSIONS dims
				     :MAXIMUM-LENGTH max-length
				     :DEFAULT default
				     :NAME name1)
			       (append (m-binary-+-row M1 M2 m n)
				       lst))
			 M3
			 m
			 n)
	 (m-binary-+-row (m-binary-+-row M1 M2 m n)
			 M3
			 m
			 n))
  :hints (("Goal"
	   :in-theory
	   (disable
	    ASSOCIATIVITY-OF-M-BINARY-+-ROW))))

(defthm
  m-binary-+-row-append-2-remove-header
  (equal (m-binary-+-row M3
			 (cons (list :HEADER
				     :DIMENSIONS dims
				     :MAXIMUM-LENGTH max-length
				     :DEFAULT default
				     :NAME name1)
			       (append (m-binary-+-row M1 M2 m n)
				       lst))
			 m
			 n)
	 (m-binary-+-row M3
			 (m-binary-+-row M1 M2 m n)
			 m
			 n))
  :hints (("Goal"
	   :in-theory (disable ASSOCIATIVITY-OF-M-BINARY-+-ROW))))

(defthm
  m-binary-+-row-remove-header-1
  (equal (m-binary-+-row (cons (list :HEADER
				     :DIMENSIONS dims
				     :MAXIMUM-LENGTH max-length
				     :DEFAULT default
				     :NAME name1)
			       (m-binary-+-row M1 M2 m n))
			 M3
			 m
			 n)
	 (m-binary-+-row (m-binary-+-row M1 M2 m n)
			 M3
			 m
			 n))
  :hints (("Goal"
	   :in-theory (disable ASSOCIATIVITY-OF-M-BINARY-+-ROW))))

(defthm
  m-binary-+-row-remove-header-2
  (equal (m-binary-+-row M3
			 (cons (list :HEADER
				     :DIMENSIONS dims
				     :MAXIMUM-LENGTH max-length
				     :DEFAULT default
				     :NAME name1)
			       (m-binary-+-row M1 M2 m n))
			 m
			 n)
	 (m-binary-+-row M3
			 (m-binary-+-row M1 M2 m n)
			 m
			 n))
  :hints (("Goal"
	   :in-theory (disable ASSOCIATIVITY-OF-M-BINARY-+-ROW))))

(defthm
  m-binary-+-row-1-remove-header-1
  (equal (m-binary-+-row-1
	  (cons (list :HEADER
		      :DIMENSIONS dims
		      :MAXIMUM-LENGTH max-length
		      :DEFAULT default
		      :NAME name1)
		(m-binary-+-row-1 M1
				  M2
				  m
				  n))
	  M3
	  m
	  n)
	 (m-binary-+-row-1
	  (m-binary-+-row-1 M1
			    M2
			    m
			    n)
	  M3
	  m
	  n))
  :hints (("Goal"
	   :in-theory (disable associativity-of-m-binary-+-row
			       associativity-of-m-binary-+-row-1))))

(defthm
  m-binary-+-row-1-remove-header-2
  (equal (m-binary-+-row-1
	  M3
	  (cons (list :HEADER
		      :DIMENSIONS dims
		      :MAXIMUM-LENGTH max-length
		      :DEFAULT default
		      :NAME name1)
		(m-binary-+-row-1 M1
				  M2
				  m
				  n))
	  m
	  n)
	 (m-binary-+-row-1
	  M3
	  (m-binary-+-row-1 M1
			    M2
			    m
			    n)
	  m
	  n))
  :hints (("Goal"
	   :in-theory (disable associativity-of-m-binary-+-row
			       associativity-of-m-binary-+-row-1))))

(defthm
  alist2p-m-binary-+-header-hack
  (IMPLIES (AND (ALIST2P '$ARG1 M2)
		(ALIST2P '$ARG2 M3)
		(EQUAL (CAR (DIMENSIONS '$ARG M1))
		       (CAR (DIMENSIONS '$ARG M2)))
		(EQUAL (CADR (DIMENSIONS '$ARG M1))
		       (CADR (DIMENSIONS '$ARG M2)))
		(EQUAL (CAR (DIMENSIONS '$ARG M1))
		       (CAR (DIMENSIONS '$ARG M3)))
		(EQUAL (CADR (DIMENSIONS '$ARG M1))
		       (CADR (DIMENSIONS '$ARG M3))))
	   (ALIST2P '$ARG2
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M1)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M1))))
				 '(:DEFAULT 0 :NAME MATRIX-SUM))
			  (M-BINARY-+-ROW-1 M2 M3 (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M1)))))))
  :hints (("Goal"
	   :in-theory (disable alist2p-m-binary-+-header)
	   :use (:instance
		 alist2p-m-binary-+-header
		 (M1 M2)
		 (M2 M3)))))

(defthm
  m-binary-+-row-1-remove-compress2-2-hack
  (IMPLIES
   (AND (ALIST2P '$ARG1 M2)
	(ALIST2P '$ARG2 M3)
	(EQUAL (CAR (DIMENSIONS '$ARG M1))
	       (CAR (DIMENSIONS '$ARG M2)))
	(EQUAL (CADR (DIMENSIONS '$ARG M1))
	       (CADR (DIMENSIONS '$ARG M2)))
	(EQUAL (CAR (DIMENSIONS '$ARG M1))
	       (CAR (DIMENSIONS '$ARG M3)))
	(EQUAL (CADR (DIMENSIONS '$ARG M1))
	       (CADR (DIMENSIONS '$ARG M3))))
   (EQUAL
    (M-BINARY-+-ROW-1
     M1
     (M-BINARY-+-ROW-1 M2 M3 (+ -1 (CAR (DIMENSIONS '$ARG M1)))
		       (+ -1 (CADR (DIMENSIONS '$ARG M1))))
     (+ -1 (CAR (DIMENSIONS '$ARG M1)))
     (+ -1 (CADR (DIMENSIONS '$ARG M1))))
    (M-BINARY-+-ROW-1
     M1
     (COMPRESS2
      '$ARG
      (CONS (LIST* :HEADER :DIMENSIONS
		   (LIST (CAR (DIMENSIONS '$ARG M1))
			 (CADR (DIMENSIONS '$ARG M1)))
		   :MAXIMUM-LENGTH
		   (+ 1
		      (* (CAR (DIMENSIONS '$ARG M1))
			 (CADR (DIMENSIONS '$ARG M1))))
		   '(:DEFAULT 0 :NAME MATRIX-SUM))
	    (M-BINARY-+-ROW-1 M2 M3 (+ -1 (CAR (DIMENSIONS '$ARG M1)))
			      (+ -1 (CADR (DIMENSIONS '$ARG M1))))))
     (+ -1 (CAR (DIMENSIONS '$ARG M1)))
     (+ -1 (CADR (DIMENSIONS '$ARG M1))))))
  :hints (("Goal"
	   :in-theory (disable m-binary-+-row-1-remove-compress2-2
			       alist2p-m-binary-+-header-hack)
	   :use ((:instance
		  m-binary-+-row-1-remove-compress2-2
		  (l1 M1)
		  (name '$arg)
		  (l2 (CONS (LIST* :HEADER :DIMENSIONS
				   (LIST (CAR (DIMENSIONS '$ARG M1))
					 (CADR (DIMENSIONS '$ARG M1)))
				   :MAXIMUM-LENGTH
				   (+ 1
				      (* (CAR (DIMENSIONS '$ARG M1))
					 (CADR (DIMENSIONS '$ARG M1))))
				   '(:DEFAULT 0 :NAME MATRIX-SUM))
			    (M-BINARY-+-ROW-1 M2 M3 (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					      (+ -1 (CADR (DIMENSIONS '$ARG M1))))))
		  (i (+ -1 (CAR (DIMENSIONS '$ARG M1))))
		  (j (+ -1 (CADR (DIMENSIONS '$ARG M1)))))
		 alist2p-m-binary-+-header-hack))))

(defthm
  associativity-of-m-+
  (equal (m-+ (m-+ M1 M2) M3)
	 (m-+ M1 M2 M3))
 :hints (("Goal"
	  :in-theory (disable commutativity-of-m-+))))

(defthm
  m-=-row-cons-1-a
  (implies (and (>= j 0)
		(> n j))
	   (equal (m-=-row (cons (cons (cons m n) val) lst)
			   M1
			   i
			   j)
		  (m-=-row lst M1 i j))))

(defthm
  m-=-row-cons-2-a
  (implies (and (>= j 0)
		(> n j))
	   (equal (m-=-row M1
			   (cons (cons (cons m n) val) lst)
			   i
			   j)
		  (m-=-row M1 lst i j))))

(defthm
  m-=-row-cons-1-a-header
  (implies (and (>= j 0)
		(> n j))
	   (equal (m-=-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (cons (cons (cons m n) val) lst))
		   M3
		   i
		   j)
		  (m-=-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   i
		   j))))

(defthm
  m-=-row-cons-2-a-header
  (implies (and (>= j 0)
		(> n j))
	   (equal (m-=-row
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (cons (cons (cons m n) val) lst))
		   i
		   j)
		  (m-=-row
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   i
		   j))))

(defthm
  m-=-row-m-binary-+-row-append-1
  (equal (m-=-row (append (m-binary-+-row M1 M2 m n)
			  lst)
		  M3
		  m
		  n)
	 (m-=-row (m-binary-+-row M1 M2 m n)
		  M3
		  m
		  n)))

(defthm
  m-=-row-m-binary-+-row-append-2
  (equal (m-=-row M3
		  (append (m-binary-+-row M1 M2 m n)
			  lst)
		  m
		  n)
	 (m-=-row M3
		  (m-binary-+-row M1 M2 m n)
		  m
		  n)))

(defthm
  m-=-row-m-binary-+-row-append-1-remove-header
  (equal (m-=-row (cons (list :HEADER
			      :DIMENSIONS dims
			      :MAXIMUM-LENGTH max-length
			      :DEFAULT default
			      :NAME name1)
			(append (m-binary-+-row M1 M2 m n)
				lst))
		  M3
		  m
		  n)
	 (m-=-row (m-binary-+-row M1 M2 m n)
		  M3
		  m
		  n)))

(defthm
  m-=-row-m-binary-+-row-append-2-remove-header
  (equal (m-=-row M3
		  (cons (list :HEADER
			      :DIMENSIONS dims
			      :MAXIMUM-LENGTH max-length
			      :DEFAULT default
			      :NAME name1)
			(append (m-binary-+-row M1 M2 m n)
				lst))
		  m
		  n)
	 (m-=-row M3
		  (m-binary-+-row M1 M2 m n)
		  m
		  n)))

(defthm
  m-=-row-m-binary-+-row-remove-header-1
  (equal (m-=-row (cons (list :HEADER
			      :DIMENSIONS dims
			      :MAXIMUM-LENGTH max-length
			      :DEFAULT default
			      :NAME name1)
			(m-binary-+-row M1 M2 m n))
		  M3
		  m
		  n)
	 (m-=-row (m-binary-+-row M1 M2 m n)
		  M3
		  m
		  n)))

(defthm
  m-=-row-m-binary-+-row-remove-header-2
  (equal (m-=-row M3
		  (cons (list :HEADER
			      :DIMENSIONS dims
			      :MAXIMUM-LENGTH max-length
			      :DEFAULT default
			      :NAME name1)
			(m-binary-+-row M1 M2 m n))
		  m
		  n)
	 (m-=-row m3
		  (m-binary-+-row M1 M2 m n)
		  m
		  n)))

(defthm
  m-=-row-m-binary-+-row-append-3
  (implies (> m i)
	   (equal (m-=-row (append (m-binary-+-row M1
						   M2
						   m
						   n)
				   lst)
			   M3
			   i
			   n)
		  (m-=-row lst
			   M3
			   i
			   n))))

(defthm
  m-=-row-m-binary-+-row-append-4
  (implies (> m i)
	   (equal (m-=-row M3
			   (append (m-binary-+-row M1
						   M2
						   m
						   n)
				   lst)
			   i
			   n)
		  (m-=-row M3
			   lst
			   i
			   n))))

(defthm
  m-=-row-m-binary-+-row-append-3-header
  (implies (> m i)
	   (equal (m-=-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-+-row M1
						 M2
						 m
						 n)
				 lst))
		   M3
		   i
		   n)
		  (m-=-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   i
		   n))))

(defthm
  m-=-row-m-binary-+-row-append-4-header
  (implies (> m i)
	   (equal (m-=-row
		   m3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-+-row M1
						 M2
						 m
						 n)
				 lst))
		   i
		   n)
		  (m-=-row
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   i
		   n))))

(defthm
  m-=-row-1-m-binary-+-row-append-1
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-=-row-1 (append (m-binary-+-row M1
						     M2
						     m
						     n)
				     lst)
			     M3
			     j
			     n)
		  (m-=-row-1 lst
			     M3
			     j
			     n))))

(defthm
  m-=-row-1-m-binary-+-row-append-2
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-=-row-1 M3
			     (append (m-binary-+-row M1
						     M2
						     m
						     n)
				     lst)
			     j
			     n)
		  (m-=-row-1 M3
			     lst
			     j
			     n))))

(defthm
  m-=-row-1-m-binary-+-row-append-1-header
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-=-row-1
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-+-row M1
						 M2
						 m
						 n)
				 lst))
		   M3
		   j
		   n)
		  (m-=-row-1
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   j
		   n))))

(defthm
  m-=-row-1-m-binary-+-row-append-2-header
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-=-row-1
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-+-row M1
						 M2
						 m
						 n)
				 lst))
		   j
		   n)
		  (m-=-row-1
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   j
		   n))))

(defthm
 m-=-row-1-m-binary-+-row-1-remove-header-1
 (equal (m-=-row-1 (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (m-binary-+-row-1 M1
					   M2
					   m
					   n))
		   M3
		   m
		   n)
	(m-=-row-1 (m-binary-+-row-1 M1 M2 m n)
		   M3
		   m
		   n)))

(defthm
 m-=-row-1-m-binary-+-row-1-remove-header-2
 (equal (m-=-row-1 M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (m-binary-+-row-1 M1
					   M2
					   m
					   n))
		   m
		   n)
	(m-=-row-1 M3
		   (m-binary-+-row-1 M1 M2 m n)
		   m
		   n)))

(defthm
  m-=-row-1-m-binary-+-row-1-m-0
  (m-=-row-1 (m-binary-+-row-1 M1
			       (m-0 m n)
			       i
			       j)
	     M1
	     i
	     j))

(defthm
  alist2p-m-0-hack
  (IMPLIES (ALIST2P NAME M)
	   (ALIST2P '$ARG1
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M))
				       (CADR (DIMENSIONS '$ARG M)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M))
				       (CADR (DIMENSIONS '$ARG M))))
				 '(:DEFAULT 0 :NAME MATRIX-SUM))
			  (M-BINARY-+-ROW-1 M
					    (M-0 (CAR (DIMENSIONS '$ARG M))
						 (CADR (DIMENSIONS '$ARG M)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M)))))))
  :hints (("Goal"
	   :in-theory (disable alist2p-m-+)
	   :use (:instance
		 alist2p-m-+
		 (M1 M)
		 (M2 (M-0 (CAR (DIMENSIONS '$ARG M))
			  (CADR (DIMENSIONS '$ARG M))))
		 (name '$arg)))))

(defthm
  ALIST2P-M-BINARY-+-HEADER-m-0-hack
  (implies (alist2p '$arg M)
	   (ALIST2P '$ARG
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M))
				       (CADR (DIMENSIONS '$ARG M)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M))
				       (CADR (DIMENSIONS '$ARG M))))
				 '(:DEFAULT 0 :NAME MATRIX-SUM))
			  (M-BINARY-+-ROW-1 M
					    (M-0 (CAR (DIMENSIONS '$ARG M))
						 (CADR (DIMENSIONS '$ARG M)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M)))))))
  :hints (("Goal"
	   :in-theory (disable ALIST2P-M-BINARY-+-HEADER)
	   :use (:instance
		 ALIST2P-M-BINARY-+-HEADER
		 (name1 '$arg)
		 (name2 '$arg)
		 (M1 M)
		 (M2 (M-0 (CAR (DIMENSIONS '$ARG M))
			  (CADR (DIMENSIONS '$ARG M))))))))

(defthm
  M-=-ROW-1-REMOVE-COMPRESS2-1-m-0-hack
 (IMPLIES (ALIST2P NAME M)
	  (M-=-ROW-1
	   (COMPRESS2 '$ARG
		      (CONS (LIST* :HEADER :DIMENSIONS
				   (LIST (CAR (DIMENSIONS '$ARG M))
					 (CADR (DIMENSIONS '$ARG M)))
				   :MAXIMUM-LENGTH
				   (+ 1
				      (* (CAR (DIMENSIONS '$ARG M))
					 (CADR (DIMENSIONS '$ARG M))))
				   '(:DEFAULT 0 :NAME MATRIX-SUM))
			    (M-BINARY-+-ROW-1 M
					      (M-0 (CAR (DIMENSIONS '$ARG M))
						   (CADR (DIMENSIONS '$ARG M)))
					      (+ -1 (CAR (DIMENSIONS '$ARG M)))
					      (+ -1 (CADR (DIMENSIONS '$ARG M))))))
	   M
	   (+ -1 (CAR (DIMENSIONS '$ARG M)))
	   (+ -1 (CADR (DIMENSIONS '$ARG M))))))

(defthm
  right-m-+-unicity-of-m-0
  (implies (alist2p name M)
	   (m-= (m-+ M (m-0 (car (dimensions name M))
			    (cadr (dimensions name M))))
		M)))

(defthm
  left-m-+-unicity-of-m-0
  (implies (alist2p name M)
	   (m-= (m-+ (m-0 (car (dimensions name M))
			  (cadr (dimensions name M)))
		     M)
		M)))

(defmacro
  m-- (x &optional (y 'nil binary-casep))
  (if binary-casep
      `(m-binary-+ ,x (m-unary-- ,y))
      `(m-unary-- ,x)))

(add-macro-alias m-- m-unary--)

(add-invisible-fns m-binary-+ m-unary--)
(add-invisible-fns m-unary-- m-unary--)

(defthm
  m-=-row-1-m-binary-+-row-1-m-unary--
  (m-=-row-1 (m-binary-+-row-1 M1
			       (m-unary-- M1)
			       i
			       j)
	     (m-0 m n)
	     i
	     j))

(defthm
  left-m-+-inverse-of-m--
  (implies (alist2p name M)
	   (m-= (m-+ (m-- M) M)
		(m-0 (car (dimensions name M))
		     (cadr (dimensions name M))))))

(defthm
  right-m-+-inverse-of-m--
  (implies (alist2p name M)
	   (m-= (m-+ M (m-- M))
		(m-0 (car (dimensions name M))
		     (cadr (dimensions name M))))))

(defthm
  m-=-row-distributivity-of-s-*-over-+
  (implies (and (alist2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (r M))
		(< j (c M)))
	   (m-=-row (s-* (+ a b) M)
		    (m-+ (s-* a M)(s-* b m))
		    i
		    j))
  :hints (("Goal"
	   :in-theory (disable m-binary-+))))

(defthm
  m-=-row-1-distributivity-of-s-*-over-+
  (implies (and (alist2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (r M))
		(< j (c M)))
	   (m-=-row-1 (s-* (+ a b) M)
		      (m-+ (s-* a M)(s-* b m))
		      i
		      j))
  :hints (("Goal"
	   :in-theory (disable m-binary-+))))

(defthm
  distributivity-of-s-*-over-+
  (implies (alist2p name M)
	   (m-= (s-* (+ a b) M)
		(m-+ (s-* a M)(s-* b m))))
  :hints (("Goal"
	   :in-theory (disable m-binary-+
			       alist2p-m-+)
	   :use ((:instance
		  alist2p-m-+
		  (M1 (s-* a M))
		  (M2 (s-* b M)))))))

(defthm
  m-=-row-distributivity-of-s-*-over-m-+
  (implies (and (equal (car (dimensions name M1))
		       (car (dimensions name M2)))
		(equal (cadr (dimensions name M1))
		       (cadr (dimensions name M2)))
		(alist2p name M1)
		(alist2p name M2)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (r M1))
		(< j (c M1)))
	   (m-=-row (s-* a (m-+ M1 M2))
		    (m-+ (s-* a M1)(s-* a M2))
		    i
		    j))
  :hints (("Goal"
	   :in-theory (disable m-binary-+))))

(defthm
   m-=-row-1-distributivity-of-s-*-over-m-+
   (implies (and (equal (car (dimensions name M1))
			(car (dimensions name M2)))
		 (equal (cadr (dimensions name M1))
			(cadr (dimensions name M2)))
		 (alist2p name M1)
		 (alist2p name M2)
		 (integerp i)
		 (integerp j)
		 (>= i 0)
		 (>= j 0)
		 (< i (r M1))
		 (< j (c M1)))
	    (m-=-row-1 (s-* a (m-+ M1 M2))
		       (m-+ (s-* a M1)(s-* a M2))
		       i
		       j))
   :hints (("Goal"
	    :in-theory (disable m-binary-+))))

(defthm
  distributivity-of-s-*-over-m-+
  (implies (and (equal (car (dimensions name M1))
		       (car (dimensions name M2)))
		(equal (cadr (dimensions name M1))
		       (cadr (dimensions name M2)))
		(alist2p name M1)
		(alist2p name M2))
	   (m-= (s-* a (m-+ M1 M2))
		(m-+ (s-* a M1)(s-* a M2))))
  :hints (("Goal"
	   :in-theory (disable m-binary-+
			       alist2p-s-*)
	   :use ((:instance
		  alist2p-s-*
		  (M (m-binary-+ M1 M2)))
		 (:instance
		  alist2p-s-*
		  (M M1))
		 (:instance
		  alist2p-s-*
		  (M M2))
		 (:instance
		  alist2p-m-+
		  (M1 (s-* a M1))
		  (M2 (s-* a M2)))))))

(defthm
  m-=-row-m-trans-m-+
  (implies (and (equal (car (dimensions name M1))
		       (car (dimensions name M2)))
		(equal (cadr (dimensions name M1))
		       (cadr (dimensions name M2)))
		(alist2p name M1)
		(alist2p name M2)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (c M1))
		(< j (r M1)))
	   (m-=-row (m-trans (m-+ M1 M2))
		    (m-+ (m-trans M1)(m-trans M2))
		    i
		    j))
  :hints (("Goal"
	   :in-theory (disable m-binary-+))))

(defthm
   m-=-row-1-m-trans-m-+
   (implies (and (equal (car (dimensions name M1))
			(car (dimensions name M2)))
		 (equal (cadr (dimensions name M1))
			(cadr (dimensions name M2)))
		 (alist2p name M1)
		 (alist2p name M2)
		 (integerp i)
		 (integerp j)
		 (>= i 0)
		 (>= j 0)
		 (< i (c M1))
		 (< j (r M1)))
	    (m-=-row-1 (m-trans (m-+ M1 M2))
		       (m-+ (m-trans M1)(m-trans M2))
		       i
		       j))
   :hints (("Goal"
	    :in-theory (disable m-binary-+))))

(defthm
  m-trans-m-+
  (implies (and (equal (car (dimensions name M1))
		       (car (dimensions name M2)))
		(equal (cadr (dimensions name M1))
		       (cadr (dimensions name M2)))
		(alist2p name M1)
		(alist2p name M2))
	   (m-= (m-trans (m-+ M1 M2))
		(m-+ (m-trans M1)(m-trans M2))))
  :hints (("Goal"
	   :in-theory (disable m-binary-+))
	  ("Subgoal 2"
	   :in-theory (disable m-binary-+
			       alist2p-m-trans)
	   :use (:instance
		 alist2p-m-trans
		 (name '$arg)
		 (M (m-+ M1 M2))))
	  ("Subgoal 1"
	   :in-theory (disable m-binary-+
			       alist2p-m-+)
	   :use (:instance
		 alist2p-m-+
		 (name '$arg)
		 (M1 (m-trans M1))
		 (M2 (m-trans M2))))))

;;;;;;;;;;;;;;;;;;
;; Matrix product:

(defun
  dot (M1 M2 i j k)
  "Return the dot product
   (M1 i 0)*(M2 0 k) + . . . + (M1 i j)*(M2 j k)."
  (declare (xargs :guard (and (integerp i)
			      (>= i 0)
			      (integerp j)
			      (>= j 0)
			      (integerp k)
			      (>= k 0)
			      (array2p '$arg1 M1)
			      (array2p '$arg2 M2)
			      (let ((dims1 (dimensions '$arg1 M1)))
				   (and (< i (first dims1))
					(< j (second dims1))))
			      (let ((dims2 (dimensions '$arg1 M2)))
				   (and (< j (first dims2))
					(< k (second dims2)))))))
  (if (zp j)
      (* (fix (aref2 '$arg1 M1 i 0))
	 (fix (aref2 '$arg2 M2 0 k)))
      (+ (* (fix (aref2 '$arg1 M1 i j))
	    (fix (aref2 '$arg2 M2 j k)))
	 (dot M1 M2 i (- j 1) k))))

(defthm
  dot-remove-compress2-1
  (implies (and (alist2p name l1)
		(integerp i)
		(>= i 0)
		(< i (car (dimensions name l1)))
		(< j (cadr (dimensions name l1))))
	   (equal (dot (compress2 name l1) l2 i j k)
		  (dot l1 l2 i j k))))

(defthm
  dot-remove-compress2-2
  (implies (and (alist2p name l2)
		(integerp k)
		(>= k 0)
		(< j (car (dimensions name l2)))
		(< k (cadr (dimensions name l2))))
	   (equal (dot l1 (compress2 name l2) i j k)
		  (dot l1 l2 i j k))))

(defthm
  m-=-row-1-implies-equal-dot-2
  (implies (and (m-=-row-1 M2 M3 n p)
		(integerp p)
		(integerp j)
		(>= j 0)
		(>= p j))
	   (equal (dot M1 M2 m n j)
		  (dot M1 M3 m n j)))
  :hints (("Goal"
	   :do-not '(generalize)
	   :in-theory (disable LEFT-CANCELLATION-FOR-*))))

(defun
  m-binary-*-row (M1 M2 m j n)
  "Return an alist with the following values:
   (dot M1 M2 m j 0), . . . , (dot M1 M2 m j n);
   ie. construct an alist of values representing
   the vector of dot products of the m'th row of M1
   with columns 0 thru n of M2."
  (declare (xargs :guard (and (integerp m)
			      (>= m 0)
			      (integerp j)
			      (>= j 0)
			      (integerp n)
			      (>= n 0)
			      (array2p '$arg1 M1)
			      (array2p '$arg2 M2)
			      (let ((dims1 (dimensions '$arg1 M1)))
				   (and (< m (first dims1))
					(< j (second dims1))))
			      (let ((dims2 (dimensions '$arg1 M2)))
				   (and (< j (first dims2))
					(< n (second dims2)))))))
  (if (zp n)
      (list (cons (cons m 0)
		  (dot M1 M2 m j 0)))
      (cons (cons (cons m n)
		  (dot M1 M2 m j n))
	    (m-binary-*-row M1 M2 m j (- n 1)))))

(defthm
  m-binary-*-row-remove-compress2-1
  (implies (and (alist2p name l1)
		(integerp i)
		(>= i 0)
		(< i (car (dimensions name l1)))
		(< j (cadr (dimensions name l1))))
	   (equal (m-binary-*-row (compress2 name l1) l2 i j k)
		  (m-binary-*-row l1 l2 i j k))))

(defthm
  m-binary-*-row-remove-compress2-2
  (implies (and (alist2p name l2)
		(integerp k)
		(>= k 0)
		(< j (car (dimensions name l2)))
		(< k (cadr (dimensions name l2))))
	   (equal (m-binary-*-row l1 (compress2 name l2) i j k)
		  (m-binary-*-row l1 l2 i j k))))

(defthm
  m-=-row-implies-equal-m-binary-*-row-1
  (implies (m-=-row M1 M2 m n)
	   (equal (m-binary-*-row M1 M3 m n p)
		  (m-binary-*-row M2 M3 m n p))))

(defthm
  m-=row-1-implies-equal-m-binary-*-row-2
  (implies (and (m-=-row-1 M2 M3 n p)
		(integerp p)
		(>= p 0))
	   (equal (m-binary-*-row M1 M2 m n p)
		  (m-binary-*-row M1 M3 m n p))))

(defthm
  assoc2-m-binary-*-row
  (implies (and (integerp p)
		(integerp j)
		(>= j 0)
		(<= j p))
	   (assoc2 m j (m-binary-*-row M1 M2 m n p))))

(defthm
  assoc2=nil-m-binary-*-row
  (implies (not (equal i m))
	   (equal (assoc2 i j (m-binary-*-row M1 M2 m n p))
		  nil)))

(defthm
  cdr-assoc2-m-binary-*-row
  (implies (and (integerp p)
		(integerp j)
		(>= j 0)
		(<= j p))
	   (equal (cdr (assoc2 m j (m-binary-*-row M1 M2 m n p)))
		  (dot M1 M2 m n j))))

(defun
  m-binary-*-row-1 (M1 M2 m j n)
  "Return an alist with all the following values:
   (dot M1 M2 0 j 0), . . . , (dot M1 M2 0 j n)
          .           .              .
          .             .            .
          .               .          .
   (dot M1 M2 m j 0), . . . , (dot M1 M2 m j n)."
  (declare (xargs :guard (and (integerp m)
			      (>= m 0)
			      (integerp j)
			      (>= j 0)
			      (integerp n)
			      (>= n 0)
			      (array2p '$arg1 M1)
			      (array2p '$arg2 M2)
			      (let ((dims1 (dimensions '$arg1 M1)))
				   (and (< m (first dims1))
					(< j (second dims1))))
			      (let ((dims2 (dimensions '$arg1 M2)))
				   (and (< j (first dims2))
					(< n (second dims2)))))))
  (if (zp m)
      (m-binary-*-row M1 M2 0 j n)
      (append (m-binary-*-row M1 M2 m j n)
	      (m-binary-*-row-1 M1 M2 (- m 1) j n))))

(defthm
  alistp-m-binary-*-row-1
  (alistp (m-binary-*-row-1 M1 M2 m n p)))

(defthm
  bounded-integerp-alistp2-m-binary-*-row-1
  (implies (and (integerp m)
		(integerp n)
		(>= i 0)
		(>= k 0)
		(< i m)
		(< k n))
	   (bounded-integer-alistp2 (m-binary-*-row-1 M1 M2 i j k)
				    m
				    n)))

(defthm
  m-binary-*-row-1-remove-compress2-1
  (implies (and (alist2p name l1)
		(integerp i)
		(>= i 0)
		(< i (car (dimensions name l1)))
		(< j (cadr (dimensions name l1))))
	   (equal (m-binary-*-row-1 (compress2 name l1) l2 i j k)
		  (m-binary-*-row-1 l1 l2 i j k))))

(defthm
  m-binary-*-row-1-remove-compress2-2
  (implies (and (alist2p name l2)
		(integerp k)
		(>= k 0)
		(< j (car (dimensions name l2)))
		(< k (cadr (dimensions name l2))))
	   (equal (m-binary-*-row-1 l1 (compress2 name l2) i j k)
		  (m-binary-*-row-1 l1 l2 i j k))))

(defthm
  m-=-row-1-implies-equal-m-binary-*-row-1-1
  (implies (m-=-row-1 M1 M2 m n)
	   (equal (m-binary-*-row-1 M1 M3 m n p)
		  (m-binary-*-row-1 M2 M3 m n p))))

(defthm
  m-=-row-1-implies-equal-m-binary-*-row-1-2
  (implies (and (m-=-row-1 M2 M3 n p)
		(integerp p)
		(>= p 0))
	   (equal (m-binary-*-row-1 M1 M2 m n p)
		  (m-binary-*-row-1 M1 M3 m n p))))

(defthm
  assoc2-m-binary-*-row-1
  (implies (and (integerp m)
		(integerp p)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(<= i m)
		(<= j p))
	   (assoc2 i j (m-binary-*-row-1 M1 M2 m n p))))

(defthm
  assoc2=nil-m-binary-*-row-1
  (implies (and (>= m 0)
		(> i m))
	   (equal (assoc2 i j (m-binary-*-row-1 M1 M2 m n p))
		  nil)))

(local (in-theory (enable assoc2-append)))

(local
 (defthm
   cdr-assoc2-m-binary-*-row-1-lemma
   (implies (and (equal (cdr (assoc2 i
				     j
				     (m-binary-*-row-1 M1
						       M2
						       (+ -1 m)
						       n
						       p)))
			(dot M1 M2 i n j))
		 (integerp j)
		 (<= 0 j)
		 (<= j p))
	    (equal (cdr (assoc2 i
				j
				(append (m-binary-*-row M1
							M2
							m
							n
							p)
					(m-binary-*-row-1 M1
							  M2
							  (+ -1 m)
							  n
							  p))))
		   (dot M1 M2 i n j)))))

(local (in-theory (disable assoc2-append)))

(defthm
  cdr-assoc2-m-binary-*-row-1
  (implies (and (integerp m)
		(integerp i)
		(integerp j)
		(integerp p)
		(>= i 0)
		(>= j 0)
		(<= i m)
		(<= j p))
	   (equal (cdr (assoc2 i j (m-binary-*-row-1 M1 M2 m n p)))
		  (dot M1 M2 i n j))))

(local (in-theory (disable cdr-assoc2-m-binary-*-row-1-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Ensuring closure of matrix multiplication.

; Let dim1 be the number of rows and dim2 be the number of columns
; in an ACL2 two dimensional array.  The product, dim1*dim2, is
; required to fit into 32 bits so that some compilers can lay down
; faster code. Thus, dim1*dim2 <= maximum-positive-32-bit-integer
;                               = 2^31 - 1
;                               = 2,147,483,647.

; This restriction on the size of dim1*dim2 means that matrices
; representable by ACL2 arrays are NOT closed under matrix
; multiplication, even when the product is mathematically defined.
; To illustrate, suppose dim1*dim2 is required to be no larger than
; 20; M1 is a matrix with 5 rows and 2 columns; and M2 is a matrix
; with 2 rows and 5 columns.  Then M1 and M2 would both be
; representable and their product, M1 * M2, would be mathematically
; defined, but not representable (since 25 > 20).

; Furthermore, when there are more than two matrices involved in a
; matrix multiplication, the final product may be both mathematically
; defined and representable by an ACL2 array, but yet not
; computable in ACL2. Let's illustrate by extending the example given
; above with M1 and M2. Suppose M0 is a matrix with 2 rows and 5
; colums. Then the product (M0 * M1) * M2 is mathematically defined,
; representable in ACL2, and computable in ACL2 (since both partial
; products (M0 * M1) and (M0 * M1) * M2 are representable in ACL2).
; But the product M0 * (M1 * M2) is mathematically defined,
; representable in ACL2, but NOT computable in ACL2 (since the
; partial product (M1 * M2) is NOT representable in ACL2).

; One way to prevent this last problem and also ensure closure for
; matrix multiplication is to require that each of dim1 and dim2
; be less than or equal to 46,340 which is the integer square root
; of 2,147,483,647, the maximum-positive-32-bit-integer. Then
; the product of dim1*dim2 is guarenteed to be less than the
; the maximum-positive-32-bit-integer. Futhermore, with this stronger
; restriction, if the product M1 * . . . * Mn is both mathematically
; defined and representable in ACL2, then, for any way of
; parenthesizing this product, all the partial products are also
; mathematically defined and representable in ACL2.

; Thus, for matrix multiplication, it is required that both the
; number of rows and the number of columns be less than or equal
; to 46,340.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun m-binary-* (M1 M2)
  "Return an alist representing the matrix product
   of the matrices represented by the alists M1
   and M2. This is done by adding a header to an
   alist containing the appropriate values."
  (declare (xargs :guard (and (array2p '$arg1 M1)
			      (array2p '$arg2 M2)
			      (= (second (dimensions '$arg1 M1))
				 (first (dimensions '$arg2 M2))))))
  (let* ((dim1 (dimensions '$arg1 M1))
	 (dim2 (dimensions '$arg2 M2))
	 (dim11 (first dim1))
	 (dim12 (second dim1))
	 (dim21 (first dim2))
	 (dim22 (second dim2)))
    (if (mbt (and (alist2p '$arg1 M1)
		  (alist2p '$arg2 M2)
		  (= dim12 dim21)))
	(cons (list :HEADER
		    :DIMENSIONS
		    (list dim11 dim22)
		    :MAXIMUM-LENGTH
		    (+ 1 (* dim11 dim22))
		    :DEFAULT 0
		    :NAME 'matrix-product)
	      (m-binary-*-row-1 (compress2 '$arg1 M1)
				(compress2 '$arg2 M2)
				(- dim11 1)
				(- dim12 1)
				(- dim22 1)))
        (* M1 M2))))

(defmacro
  m-* (&rest rst)
  (if rst
      (if (cdr rst)
	  (xxxjoin 'm-binary-* rst)
	  (car rst))
      1))

(add-binop m-* m-binary-*)

(defthm
  alist2p-m-*
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (second (dimensions name M1))
		       (first  (dimensions name M2))))
	   (alist2p name (m-* M1 M2)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((m-* M1 M2))))
  :hints (("Goal"
	   :in-theory (enable alist2p header
			      dimensions
			      maximum-length))))

(defthm
  array2p-m-*-1
  (implies (and (array2p name M1)
		(array2p name M2)
		(equal (second (dimensions name M1))
		       (first  (dimensions name M2)))
		(< (* (first (dimensions name M1))
		      (second (dimensions name M2)))
		   *MAXIMUM-POSITIVE-32-BIT-INTEGER*))
	   (array2p name (m-* M1 M2)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((m-* M1 M2))))
  :hints (("Goal"
	   :in-theory (enable array2p header
			      dimensions
			      maximum-length))))

(defthm
  array2p-m-*
  (implies (and (array2p name M1)
		(array2p name M2)
		(equal (second (dimensions name M1))
		       (first  (dimensions name M2)))
		(<= (first (dimensions name M1))
		    *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*)
		(<= (second (dimensions name M2))
		    *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*))
	   (array2p name (m-* M1 M2)))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((m-* M1 M2))))
  :hints (("Goal"
	   :in-theory (enable array2p header
			      dimensions
			      maximum-length))))

(defthm
  dimensions-m-*
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (second (dimensions name M1))
		       (first  (dimensions name M2))))
	   (equal (dimensions name (m-* M1 M2))
		  (list (first (dimensions name M1))
			(second (dimensions name M2)))))
  :hints (("Goal"
	   :in-theory (enable alist2p dimensions header))))

(defthm
  matrixp-m-*
  (implies (and (matrixp m n X1)
		(matrixp n p X2))
	   (matrixp m p (m-* X1 X2)))
  :hints (("Goal"
	   :in-theory (disable m-binary-*))))

(defthm
  default-m-*
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (second (dimensions name M1))
		       (first  (dimensions name M2))))
	   (equal (default name (m-* M1 M2))
		  0))
  :hints (("Goal"
	   :in-theory (enable alist2p default header))))

(defthm
  maximum-length-m-*
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (second (dimensions name M1))
		       (first  (dimensions name M2))))
	   (equal (maximum-length name (m-* M1 M2))
		  (+ 1 (* (first (dimensions name M1))
			  (second (dimensions name M2))))))
  :hints (("Goal"
	   :in-theory (enable alist2p maximum-length header))))

(defthm
  aref2-m-*
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (second (dimensions name M1))
		       (first  (dimensions name M2)))
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (first (dimensions name M1)))
		(< j (second (dimensions name M2))))
	   (equal (aref2 name (m-* M1 M2) i j)
		  (dot M1
		       M2
		       i
		       (+ -1 (second (dimensions name M1)))
		       j)))
  :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(defcong
  ;; M-=-IMPLIES-EQUAL-M-*-1
  m-= equal (M-* M1 M2) 1)

(defcong
  ;; M-=-IMPLIES-EQUAL-M-*-2
  m-= equal (M-* M1 M2) 2)

(defthm
  m-=-row-m-binary-*-row-append-1
  (equal (m-=-row (append (m-binary-*-row M1 M2 m n p)
			  lst)
		  M3
		  m
		  p)
	 (m-=-row (m-binary-*-row M1 M2 m n p)
		  M3
		  m
		  p)))

(defthm
  m-=-row-m-binary-*-row-append-2
  (equal (m-=-row M3
		  (append (m-binary-*-row M1 M2 m n p)
			  lst)
		  m
		  p)
	 (m-=-row M3
		  (m-binary-*-row M1 M2 m n p)
		  m
		  p)))

(defthm
  m-=-row-m-binary-*-row-append-1-remove-header
  (equal (m-=-row (cons (list :HEADER
			      :DIMENSIONS dims
			      :MAXIMUM-LENGTH max-length
			      :DEFAULT default
			      :NAME name1)
			(append (m-binary-*-row M1 M2 m n p)
				lst))
		  M3
		  m
		  p)
	 (m-=-row (m-binary-*-row M1 M2 m n p)
		  M3
		  m
		  p)))

(defthm
  m-=-row-m-binary-*-row-append-2-remove-header
  (equal (m-=-row M3
		  (cons (list :HEADER
			      :DIMENSIONS dims
			      :MAXIMUM-LENGTH max-length
			      :DEFAULT default
			      :NAME name1)
			(append (m-binary-*-row M1 M2 m n p)
				lst))
		  m
		  p)
	 (m-=-row M3
		  (m-binary-*-row M1 M2 m n p)
		  m
		  p)))

(defthm
  m-=-row-m-binary-*-row-remove-header-1
  (equal (m-=-row (cons (list :HEADER
			      :DIMENSIONS dims
			      :MAXIMUM-LENGTH max-length
			      :DEFAULT default
			      :NAME name1)
			(m-binary-*-row M1 M2 m n p))
		  M3
		  m
		  p)
	 (m-=-row (m-binary-*-row M1 M2 m n p)
		  M3
		  m
		  p)))

(defthm
  m-=-row-m-binary-*-row-remove-header-2
  (equal (m-=-row M3
		  (cons (list :HEADER
			      :DIMENSIONS dims
			      :MAXIMUM-LENGTH max-length
			      :DEFAULT default
			      :NAME name1)
			(m-binary-*-row M1 M2 m n p))
		  m
		  p)
	 (m-=-row m3
		  (m-binary-*-row M1 M2 m n p)
		  m
		  p)))

(defthm
  aref2-append-m-binary-*-row
  (implies (and (> m i))
	   (equal (aref2 name (append (m-binary-*-row M1 M2 m j k)
				      lst)
			 i n)
		  (aref2 name lst i n))))

(defthm
  aref2-append-m-binary-*-row-header
  (implies (and (> m i))
	   (equal (aref2
		   name
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-*-row M1 M2 m j k)
				 lst))
		   i
		   n)
		  (aref2
		   name
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   i
		   n))))

(defthm
  m-=-row-m-binary-*-row-append-3
  (implies (> m i)
	   (equal (m-=-row (append (m-binary-*-row M1
						   M2
						   m
						   n
						   p)
				   lst)
			   M3
			   i
			   p)
		  (m-=-row lst
			   M3
			   i
			   p))))

(defthm
  m-=-row-m-binary-*-row-append-4
  (implies (> m i)
	   (equal (m-=-row M3
			   (append (m-binary-*-row M1
						   M2
						   m
						   n
						   p)
				   lst)
			   i
			   p)
		  (m-=-row M3
			   lst
			   i
			   p))))

(defthm
  m-=-row-m-binary-*-row-append-3-header
  (implies (> m i)
	   (equal (m-=-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-*-row M1
						 M2
						 m
						 n
						 p)
				 lst))
		   M3
		   i
		   p)
		  (m-=-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   i
		   p))))

(defthm
  m-=-row-m-binary-*-row-append-4-header
  (implies (> m i)
	   (equal (m-=-row
		   m3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-*-row M1
						 M2
						 m
						 n
						 p)
				 lst))
		   i
		   p)
		  (m-=-row
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   i
		   p))))

(defthm
  m-=-row-1-m-binary-*-row-append-1
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-=-row-1 (append (m-binary-*-row M1
						     M2
						     m
						     n
						     p)
				     lst)
			     M3
			     j
			     p)
		  (m-=-row-1 lst
			     M3
			     j
			     p))))

(defthm
  m-=-row-1-m-binary-*-row-append-2
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-=-row-1 M3
			     (append (m-binary-*-row M1
						     M2
						     m
						     n
						     p)
				     lst)
			     j
			     p)
		  (m-=-row-1 M3
			     lst
			     j
			     p))))

(defthm
  m-=-row-1-m-binary-*-row-append-1-header
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-=-row-1
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-*-row M1
						 M2
						 m
						 n
						 p)
				 lst))
		   M3
		   j
		   p)
		  (m-=-row-1
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   j
		   p))))

(defthm
  m-=-row-1-m-binary-*-row-append-2-header
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-=-row-1
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-*-row M1
						 M2
						 m
						 n
						 p)
				 lst))
		   j
		   p)
		  (m-=-row-1
		   M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   j
		   p))))

(defthm
 m-=-row-1-m-binary-*-row-1-remove-header-1
 (equal (m-=-row-1 (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (m-binary-*-row-1 M1
					   M2
					   m
					   n
					   p))
		   M3
		   m
		   p)
	(m-=-row-1 (m-binary-*-row-1 M1 M2 m n p)
		   M3
		   m
		   p)))

(defthm
 m-=-row-1-m-binary-*-row-1-remove-header-2
 (equal (m-=-row-1 M3
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (m-binary-*-row-1 M1
					   M2
					   m
					   n
					   p))
		   m
		   p)
	(m-=-row-1 M3
		   (m-binary-*-row-1 M1 M2 m n p)
		   m
		   p)))

(defthm
  dot-m-0-1
  (equal (dot (m-0 m n) M1 i j k)
	 0))

(defthm
  dot-m-0-2
  (equal (dot M1 (m-0 m n) i j k)
	 0))

(defthm
  m-=-row-m-binary-*-row-m-0-1
  (m-=-row (m-binary-*-row (m-0 m n)
			   M1
			   i
			   j
			   k)
	   (m-0 m p)
	   i
	   k))

(defthm
  m-=-row-m-binary-*-row-m-0-2
  (m-=-row (m-binary-*-row M1
			   (m-0 n p)
			   i
			   j
			   k)
	   (m-0 m p)
	   i
	   k))

(defthm
  m-=-row-1-m-binary-*-row-1-m-0-1
  (m-=-row-1 (m-binary-*-row-1 (m-0 m n)
			       M1
			       i
			       j
			       k)
	     (m-0 m p)
	     i
	     k))

(defthm
  m-=-row-1-m-binary-*-row-1-m-0-2
  (m-=-row-1 (m-binary-*-row-1 M1
			       (m-0 n p)
			       i
			       j
			       k)
	     (m-0 m p)
	     i
	     k))

(defthm
  alist2p-m-binary-*-row-1-header-m-0-hack-1
  (implies (and (ALIST2P NAME M1)
		(INTEGERP M)
		(< 0 M))
	   (ALIST2P name1
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST M (CADR (DIMENSIONS '$ARG M1)))
				 :MAXIMUM-LENGTH
				 (+ 1 (* M (CADR (DIMENSIONS '$ARG M1))))
				 '(:DEFAULT 0 :NAME MATRIX-PRODUCT))
			  (M-BINARY-*-ROW-1 (M-0 M (CAR (DIMENSIONS '$ARG M1)))
					    M1
					    (+ -1 M)
					    (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M1)))))))
  :hints (("Goal"
	   :in-theory (disable Alist2P-M-*)
	   :use (:instance
		 Alist2P-M-*
		 (M1 (m-0 m (first (dimensions name M1))))
		 (M2 M1)))))

(defthm
  left-nullity-of-m-0-for-m-*
  (implies (and (alist2p name M1)
		(integerp m)
		(> m 0))
	   (m-= (m-* (m-0 m (first (dimensions name M1)))
		     M1)
		(m-0 m (second (dimensions name M1))))))

(defthm
  alist2p-m-binary-*-row-1-header-m-0-hack-2
  (implies (and (ALIST2P NAME M1)
		(INTEGERP p)
		(< 0 p))
	   (ALIST2P name1
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M1)) P)
				 :MAXIMUM-LENGTH
				 (+ 1 (* P (CAR (DIMENSIONS '$ARG M1))))
				 '(:DEFAULT 0 :NAME MATRIX-PRODUCT))
			  (M-BINARY-*-ROW-1 M1 (M-0 (CADR (DIMENSIONS '$ARG M1)) P)
					    (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M1)))
					    (+ -1 P)))))
  :hints (("Goal"
	   :in-theory (disable Alist2P-M-*)
	   :use (:instance
		 Alist2P-M-*
		 (M2 (M-0 (CADR (DIMENSIONS '$ARG M1)) P))))))

(defthm
  right-nullity-of-m-0-for-m-*
  (implies (and (alist2p name M1)
		(integerp p)
		(> p 0))
	   (m-= (m-* M1
		     (m-0 (second (dimensions name M1))
			  p))
		(m-0 (first (dimensions name M1))
		     p))))

(defthm
  aref2-m-1
  (implies (and (integerp i)
		(integerp n)
		(<= 0 i)
		(< i n))
	   (equal (aref2 name (m-1 n) i j)
		  (if (equal i j)
		      1
		      0))))

(defthm
  dot-m-1-1
  (implies (and (integerp i)
		(integerp j)
		(integerp m)
		(>= i 0)
		(>= j 0)
		(> m i))
	   (equal (dot (m-1 m) M1 i j k)
		  (if (<= i j)
		      (fix (aref2 '$arg M1 i k))
		      0))))

(defthm
  dot-m-1-2
  (implies (and (integerp j)
		(integerp k)
		(integerp m)
		(>= j 0)
		(>= k 0)
		(> m j))
	   (equal (dot M1 (m-1 m) i j k)
		  (if (<= k j)
		      (fix (aref2 '$arg M1 i k))
		      0))))

(defthm
  m-=-row-m-binary-*-row-m-1-1
  (implies  (and (integerp i)
		 (integerp j)
		 (integerp m)
		 (>= i 0)
		 (>= j i)
		 (> m i))
	    (m-=-row (m-binary-*-row (m-1 m)
				     M1
				     i
				     j
				     k)
		     M1
		     i
		     k)))

(defthm
  m-=-row-m-binary-*-row-m-1-2
  (implies (and (integerp j)
		(integerp k)
		(integerp m)
		(>= j k)
		(>= k 0)
		(> m j))
	    (m-=-row (m-binary-*-row M1
				     (m-1 m)
				     i
				     j
				     k)
		     M1
		     i
		     k)))

(defthm
  m-=-row-1-m-binary-*-row-1-m-1-1
  (implies  (and (integerp i)
		 (integerp j)
		 (integerp m)
		 (>= i 0)
		 (>= j i)
		 (> m i))
	    (m-=-row-1 (m-binary-*-row-1 (m-1 m)
					 M1
					 i
					 j
					 k)
		       M1
		       i
		       k)))

(defthm
  m-=-row-1-m-binary-*-row-1-m-1-2
  (implies (and (integerp j)
		(integerp k)
		(integerp m)
		(>= j k)
		(>= k 0)
		(> m j))
	   (m-=-row-1 (m-binary-*-row-1 M1
					(m-1 m)
					i
					j
					k)
		      M1
		      i
		      k)))

(defthm
  alist2p-m-binary-*-row-1-header-m-1-hack-1
  (IMPLIES (ALIST2P NAME M1)
	   (ALIST2P name1
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M1)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M1))))
				 '(:DEFAULT 0 :NAME MATRIX-PRODUCT))
			  (M-BINARY-*-ROW-1 (M-1 (CAR (DIMENSIONS '$ARG M1)))
					    M1
					    (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M1)))))))
 :hints (("Goal"
	  :in-theory (disable Alist2P-M-*)
	  :use (:instance
		 Alist2P-M-*
		 (M1 (m-1 (first (dimensions name M1))))
		 (M2 M1)))))


(defthm
  left-unity-of-m-1-for-m-*
  (implies (alist2p name M1)
	   (m-= (m-* (m-1 (first (dimensions name M1)))
		     M1)
		M1)))

(defthm
  alist2p-m-binary-*-row-1-header-m-1-hack-2
  (IMPLIES (ALIST2P NAME M1)
	   (ALIST2P name1
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M1)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M1))))
				 '(:DEFAULT 0 :NAME MATRIX-PRODUCT))
			  (M-BINARY-*-ROW-1 M1 (M-1 (CADR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M1)))))))
  :hints (("Goal"
	   :in-theory (disable Alist2P-M-*)
	   :use (:instance
		 Alist2P-M-*
		 (M2 (m-1 (second (dimensions name M1))))))))

(defthm
  right-unity-of-m-1-for-m-*
  (implies (alist2p name M1)
	   (m-= (m-* M1
		     (m-1 (second (dimensions name M1))))
		M1)))

(defthm
  dot-cons-1
  (implies (and (>= p 0)
		(> j p))
	   (equal (dot (cons (cons (cons m j) val)
			     lst)
		       M3
		       m
		       p
		       q)
		  (dot lst
		       M3
		       m
		       p
		       q))))

(defthm
  dot-cons-header-1
  (implies (and (>= p 0)
		(> j p))
	   (equal (dot (cons (list :HEADER
				   :DIMENSIONS dims
				   :MAXIMUM-LENGTH max-length
				   :DEFAULT default
				   :NAME name1)
			     (cons (cons (cons m j) val)
				   lst))
		       M3
		       m
		       p
		       q)
		  (dot (cons (list :HEADER
				   :DIMENSIONS dims
				   :MAXIMUM-LENGTH max-length
				   :DEFAULT default
				   :NAME name1)
			     lst)
		       M3
		       m
		       p
		       q))))

(defthm
  dot-cons-m-binary-*-row-append-1
  (implies (> j p)
	   (equal (dot (cons (cons (cons m j) val)
			     (append (m-binary-*-row M1
						     M2
						     m
						     n
						     p)
				     lst))
		       M3
		       m
		       p
		       q)
		  (dot (cons (cons (cons m j) val)
			     (m-binary-*-row M1
					     M2
					     m
					     n
					     p))
		       M3
		       m
		       p
		       q))))

(defthm
  dot-m-binary-*-row-append-1
  (equal (dot (append (m-binary-*-row M1 M2 m n p)
		      lst)
	      M3
	      m
	      p
	      q)
	 (dot (m-binary-*-row M1 M2 m n p)
	      M3
	      m
	      p
	      q)))

(defthm
  dot-m-binary-*-row-append-3
  (implies (> m i)
	   (equal (dot (append (m-binary-*-row M1 M2 m n p)
			       lst)
		       M3
		       i
		       p
		       q)
		  (dot lst
		       M3
		       i
		       p
		       q))))

(defthm
  dot-m-binary-*-row-append-3-header
  (implies (> m i)
	   (equal (dot
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-*-row M1
						 M2
						 m
						 n
						 p)
				 lst))
		   M3
		   i
		   p
		   q)
		  (dot
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   i
		   p
		   q))))

(defthm
  dot-m-binary-*-row-append-remove-header-1
  (equal (dot (cons (list :HEADER
			  :DIMENSIONS dims
			  :MAXIMUM-LENGTH max-length
			  :DEFAULT default
			  :NAME name1)
		    (append (m-binary-*-row M1 M2 m n p)
			    lst))
	      M3
	      m
	      p
	      q)
	 (dot (m-binary-*-row M1 M2 m n p)
	      M3
	      m
	      p
	      q)))

(defthm
  dot-m-binary-*-row-remove-header-1
  (equal (dot (cons (list :HEADER
			  :DIMENSIONS dims
			  :MAXIMUM-LENGTH max-length
			  :DEFAULT default
			  :NAME name1)
		    (m-binary-*-row M1 M2 m n p))
	      M3
	      m
	      p
	      q)
	 (dot (m-binary-*-row M1 M2 m n p)
	      M3
	      m
	      p
	      q)))

(defthm
  m-binary-*-row-m-binary-*-row-append-1
  (equal (m-binary-*-row (append (m-binary-*-row M1 M2 m n p)
				 lst)
			 M3
			 m
			 p
			 q)
	 (m-binary-*-row (m-binary-*-row M1 M2 m n p)
			 M3
			 m
			 p
			 q)))

(defthm
  m-binary-*-row-m-binary-*-row-append-1-remove-header
  (equal (m-binary-*-row (cons (list :HEADER
				     :DIMENSIONS dims
				     :MAXIMUM-LENGTH max-length
				     :DEFAULT default
				     :NAME name1)
			       (append (m-binary-*-row M1 M2 m n p)
				       lst))
			 M3
			 m
			 p
			 q)
	 (m-binary-*-row (m-binary-*-row M1 M2 m n p)
			 M3
			 m
			 p
			 q)))

(defthm
  m-binary-*-row-m-binary-*-row-remove-header-1
  (equal (m-binary-*-row (cons (list :HEADER
				     :DIMENSIONS dims
				     :MAXIMUM-LENGTH max-length
				     :DEFAULT default
				     :NAME name1)
			       (m-binary-*-row M1 M2 m n p))
			 M3
			 m
			 p
			 q)
	 (m-binary-*-row (m-binary-*-row M1 M2 m n p)
			 M3
			 m
			 p
			 q)))

(defthm
  m-binary-*-row-m-binary-*-row-append-3
  (implies (> m i)
	   (equal (m-binary-*-row (append (m-binary-*-row M1
							  M2
							  m
							  n
							  p)
					  lst)
				  M3
				  i
				  p
				  q)
		  (m-binary-*-row lst
				  M3
				  i
				  p
				  q))))

(defthm
  m-binary-*-row-m-binary-*-row-append-3-header
  (implies (> m i)
	   (equal (m-binary-*-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-*-row M1
						 M2
						 m
						 n
						 p)
				 lst))
		   M3
		   i
		   p
		   q)
		  (m-binary-*-row
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   i
		   p
		   q))))

(defthm
  m-binary-*-row-1-m-binary-*-row-append-1
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-binary-*-row-1 (append (m-binary-*-row M1
							    M2
							    m
							    n
							    p)
					    lst)
				    M3
				    j
				    p
				    q)
		  (m-binary-*-row-1 lst
				    M3
				    j
				    p
				    q))))

(defthm
  m-binary-*-row-1-m-binary-*-row-append-1-header
  (implies (and (>= j 0)
		(< j m))
	   (equal (m-binary-*-row-1
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 (append (m-binary-*-row M1
						 M2
						 m
						 n
						 p)
				 lst))
		   M3
		   j
		   p
		   q)
		  (m-binary-*-row-1
		   (cons (list :HEADER
			       :DIMENSIONS dims
			       :MAXIMUM-LENGTH max-length
			       :DEFAULT default
			       :NAME name1)
			 lst)
		   M3
		   j
		   p
		   q))))

(defthm
  m-binary-*-row-1-m-binary-*-row-1-remove-header-1
  (equal (m-binary-*-row-1 (cons (list :HEADER
				       :DIMENSIONS dims
				       :MAXIMUM-LENGTH max-length
				       :DEFAULT default
				       :NAME name1)
				 (m-binary-*-row-1 M1
						   M2
						   m
						   n
						   p))
			   M3
			   m
			   p
			   q)
	 (m-binary-*-row-1 (m-binary-*-row-1 M1 M2 m n p)
			   M3
			   m
			   p
			   q)))

(defthm
  m-binary-*-row-1-m-binary-*-row-1-remove-header-2
  (implies (and (integerp q)
		(>= q 0))
	   (equal (m-binary-*-row-1 M3
				    (cons (list :HEADER
						:DIMENSIONS dims
						:MAXIMUM-LENGTH
						max-length
						:DEFAULT default
						:NAME name1)
					  (m-binary-*-row-1 M1
							    M2
							    n
							    p
							    q))
				    m
				    n
				    q)
		  (m-binary-*-row-1 M3
				    (m-binary-*-row-1 M1 M2 n p q)
				    m
				    n
				    q)))
  :hints (("Goal"
	   :use (:instance
		 m-=-row-1-implies-equal-m-binary-*-row-1-2
		 (M1 M3)
		 (M2 (cons (list :HEADER
				 :DIMENSIONS dims
				 :MAXIMUM-LENGTH
				 max-length
				 :DEFAULT default
				 :NAME name1)
			   (m-binary-*-row-1 M1
					     M2
					     n
					     p
					     q)))
		 (M3 (m-binary-*-row-1 M1 M2 n p q))
		 (p q)))))

(defthm
  aref2-m-binary-*-row-lemma
  (implies (and (>= q i)
		(integerp q)
		(integerp i)
		(>= i j))
	   (equal (aref2 name (m-binary-*-row M2 M3 n p q) n j)
		  (aref2 name (m-binary-*-row M2 M3 n p i) n j)))
  :rule-classes nil)

(defthm
  aref2-m-binary-*-row
  (implies (and (> q i)
		(integerp q)
		(integerp i)
		(>= i j))
	   (equal (aref2 name (m-binary-*-row M2 M3 n p q) n j)
		  (aref2 name (m-binary-*-row M2 M3 n p i) n j)))
  :hints (("Goal"
	   :use aref2-m-binary-*-row-lemma)))

(defthm
  m-=-row-m-binary-*-row-q>i
  (implies (and (integerp q)
		(integerp i)
		(>= i 0)
		(> q i))
	   (m-=-row (m-binary-*-row M2 M3 n p q)
		    (m-binary-*-row M2 M3 n p i)
		    n
		    i)))

(defthm
  m-=-row-implies-m-=-row-q>i-lemma
  (implies (and (m-=-row M1 M2 n q)
		(integerp q)
		(integerp i)
		(>= q i))
	   (m-=-row M1 M2 n i))
  :rule-classes nil)

(defthm
  m-=-row-implies-m-=-row-q>i
  (implies (and (m-=-row M1 M2 n q)
		(integerp q)
		(integerp i)
		(> q i))
	   (m-=-row M1 M2 n i))
 :hints (("Goal"
	  :use m-=-row-implies-m-=-row-q>i-lemma)))

(defthm
  m-=-row-append-m-binary-*-row-q>i
  (implies (and (integerp q)
		(integerp i)
		(> q i))
	   (m-=-row (append (m-binary-*-row M2 M3 n p q)
			    lst)
		    (m-binary-*-row M2 M3 n p q)
		    n
		    i))
  :hints (("Goal"
	   :in-theory (disable m-=-row-implies-m-=-row-q>i)
	   :use (:instance
		 m-=-row-implies-m-=-row-q>i
		 (M1 (append (m-binary-*-row M2 M3 n p q)
			     lst))
		 (M2 (m-binary-*-row M2 M3 n p q))))))

(defthm
  m-=-row-append-m-binary-*-row-q>i-1
  (implies (and (integerp q)
		(integerp i)
		(>= i 0)
		(> q i))
	   (m-=-row (append (m-binary-*-row M2 M3 n p q)
			    lst)
		    (m-binary-*-row M2 M3 n p i)
		    n
		    i))
  :hints (("Goal"
	   :in-theory (disable TRANSITIVITY-OF-M-=-ROW)
	   :use (:instance
		 TRANSITIVITY-OF-M-=-ROW
		 (M1 (append (m-binary-*-row M2 M3 n p q)
			     lst))
		 (M2 (m-binary-*-row M2 M3 n p q))
		 (M3 (m-binary-*-row M2 M3 n p i))
		 (m n)
		 (n i)))))

(defthm
  m-=-row-m-binary-*-row-1-q>i
  (implies (and (> q i)
		(integerp n)
		(integerp q)
		(integerp i)
		(>= n 0)
		(>= i 0))
	   (m-=-row (m-binary-*-row-1 M2 M3 n p q)
		    (m-binary-*-row-1 M2 M3 n p i)
		    n
		    i)))

(defthm
  m-=-row-1-implies-m-=-row
  (implies (and (m-=-row-1 M1 M2 n q)
		(integerp n)
		(>= n 0))
	   (m-=-row M1 M2 n q)))

(defthm
  m-=-row-1-implies-m-=-row-q>i
  (implies (and (m-=-row-1 M1 M2 n q)
		(integerp q)
		(integerp i)
		(> q i)
		(integerp n)
		(>= n 0))
	   (m-=-row M1 M2 n i))
  :hints (("Goal"
	   :use m-=-row-implies-m-=-row-q>i)))

(defthm
  m-=-row-1-implies-m-=-row-1-q>i
  (implies (and (m-=-row-1 M1 M2 n q)
		(integerp q)
		(integerp i)
		(> q i)
		(integerp n)
		(>= n 0))
	   (m-=-row-1 M1 M2 n i)))

(defthm
  m-=-row-1-append-m-binary-*-row-n>j
  (implies (and (>= j 0)
		(> n j))
	   (m-=-row-1 (append (m-binary-*-row M2
					      M3
					      n
					      p
					      q)
			      lst)
		      lst
		      j
		      q)))

(defthm
  m-=-row-1-append-m-binary-*-row-n>j-q>i
  (implies (and (m-=-row-1 lst1 lst2 j i)
		(>= j 0)
		(> n j))
	   (m-=-row-1 (append (m-binary-*-row M2
					      M3
					      n
					      p
					      q)
			      lst1)
		      lst2
		      j
		      i)))

(defthm
  m-=-row-1-m-binary-*-row-1-q>i
  (implies (and (> q i)
		(integerp q)
		(integerp i)
		(>= i 0))
	   (m-=-row-1 (m-binary-*-row-1 M2 M3 n p q)
		      (m-binary-*-row-1 M2 M3 n p i)
		      n
		      i)))

(defthm
  m-binary-*-row-m-binary-*-row-1-q>i
  (implies (and (integerp q)
		(integerp i)
		(>= i 0)
		(> q i))
	   (equal (m-binary-*-row M1
				  (m-binary-*-row-1 M2
						    M3
						    n
						    p
						    q)
				  m
				  n
				  i)
		  (m-binary-*-row M1
				  (m-binary-*-row-1 M2
						    M3
						    n
						    p
						    i)
				  m
				  n
				  i)))
  :hints (("Goal"
	   :in-theory (disable
		       m-=row-1-implies-equal-m-binary-*-row-2)
	   :use (:instance
		 m-=row-1-implies-equal-m-binary-*-row-2
		 (M2 (m-binary-*-row-1 M2 M3 n p q))
		 (M3 (m-binary-*-row-1 M2 M3 n p i))
		 (p i)))))

(defthm
  m-=-row-implies-equal-m-binary-*-row
  (implies (m-=-row (m-binary-*-row M1 M2 m n q)
		    (m-binary-*-row M3 M4 m p q)
		    m
		    q)
	   (equal (m-binary-*-row M1 M2 m n q)
		  (m-binary-*-row M3 M4 m p q))))

(defthm
  m-=-row-1-implies-equal-m-binary-*-row-1
  (implies (m-=-row-1 (m-binary-*-row-1 M1 M2 m n q)
		      (m-binary-*-row-1 M3 M4 m p q)
		      m
		      q)
	   (equal (m-binary-*-row-1 M1 M2 m n q)
		  (m-binary-*-row-1 M3 M4 m p q))))

(defthm
  aref2-append-m-binary-*-row-1
  (implies (and (integerp q)
		(>= q 0))
	   (equal (aref2 name
			 (append (m-binary-*-row M2
						 M3
						 n
						 p
						 q)
				 lst)
			 n
			 q)
		  (aref2 name
			 (m-binary-*-row M2
					 M3
					 n
					 p
					 q)
			 n
			 q))))

(defthm
  dot-append-m-binary-*-row
  (implies (and (>= j 0)
		(> n j))
	   (equal (dot M1
		       (append (m-binary-*-row M2
					       M3
					       n
					       p
					       q)
			       lst)
		       m
		       j
		       q)
		  (dot M1
		       lst
		       m
		       j
		       q))))

(defthm
  aref2-m-binary-*-row-0
  (implies (and (integerp q)
		(>= q 0))
	   (equal (aref2 name
			 (m-binary-*-row M2 M3 n 0 q)
			 n
			 q)
		  (* (aref2 name M2 n 0)
		     (aref2 name M3 0 q)))))

(defthm
  dot-m-binary-*-row-1-0
  (implies (and (integerp q)
		(>= q 0))
	   (equal (dot M1
		       (m-binary-*-row-1 M2
					 M3
					 n
					 0
					 q)
		       m
		       n
		       q)
		  (* (aref2 name M3 0 q)
		     (dot M1 M2 m n 0)))))

(defthm
  aref2-m-binary-*-row-p>0
  (implies (and (integerp p)
		(integerp q)
		(> p 0)
		(>= q 0))
	   (equal (+ (* (aref2 name M2 n p)
			(aref2 name M3 p q))
		     (aref2 name
			    (m-binary-*-row M2
					    M3
					    n
					    (+ -1 p)
					    q)
			    n
			    q))
		  (aref2 name
			 (m-binary-*-row M2 M3 n p q)
			 n
			 q))))

(defthm
  dot-m-binary-*-row-1-p>0
  (implies (and (integerp n)
		(integerp p)
		(integerp q)
		(>= n 0)
		(> p 0)
		(>= q 0))
	   (equal (+ (* (aref2 name M3 p q)
			(dot M1 M2 m n p))
		     (dot M1
			  (m-binary-*-row-1 M2
					    M3
					    n
					    (+ -1 p)
					    q)
			  m
			  n
			  q))
		  (dot M1
		       (m-binary-*-row-1 M2
					 M3
					 n
					 p
					 q)
		       m
		       n
		       q)))
  :hints (("Subgoal *1/4"
	   :in-theory (disable
		       aref2-m-binary-*-row-p>0)
	   :use aref2-m-binary-*-row-p>0)
	  ("Subgoal *1/1"
	   :do-not '(generalize))))

(defthm
  dot-m-binary-*-row-associativity
  (implies (and (integerp n)
		(integerp p)
		(integerp q)
		(>= n 0)
		(>= p 0)
		(>= q 0))
	   (equal (dot (m-binary-*-row M1 M2 m n p)
		       M3
		       m
		       p
		       q)
		  (dot M1
		       (m-binary-*-row-1 M2 M3 n p q)
		       m
		       n
		       q)))
  :hints (("Subgoal *1/4.1"
	   :in-theory (disable dot-m-binary-*-row-1-p>0)
	   :use dot-m-binary-*-row-1-p>0)))

(defthm
  m-=-row-m-binary-*-row-associativity
  (implies (and (integerp n)
		(integerp p)
		(integerp q)
		(>= n 0)
		(>= p 0)
		(>= q 0))
	   (m-=-row (m-binary-*-row (m-binary-*-row M1
						    M2
						    m
						    n
						    p)
				    M3
				    m
				    p
				    q)
		    (m-binary-*-row M1
				    (m-binary-*-row-1
				     M2
				     M3
				     n
				     p
				     q)
				    m
				    n
				    q)
		    m
		    q)))

(defthm
  m-=-row-1-m-binary-*-row-1-associativity
  (implies
   (and (integerp n)
	(integerp p)
	(integerp q)
	(>= n 0)
	(>= p 0)
	(>= q 0))
   (m-=-row-1 (m-binary-*-row-1 (m-binary-*-row-1 M1
						  M2
						  m
						  n
						  p)
				M3
				m
				p
				q)
	      (m-binary-*-row-1 M1
				(m-binary-*-row-1 M2
						  M3
						  n
						  p
						  q)
				m
				n
				q)
	      m
	      q)))

(defthm
  m-binary-*-row-1-associativity
  (implies
   (and (integerp n)
	(integerp p)
	(integerp q)
	(>= n 0)
	(>= p 0)
	(>= q 0))
   (equal (m-binary-*-row-1 (m-binary-*-row-1 M1
					      M2
					      m
					      n
					      p)
			    M3
			    m
			    p
			    q)
	  (m-binary-*-row-1 M1
			    (m-binary-*-row-1 M2
					      M3
					      n
					      p
					      q)
			    m
			    n
			    q)))
  :hints (("Goal"
	   :in-theory
	   (disable
	    m-=-row-1-implies-equal-m-binary-*-row-1)
	   :use
	   (:instance
	    m-=-row-1-implies-equal-m-binary-*-row-1
	    (M1 (m-binary-*-row-1 M1 M2 m n p))
	    (M2 M3)
	    (M3 M1)
	    (M4 (m-binary-*-row-1 M2 M3 n p q))
	    (n p)
	    (p n)))))

(defthm
  alist2p-m-binary-*-row-1-header-hack-1
  (IMPLIES (AND (ALIST2P '$ARG1 M1)
		(ALIST2P '$ARG2 M2)
		(EQUAL (CADR (DIMENSIONS '$ARG M1))
		       (CAR (DIMENSIONS '$ARG M2)))
		(EQUAL (CADR (DIMENSIONS '$ARG M2))
		       (CAR (DIMENSIONS '$ARG M3))))
	   (ALIST2P name
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M1))
				       (CAR (DIMENSIONS '$ARG M3)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M1))
				       (CAR (DIMENSIONS '$ARG M3))))
				 '(:DEFAULT 0 :NAME MATRIX-PRODUCT))
			  (M-BINARY-*-ROW-1 M1
					    M2
					    (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M2)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M3)))))))
  :HINTS (("Goal"
	   :IN-THEORY (ENABLE Alist2P HEADER DIMENSIONS MAXIMUM-LENGTH))))

(defthm
  alist2p-m-binary-*-row-1-header-hack-2
  (IMPLIES (AND (ALIST2P '$ARG1 M2)
		(ALIST2P '$ARG2 M3)
		(EQUAL (CADR (DIMENSIONS '$ARG M1))
		       (CAR (DIMENSIONS '$ARG M2)))
		(EQUAL (CADR (DIMENSIONS '$ARG M2))
		       (CAR (DIMENSIONS '$ARG M3))))
	   (ALIST2P name
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M2))
				       (CADR (DIMENSIONS '$ARG M3)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M2))
				       (CADR (DIMENSIONS '$ARG M3))))
				 '(:DEFAULT 0 :NAME MATRIX-PRODUCT))
			  (M-BINARY-*-ROW-1 M2
					    M3
					    (+ -1 (CAR (DIMENSIONS '$ARG M2)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M3)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M3)))))))
  :HINTS (("Goal"
	   :IN-THEORY (ENABLE Alist2P HEADER DIMENSIONS MAXIMUM-LENGTH))))

(defthm
  associativity-of-m-*
  (equal (m-* (m-* M1 M2) M3)
	 (m-* M1 M2 M3)))

(defthm
  m-binary-*-row-1-m-binary-+-row-1-remove-header-1
  (equal (m-binary-*-row-1 (cons (list :HEADER
				       :DIMENSIONS dims
				       :MAXIMUM-LENGTH max-length
				       :DEFAULT default
				       :NAME name1)
				 (m-binary-+-row-1 M1
						   M2
						   i
						   j))
			   M3
			   i
			   j
			   k)
	 (m-binary-*-row-1 (m-binary-+-row-1 M1 M2 i j)
			   M3
			   i
			   j
			   k))
  :hints (("Goal"
	   :use (:instance
		 m-=-row-1-implies-equal-m-binary-*-row-1-1
		 (M1 (cons (list :HEADER
				       :DIMENSIONS dims
				       :MAXIMUM-LENGTH max-length
				       :DEFAULT default
				       :NAME name1)
				 (m-binary-+-row-1 M1
						   M2
						   i
						   j)))
		 (M2 (m-binary-+-row-1 M1 M2 i j))
		 (m i)
		 (n j)
		 (p k)))))

(defthm
  m-binary-*-row-1-m-binary-+-row-1-remove-header-2
  (implies (and (integerp k)
		(>= k 0))
	   (equal (m-binary-*-row-1 M1
				    (cons (list :HEADER
						:DIMENSIONS dims
						:MAXIMUM-LENGTH max-length
						:DEFAULT default
						:NAME name1)
					  (m-binary-+-row-1 M2
							    M3
							    j
							    k))
				    i
				    j
				    k)
		  (m-binary-*-row-1 M1
				    (m-binary-+-row-1 M2
						      M3
						      j
						      k)
				    i
				    j
				    k)))
  :hints (("Goal"
	   :use (:instance
		 m-=-row-1-implies-equal-m-binary-*-row-1-2
		 (M2 (cons (list :HEADER
				 :DIMENSIONS dims
				 :MAXIMUM-LENGTH max-length
				 :DEFAULT default
				 :NAME name1)
			   (m-binary-+-row-1 M2
					     M3
					     j
					     k)))
		 (M3 (m-binary-+-row-1 M2
				       M3
				       j
				       k))
		 (n j)
		 (p k)
		 (m i)))))

(defthm
  m-binary-+-row-1-m-binary-*-row-1-remove-header-1
  (equal (m-binary-+-row-1 (cons (list :HEADER
				       :DIMENSIONS dims
				       :MAXIMUM-LENGTH max-length
				       :DEFAULT default
				       :NAME name1)
				 (m-binary-*-row-1 M1
						   M2
						   i
						   j
						   k))
			   M3
			   i
			   k)
	 (m-binary-+-row-1 (m-binary-*-row-1 M1 M2 i j k)
			   M3
			   i
			   k))
  :hints (("Goal"
	   :use (:instance
		 m-=-row-1-implies-equal-m-binary-+-row-1-1
		 (M1  (cons (list :HEADER
				  :DIMENSIONS dims
				  :MAXIMUM-LENGTH max-length
				  :DEFAULT default
				  :NAME name1)
			    (m-binary-*-row-1 M1
					      M2
					      i
					      j
					      k)))
		 (M2 (m-binary-*-row-1 M1 M2 i j k))
		 (m i)
		 (n k)))))

(defthm
  m-binary-+-row-1-m-binary-*-row-1-remove-header-2
  (equal (m-binary-+-row-1 M1
			   (cons (list :HEADER
				       :DIMENSIONS dims
				       :MAXIMUM-LENGTH max-length
				       :DEFAULT default
				       :NAME name1)
				 (m-binary-*-row-1 M2
						   M3
						   i
						   j
						   k))
			   i
			   k)
	 (m-binary-+-row-1 M1
			   (m-binary-*-row-1 M2 M3 i j k)
			   i
			   k))
  :hints (("Goal"
	   :use (:instance
		 m-=-row-1-implies-equal-m-binary-+-row-1-2
		 (M2  (cons (list :HEADER
				  :DIMENSIONS dims
				  :MAXIMUM-LENGTH max-length
				  :DEFAULT default
				  :NAME name1)
			    (m-binary-*-row-1 M2
					      M3
					      i
					      j
					      k)))
		 (M3 (m-binary-*-row-1 M2 M3 i j k))
		 (m i)
		 (n k)))))

(defthm
  distributivity-aref2-m-binary-+-row
  (implies (and (integerp k)
		(>= k 0))
	   (equal (* x
		     (aref2 '$arg
			    (m-binary-+-row M2
					    M3
					    j
					    k)
			    j
			    k))
		  (+ (* x (aref2 '$arg M2 j k))
		     (* x (aref2 '$arg M3 j k))))))

(defthm
  aref2-append-m-binary-+-row-a
  (implies (and (integerp k)
		(>= k 0))
	   (equal (aref2 '$arg (append (m-binary-+-row M2 M3 j k)
				       lst)
			 j
			 k)
		  (aref2 '$arg (m-binary-+-row M2 M3 j k) j k))))

(defthm
  aref2-append-m-binary-+-row-b
  (implies (and (integerp k)
		(>= k 0)
		(integerp k1)
		(< k k1))
	   (equal (aref2 '$arg (append (m-binary-+-row M2 M3 j k1)
				       lst)
			 j
			 k)
		  (aref2 '$arg (m-binary-+-row M2 M3 j k) j k))))

(defthm
  dot-remove-cons
  (implies (and (>= l 0)
		(< l j))
	   (equal (dot M1
		       (cons (cons (cons j k) val) lst)
		       i
		       l
		       k)
		  (dot M1 lst i l k))))

(defthm
  dot-remove-cons-1
  (implies (< k k1)
	   (equal (dot M1
		       (cons (cons (cons j k1) val) lst)
		       i
		       l
		       k)
		  (dot M1 lst i l k))))

(defthm
  dot-append-m-binary-+-row
  (implies (and (>= l 0)
		(< l j))
	   (equal (dot M1
		       (append (m-binary-+-row M2 M3 j k1)
			       lst)
		       i
		       l
		       k)
		  (dot M1 lst i l k))))

(defthm
  dot-m-binary-+-row-1
  (implies (and (integerp k)
		(>= k 0))
	   (equal (dot M1
		       (m-binary-+-row-1 M2 M3 j k)
		       i
		       j
		       k)
		  (+ (dot M1 M2 i j k)
		     (dot M1 M3 i j k)))))

(defthm
  dot-m-binary-+-row-1-a
  (implies (and (< k k1)
		(integerp k)
		(>= k 0)
		(integerp k1))
	   (equal (dot M1
		       (m-binary-+-row-1 M2 M3 j k1)
		       i
		       j
		       k)
		  (+ (dot M1 M2 i j k)
		     (dot M1 M3 i j k))))
  :hints (("Goal"
	   :do-not '(generalize))))

(defthm
  dot-m-binary-+-row-1-b
  (implies (and (<= k k1)
		(integerp k)
		(>= k 0)
		(integerp k1))
	   (equal (dot M1
		       (m-binary-+-row-1 M2 M3 j k1)
		       i
		       j
		       k)
		  (+ (dot M1 M2 i j k)
		     (dot M1 M3 i j k))))
  :hints (("Goal"
	   :cases ((< k k1)))))

(defthm
  m-binary-*-row-remove-cons
  (implies (and (>= l 0)
		(< l j))
	   (equal (m-binary-*-row M1
				  (cons (cons (cons j k1) val) lst)
				  i
				  l
				  k)
		  (m-binary-*-row M1 lst i l k))))

(defthm
  m-binary-*-row-remove-cons-1
  (implies (and (>= k 0)
		(< k k1))
	   (equal (m-binary-*-row M1
				  (cons (cons (cons j k1) val) lst)
				  i
				  j
				  k)
		  (m-binary-*-row M1 lst i j k))))

(defthm
  distributivity-m-binary-*-append-row-m-binary-+-row
  (implies (and (integerp j)
		(integerp k)
		(>= j 0)
		(>= l 0)
		(>= k l))
	   (equal (m-binary-*-row M1
				  (append (m-binary-+-row M2 M3 j l)
					  (m-binary-+-row-1 M2 M3 (+ -1 j) k))
				  i
				  j
				  l)
		  (m-binary-+-row (m-binary-*-row M1 M2 i j l)
				  (m-binary-*-row M1 M3 i j l)
				  i
				  l))))

(defthm
  distributivity-m-binary-*-row-m-binary-+-row-case-j=0
  (equal (m-binary-*-row M1
			 (m-binary-+-row M2 M3 0 k)
			 i
			 0
			 k)
	 (m-binary-+-row (m-binary-*-row M1 M2 i 0 k)
			 (m-binary-*-row M1 M3 i 0 k)
			 i
			 k)))

(defthm
  distributivity-m-binary-*-row-m-binary-+-row-a
  (implies (and (integerp k)
		(<= l k)
		(>= l 0))
	   (equal (m-binary-*-row M1
				  (m-binary-+-row-1 M2 M3 j k)
				  i
				  j
				  l)
		  (m-binary-+-row (m-binary-*-row M1 M2 i j l)
				  (m-binary-*-row M1 M3 i j l)
				  i
				  l))))

(defthm
  distributivity-m-binary-*-row-m-binary-+-row
  (equal (m-binary-*-row M1
			 (m-binary-+-row-1 M2 M3 j k)
			 i
			 j
			 k)
	 (m-binary-+-row (m-binary-*-row M1 M2 i j k)
			 (m-binary-*-row M1 M3 i j k)
			 i
			 k)))

(defthm
  m-binary-+-row-1-remove-cons-1
  (implies (and (>= i1 0)
		(< i1 i))
	   (equal (m-binary-+-row-1 (cons (cons (cons i j) val)
					  lst1)
				    lst2
				    i1
				    j)
		  (m-binary-+-row-1 lst1
				    lst2
				    i1
				    j))))

(defthm
  m-binary-+-row-1-remove-cons-2
  (implies (and (>= i1 0)
		(< i1 i))
	   (equal (m-binary-+-row-1 lst1
				    (cons (cons (cons i j) val)
					  lst2)
				    i1
				    j)
		  (m-binary-+-row-1 lst1
				    lst2
				    i1
				    j))))

(defthm
  m-binary-+-row-remove-append-1
  (equal (m-binary-+-row (append (m-binary-*-row M1 M2 i j k)
				 lst1)
			 lst2
			 i
			 k)
	 (m-binary-+-row (m-binary-*-row M1 M2 i j k)
			 lst2
			 i
			 k)))

(defthm
  m-binary-+-row-remove-append-2
  (equal (m-binary-+-row lst1
			 (append (m-binary-*-row M1 M2 i j k)
				 lst2)
			 i
			 k)
	 (m-binary-+-row lst1
			 (m-binary-*-row M1 M2 i j k)
			 i
			 k)))

(defthm
  m-binary-+-row-remove-append-1a
  (implies (< i1 i)
	   (equal (m-binary-+-row (append (m-binary-*-row M1 M2 i j k)
					  lst1)
				  lst2
				  i1
				  k)
		  (m-binary-+-row lst1
				  lst2
				  i1
				  k))))

(defthm
  m-binary-+-row-remove-append-2a
  (implies (< i1 i)
	   (equal (m-binary-+-row lst1
				  (append (m-binary-*-row M1 M2 i j k)
					  lst2)
				  i1
				  k)
		  (m-binary-+-row lst1
				  lst2
				  i1
				  k))))

(defthm
  m-binary-+-row-1-remove-append-1a
  (implies (and (> i 0)
		(< i1 i))
	   (equal (m-binary-+-row-1 (append (m-binary-*-row M1 M2 i j k)
					    lst1)
				    lst2
				    i1
				    k)
		  (m-binary-+-row-1 lst1
				    lst2
				    i1
				    k))))

(defthm
  m-binary-+-row-1-remove-append-1b
  (implies (and (> i 0)
		(< i1 i))
	   (equal (m-binary-+-row-1 lst1
				    (append (m-binary-*-row M1 M2 i j k)
					    lst2)
				    i1
				    k)
		  (m-binary-+-row-1 lst1
				    lst2
				    i1
				    k))))

(defthm
  left-distributivity-m-binary-*-row-1-m-binary-+-row-1
  (equal (m-binary-*-row-1 M1
			   (m-binary-+-row-1 M2
					     M3
					     j
					     k)
			   i
			   j
			   k)
	 (m-binary-+-row-1 (m-binary-*-row-1 M1
					     M2
					     i
					     j
					     k)
			   (m-binary-*-row-1 M1
					     M3
					     i
					     j
					     k)
			   i
			   k)))

(defthm
  alist2p-header-m-binary-*-row-1-crock
  (IMPLIES (AND (ALIST2P name1 M1)
		(ALIST2P name2 M2))
	   (ALIST2P name
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M2)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M2))))
				 '(:DEFAULT 0 :NAME MATRIX-PRODUCT))
			  (M-BINARY-*-ROW-1 M1
					    M2
					    (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M2)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M2)))))))
  :HINTS (("Goal"
	   :IN-THEORY (ENABLE Alist2P HEADER DIMENSIONS MAXIMUM-LENGTH))))

(defthm
  alist2p-header-m-binary-*-row-1-crock-1
  (IMPLIES (AND (ALIST2P name1 M1)
		(ALIST2P name2 M2))
	   (ALIST2P name
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M2)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M2))))
				 '(:DEFAULT 0 :NAME MATRIX-PRODUCT))
			  (M-BINARY-+-ROW-1
			   (M-BINARY-*-ROW-1 M1
					     M2
					     (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					     (+ -1 (CAR (DIMENSIONS '$ARG M2)))
					     (+ -1 (CADR (DIMENSIONS '$ARG M2))))
			   (M-BINARY-*-ROW-1 M1
					     M3
					     (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					     (+ -1 (CAR (DIMENSIONS '$ARG M2)))
					     (+ -1 (CADR (DIMENSIONS '$ARG M2))))
			   (+ -1 (CAR (DIMENSIONS '$ARG M1)))
			   (+ -1 (CADR (DIMENSIONS '$ARG M2)))))))
  :HINTS (("Goal"
	   :IN-THEORY (ENABLE Alist2P HEADER DIMENSIONS MAXIMUM-LENGTH))))

(defthm
 alist2p-header-m-binary-*-row-1-crock-2
 (IMPLIES (AND (ALIST2P name1 M1)
	       (ALIST2P name2 M2))
	  (ALIST2P name
		   (CONS (LIST* :HEADER :DIMENSIONS
				(LIST (CAR (DIMENSIONS '$ARG M1))
				      (CADR (DIMENSIONS '$ARG M2)))
				:MAXIMUM-LENGTH
				(+ 1
				   (* (CAR (DIMENSIONS '$ARG M1))
				      (CADR (DIMENSIONS '$ARG M2))))
				'(:DEFAULT 0 :NAME MATRIX-SUM))
			 (M-BINARY-+-ROW-1
			  (M-BINARY-*-ROW-1 M1
					    M2
					    (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M2)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M2))))
			  (M-BINARY-*-ROW-1 M1
					    M3
					    (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M2)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M2))))
			  (+ -1 (CAR (DIMENSIONS '$ARG M1)))
			  (+ -1 (CADR (DIMENSIONS '$ARG M2)))))))
 :HINTS (("Goal"
	  :IN-THEORY (ENABLE Alist2P HEADER DIMENSIONS MAXIMUM-LENGTH))))

(defthm
  alist2p-header-m-binary-*-row-1-crock-3
  (IMPLIES (AND (ALIST2P name1 M1)
		(ALIST2P name2 M2))
	   (ALIST2P name
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M2)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M2))))
				 '(:DEFAULT 0 :NAME MATRIX-PRODUCT))
			  (M-BINARY-*-ROW-1 M1
					    M3
					    (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					    (+ -1 (CAR (DIMENSIONS '$ARG M2)))
					    (+ -1 (CADR (DIMENSIONS '$ARG M2)))))))
  :HINTS (("Goal"
	   :IN-THEORY (ENABLE Alist2P HEADER DIMENSIONS MAXIMUM-LENGTH))))

(defthm
  left-distributivity-of-m-*-over-m-+
  (m-= (m-* M1 (m-+ M2 M3))
       (m-+ (m-* M1 M2)
	    (m-* M1 M3))))

(defthm
  right-dot-m-binary-+-row
  (equal (dot (m-binary-+-row M1
			      M2
			      i
			      j)
	      M3
	      i
	      j
	      k)
	 (+ (dot M1 M3 i j k)
	    (dot M2 M3 i j k))))

(defthm
  right-distributivity-m-binary-*-row-m-binary-+-row
  (equal (m-binary-*-row (m-binary-+-row M1
					 M2
					 i
					 j)
			 M3
			 i
			 j
			 k)
	 (m-binary-+-row (m-binary-*-row M1
					 M3
					 i
					 j
					 k)
			 (m-binary-*-row M2
					 M3
					 i
					 j
					 k)
			 i
			 k)))

(defthm
  dot-m-binary-+-row-remove-append
  (equal (dot (append (m-binary-+-row M1
				      M2
				      i
				      j)
		      lst)
	      M3
	      i
	      j
	      k)
	 (dot (m-binary-+-row M1
			      M2
			      i
			      j)
	      M3
	      i
	      j
	      k)))

(defthm
  dot-m-binary-+-row-remove-append-a
  (implies (> i i1)
	   (equal (dot (append (m-binary-+-row M1
					       M2
					       i
					       j)
			       lst)
		       M3
		       i1
		       j
		       k)
		  (dot lst
		       M3
		       i1
		       j
		       k))))

(defthm
  m-binary-*-row-m-binary-+-row-remove-append
  (equal (m-binary-*-row (append (m-binary-+-row M1
						 M2
						 i
						 j)
				 lst)
			 M3
			 i
			 j
			 k)
	 (m-binary-+-row (m-binary-*-row M1
					 M3
					 i
					 j
					 k)
			 (m-binary-*-row M2
					 M3
					 i
					 j
					 k)
			 i
			 k)))

(defthm
  m-binary-*-row-m-binary-+-row-remove-append-a
  (implies (> i i1)
	   (equal (m-binary-*-row (append (m-binary-+-row M1
							  M2
							  i
							  j)
					  lst)
				  M3
				  i1
				  j
				  k)
		  (m-binary-*-row lst
				  M3
				  i1
				  j
				  k))))

(defthm
    m-binary-*-row-1-m-binary-+-row-remove-append-a
    (implies (and (>= i1 0)
		  (> i i1))
	     (equal (m-binary-*-row-1 (append (m-binary-+-row M1
							      M2
							      i
							      j)
					      lst)
				      M3
				      i1
				      j
				      k)
		    (m-binary-*-row-1 lst
				      M3
				      i1
				      j
				      k))))

(defthm
  right-distributivity-m-binary-*-row-1-m-binary-+-row-1
  (equal (m-binary-*-row-1 (m-binary-+-row-1 M1
					     M2
					     i
					     j)
			   M3
			   i
			   j
			   k)
	 (m-binary-+-row-1 (m-binary-*-row-1 M1
					     M3
					     i
					     j
					     k)
			   (m-binary-*-row-1 M2
					     M3
					     i
					     j
					     k)
			   i
			   k)))

(defthm
  alist2p-header-m-binary-*-row-1-crock-4
  (IMPLIES (AND (ALIST2P name1 M1)
		(ALIST2P name2 M3))
	   (ALIST2P name
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M3)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M3))))
				 '(:DEFAULT 0 :NAME MATRIX-PRODUCT))
			  (M-BINARY-+-ROW-1
			   (M-BINARY-*-ROW-1 M1
					     M3
					     (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					     (+ -1 (CAR (DIMENSIONS '$ARG M3)))
					     (+ -1 (CADR (DIMENSIONS '$ARG M3))))
			   (M-BINARY-*-ROW-1 M2
					     M3
					     (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					     (+ -1 (CAR (DIMENSIONS '$ARG M3)))
					     (+ -1 (CADR (DIMENSIONS '$ARG M3))))
			   (+ -1 (CAR (DIMENSIONS '$ARG M1)))
			   (+ -1 (CADR (DIMENSIONS '$ARG M3)))))))
  :HINTS (("Goal"
	   :IN-THEORY (ENABLE Alist2P HEADER DIMENSIONS MAXIMUM-LENGTH))))

(defthm
  alist2p-header-m-binary-*-row-1-crock-5
  (IMPLIES (AND (ALIST2P name1 M1)
		(ALIST2P name2 M3))
	   (ALIST2p name
		    (CONS (LIST* :HEADER :DIMENSIONS
				 (LIST (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M3)))
				 :MAXIMUM-LENGTH
				 (+ 1
				    (* (CAR (DIMENSIONS '$ARG M1))
				       (CADR (DIMENSIONS '$ARG M3))))
				 '(:DEFAULT 0 :NAME MATRIX-SUM))
			  (M-BINARY-+-ROW-1
			   (M-BINARY-*-ROW-1 M1
					     M3
					     (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					     (+ -1 (CAR (DIMENSIONS '$ARG M3)))
					     (+ -1 (CADR (DIMENSIONS '$ARG M3))))
			   (M-BINARY-*-ROW-1 M2
					     M3
					     (+ -1 (CAR (DIMENSIONS '$ARG M1)))
					     (+ -1 (CAR (DIMENSIONS '$ARG M3)))
					     (+ -1 (CADR (DIMENSIONS '$ARG M3))))
			   (+ -1 (CAR (DIMENSIONS '$ARG M1)))
			   (+ -1 (CADR (DIMENSIONS '$ARG M3)))))))
  :HINTS (("Goal"
	   :IN-THEORY (ENABLE Alist2P HEADER DIMENSIONS MAXIMUM-LENGTH))))

(defthm
  right-distributivity-of-m-*-over-m-+
  (m-= (m-* (m-+ M1 M2) M3)
       (m-+ (m-* M1 M3)
	    (m-* M2 M3))))

(defthm
  m-=-row-1-m-trans-m-1
  (implies (and (integerp n)
		(< i n))
	   (m-=-row-1 (m-trans (m-1 n))
		      (m-1 n)
		      i
		      j)))

(defthm
  m-=-m-trans-m-1
  (implies (and (integerp n)
		(> n 0))
	   (m-= (m-trans (m-1 n))
		(m-1 n))))

(defthm
  dot-s-*-left=*-dot
  (equal (dot (s-* a M1)
	      M2
	      i
	      k
	      j)
	 (* a (dot M1
		   M2
		   i
		   k
		   j))))

(defthm
  dot-s-*-right=*-dot
  (equal (dot M1
	      (s-* a M2)
	      i
	      k
	      j)
	 (* a (dot M1
		   M2
		   i
		   k
		   j))))

(defthm
  m-=-row-m-*-s-*-left
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (c M1)(r M2))
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (r M1))
		(< j (c M2)))
	   (m-=-row (m-* (s-* a M1) M2)
		    (s-* a (m-* M1 M2))
		    i
		    j))
  :hints (("Goal"
	   :in-theory (disable m-binary-*))))

(defthm
  m-=-row-m-*-s-*-right
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (c M1)(r M2))
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (r M1))
		(< j (c M2)))
	   (m-=-row (m-* M1 (s-* a M2))
		    (s-* a (m-* M1 M2))
		    i
		    j))
  :hints (("Goal"
	   :in-theory (disable m-binary-*))))

(defthm
   m-=-row-1-m-*-s-*-left
   (implies (and (alist2p name M1)
		 (alist2p name M2)
		 (equal (c M1)(r M2))
		 (integerp i)
		 (integerp j)
		 (>= i 0)
		 (>= j 0)
		 (< i (r M1))
		 (< j (c M2)))
	    (m-=-row-1 (m-* (s-* a M1) M2)
		       (s-* a (m-* M1 M2))
		       i
		       j))
   :hints (("Goal"
	    :in-theory (disable m-binary-*))))

(defthm
   m-=-row-1-m-*-s-*-right
   (implies (and (alist2p name M1)
		 (alist2p name M2)
		 (equal (c M1)(r M2))
		 (integerp i)
		 (integerp j)
		 (>= i 0)
		 (>= j 0)
		 (< i (r M1))
		 (< j (c M2)))
	    (m-=-row-1 (m-* M1 (s-* a M2))
		       (s-* a (m-* M1 M2))
		       i
		       j))
   :hints (("Goal"
	    :in-theory (disable m-binary-*))))

(defthm
  m-*-s-*-left
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (c M1)(r M2)))
	   (m-= (m-* (s-* a M1) M2)
		(s-* a (m-* M1 M2))))
  :hints (("Goal"
	   :in-theory (disable m-binary-*))
	  ("Subgoal 2"
	   :in-theory (disable m-binary-*
			       alist2p-m-*)
	   :use (:instance
		 alist2p-m-*
		 (name '$arg)
		 (M1 (s-* a M1))))
	  ("Subgoal 1"
	   :in-theory (disable m-binary-*
			       alist2p-s-*)
	   :use (:instance
		 alist2p-s-*
		 (name '$arg)
		 (M (m-* M1 M2))))))

(defthm
  m-*-s-*-right
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (c M1)(r M2)))
	   (m-= (m-* M1 (s-* a M2))
		(s-* a (m-* M1 M2))))
  :hints (("Goal"
	   :in-theory (disable m-binary-*))
	  ("Subgoal 2"
	   :in-theory (disable m-binary-*
			       alist2p-m-*)
	   :use (:instance
		 alist2p-m-*
		 (name '$arg)
		 (M2 (s-* a M2))))
	  ("Subgoal 1"
	   :in-theory (disable m-binary-*
			       alist2p-s-*)
	   :use (:instance
		 alist2p-s-*
		 (name '$arg)
		 (M (m-* M1 M2))))))

(defthm
  dot-m-trans-m-trans
  (equal (dot (m-trans M2)
	      (m-trans M1)
	      j
	      k
	      i)
	 (dot M1
	      M2
	      i
	      k
	      j)))

(defthm
  m-=-row-m-trans-m-*=m-*-m-trans
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (c M1)(r M2))
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (r M1))
		(< j (c M2)))
	   (m-=-row (m-trans (m-* M1 M2))
		    (m-* (m-trans M2)(m-trans M1))
		    j
		    i))
  :hints (("Goal"
	   :in-theory (disable m-binary-*))))

(defthm
  m-=-row-1-m-trans-m-*=m-*-m-trans
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (c M1)(r M2))
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (r M1))
		(< j (c M2)))
	   (m-=-row-1 (m-trans (m-* M1 M2))
		      (m-* (m-trans M2)(m-trans M1))
		      j
		      i))
  :hints (("Goal"
	   :in-theory (disable m-binary-*))))

(defthm
  m-trans-m-*=m-*-m-trans
  (implies (and (alist2p name M1)
		(alist2p name M2)
		(equal (c M1)(r M2)))
	   (m-= (m-trans (m-* M1 M2))
		(m-* (m-trans M2)(m-trans M1))))
  :hints (("Goal"
	   :in-theory (disable m-binary-*))
	  ("Subgoal 2"
	   :in-theory (disable m-binary-*
			       alist2p-m-trans)
	   :use (:instance
		 alist2p-m-trans
		 (name '$arg)
		 (M (m-* M1 M2))))
	  ("Subgoal 1"
	   :in-theory (disable m-binary-*
			       alist2p-m-*)
	   :use (:instance
		 alist2p-m-*
		 (name '$arg)
		 (M1 (m-trans M2))
		 (M2 (m-trans M1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Row and column operations on ACL2 arrays:

(defthm
  Ri<->Rj-loop-guard-hack
  (IMPLIES (AND (< K (CADR (DIMENSIONS '$ARG M)))
		(< I (CAR (DIMENSIONS '$ARG M)))
		(<= 0 K)
		(<= 0 I)
		(INTEGERP I)
		(integerp k)
		(ARRAY2P '$ARG M)
		(SYMBOLP NAME))
	   (ARRAY2P NAME
		    (ASET2 '$ARG
			   M
			   I
			   K
			   (AREF2 '$ARG M J K))))
  :hints (("Goal"
	   :in-theory (disable ARRAY2P-ASET2)
	   :use (:instance
		 ARRAY2P-ASET2
		 (L M)
		 (j k)
		 (val (AREF2 '$ARG M J K))))))

(defthm
  Ri<->Rj-loop-guard-hack-1
  (IMPLIES (AND (< K (CADR (DIMENSIONS '$ARG M)))
		(< J (CAR (DIMENSIONS '$ARG M)))
		(< I (CAR (DIMENSIONS '$ARG M)))
		(<= 0 K)
		(<= 0 J)
		(<= 0 I)
		(INTEGERP J)
		(INTEGERP I)
		(integerp k)
		(ARRAY2P NAME M))
	   (ARRAY2P NAME
		    (ASET2 '$ARG
			   (ASET2 '$ARG
				  M
				  I
				  K
				  (AREF2 '$ARG M J K))
			   J
			   K
			   (AREF2 '$ARG M I K))))
  :hints (("Goal"
	   :in-theory (disable ARRAY2P-ASET2)
	   :use (:instance
		 ARRAY2P-ASET2
		 (L (ASET2 '$ARG
			   M
			   I
			   K
			   (AREF2 '$ARG M J K)))
		 (i j)
		 (j k)
		 (val (AREF2 '$ARG M I K))))))

(defun
  Ri<->Rj-loop (name M i j k)
  (declare (xargs :guard (and (array2p name M)
			      (integerp i)
			      (integerp j)
			      (integerp k)
			      (>= i 0)
			      (>= j 0)
			      (>= k 0)
			      (let* ((dims (dimensions name M))
				     (dims1 (first dims))
				     (dims2 (second dims)))
				   (and (< i dims1)
					(< j dims1)
					(< k dims2))))))
  (if (zp k)
      (let ((temp (aref2 name M i 0)))
	   (aset2 name
		  (aset2 name
			 M
			 i
			 0
			 (aref2 name
				M
				j
				0))
		  j
		  0
		  temp))
      (Ri<->Rj-loop name
		    (let ((temp (aref2 name M i k)))
		         (aset2 name
				(aset2 name
				       M
				       i
				       k
				       (aref2 name
					      M
					      j
					      k))
				j
				k
				temp))
		    i
		    j
		    (- k 1))))

(defun
  Ri<->Rj (name M i j)
  "Return the result of interchanging
   row i and row j in array M."
  (declare (xargs :guard (and (array2p name M)
			      (integerp i)
			      (integerp j)
			      (/= i j)
			      (>= i 0)
			      (>= j 0)
			      (let* ((dims (dimensions name M))
				     (dims1 (first dims)))
				   (and (< i dims1)
					(< j dims1))))))
  (Ri<->Rj-loop name
		M
		i
		j
		(- (second (dimensions name M)) 1)))

(defthm
  Ci<->Cj-loop-guard-hack
  (IMPLIES (AND (< K (CAR (DIMENSIONS '$ARG M)))
		(< I (CADR (DIMENSIONS '$ARG M)))
		(<= 0 K)
		(<= 0 I)
		(INTEGERP I)
		(integerp k)
		(ARRAY2P '$ARG M)
		(SYMBOLP NAME))
	   (ARRAY2P NAME
		    (ASET2 '$ARG
			   M
			   K
			   I
			   (AREF2 '$ARG M K J))))
  :hints (("Goal"
	   :in-theory (disable ARRAY2P-ASET2)
	   :use (:instance
		 ARRAY2P-ASET2
		 (L M)
		 (i k)
		 (j i)
		 (val (AREF2 '$ARG M K j))))))

(defthm
  Ci<->Cj-loop-guard-hack-1
  (IMPLIES (AND (< K (CAR (DIMENSIONS '$ARG M)))
		(< J (CADR (DIMENSIONS '$ARG M)))
		(< I (CADR (DIMENSIONS '$ARG M)))
		(<= 0 K)
		(<= 0 J)
		(<= 0 I)
		(INTEGERP J)
		(INTEGERP I)
		(integerp k)
		(ARRAY2P NAME M))
	   (ARRAY2P NAME
		    (ASET2 '$ARG
			   (ASET2 '$ARG
				  M
				  K
				  I
				  (AREF2 '$ARG M K J))
			   K
			   J
			   (AREF2 '$ARG M K I))))
  :hints (("Goal"
	   :in-theory (disable ARRAY2P-ASET2)
	   :use (:instance
		 ARRAY2P-ASET2
		 (L (ASET2 '$ARG
			   M
			   K
			   I
			   (AREF2 '$ARG M K J)))
		 (i k)
		 (val (AREF2 '$ARG M K i))))))

(defun
  Ci<->Cj-loop (name M i j k)
  (declare (xargs :guard (and (array2p name M)
			      (integerp i)
			      (integerp j)
			      (integerp k)
			      (>= i 0)
			      (>= j 0)
			      (>= k 0)
			      (let* ((dims (dimensions name M))
				     (dims1 (first dims))
				     (dims2 (second dims)))
				   (and (< i dims2)
					(< j dims2)
					(< k dims1))))))
  (if (zp k)
      (let ((temp (aref2 name M 0 i)))
	   (aset2 name
		  (aset2 name
			 M
			 0
			 i
			 (aref2 name
				M
				0
				j))
		  0
		  j
		  temp))
      (Ci<->Cj-loop name
		    (let ((temp (aref2 name M k i)))
		         (aset2 name
				(aset2 name
				       M
				       k
				       i
				       (aref2 name
					      M
					      k
					      j))
				k
				j
				temp))
		    i
		    j
		    (- k 1))))

(defun
  Ci<->Cj (name M i j)
  "Return the result of interchanging
   column i and column j in array M."
  (declare (xargs :guard (and (array2p name M)
			      (integerp i)
			      (integerp j)
			      (/= i j)
			      (>= i 0)
			      (>= j 0)
			      (let* ((dims (dimensions name M))
				     (dims2 (second dims)))
				   (and (< i dims2)
					(< j dims2))))))
  (Ci<->Cj-loop name
		M
		i
		j
		(- (first (dimensions name M)) 1)))

(defthm
  Ri<-aRi-loop-guard-hack
  (IMPLIES (AND (< K (CADR (DIMENSIONS '$ARG M)))
		(< I (CAR (DIMENSIONS '$ARG M)))
		(<= 0 K)
		(<= 0 I)
		(INTEGERP I)
		(integerp k)
		(ARRAY2P NAME M))
	   (ARRAY2P NAME (ASET2 '$ARG M I K 0)))
  :hints (("Goal"
	   :in-theory (disable array2p-aset2)
	   :use (:instance
		 array2p-aset2
		 (L M)
		 (j k)
		 (val 0)))))

(defthm
  Ri<-aRi-loop-guard-hack-1
  (IMPLIES (AND (< K (CADR (DIMENSIONS '$ARG M)))
		(< I (CAR (DIMENSIONS '$ARG M)))
		(<= 0 K)
		(<= 0 I)
		(integerp k)
		(INTEGERP I)
		(ARRAY2P NAME M))
	   (ARRAY2P NAME
		    (ASET2 '$ARG
			   M
			   I
			   K
			   (* A (AREF2 '$ARG M I K)))))
  :hints (("Goal"
	   :in-theory (disable array2p-aset2)
	   :use (:instance
		 array2p-aset2
		 (L M)
		 (j k)
		 (val (* A (AREF2 '$ARG M I K)))))))

(defun
  Ri<-aRi-loop (name M a i k)
  (declare (xargs :guard (and (acl2-numberp a)
			      (array2p name M)
			      (integerp i)
			      (integerp k)
			      (>= i 0)
			      (>= k 0)
			      (let ((dims (dimensions name M)))
				   (and (< i (first dims))
					(< k (second dims)))))))
  (if (zp k)
      (aset2 name
	     M
	     i
	     0
	     (* a (fix (aref2 name
			      M
			      i
			      0))))
    (Ri<-aRi-loop name
		  (aset2 name
			 M
			 i
			 k
			 (* a (fix (aref2 name
					  M
					  i
					  k))))
		  a
		  i
		  (- k 1))))

(defun
  Ri<-aRi (name M a i)
  "Return the result of replacing each element,
   Mij, in row i of array M, with (* a Mij)."
  (declare (xargs :guard (and (acl2-numberp a)
			      (array2p name M)
			      (integerp i)
			      (>= i 0)
			      (< i (first (dimensions name M))))))
  (Ri<-aRi-loop name
		M
		a
		i
		(- (second (dimensions name M)) 1)))

(defun
  Ci<-aCi-loop (name M a i k)
  (declare (xargs :guard (and (acl2-numberp a)
			      (array2p name M)
			      (integerp i)
			      (integerp k)
			      (>= i 0)
			      (>= k 0)
			      (let* ((dims (dimensions name M))
				     (dims1 (first dims))
				     (dims2 (second dims)))
				   (and (< i dims2)
					(< k dims1))))))

  (if (zp k)
      (aset2 name
	     M
	     0
	     i
	     (* a (fix (aref2 name
			      M
			      0
			      i))))
    (Ci<-aCi-loop name
		  (aset2 name
			 M
			 k
		         i
			 (* a (fix (aref2 name
					  M
					  k
					  i))))
		  a
		  i
		  (- k 1))))

(defun
  Ci<-aCi (name M a i)
  "Return the result of replacing each element,
   Mji, in column i of array M, with (* a Mji)."
  (declare (xargs :guard (and (acl2-numberp a)
			      (array2p name M)
			      (integerp i)
			      (>= i 0)
			      (< i (second (dimensions name M))))))
  (Ci<-aCi-loop name
		M
		a
		i
		(- (first (dimensions name M)) 1)))

(defthm
  Rj<-aRi+Rj-loop-guard-hack
  (IMPLIES (AND (< K (CADR (DIMENSIONS '$ARG M)))
		(< J (CAR (DIMENSIONS '$ARG M)))
		(<= 0 K)
		(<= 0 J)
		(INTEGERP J)
		(integerp k)
		(ARRAY2P NAME M))
	  (ARRAY2P NAME
		   (ASET2 '$ARG
			  M
			  J
			  K
			  (* A (AREF2 '$ARG M I K)))))
 :hints (("Goal"
	   :in-theory (disable array2p-aset2)
	   :use (:instance
		 array2p-aset2
		 (L M)
		 (i j)
		 (j k)
		 (val (* A (AREF2 '$ARG M I K)))))))

(defthm
  Rj<-aRi+Rj-loop-guard-hack-1
  (IMPLIES (AND (< K (CADR (DIMENSIONS '$ARG M)))
		(< J (CAR (DIMENSIONS '$ARG M)))
		(<= 0 K)
		(<= 0 J)
		(INTEGERP J)
		(integerp k)
		(ARRAY2P NAME M))
	   (ARRAY2P NAME
		    (ASET2 '$ARG
			   M
			   J
			   K
			   (+ (AREF2 '$ARG M J K)
			      (* A (AREF2 '$ARG M I K))))))
  :hints (("Goal"
	   :in-theory (disable array2p-aset2)
	   :use (:instance
		 array2p-aset2
		 (L M)
		 (i j)
		 (j k)
		 (val (+ (AREF2 '$ARG M J K)
			 (* A (AREF2 '$ARG M I K))))))))

(defun
  Rj<-aRi+Rj-loop (name M a i j k)
  (declare (xargs :guard (and (acl2-numberp a)
			      (array2p name M)
			      (integerp i)
			      (integerp j)
			      (integerp k)
			      (>= i 0)
			      (>= j 0)
			      (>= k 0)
			      (let* ((dims (dimensions name M))
				     (dims1 (first dims)))
				    (and (< i dims1)
					 (< j dims1)
					 (< k (second dims)))))))
  (if (zp k)
      (aset2 name
	     M
	     j
	     0
	     (+ (* a (fix (aref2 name
				 M
				 i
				 0)))
		(fix (aref2 name
			    M
			    j
			    0))))
    (Rj<-aRi+Rj-loop name
		     (aset2 name
			    M
			    j
			    k
			    (+ (* a (fix (aref2 name
						M
						i
						k)))
			       (fix (aref2 name
					   M
					   j
					   k))))
		     a
		     i
		     j
		     (- k 1))))

(defun
  Rj<-aRi+Rj (name M a i j)
  "Return the result of replacing each element,
   Mjk, in row j of matrix M, with (+ (* a Mik) Mjk)."
  (declare (xargs :guard (and (acl2-numberp a)
			      (array2p name M)
			      (integerp i)
			      (integerp j)
			      (/= i j)
			      (>= i 0)
			      (>= j 0)
			      (let* ((dims (dimensions name M))
				     (dims1 (first dims)))
				    (and (< i dims1)
					 (< j dims1))))))
  (Rj<-aRi+Rj-loop name
		   M
		   a
		   i
		   j
		   (- (second (dimensions name M)) 1)))

(defthm
  Cj<-aCi+Cj-loop-guard-hack
  (IMPLIES (AND (< K (CAR (DIMENSIONS '$ARG M)))
		(< J (CADR (DIMENSIONS '$ARG M)))
		(<= 0 K)
		(<= 0 J)
		(INTEGERP J)
		(integerp k)
		(ARRAY2P NAME M))
	   (ARRAY2P NAME
		    (ASET2 '$ARG
			   M
			   K
			   J
			   (* A (AREF2 '$ARG M K I)))))
  :hints (("Goal"
	   :in-theory (disable array2p-aset2)
	   :use (:instance
		 array2p-aset2
		 (L M)
		 (i k)
		 (val (* A (AREF2 '$ARG M K i)))))))

(defthm
  Cj<-aCi+Cj-loop-guard-hack-1
  (IMPLIES (AND (< K (CAR (DIMENSIONS '$ARG M)))
		(< J (CADR (DIMENSIONS '$ARG M)))
		(< I (CADR (DIMENSIONS '$ARG M)))
		(<= 0 K)
		(<= 0 J)
		(<= 0 I)
		(INTEGERP J)
		(INTEGERP I)
		(integerp k)
		(ARRAY2P NAME M))
	  (ARRAY2P NAME
		   (ASET2 '$ARG
			  M
			  K
			  J
			  (+ (AREF2 '$ARG M K J)
			     (* A (AREF2 '$ARG M K I))))))
  :hints (("Goal"
	   :in-theory (disable array2p-aset2)
	   :use (:instance
		 array2p-aset2
		 (L M)
		 (i k)
		 (val (+ (AREF2 '$ARG M K j)
			 (* A (AREF2 '$ARG M K i))))))))

(defun
  Cj<-aCi+Cj-loop (name M a i j k)
  (declare (xargs :guard (and (acl2-numberp a)
			      (array2p name M)
			      (integerp i)
			      (integerp j)
			      (integerp k)
			      (>= i 0)
			      (>= j 0)
			      (>= k 0)
			      (let* ((dims (dimensions name M))
				     (dims2 (second dims)))
				   (and (< i dims2)
					(< j dims2)
					(< k (first dims)))))))
  (if (zp k)
      (aset2 name
	     M
	     0
	     j
	     (+ (* a (fix (aref2 name
				 M
				 0
				 i)))
		(fix (aref2 name
			    M
			    0
			    j))))
    (Cj<-aCi+Cj-loop name
		     (aset2 name
			    M
			    k
			    j
			    (+ (* a (fix (aref2 name
						M
						k
						i)))
			       (fix (aref2 name
					   M
					   k
					   j))))
		     a
		     i
		     j
		     (- k 1))))

(defun
  Cj<-aCi+Cj (name M a i j)
  "Return the result of replacing each element,
   Mkj, in column j of matrix M, with (+ (* a Mki)
                                         Mkj)."
  (declare (xargs :guard (and (acl2-numberp a)
			      (array2p name M)
			      (integerp i)
			      (integerp j)
			      (/= i j)
			      (>= i 0)
			      (>= j 0)
			      (let* ((dims (dimensions name M))
				     (dims2 (second dims)))
				    (and (< i dims2)
					 (< j dims2))))))

  (Cj<-aCi+Cj-loop name
		   M
		   a
		   i
		   j
		   (- (first (dimensions name M)) 1)))

(local (in-theory (disable ARRAY2P-$ARG-EQUAL-PARTS)))

(defthm
  Ri<->Rj-loop-equal-parts
  (implies (and (alist2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (first (dimensions name M)))
		(< j (first (dimensions name M)))
		(< k (second (dimensions name M))))
	   (and (equal (header name (Ri<->Rj-loop name M i j k))
		       (header name M))
		(equal (dimensions name (Ri<->Rj-loop name M i j k))
		       (dimensions name M))
		(equal (maximum-length name
				       (Ri<->Rj-loop name M i j k))
		       (maximum-length name M))
		(equal (default name (Ri<->Rj-loop name M i j k))
		       (default name M)))))

(defthm
  Ci<->Cj-loop-equal-parts
  (implies (and (alist2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (second (dimensions name M)))
		(< j (second (dimensions name M)))
		(< k (first (dimensions name M))))
	   (and (equal (header name (Ci<->Cj-loop name M i j k))
		       (header name M))
		(equal (dimensions name (Ci<->Cj-loop name M i j k))
		       (dimensions name M))
		(equal (maximum-length name
				       (Ci<->Cj-loop name M i j k))
		       (maximum-length name M))
		(equal (default name (Ci<->Cj-loop name M i j k))
		       (default name M)))))

(defthm
  Ri<-aRi-loop-equal-parts
  (implies (and (alist2p name M)
		(integerp i)
		(>= i 0)
		(< i (first (dimensions name M)))
		(< k (second (dimensions name M))))
	   (and (equal (header name (Ri<-aRi-loop name M a i k))
		       (header name M))
		(equal (dimensions name (Ri<-aRi-loop name M a i k))
		       (dimensions name M))
		(equal (maximum-length name
				       (Ri<-aRi-loop name M a i k))
		       (maximum-length name M))
		(equal (default name (Ri<-aRi-loop name M a i k))
		       (default name M)))))

(defthm
  Ci<-aCi-loop-equal-parts
  (implies (and (alist2p name M)
		(integerp i)
		(>= i 0)
		(< i (second (dimensions name M)))
		(< k (first (dimensions name M))))
	   (and (equal (header name (Ci<-aCi-loop name M a i k))
		       (header name M))
		(equal (dimensions name (Ci<-aCi-loop name M a i k))
		       (dimensions name M))
		(equal (maximum-length name
				       (Ci<-aCi-loop name M a i k))
		       (maximum-length name M))
		(equal (default name (Ci<-aCi-loop name M a i k))
		       (default name M)))))

(defthm
  Rj<-aRi+Rj-loop-equal-parts
  (implies (and (alist2p name M)
		(integerp j)
		(>= j 0)
		(< j (first (dimensions name M)))
		(< k (second (dimensions name M))))
	   (and (equal (header name
			       (Rj<-aRi+Rj-loop name M a i j k))
		       (header name M))
		(equal (dimensions name
				   (Rj<-aRi+Rj-loop name M a i j k))
		       (dimensions name M))
		(equal (maximum-length name
				       (Rj<-aRi+Rj-loop name M a i j k))
		       (maximum-length name M))
		(equal (default name (Rj<-aRi+Rj-loop name M a i j k))
		       (default name M)))))

(defthm
  Cj<-aCi+Cj-loop-equal-parts
  (implies (and (alist2p name M)
		(integerp j)
		(>= j 0)
		(< j (second (dimensions name M)))
		(< k (first (dimensions name M))))
	   (and (equal (header name
			       (Cj<-aCi+Cj-loop name M a i j k))
		       (header name M))
		(equal (dimensions name
				   (Cj<-aCi+Cj-loop name M a i j k))
		       (dimensions name M))
		(equal (maximum-length name
				       (Cj<-aCi+Cj-loop name M a i j k))
		       (maximum-length name M))
		(equal (default name (Cj<-aCi+Cj-loop name M a i j k))
		       (default name M)))))

(defthm
  alist2p-Ri<->Rj-loop
  (implies (and (alist2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (first (dimensions name M)))
		(< j (first (dimensions name M)))
		(< k (second (dimensions name M))))
	   (alist2p name (Ri<->Rj-loop name M i j k))))

(defthm
  array2p-Ri<->Rj-loop
  (implies (and (array2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (first (dimensions name M)))
		(< j (first (dimensions name M)))
		(< k (second (dimensions name M))))
	   (array2p name (Ri<->Rj-loop name M i j k))))

(defthm
  alist2p-Ci<->Cj-loop
  (implies (and (alist2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (second (dimensions name M)))
		(< j (second (dimensions name M)))
		(< k (first (dimensions name M))))
	   (alist2p name (Ci<->Cj-loop name M i j k))))

(defthm
  array2p-Ci<->Cj-loop
  (implies (and (array2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (second (dimensions name M)))
		(< j (second (dimensions name M)))
		(< k (first (dimensions name M))))
	   (array2p name (Ci<->Cj-loop name M i j k))))

(defthm
  alist2p-Ri<-aRi-loop
  (implies (and (alist2p name M)
		(integerp i)
		(>= i 0)
		(< i (first (dimensions name M)))
		(< k (second (dimensions name M))))
	   (alist2p name (Ri<-aRi-loop name M a i k))))

(defthm
  array2p-Ri<-aRi-loop
  (implies (and (array2p name M)
		(integerp i)
		(>= i 0)
		(< i (first (dimensions name M)))
		(< k (second (dimensions name M))))
	   (array2p name (Ri<-aRi-loop name M a i k))))

(defthm
  alist2p-Ci<-aCi-loop
  (implies (and (alist2p name M)
		(integerp i)
		(>= i 0)
		(< i (second (dimensions name M)))
		(< k (first (dimensions name M))))
	   (alist2p name (Ci<-aCi-loop name M a i k))))

(defthm
  array2p-Ci<-aCi-loop
  (implies (and (array2p name M)
		(integerp i)
		(>= i 0)
		(< i (second (dimensions name M)))
		(< k (first (dimensions name M))))
	   (array2p name (Ci<-aCi-loop name M a i k))))

(defthm
  alist2p-Rj<-aRi+Rj-loop
  (implies (and (alist2p name M)
		(integerp j)
		(>= j 0)
		(< j (first (dimensions name M)))
		(< k (second (dimensions name M))))
	   (alist2p name (Rj<-aRi+Rj-loop name M a i j k))))

(defthm
  array2p-Rj<-aRi+Rj-loop
  (implies (and (array2p name M)
		(integerp j)
		(>= j 0)
		(< j (first (dimensions name M)))
		(< k (second (dimensions name M))))
	   (array2p name (Rj<-aRi+Rj-loop name M a i j k))))

(defthm
  alist2p-Cj<-aCi+Cj-loop
  (implies (and (alist2p name M)
		(integerp j)
		(>= j 0)
		(< j (second (dimensions name M)))
		(< k (first (dimensions name M))))
	   (alist2p name (Cj<-aCi+Cj-loop name M a i j k))))

(defthm
  array2p-Cj<-aCi+Cj-loop
  (implies (and (array2p name M)
		(integerp j)
		(>= j 0)
		(< j (second (dimensions name M)))
		(< k (first (dimensions name M))))
	   (array2p name (Cj<-aCi+Cj-loop name M a i j k))))

(local (in-theory (enable ARRAY2P-$ARG-EQUAL-PARTS)))

(defthm
  dimensions-Ri<->Rj
  (implies (and (alist2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (first (dimensions name M)))
		(< j (first (dimensions name M))))
	   (equal (dimensions name (Ri<->Rj name M i j))
		  (dimensions name M))))

(defthm
  dimensions-Ci<->Cj
  (implies (and (alist2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (second (dimensions name M)))
		(< j (second (dimensions name M))))
	   (equal (dimensions name (Ci<->Cj name M i j))
		  (dimensions name M))))

(defthm
  dimensions-Ri<-aRi
  (implies (and (alist2p name M)
		(integerp i)
		(>= i 0)
		(< i (first (dimensions name M))))
	   (equal (dimensions name (Ri<-aRi name M a i))
		  (dimensions name M))))

(defthm
  dimensions-Ci<-aCi
  (implies (and (alist2p name M)
		(integerp i)
		(>= i 0)
		(< i (second (dimensions name M))))
	   (equal (dimensions name (Ci<-aCi name M a i))
		  (dimensions name M))))

(defthm
  dimensions-Rj<-aRi+Rj
  (implies (and (alist2p name M)
		(integerp j)
		(>= j 0)
		(< j (first (dimensions name M))))
	   (equal (dimensions name (Rj<-aRi+Rj name M a i j))
		  (dimensions name M))))

(defthm
  dimensions-Cj<-aCi+Cj
  (implies (and (alist2p name M)
		(integerp j)
		(>= j 0)
		(< j (second (dimensions name M))))
	   (equal (dimensions name (Cj<-aCi+Cj name M a i j))
		  (dimensions name M))))

(defthm
  alist2p-Ri<->Rj
  (implies (and (alist2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (first (dimensions name M)))
		(< j (first (dimensions name M))))
	   (alist2p name (Ri<->Rj name M i j))))

(defthm
  array2p-Ri<->Rj
  (implies (and (array2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (first (dimensions name M)))
		(< j (first (dimensions name M))))
	   (array2p name (Ri<->Rj name M i j))))

(defthm
  alist2p-Ci<->Cj
  (implies (and (alist2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (second (dimensions name M)))
		(< j (second (dimensions name M))))
	   (alist2p name (Ci<->Cj name M i j))))

(defthm
  array2p-Ci<->Cj
  (implies (and (array2p name M)
		(integerp i)
		(integerp j)
		(>= i 0)
		(>= j 0)
		(< i (second (dimensions name M)))
		(< j (second (dimensions name M))))
	   (array2p name (Ci<->Cj name M i j))))

(defthm
  alist2p-Ri<-aRi
  (implies (and (alist2p name M)
		(integerp i)
		(>= i 0)
		(< i (first (dimensions name M))))
	   (alist2p name (Ri<-aRi name M a i))))

(defthm
  array2p-Ri<-aRi
  (implies (and (array2p name M)
		(integerp i)
		(>= i 0)
		(< i (first (dimensions name M))))
	   (array2p name (Ri<-aRi name M a i))))

(defthm
  alist2p-Ci<-aCi
  (implies (and (alist2p name M)
		(integerp i)
		(>= i 0)
		(< i (second (dimensions name M))))
	   (alist2p name (Ci<-aCi name M a i))))

(defthm
  array2p-Ci<-aCi
  (implies (and (array2p name M)
		(integerp i)
		(>= i 0)
		(< i (second (dimensions name M))))
	   (array2p name (Ci<-aCi name M a i))))

(defthm
  alist2p-Rj<-aRi+Rj
  (implies (and (alist2p name M)
		(integerp j)
		(>= j 0)
		(< j (first (dimensions name M))))
	   (alist2p name (Rj<-aRi+Rj name M a i j))))

(defthm
  array2p-Rj<-aRi+Rj
  (implies (and (array2p name M)
		(integerp j)
		(>= j 0)
		(< j (first (dimensions name M))))
	   (array2p name (Rj<-aRi+Rj name M a i j))))

(defthm
  alist2p-Cj<-aCi+Cj
  (implies (and (alist2p name M)
		(integerp j)
		(>= j 0)
		(< j (second (dimensions name M))))
	   (alist2p name (Cj<-aCi+Cj name M a i j))))

(defthm
  array2p-Cj<-aCi+Cj
  (implies (and (array2p name M)
		(integerp j)
		(>= j 0)
		(< j (second (dimensions name M))))
	   (array2p name (Cj<-aCi+Cj name M a i j))))

(in-theory (disable Ri<->Rj
		    Ci<->Cj
		    Ri<-aRi
		    Ci<-aCi
		    Rj<-aRi+Rj
		    Cj<-aCi+Cj))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Matrix inverse and determinant:

;; Description of algorithm for computing the
;;  inverse and determinant.

;; Input a square matrix M.

;; let A <- I
;;     B <- I
;;     C <- M
;;     D <- 1

;; Row reduce C to I.
;;   Apply same row operations to B.
;;   Multiply A successively on right by
;;        inverse of same row operations.
;;        (Done with equivalent column operations.)
;;   Modify D according to column operations on A.
;;       Ci<->Cj:    D <- -1 * D
;;       Ci<-aCi:    D <-  a * D
;;       Cj<-aCi+Cj: D <-  D

;; Invariants
;;      A * B = I
;;      B * M = C
;;      D = determinant of A

;;   After termination
;;      A = left inverse of B
;;      B = left inverse of M (because C contains I
;;                                after termination)

;; Prove that after termination A = M:
;;      A = A * I = A * (B * M)
;;                = (A * B) * M = I * M = M

;; Thus B is both left and right inverse of M
;;      and D is the determinant of M.

;; Inverse row operations:
;;   (Ri<->Rj)^(-1)    = Ri<->Rj
;;   (Ri<-aRi)^(-1)    = Ri<-(/a)Ri
;;   (Rj<-aRi+Rj)^(-1) = Rj<-(-a)Ri+Rj

;; Equivalent row and column operations as
;;  applied to identity matrix: I
;;    Ri<->Rj(I)    = Ci<->Cj(I)
;;    Ri<-aRi(I)    = Ci<-aCi(I)
;;    Rj<-aRi+Rj(I) = Ci<-aCj+Ci(I)

;; Row operation applied to M is the same as
;;     multiplying M on the LEFT by the result
;;     of applying the same operation to I.

;; Column operation applied to M is the same as
;;     multiplying M on the RIGHT by the result
;;     of applying the same operation to I.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun
  zero-column (A B C i1 j i)
  "For k = i downto 0,
    when k differs from i1 and (aref2 '$C C k j) is a nonzero number then
     replace column i1 in A with (aref2 '$C C k j) * column k + column i1,
     replace row k in B with (- (aref2 '$C C k j)) * row i1 + row k,
     replace row k in C with (- (aref2 '$C C k j)) * row i1 + row k.
   When (aref2 '$C C i1 j) = 1, then all other entries in the jth
   column of C are modified to 0."
  (declare (xargs :guard (and (array2p '$a A)
			      (array2p '$b B)
			      (array2p '$c C)
			      (integerp i)
			      (>= i 0)
			      (integerp i1)
			      (>= i1 0)
			      (integerp j)
			      (>= j 0)
			      (< i (second
				    (dimensions '$a
						A)))
			      (< i (first
				    (dimensions '$b
						B)))
			      (< i (first
				    (dimensions '$c
						C)))
			      (< i1 (second
				     (dimensions '$a
						 A)))
			      (< i1 (first
				     (dimensions '$b
						 B)))
			      (< i1 (first
				     (dimensions '$c
						 C)))
			      (< j (second
				    (dimensions '$c
						C))))))
  (if (zp i)
      (if (not (zp i1))
	  (let ((val (fix (aref2 '$C C 0 j))))
	       (if (= val 0)
		   (mv A B C)
		   (mv (Cj<-aCi+Cj '$A A val     0 i1)
		       (Rj<-aRi+Rj '$B B (- val) i1 0)
		       (Rj<-aRi+Rj '$C C (- val) i1 0))))
	  (mv A B C))
      (if (not (equal i i1))
	  (let ((val (fix (aref2 '$C C i j))))
	       (if (= val 0)
		   (zero-column A B C i1 j (- i 1))
		   (zero-column (Cj<-aCi+Cj '$A A val     i i1)
				(Rj<-aRi+Rj '$B B (- val) i1 i)
				(Rj<-aRi+Rj '$C C (- val) i1 i)
				i1
				j
				(- i 1))))
	  (zero-column A B C i1 j (- i 1)))))

(defthm
  dimensions-RJ<-ARI+RJ-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP J)
		(>= J 0)
		(< J (FIRST (DIMENSIONS NAME M))))
	   (EQUAL (DIMENSIONS NAME (RJ<-ARI+RJ NAME1 M A I J))
		  (DIMENSIONS NAME M)))
  :hints (("Goal"
	   :in-theory (disable dimensions-RJ<-ARI+RJ)
	   :use (:instance
		 dimensions-RJ<-ARI+RJ
		 (name name1)))))

(DEFTHM
  DIMENSIONS-CJ<-ACI+CJ-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP J)
		(>= J 0)
		(< J (SECOND (DIMENSIONS NAME M))))
	   (EQUAL (DIMENSIONS NAME (CJ<-ACI+CJ NAME1 M A I J))
		  (DIMENSIONS NAME M)))
  :hints (("Goal"
	   :in-theory (disable dimensions-CJ<-ACI+CJ)
	   :use (:instance
		 dimensions-CJ<-ACI+CJ
		 (name name1)))))

(DEFTHM
  ALIST2P-RJ<-ARI+RJ-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP J)
		(>= J 0)
		(< J (FIRST (DIMENSIONS NAME M))))
	   (ALIST2P NAME (RJ<-ARI+RJ NAME1 M A I J)))
  :hints (("Goal"
	   :in-theory (disable ALIST2P-RJ<-ARI+RJ)
	   :use (:instance
		 ALIST2P-RJ<-ARI+RJ
		 (name name1)))))

(DEFTHM
  ALIST2P-CJ<-ACI+CJ-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP J)
		(>= J 0)
		(< J (SECOND (DIMENSIONS NAME M))))
	   (ALIST2P NAME (CJ<-ACI+CJ NAME1 M A I J)))
  :hints (("Goal"
	   :in-theory (disable ALIST2P-CJ<-ACI+CJ)
	   :use (:instance
		 ALIST2P-CJ<-ACI+CJ
		 (name name1)))))

(DEFTHM
  ARRAY2P-RJ<-ARI+RJ-1
  (IMPLIES (AND (symbolp name1)
		(ARRAY2P NAME M)
		(INTEGERP J)
		(>= J 0)
		(< J (FIRST (DIMENSIONS NAME M))))
	   (ARRAY2P NAME (RJ<-ARI+RJ NAME1 M A I J)))
  :hints (("Goal"
	   :in-theory (disable Array2P-RJ<-ARI+RJ)
	   :use (:instance
		 Array2P-RJ<-ARI+RJ
		 (name name1)))))

(DEFTHM
  ARRAY2P-CJ<-ACI+CJ-1
  (IMPLIES (AND (symbolp name1)
		(ARRAY2P NAME M)
		(INTEGERP J)
		(>= J 0)
		(< J (SECOND (DIMENSIONS NAME M))))
	   (ARRAY2P NAME (CJ<-ACI+CJ NAME1 M A I J)))
  :hints (("Goal"
	   :in-theory (disable Array2P-CJ<-ACI+CJ)
	   :use (:instance
		 Array2P-CJ<-ACI+CJ
		 (name name1)))))

(defthm
  dimensions-zero-column-A
  (implies (and (alist2p name A)
		(integerp i1)
		(>= i1 0)
		(< i1 (second (dimensions name A))))
	   (equal (dimensions name (car (zero-column A B C i1 j i)))
		  (dimensions name A))))

(defthm
  alist2p-zero-column-A
  (implies (and (alist2p name A)
		(integerp i1)
		(>= i1 0)
		(< i1 (second (dimensions name A))))
	   (alist2p name (car (zero-column A B C i1 j i)))))

(defthm
  array2p-zero-column-A
  (implies (and (array2p name A)
		(integerp i1)
		(>= i1 0)
		(< i1 (second (dimensions name A))))
	   (array2p name (car (zero-column A B C i1 j i)))))

(defthm
  dimensions-zero-column-B
  (implies (and (alist2p name B)
		(< i (first (dimensions name B))))
	   (equal (dimensions name (cadr (zero-column A B C i1 j i)))
		  (dimensions name B))))

(defthm
  alist2p-zero-column-B
  (implies (and (alist2p name B)
		(< i (first (dimensions name B))))
	   (alist2p name (cadr (zero-column A B C i1 j i)))))

(defthm
  array2p-zero-column-B
  (implies (and (array2p name B)
		(< i (first (dimensions name B))))
	   (array2p name (cadr (zero-column A B C i1 j i)))))

(defthm
  dimensions-zero-column-C
  (implies (and (alist2p name C)
		(< i (first (dimensions name C))))
	   (equal (dimensions name (caddr (zero-column A B C i1 j i)))
		  (dimensions name C))))

(defthm
  alist2p-zero-column-C
  (implies (and (alist2p name C)
		(< i (first (dimensions name C))))
	   (alist2p name (caddr (zero-column A B C i1 j i)))))

(defthm
  array2p-zero-column-C
  (implies (and (array2p name C)
		(< i (first (dimensions name C))))
	   (array2p name (caddr (zero-column A B C i1 j i)))))

(defun
  find-non-zero-col (name C i j k)
  "Determine if there is a nonzero value among
   C(i k), C(i+1) k), . . . , C(j k).
   If not, return nil, otherwise return the
   first n such that C(n k) is nonzero."
  (declare (xargs :measure (let ((i (nfix i))
				 (j (nfix j)))
			        (if (> i j)
				    0
				    (- (+ j 1) i)))
		  :guard (and (array2p name C)
			      (integerp i)
			      (integerp j)
			      (integerp k)
			      (>= k 0)
			      (< j (first
				    (dimensions name
						C)))
			      (< k (second
				    (dimensions name
						C))))))
  (let ((i (nfix i))
	(j (nfix j)))
       (cond ((> i j) nil)
	     ((zerop (fix (aref2 name C i k)))
	      (find-non-zero-col name C (+ i 1) j k))
	     (t i))))

(defthm
  find-non-zero-col-inequality
  (implies (>= j 0)
	   (<= (find-non-zero-col name C i j k)
	       j))
  :rule-classes (:rewrite :linear))

(defthm
  find-non-zero-col-inequality-1
  (implies (and (find-non-zero-col name C i j k)
		(integerp i))
	   (>= (find-non-zero-col name C i j k)
	       i))
  :rule-classes (:rewrite :linear))

(defthm
  aref2-find-non-zero-col
  (implies (find-non-zero-col name C i j k)
	   (and (acl2-numberp
		 (aref2 name
			C
			(find-non-zero-col name
					   C
					   i
					   j
					   k)
			k))
		(not (equal
		      (aref2 name
			     C
			     (find-non-zero-col name
						C
						i
						j
						k)
			     k)
		      0))))
  :rule-classes :type-prescription)

(defun
  find-non-zero-col-1 (name C i j k n)
  "Determine if there is a nonzero value among
     C(i k)    C(i k+1)  . . .  C(i n)
   C(i+1) k)  C(i+1 k+1) . . . C(i+1 n)
       .          .      .        .
       .          .        .      .
       .          .          .    .
     C(j k)    C(j k+1)  . . .  C(j n)
   If not, return nil, otherwise return the
   first, obtained by searching column by column,
   pair p q, such that C(p q) is nonzero."
  (declare (xargs :measure (let ((k (nfix k))
				 (n (nfix n)))
			        (if (> k n)
				    0
				    (- (+ n 1) k)))
		  :guard (and (array2p name C)
			      (integerp i)
			      (integerp j)
			      (integerp k)
			      (integerp n)
			      (< j (first (dimensions name C)))
			      (< n (second (dimensions name C))))))
  (let ((k (nfix k))
	(n (nfix n)))
       (if (> k n)
	   nil
	   (let ((p (find-non-zero-col name C i j k)))
	        (if p
		    (list p k)
		    (find-non-zero-col-1 name
					 C
					 i
					 j
					 (+ k 1)
					 n))))))

(defthm
  natp-car-find-non-zero-col-1
  (implies (find-non-zero-col-1 name C i j k n)
	   (and (integerp (car (find-non-zero-col-1 name C i j k n)))
		(>= (car (find-non-zero-col-1 name C i j k n)) 0)))
  :rule-classes :type-prescription)

(defthm
  natp-cadr-find-non-zero-col-1
  (implies (find-non-zero-col-1 name C i j k n)
	   (and (integerp (cadr (find-non-zero-col-1 name C i j k n)))
		(>= (cadr (find-non-zero-col-1 name C i j k n)) 0)))
  :rule-classes :type-prescription)

(defthm
  find-non-zero-col-1-inequality
  (implies (>= j 0)
	   (<= (first (find-non-zero-col-1 name C i j k n))
	       j))
  :rule-classes (:rewrite :linear))

(defthm
  find-non-zero-col-1-inequality-1
  (implies (and (find-non-zero-col-1 name C i j k n)
		(integerp i))
	   (>= (first (find-non-zero-col-1 name C i j k n))
	       i))
  :rule-classes (:rewrite :linear))

(defthm
  find-non-zero-col-1-inequality-2
  (implies (and (>= n 0))
	   (<= (second (find-non-zero-col-1 name C i j k n))
	       n))
  :rule-classes (:rewrite :linear))

(defthm
  find-non-zero-col-1-inequality-3
  (implies (and (find-non-zero-col-1 name C i j k n)
		(integerp k))
	   (>= (second (find-non-zero-col-1 name C i j k n))
	       k))
  :rule-classes (:rewrite :linear))

(defthm
  type-aref2-find-non-zero-col-1
  (implies (find-non-zero-col-1 name1 C i j k n)
	   (and (acl2-numberp
		 (aref2 name
			C
			(car
			 (find-non-zero-col-1 name1
					      C
					      i
					      j
					      k
					      n))
			(cadr
			 (find-non-zero-col-1 name1
					      C
					      i
					      j
					      k
					      n))))
		(not
		 (equal
		  (aref2 name
			 C
			 (car
			  (find-non-zero-col-1 name1
					       C
					       i
					       j
					       k
					       n))
			 (cadr
			  (find-non-zero-col-1 name1
					       C
					       i
					       j
					       k
					       n)))
		  0))))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :do-not '(generalize))))

(DEFTHM
  DIMENSIONS-RI<-ARI-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP I)
		(>= I 0)
		(< I (FIRST (DIMENSIONS NAME M))))
	   (EQUAL (DIMENSIONS NAME (RI<-ARI NAME1 M A I))
		  (DIMENSIONS NAME M)))
  :hints (("Goal"
	   :in-theory (disable DIMENSIONS-RI<-ARI)
	   :use (:instance
		 DIMENSIONS-RI<-ARI
		 (name name1)))))

(DEFTHM
  DIMENSIONS-CI<-ACI-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP I)
		(>= I 0)
		(< I (SECOND (DIMENSIONS NAME M))))
	   (EQUAL (DIMENSIONS NAME (CI<-ACI NAME1 M A I))
		  (DIMENSIONS NAME M)))
  :hints (("Goal"
	   :in-theory (disable DIMENSIONS-CI<-ACI)
	   :use (:instance
		 DIMENSIONS-CI<-ACI
		 (name name1)))))

(DEFTHM
  DIMENSIONS-RI<->RJ-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP I)
		(INTEGERP J)
		(>= I 0)
		(>= J 0)
		(< I (FIRST (DIMENSIONS NAME M)))
		(< J (FIRST (DIMENSIONS NAME M))))
	   (EQUAL (DIMENSIONS NAME (RI<->RJ NAME1 M I J))
		  (DIMENSIONS NAME M)))
  :hints (("Goal"
	   :in-theory (disable DIMENSIONS-RI<->RJ)
	   :use (:instance
		 DIMENSIONS-RI<->RJ
		 (name name1)))))

(DEFTHM
  DIMENSIONS-CI<->CJ-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP I)
		(INTEGERP J)
		(>= I 0)
		(>= J 0)
		(< I (SECOND (DIMENSIONS NAME M)))
		(< J (SECOND (DIMENSIONS NAME M))))
	   (EQUAL (DIMENSIONS NAME (CI<->CJ NAME1 M I J))
		  (DIMENSIONS NAME M)))
  :hints (("Goal"
	   :in-theory (disable DIMENSIONS-CI<->CJ)
	   :use (:instance
		 DIMENSIONS-CI<->CJ
		 (name name1)))))

(defthm
  lemma-32-hack
  (IMPLIES (AND (< J (CADR (DIMENSIONS '$ARG A)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$A A)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< (+ 1 I)
	      (CADR
	       (DIMENSIONS
		'$a
		(CAR (ZERO-COLUMN
		      (CI<-ACI '$A
			       (CI<->CJ '$A
					A
					I
					(CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (AREF2 '$ARG
				      C
				      (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				      (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       I)
		      (RI<-ARI '$B
			       (RI<->RJ '$B
					B
					I
					(CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (/ (AREF2 '$ARG
					 C
					 (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					 (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			       I)
		      (RI<-ARI '$C
			       (RI<->RJ '$C
					C
					I
					(CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (/ (AREF2 '$ARG
					 C
					 (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					 (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			       I)
		      I
		      (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))
		      J))))))
  :rule-classes nil)

(defthm
  lemma-32-hack-1
  (IMPLIES (AND (< J (CADR (DIMENSIONS '$ARG A)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$A A)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< (+ 1 I)
	      (CADR
	       (DIMENSIONS
		'$arg
		(CAR (ZERO-COLUMN
		      (CI<-ACI '$A
			       (CI<->CJ '$A
					A
					I
					(CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (AREF2 '$ARG
				      C
				      (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				      (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       I)
		      (RI<-ARI '$B
			       (RI<->RJ '$B
					B
					I
					(CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (/ (AREF2 '$ARG
					 C
					 (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					 (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			       I)
		      (RI<-ARI '$C
			       (RI<->RJ '$C
					C
					I
					(CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (/ (AREF2 '$ARG
					 C
					 (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					 (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			       I)
		      I
		      (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))
		      J))))))
  :hints (("Goal"
	   :in-theory (disable NATP-CAR-FIND-NON-ZERO-COL-1)
	   :use lemma-32-hack)))

(defthm
  lemma-23-hack
  (IMPLIES (AND (< J (CADR (DIMENSIONS '$ARG A)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP J)
		(INTEGERP I)
		(ARRAY2P '$A A)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< J
	      (CADR
	       (DIMENSIONS
		'$A
		(CAR (ZERO-COLUMN
		      (CI<-ACI '$A
			       (CI<->CJ '$A
					A
					I
					(CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (AREF2 '$ARG
				      C
				      (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				      (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       I)
		      (RI<-ARI '$B
			       (RI<->RJ '$B
					B
					I
					(CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (/ (AREF2 '$ARG
					 C
					 (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					 (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			       I)
		      (RI<-ARI '$C
			       (RI<->RJ '$C
                                C
				I
                                (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (/ (AREF2 '$ARG
					 C
					 (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					 (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			       I)
		      I
		      (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))
		      J))))))
  :rule-classes nil)

(defthm
  lemma-23-hack-1
  (IMPLIES (AND (< J (CADR (DIMENSIONS '$ARG A)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP J)
		(INTEGERP I)
		(ARRAY2P '$A A)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< J
	      (CADR
	       (DIMENSIONS
		'$arg
		(CAR (ZERO-COLUMN
		      (CI<-ACI '$A
			       (CI<->CJ '$A
					A
					I
					(CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (AREF2 '$ARG
				      C
				      (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				      (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       I)
		      (RI<-ARI '$B
			       (RI<->RJ '$B
					B
					I
					(CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (/ (AREF2 '$ARG
					 C
					 (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					 (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			       I)
		      (RI<-ARI '$C
			       (RI<->RJ '$C
                                C
				I
                                (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			       (/ (AREF2 '$ARG
					 C
					 (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					 (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			       I)
		      I
		      (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))
		      J))))))
  :hints (("Goal"
	   :in-theory (disable NATP-CAR-FIND-NON-ZERO-COL-1)
	   :use lemma-23-hack)))

(defthm
  lemma-19-hack
  (IMPLIES (AND (< J (CADR (DIMENSIONS '$ARG A)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$A A)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< J
	      (CADR
	       (DIMENSIONS '$A
			   (CI<-ACI '$A
				    (CI<->CJ '$A
					     A
					     I
					     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
				    (AREF2 '$ARG
					   C
					   (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					   (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
				    I)))))
  :rule-classes nil)

(defthm
  lemma-19-hack-1
  (IMPLIES (AND (< J (CADR (DIMENSIONS '$ARG A)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$A A)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< J
	      (CADR
	       (DIMENSIONS '$Arg
			   (CI<-ACI '$A
				    (CI<->CJ '$A
					     A
					     I
					     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
				    (AREF2 '$ARG
					   C
					   (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					   (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
				    I)))))
  :hints (("Goal"
	   :in-theory (disable NATP-CAR-FIND-NON-ZERO-COL-1)
	   :use lemma-19-hack)))

(defthm
  lemma-18-hack
  (IMPLIES (AND (< J (CAR (DIMENSIONS '$ARG B)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$B B)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< I
	      (CAR (DIMENSIONS
		    '$B
		    (RI<-ARI '$B
			     (RI<->RJ '$B
				      B
				      I
				      (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			     (/ (AREF2 '$ARG
				       C
				       (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				       (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			     I)))))
  :rule-classes nil)

(defthm
  lemma-18-hack-1
  (IMPLIES (AND (< J (CAR (DIMENSIONS '$ARG B)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$B B)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< I
	      (CAR (DIMENSIONS
		    '$arg
		    (RI<-ARI '$B
			     (RI<->RJ '$B
				      B
				      I
				      (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			     (/ (AREF2 '$ARG
				       C
				       (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				       (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			     I)))))
  :hints (("Goal"
	   :in-theory (disable NATP-CAR-FIND-NON-ZERO-COL-1)
	   :use lemma-18-hack)))

(defthm
  lemma-16-hack
  (IMPLIES (AND (< J (CAR (DIMENSIONS '$ARG B)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$B B)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< J
	      (CAR
	       (DIMENSIONS
		'$b
		(CADR
		 (ZERO-COLUMN
		  (CI<-ACI '$A
			   (CI<->CJ '$A
				    A
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (AREF2 '$ARG
				  C
				  (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				  (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   I)
		  (RI<-ARI '$B
			   (RI<->RJ '$B
				    B
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (/ (AREF2 '$ARG
				     C
				     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				     (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			   I)
		  (RI<-ARI '$C
			   (RI<->RJ '$C
				    C
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (/ (AREF2 '$ARG
				     C
				     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				     (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			   I)
		  I
		  (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))
		  J))))))
  :rule-classes nil)

(defthm
  lemma-16-hack-1
  (IMPLIES (AND (< J (CAR (DIMENSIONS '$ARG B)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$B B)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< J
	      (CAR
	       (DIMENSIONS
		'$arg
		(CADR
		 (ZERO-COLUMN
		  (CI<-ACI '$A
			   (CI<->CJ '$A
				    A
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (AREF2 '$ARG
				  C
				  (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				  (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   I)
		  (RI<-ARI '$B
			   (RI<->RJ '$B
				    B
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (/ (AREF2 '$ARG
				     C
				     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				     (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			   I)
		  (RI<-ARI '$C
			   (RI<->RJ '$C
				    C
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (/ (AREF2 '$ARG
				     C
				     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				     (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			   I)
		  I
		  (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))
		  J))))))
  :hints (("Goal"
	   :in-theory (disable NATP-CAR-FIND-NON-ZERO-COL-1)
	   :use lemma-16-hack)))

(defthm
  lemma-15-hack
  (IMPLIES (AND (< J (CAR (DIMENSIONS '$ARG B)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$B B)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< J
	      (CAR (DIMENSIONS
		    '$b
		    (RI<-ARI '$B
			     (RI<->RJ '$B
				      B
				      I
				      (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			     (/ (AREF2 '$ARG
				       C
				       (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				       (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			     I)))))
  :rule-classes nil)

(defthm
  lemma-15-hack-1
  (IMPLIES (AND (< J (CAR (DIMENSIONS '$ARG B)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$B B)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< J
	      (CAR (DIMENSIONS
		    '$arg
		    (RI<-ARI '$B
			     (RI<->RJ '$B
				      B
				      I
				      (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			     (/ (AREF2 '$ARG
				       C
				       (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				       (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			     I)))))
  :hints (("Goal"
	   :in-theory (disable NATP-CAR-FIND-NON-ZERO-COL-1)
	   :use lemma-15-hack)))

(defthm
  lemma-15-crock
  (IMPLIES (AND (< J (CADR (DIMENSIONS '$ARG A)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$A A)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< I
	      (CADR
	       (DIMENSIONS '$a
			   (CI<-ACI '$A
				    (CI<->CJ '$A
					     A
					     I
					     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
				    (AREF2 '$ARG
					   C
					   (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					   (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
				    I)))))
  :rule-classes nil)

(defthm
  lemma-15-crock-1
  (IMPLIES (AND (< J (CADR (DIMENSIONS '$ARG A)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$A A)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< I
	      (CADR
	       (DIMENSIONS '$arg
			   (CI<-ACI '$A
				    (CI<->CJ '$A
					     A
					     I
					     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
				    (AREF2 '$ARG
					   C
					   (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
					   (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
				    I)))))
  :hints (("Goal"
	   :in-theory (disable NATP-CAR-FIND-NON-ZERO-COL-1)
	   :use lemma-15-crock)))

(defthm
  lemma-10-hack
  (IMPLIES (AND (< J (CAR (DIMENSIONS '$ARG B)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$B B)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< (+ 1 I)
	      (CAR
	       (DIMENSIONS
		'$b
		(CADR
		 (ZERO-COLUMN
		  (CI<-ACI '$A
			   (CI<->CJ '$A
				    A
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (AREF2 '$ARG
				  C
				  (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				  (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   I)
		  (RI<-ARI '$B
			   (RI<->RJ '$B
				    B
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (/ (AREF2 '$ARG
				     C
				     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				     (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			   I)
		  (RI<-ARI '$C
			   (RI<->RJ '$C
				    C
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (/ (AREF2 '$ARG
				     C
				     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				     (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			   I)
		  I
		  (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))
		  J))))))
  :rule-classes nil)

(defthm
  lemma-10-hack-1
  (IMPLIES (AND (< J (CAR (DIMENSIONS '$ARG B)))
		(<= 0 J)
		(<= 0 I)
		(INTEGERP I)
		(ARRAY2P '$B B)
		(FIND-NON-ZERO-COL-1 '$C C I J K N)
		(NOT (EQUAL (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
			    I)))
	   (< (+ 1 I)
	      (CAR
	       (DIMENSIONS
		'$arg
		(CADR
		 (ZERO-COLUMN
		  (CI<-ACI '$A
			   (CI<->CJ '$A
				    A
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (AREF2 '$ARG
				  C
				  (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				  (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   I)
		  (RI<-ARI '$B
			   (RI<->RJ '$B
				    B
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (/ (AREF2 '$ARG
				     C
				     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				     (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			   I)
		  (RI<-ARI '$C
			   (RI<->RJ '$C
				    C
				    I
				    (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N)))
			   (/ (AREF2 '$ARG
				     C
				     (CAR (FIND-NON-ZERO-COL-1 '$C C I J K N))
				     (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))))
			   I)
		  I
		  (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))
		  J))))))
  :hints (("Goal"
	   :in-theory (disable NATP-CAR-FIND-NON-ZERO-COL-1)
	   :use lemma-10-hack)))

(defthm
  lemma-1-hack
  (IMPLIES (AND (FIND-NON-ZERO-COL-1 '$C C I J K N)
		(< J (CAR (DIMENSIONS '$ARG C)))
		(<= 0 J)
		(INTEGERP J)
		(ARRAY2P '$C C)
		(NOT (EQUAL I J))
		(EQUAL (CADR (FIND-NON-ZERO-COL-1 '$C C I J K N))
		       I))
	   (< (+ 1 I) (CAR (DIMENSIONS '$ARG C)))))

(defun
  determinant-inverse-loop (A B C D i j k n)
  "Process columns k thru n,
      restricted to rows i thru j."
  (declare (xargs :measure (let ((k (nfix k))
				 (n (nfix n)))
			        (if (> k n)
				    0
				    (- (+ n 1) k)))
		  :guard (and (array2p '$a A)
			      (array2p '$b B)
			      (array2p '$c C)
			      (acl2-numberp D)
			      (integerp i)
			      (integerp j)
			      (integerp k)
			      (integerp n)
			      (>= i 0)
			      (>= j 0)
			      (>= k 0)
			      (>= n 0)
			      (< i (second
				    (dimensions '$a
						A)))
			      (< i (first
				    (dimensions '$b
						B)))
			      (< i (first
				    (dimensions '$c
						C)))
			      (< j (second
				    (dimensions '$a
						A)))
			      (< j (first
				    (dimensions '$b
						B)))
			      (< j (first
				    (dimensions '$c
						C)))
			      (< n (second
				    (dimensions '$c
						C))))
		  :verify-guards nil))
  (let ((k (nfix k))
	(n (nfix n))
	(i (nfix i))
	(j (nfix j)))
       (if (> k n)
	   (mv A B C D)
	   (let
	    ((indices (find-non-zero-col-1 '$C C i j k n)))
	    (if indices
		(let*
		 ((p (first indices))
		  (q (second indices))
		  (val (aref2 '$C C p q)))
		 (if (= p i)
		     (mv-let
		      (A B C)
		      (zero-column (Ci<-aCi '$A A val     i)
				   (Ri<-aRi '$B B (/ val) i)
				   (Ri<-aRi '$C C (/ val) i)
				   i
				   q
				   j)
		      (cond ((= i j)
			     (mv A B C (* val D)))
			    ((= q i)
			     (determinant-inverse-loop A B C
						       (* val D)
						       (+ i 1)
						       j
						       (+ q 1)
						       n))
			    (t
			     (determinant-inverse-loop A B C
						       (* val D)
						       0
						       j
						       (+ q 1)
						       n))))
		     (mv-let
		      (A B C)
		      (zero-column (Ci<-aCi '$A (Ci<->Cj '$A A i p) val    i)
				   (Ri<-aRi '$B (Ri<->Rj '$B B i p)(/ val) i)
				   (Ri<-aRi '$C (Ri<->Rj '$C C i p)(/ val) i)
				   i
				   q
				   j)
		      (cond ((= i j)
			     (mv A B C (* val (- D))))
			    ((= q i)
			     (determinant-inverse-loop A B C
						       (* val (- D))
						       (+ i 1)
						       j
						       (+ q 1)
						       n))
			    (t
			     (determinant-inverse-loop A B C
						       0
						       (+ i 1)
						       j
						       (+ q 1)
						       n))))))
	        (mv A B C 0))))))

(defthm
  mv-nth-1
  (equal (mv-nth 1 L)
	 (cadr L)))

(defthm
  mv-nth-2
  (equal (mv-nth 2 L)
	 (caddr L)))

(verify-guards determinant-inverse-loop)

(defthm
  sq-array2p-m-1
  (IMPLIES (AND (EQUAL (CAR (DIMENSIONS name M))
		       (CADR (DIMENSIONS name M)))
		(ARRAY2P name M))
	   (ARRAY2P name
		    (M-1 (CAR (DIMENSIONS name M)))))
  :hints (("Goal"
	   :use (:theorem
		 (implies (array2p name M)
			  (< (* (first (dimensions name M))
				(second (dimensions name M)))
			     *MAXIMUM-POSITIVE-32-BIT-INTEGER*))))))

(defthm
  sq-array2p-m-1-a
  (IMPLIES (AND (EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M)))
		(ARRAY2P name1 M)
		(symbolp name))
	   (ARRAY2P name
		    (M-1 (CAR (DIMENSIONS '$ARG M)))))
  :hints (("Goal"
	   :in-theory (disable sq-array2p-m-1)
	   :use  sq-array2p-m-1)))

(defthm
  sq-array2p-compress2
  (IMPLIES (AND (EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M)))
		(ARRAY2P name M)
		(symbolp name1))
	   (ARRAY2P name1
		    (COMPRESS2 name2
			       (M-1 (CAR (DIMENSIONS '$ARG M))))))
  :hints (("Goal"
	   :in-theory (disable ARRAY2P-COMPRESS2)
	   :use (:instance
		 ARRAY2P-COMPRESS2
		 (L (M-1 (CAR (DIMENSIONS '$ARG M))))
		 (name name1)))))

(defun
  determinant-inverse (M)
  "Return multiple values A, B, C, and D.
   If M is a square array, the determinant of
   M is returned in D.  If the determinant is
   nonzero, then the matrix inverse of M is
   returned in B."
  (declare (xargs :guard (and (array2p '$c M)
			      (let ((dims (dimensions '$c M)))
				   (= (first dims)
				      (second dims))))))
  (let ((dims (dimensions '$c M)))
       (if (mbt (and (alist2p '$c M)
		     (= (first dims)
			(second dims))))
	   (let ((dim1 (first dims)))
	        (determinant-inverse-loop (compress2 '$A (m-1 dim1))
					  (compress2 '$B (m-1 dim1))
					  (compress2 '$C M)
					  1 ;; initial value of D
					  0
					  (- dim1 1)
					  0
					  (- (second (dimensions '$c M)) 1)))
	   (mv M (/ M) 1 M))))

(defun
  determinant (M)
  (declare (xargs :guard (and (array2p '$c M)
			      (let ((dims (dimensions '$c M)))
				   (= (first dims)
				      (second dims))))))
  (mv-let (A B C D)
	  (determinant-inverse M)
	  (declare (ignore A B C))
	  D))

(defun
  m-/ (M)
  (declare (xargs :guard (and (array2p '$c M)
			      (let ((dims (dimensions '$c M)))
				   (= (first dims)
				      (second dims))))))
  (mv-let (A B C D)
	  (determinant-inverse M)
	  (declare (ignore A C D))
	  B))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Eventually, we will prove that for square matrices
;;  whenever the determinant is not 0, then m-/
;;  computes the two-sided inverse; and whenever the
;;  determinant is 0 then there is no inverse.
;;  Also it will be proved that non-square matrices
;;  do not have two-sided inverses.

;;  Meanwhile the definition of singualar given
;;  immediately below is replaced by the second one
;;  below.

;; (defun
;;   m-singularp (M)
;;   (declare (xargs :guard (array2p '$c M)))
;;   (not (and (mbt (alist2p '$c M))
;;             (let ((dims (dimensions '$c M)))
;;                  (= (first dims)
;;                     (second dims)))
;;             (= (determinant M) 0))))
|#;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun
  m-singularp (M)
  (declare (xargs :guard (array2p '$c M)
		  :verify-guards nil))
  (not (and (mbt (alist2p '$c M))
	    (let ((dims (dimensions '$c M)))
	         (= (first dims)
		    (second dims)))
	    (m-= (m-* M (m-/ M))
		 (m-1 (r M)))
	    (m-= (m-* (m-/ M) M)
		 (m-1 (r M))))))

(defthm
  non-singular-implies-square
  (implies (not (m-singularp M))
	   (equal (equal (c M)(r M))
		  t)))

(defthm
  left-m-*-inverse-of-m-/
  (implies (not (m-singularp M))
	   (m-= (m-* (m-/ M) M)
		(m-1 (r M)))))

(defthm
  right-m-*-inverse-of-m-/
  (implies (not (m-singularp M))
	   (m-= (m-* M (m-/ M))
		(m-1 (r M)))))

(DEFTHM
  ALIST2P-CI<->CJ-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP I)
		(INTEGERP J)
		(>= I 0)
		(>= J 0)
		(< I (SECOND (DIMENSIONS NAME M)))
		(< J (SECOND (DIMENSIONS NAME M))))
	   (ALIST2P NAME (CI<->CJ NAME1 M I J)))
  :HINTS (("Goal"
	   :IN-THEORY (DISABLE alist2p-CI<->CJ)
	   :USE (:INSTANCE
		 alist2p-CI<->CJ
		 (NAME NAME1)))))

(DEFTHM
  Array2P-CI<->CJ-1
  (IMPLIES (AND (symbolp name1)
		(Array2P NAME M)
		(INTEGERP I)
		(INTEGERP J)
		(>= I 0)
		(>= J 0)
		(< I (SECOND (DIMENSIONS NAME M)))
		(< J (SECOND (DIMENSIONS NAME M))))
	   (Array2P NAME (CI<->CJ NAME1 M I J)))
  :HINTS (("Goal"
	   :IN-THEORY (DISABLE array2p-CI<->CJ)
	   :USE (:INSTANCE
		 array2p-CI<->CJ
		 (NAME NAME1)))))

(DEFTHM
  ALIST2P-RI<->RJ-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP I)
		(INTEGERP J)
		(>= I 0)
		(>= J 0)
		(< I (FIRST (DIMENSIONS NAME M)))
		(< J (FIRST (DIMENSIONS NAME M))))
	   (ALIST2P NAME (RI<->RJ NAME1 M I J)))
  :HINTS (("Goal"
	   :IN-THEORY (DISABLE alist2p-RI<->RJ)
	   :USE (:INSTANCE
		 alist2p-RI<->RJ
		 (NAME NAME1)))))

(DEFTHM
  Array2P-RI<->RJ-1
  (IMPLIES (AND (symbolp name1)
		(Array2P NAME M)
		(INTEGERP I)
		(INTEGERP J)
		(>= I 0)
		(>= J 0)
		(< I (FIRST (DIMENSIONS NAME M)))
		(< J (FIRST (DIMENSIONS NAME M))))
	   (Array2P NAME (RI<->RJ NAME1 M I J)))
  :HINTS (("Goal"
	   :IN-THEORY (DISABLE array2p-RI<->RJ)
	   :USE (:INSTANCE
		 array2p-RI<->RJ
		 (NAME NAME1)))))

(DEFTHM
  ALIST2P-RI<-ARI-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP I)
		(>= I 0)
		(< I (FIRST (DIMENSIONS NAME M))))
	   (ALIST2P NAME (RI<-ARI NAME1 M A I)))
  :HINTS (("Goal"
	   :IN-THEORY (DISABLE alist2p-RI<-ARI)
	   :USE (:INSTANCE
		 alist2p-RI<-ARI
		 (NAME NAME1)))))

(DEFTHM
  Array2P-RI<-ARI-1
  (IMPLIES (AND (symbolp name1)
		(Array2P NAME M)
		(INTEGERP I)
		(>= I 0)
		(< I (FIRST (DIMENSIONS NAME M))))
	   (Array2P NAME (RI<-ARI NAME1 M A I)))
  :HINTS (("Goal"
	   :IN-THEORY (DISABLE array2p-RI<-ARI)
	   :USE (:INSTANCE
		 array2p-RI<-ARI
		 (NAME NAME1)))))

(DEFTHM
  ALIST2P-CI<-ACI-1
  (IMPLIES (AND (ALIST2P NAME M)
		(INTEGERP I)
		(>= I 0)
		(< I (second (DIMENSIONS NAME M))))
	   (ALIST2P NAME (CI<-ACI NAME1 M A I)))
  :HINTS (("Goal"
	   :IN-THEORY (DISABLE alist2p-CI<-ACI)
	   :USE (:INSTANCE
		 alist2p-CI<-ACI
		 (NAME NAME1)))))

(DEFTHM
  Array2P-CI<-ACI-1
  (IMPLIES (AND (symbolp name1)
		(Array2P NAME M)
		(INTEGERP I)
		(>= I 0)
		(< I (second (DIMENSIONS NAME M))))
	   (Array2P NAME (CI<-ACI NAME1 M A I)))
  :HINTS (("Goal"
	   :IN-THEORY (DISABLE array2p-CI<-ACI)
	   :USE (:INSTANCE
		 array2p-CI<-ACI
		 (NAME NAME1)))))

(defthm
  array2p-alist2p-1
  (implies (and (array2p name1 L)
		(symbolp name))
	   (alist2p name  L))
  :hints (("Goal"
	   :in-theory (disable array2p-alist2p)
	   :use array2p-alist2p)))

(defthm
  dimensions-DETERMINANT-INVERSE-LOOP-A
  (IMPLIES (AND (Alist2P '$A A)
		(Alist2P '$B B)
		(Alist2P '$C C)
		(INTEGERP I)
		(INTEGERP J)
		(INTEGERP K)
		(INTEGERP N)
		(<= 0 I)
		(<= 0 J)
		(<= 0 K)
		(<= 0 N)
		(< I (CADR (DIMENSIONS '$ARG A)))
		(< I (CAR (DIMENSIONS '$ARG B)))
		(< I (CAR (DIMENSIONS '$ARG C)))
		(< J (CADR (DIMENSIONS '$ARG A)))
		(< J (CAR (DIMENSIONS '$ARG B)))
		(< J (CAR (DIMENSIONS '$ARG C)))
		(< N (CADR (DIMENSIONS '$ARG C))))
	  (EQUAL (DIMENSIONS
		  name
		  (CAR (DETERMINANT-INVERSE-LOOP A
						 B
						 C
						 D
						 I
						 J
						 K
						 N)))
		 (DIMENSIONS name A))))

(defthm
  dimensions-DETERMINANT-INVERSE-LOOP-B
  (IMPLIES (AND (Alist2P '$A A)
		(Alist2P '$B B)
		(Alist2P '$C C)
		(INTEGERP I)
		(INTEGERP J)
		(INTEGERP K)
		(INTEGERP N)
		(<= 0 I)
		(<= 0 J)
		(<= 0 K)
		(<= 0 N)
		(< I (CADR (DIMENSIONS '$ARG A)))
		(< I (CAR (DIMENSIONS '$ARG B)))
		(< I (CAR (DIMENSIONS '$ARG C)))
		(< J (CADR (DIMENSIONS '$ARG A)))
		(< J (CAR (DIMENSIONS '$ARG B)))
		(< J (CAR (DIMENSIONS '$ARG C)))
		(< N (CADR (DIMENSIONS '$ARG C))))
	  (EQUAL (DIMENSIONS
		  name
		  (CADR (DETERMINANT-INVERSE-LOOP A
						  B
						  C
						  D
						  I
						  J
						  K
						  N)))
		 (DIMENSIONS name B))))

(defthm
  dimensions-DETERMINANT-INVERSE-LOOP-C
  (IMPLIES (AND (Alist2P '$A A)
		(Alist2P '$B B)
		(Alist2P '$C C)
		(INTEGERP I)
		(INTEGERP J)
		(INTEGERP K)
		(INTEGERP N)
		(<= 0 I)
		(<= 0 J)
		(<= 0 K)
		(<= 0 N)
		(< I (CADR (DIMENSIONS '$ARG A)))
		(< I (CAR (DIMENSIONS '$ARG B)))
		(< I (CAR (DIMENSIONS '$ARG C)))
		(< J (CADR (DIMENSIONS '$ARG A)))
		(< J (CAR (DIMENSIONS '$ARG B)))
		(< J (CAR (DIMENSIONS '$ARG C)))
		(< N (CADR (DIMENSIONS '$ARG C))))
	  (EQUAL (DIMENSIONS
		  name
		  (CADDR (DETERMINANT-INVERSE-LOOP A
						   B
						   C
						   D
						   I
						   J
						   K
						   N)))
		 (DIMENSIONS name C))))

(defthm
  alist2p-DETERMINANT-INVERSE-LOOP-A
  (IMPLIES (AND (Alist2P '$A A)
		(Alist2P '$B B)
		(Alist2P '$C C)
		(INTEGERP I)
		(INTEGERP J)
		(INTEGERP K)
		(INTEGERP N)
		(<= 0 I)
		(<= 0 J)
		(<= 0 K)
		(<= 0 N)
		(< I (CADR (DIMENSIONS '$ARG A)))
		(< I (CAR (DIMENSIONS '$ARG B)))
		(< I (CAR (DIMENSIONS '$ARG C)))
		(< J (CADR (DIMENSIONS '$ARG A)))
		(< J (CAR (DIMENSIONS '$ARG B)))
		(< J (CAR (DIMENSIONS '$ARG C)))
		(< N (CADR (DIMENSIONS '$ARG C))))
	  (alist2p '$a (CAR (DETERMINANT-INVERSE-LOOP A
						      B
						      C
						      D
						      I
						      J
						      K
						      N))))

  :hints (("Goal"
	   :do-not '(generalize))))

(defthm
  alist2p-DETERMINANT-INVERSE-LOOP-B
  (IMPLIES (AND (Alist2P '$A A)
		(Alist2P '$B B)
		(Alist2P '$C C)
		(INTEGERP I)
		(INTEGERP J)
		(INTEGERP K)
		(INTEGERP N)
		(<= 0 I)
		(<= 0 J)
		(<= 0 K)
		(<= 0 N)
		(< I (CADR (DIMENSIONS '$ARG A)))
		(< I (CAR (DIMENSIONS '$ARG B)))
		(< I (CAR (DIMENSIONS '$ARG C)))
		(< J (CADR (DIMENSIONS '$ARG A)))
		(< J (CAR (DIMENSIONS '$ARG B)))
		(< J (CAR (DIMENSIONS '$ARG C)))
		(< N (CADR (DIMENSIONS '$ARG C))))
	  (alist2p '$b (CAdR (DETERMINANT-INVERSE-LOOP A
						       B
						       C
						       D
						       I
						       J
						       K
						       N))))

  :hints (("Goal"
	   :do-not '(generalize))))

(defthm
  alist2p-DETERMINANT-INVERSE-LOOP-C
  (IMPLIES (AND (Alist2P '$A A)
		(Alist2P '$B B)
		(Alist2P '$C C)
		(INTEGERP I)
		(INTEGERP J)
		(INTEGERP K)
		(INTEGERP N)
		(<= 0 I)
		(<= 0 J)
		(<= 0 K)
		(<= 0 N)
		(< I (CADR (DIMENSIONS '$ARG A)))
		(< I (CAR (DIMENSIONS '$ARG B)))
		(< I (CAR (DIMENSIONS '$ARG C)))
		(< J (CADR (DIMENSIONS '$ARG A)))
		(< J (CAR (DIMENSIONS '$ARG B)))
		(< J (CAR (DIMENSIONS '$ARG C)))
		(< N (CADR (DIMENSIONS '$ARG C))))
	  (alist2p '$C (CAddR (DETERMINANT-INVERSE-LOOP A
							B
							C
							D
							I
							J
							K
							N))))

  :hints (("Goal"
	   :do-not '(generalize))))

(defthm
  array2p-DETERMINANT-INVERSE-LOOP-A
  (IMPLIES (AND (Array2P '$A A)
		(Array2P '$B B)
		(Array2P '$C C)
		(INTEGERP I)
		(INTEGERP J)
		(INTEGERP K)
		(INTEGERP N)
		(<= 0 I)
		(<= 0 J)
		(<= 0 K)
		(<= 0 N)
		(< I (CADR (DIMENSIONS '$ARG A)))
		(< I (CAR (DIMENSIONS '$ARG B)))
		(< I (CAR (DIMENSIONS '$ARG C)))
		(< J (CADR (DIMENSIONS '$ARG A)))
		(< J (CAR (DIMENSIONS '$ARG B)))
		(< J (CAR (DIMENSIONS '$ARG C)))
		(< N (CADR (DIMENSIONS '$ARG C))))
	  (array2p '$a (CAR (DETERMINANT-INVERSE-LOOP A
						       B
						       C
						       D
						       I
						       J
						       K
						       N))))

  :hints (("Goal"
	   :do-not '(generalize))))

(defthm
  array2p-DETERMINANT-INVERSE-LOOP-B
  (IMPLIES (AND (Array2P '$A A)
		(Array2P '$B B)
		(Array2P '$C C)
		(INTEGERP I)
		(INTEGERP J)
		(INTEGERP K)
		(INTEGERP N)
		(<= 0 I)
		(<= 0 J)
		(<= 0 K)
		(<= 0 N)
		(< I (CADR (DIMENSIONS '$ARG A)))
		(< I (CAR (DIMENSIONS '$ARG B)))
		(< I (CAR (DIMENSIONS '$ARG C)))
		(< J (CADR (DIMENSIONS '$ARG A)))
		(< J (CAR (DIMENSIONS '$ARG B)))
		(< J (CAR (DIMENSIONS '$ARG C)))
		(< N (CADR (DIMENSIONS '$ARG C))))
	  (array2p '$b (CAdR (DETERMINANT-INVERSE-LOOP A
						       B
						       C
						       D
						       I
						       J
						       K
						       N))))

  :hints (("Goal"
	   :do-not '(generalize))))

(defthm
  array2p-DETERMINANT-INVERSE-LOOP-C
  (IMPLIES (AND (Array2P '$A A)
		(Array2P '$B B)
		(Array2P '$C C)
		(INTEGERP I)
		(INTEGERP J)
		(INTEGERP K)
		(INTEGERP N)
		(<= 0 I)
		(<= 0 J)
		(<= 0 K)
		(<= 0 N)
		(< I (CADR (DIMENSIONS '$ARG A)))
		(< I (CAR (DIMENSIONS '$ARG B)))
		(< I (CAR (DIMENSIONS '$ARG C)))
		(< J (CADR (DIMENSIONS '$ARG A)))
		(< J (CAR (DIMENSIONS '$ARG B)))
		(< J (CAR (DIMENSIONS '$ARG C)))
		(< N (CADR (DIMENSIONS '$ARG C))))
	  (array2p '$C (CAddR (DETERMINANT-INVERSE-LOOP A
							B
							C
							D
							I
							J
							K
							N))))

  :hints (("Goal"
	   :do-not '(generalize))))

(defthm
  dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-A
  (IMPLIES (ALIST2P '$C M)
	   (EQUAL (DIMENSIONS
		   '$ARG
		   (CAR
		    (DETERMINANT-INVERSE-LOOP
		     (COMPRESS2
		      '$ARG
		      (M-1 (CAR (DIMENSIONS '$ARG M))))
		     (COMPRESS2
		      '$ARG
		      (M-1 (CAR (DIMENSIONS '$ARG M))))
		     (COMPRESS2 '$ARG M)
		     D
		     0
		     (+ -1
			(CAR (DIMENSIONS '$ARG M)))
		     0
		     (+ -1
			(CAdR (DIMENSIONS '$ARG M))))))
		  (LIST (CAR (DIMENSIONS '$ARG M))
			(CAR (DIMENSIONS '$ARG M)))))
  :hints (("Goal"
	   :in-theory (disable dimensions-DETERMINANT-INVERSE-LOOP-A)
	   :use (:instance
		 dimensions-DETERMINANT-INVERSE-LOOP-A
		 (A (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (B (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (C (COMPRESS2 '$ARG M))
		 (i 0)
		 (j (+ -1 (CAR (DIMENSIONS '$ARG M))))
		 (k 0)
		 (n (+ -1 (CAdR (DIMENSIONS '$ARG M))))))))

(defthm
  dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-A-1
  (IMPLIES (and (ALIST2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M))))
	   (EQUAL (DIMENSIONS
		   '$ARG
		   (CAR
		    (DETERMINANT-INVERSE-LOOP
		     (COMPRESS2
		      '$ARG
		      (M-1 (CAR (DIMENSIONS '$ARG M))))
		     (COMPRESS2
		      '$ARG
		      (M-1 (CAR (DIMENSIONS '$ARG M))))
		     (COMPRESS2 '$ARG M)
		     D
		     0
		     (+ -1
			(CAR (DIMENSIONS '$ARG M)))
		     0
		     (+ -1
			(CAR (DIMENSIONS '$ARG M))))))
		  (LIST (CAR (DIMENSIONS '$ARG M))
			(CAR (DIMENSIONS '$ARG M)))))
  :hints
  (("Goal"
    :in-theory
    (disable
     dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-A)
    :use
    dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-A)))

(defthm
  dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-B
  (IMPLIES (ALIST2P '$C M)
	   (EQUAL (DIMENSIONS
		   '$ARG
		   (CAdR
		    (DETERMINANT-INVERSE-LOOP
		     (COMPRESS2
		      '$ARG
		      (M-1 (CAR (DIMENSIONS '$ARG M))))
		     (COMPRESS2
		      '$ARG
		      (M-1 (CAR (DIMENSIONS '$ARG M))))
		     (COMPRESS2 '$ARG M)
		     D
		     0
		     (+ -1
			(CAR (DIMENSIONS '$ARG M)))
		     0
		     (+ -1
			(CAdR (DIMENSIONS '$ARG M))))))
		  (LIST (CAR (DIMENSIONS '$ARG M))
			(CAR (DIMENSIONS '$ARG M)))))
  :hints (("Goal"
	   :in-theory (disable dimensions-DETERMINANT-INVERSE-LOOP-B)
	   :use (:instance
		 dimensions-DETERMINANT-INVERSE-LOOP-B
		 (A (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (B (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (C (COMPRESS2 '$ARG M))
		 (i 0)
		 (j (+ -1 (CAR (DIMENSIONS '$ARG M))))
		 (k 0)
		 (n (+ -1 (CAdR (DIMENSIONS '$ARG M))))))))

(defthm
  dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-B-1
  (IMPLIES (and (ALIST2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M))))
	   (EQUAL (DIMENSIONS
		   '$ARG
		   (CAdR
		    (DETERMINANT-INVERSE-LOOP
		     (COMPRESS2
		      '$ARG
		      (M-1 (CAR (DIMENSIONS '$ARG M))))
		     (COMPRESS2
		      '$ARG
		      (M-1 (CAR (DIMENSIONS '$ARG M))))
		     (COMPRESS2 '$ARG M)
		     D
		     0
		     (+ -1
			(CAR (DIMENSIONS '$ARG M)))
		     0
		     (+ -1
			(CAR (DIMENSIONS '$ARG M))))))
		  (LIST (CAR (DIMENSIONS '$ARG M))
			(CAR (DIMENSIONS '$ARG M)))))
  :hints
  (("Goal"
    :in-theory
    (disable
     dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-B)
    :use
    dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-B)))

(defthm
  dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-C
  (IMPLIES (ALIST2P '$C M)
	   (EQUAL (DIMENSIONS
		   '$ARG
		   (CAddR
		    (DETERMINANT-INVERSE-LOOP
		     (COMPRESS2
		      '$ARG
		      (M-1 (CAR
			    (DIMENSIONS '$ARG M))))
		     (COMPRESS2
		      '$ARG
		      (M-1
		       (CAR (DIMENSIONS '$ARG M))))
		     (COMPRESS2 '$ARG M)
		     D
		     0
		     (+ -1
			(CAR (DIMENSIONS '$ARG M)))
		     0
		     (+ -1
			(CAdR (DIMENSIONS '$ARG M))))))
		  (dimensions '$arg M)))
  :hints (("Goal"
	   :in-theory (disable dimensions-DETERMINANT-INVERSE-LOOP-c)
	   :use (:instance
		 dimensions-DETERMINANT-INVERSE-LOOP-c
		 (A (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (B (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (C (COMPRESS2 '$ARG M))
		 (i 0)
		 (j (+ -1 (CAR (DIMENSIONS '$ARG M))))
		 (k 0)
		 (n (+ -1 (CAdR (DIMENSIONS '$ARG M))))))))

(defthm
  dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-C-1
  (IMPLIES (and (ALIST2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M))))
	   (EQUAL (DIMENSIONS
		   '$ARG
		   (CAddR
		    (DETERMINANT-INVERSE-LOOP
		     (COMPRESS2
		      '$ARG
		      (M-1 (CAR
			    (DIMENSIONS '$ARG M))))
		     (COMPRESS2
		      '$ARG
		      (M-1
		       (CAR (DIMENSIONS '$ARG M))))
		     (COMPRESS2 '$ARG M)
		     D
		     0
		     (+ -1
			(CAR (DIMENSIONS '$ARG M)))
		     0
		     (+ -1
			(CAR (DIMENSIONS '$ARG M))))))
		  (dimensions '$arg M)))
  :hints
  (("Goal"
    :in-theory
    (disable
     dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-C)
    :use
    dimensions-DETERMINANT-INVERSE-LOOP-COMPRESS2-C)))

(defthm
  dimensions-m-/
  (implies (and (alist2p name M)
		(equal (first (dimensions name M))
		       (second (dimensions name M))))
	   (equal (dimensions name (m-/ M))
		  (list (car (dimensions name M))
			(car (dimensions name M))))))

(defthm
  alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-A
  (IMPLIES (ALIST2P '$C M)
	   (alist2p name
		    (CAR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAdR (DIMENSIONS '$ARG M)))))))
  :hints (("Goal"
	   :in-theory (disable alist2p-DETERMINANT-INVERSE-LOOP-A)
	   :use (:instance
		 alist2p-DETERMINANT-INVERSE-LOOP-A
		 (A (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (B (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (C (COMPRESS2 '$ARG M))
		 (i 0)
		 (j (+ -1 (CAR (DIMENSIONS '$ARG M))))
		 (k 0)
		 (n (+ -1 (CAdR (DIMENSIONS '$ARG M))))))))

(defthm
  alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-A-1
  (IMPLIES (and (ALIST2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M))))
	   (alist2p name
		    (CAR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))))))
  :hints
  (("Goal"
    :in-theory
    (disable
     alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-A)
    :use
    alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-A)))

(defthm
  alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B
  (IMPLIES (ALIST2P '$C M)
	   (alist2p name
		    (CAdR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAdR (DIMENSIONS '$ARG M)))))))
  :hints (("Goal"
	   :in-theory (disable alist2p-DETERMINANT-INVERSE-LOOP-B)
	   :use (:instance
		 alist2p-DETERMINANT-INVERSE-LOOP-B
		 (A (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (B (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (C (COMPRESS2 '$ARG M))
		 (i 0)
		 (j (+ -1 (CAR (DIMENSIONS '$ARG M))))
		 (k 0)
		 (n (+ -1 (CAdR (DIMENSIONS '$ARG M))))))))

(defthm
  alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B-1
  (IMPLIES (and (ALIST2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M))))
	   (alist2p name
		    (CAdR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))))))
  :hints
  (("Goal"
    :in-theory
    (disable
     alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B)
    :use
    alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B)))

(defthm
  alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-C
  (IMPLIES (ALIST2P '$C M)
	   (alist2p name
		    (CAddR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR
			     (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1
			(CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAdR (DIMENSIONS '$ARG M)))))))
  :hints (("Goal"
	   :in-theory (disable alist2p-DETERMINANT-INVERSE-LOOP-c)
	   :use (:instance
		 alist2p-DETERMINANT-INVERSE-LOOP-c
		 (A (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (B (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (C (COMPRESS2 '$ARG M))
		 (i 0)
		 (j (+ -1 (CAR (DIMENSIONS '$ARG M))))
		 (k 0)
		 (n (+ -1 (CAdR (DIMENSIONS '$ARG M))))))))

(defthm
  alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-C-1
  (IMPLIES (and (ALIST2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M))))
	   (alist2p name
		    (CAddR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR
			     (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1
			(CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))))))
  :hints
  (("Goal"
    :in-theory
    (disable
     alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-C)
    :use
    alist2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-C)))

(defthm
  alist2p-m-/
  (implies (and (alist2p name M)
		(equal (first (dimensions name M))
		       (second (dimensions name M))))
		(alist2p name (m-/ M))))

(defTHM
  ARRAY2P-COMPRESS2-1
  (IMPLIES (ARRAY2P NAME L)
	   (ARRAY2P NAME (COMPRESS2 NAME1 L))))

(defthm
  array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-A
  (IMPLIES (and (Array2P '$C M)
		(< (* (CAR (DIMENSIONS '$ARG M))
		      (CAR (DIMENSIONS '$ARG M)))
		   *MAXIMUM-POSITIVE-32-BIT-INTEGER*)
		(symbolp name))
	   (array2p name
		    (CAR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAdR (DIMENSIONS '$ARG M)))))))
  :hints (("Goal"
	   :in-theory (disable array2p-DETERMINANT-INVERSE-LOOP-A)
	   :use (:instance
		 array2p-DETERMINANT-INVERSE-LOOP-A
		 (A (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (B (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (C (COMPRESS2 '$ARG M))
		 (i 0)
		 (j (+ -1 (CAR (DIMENSIONS '$ARG M))))
		 (k 0)
		 (n (+ -1 (CAdR (DIMENSIONS '$ARG M))))))))

(defthm
  array2p-rewrite-linear-1
  (implies (array2p name M)
	   (< (* (CAR (DIMENSIONS name M))
		 (CAdR (DIMENSIONS name M)))
	      *MAXIMUM-POSITIVE-32-BIT-INTEGER*))
  :rule-classes (:rewrite :linear))

(defthm
  array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-A-1
  (IMPLIES (and (Array2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M)))
		(symbolp name))
	   (array2p name
		    (CAR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))))))
  :hints
  (("Goal"
    :in-theory
    (disable
     array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-A
     array2p-rewrite-linear-1)
    :use
    (array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-A
     (:instance
      array2p-rewrite-linear-1
      (name '$arg))))))

(defthm
  array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B
  (IMPLIES (and (Array2P '$C M)
		(< (* (CAR (DIMENSIONS '$ARG M))
		      (CAR (DIMENSIONS '$ARG M)))
		   *MAXIMUM-POSITIVE-32-BIT-INTEGER*)
		(symbolp name))
	   (array2p name
		    (CAdR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAdR (DIMENSIONS '$ARG M)))))))
  :hints (("Goal"
	   :in-theory (disable array2p-DETERMINANT-INVERSE-LOOP-B)
	   :use (:instance
		 array2p-DETERMINANT-INVERSE-LOOP-B
		 (A (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (B (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (C (COMPRESS2 '$ARG M))
		 (i 0)
		 (j (+ -1 (CAR (DIMENSIONS '$ARG M))))
		 (k 0)
		 (n (+ -1 (CAdR (DIMENSIONS '$ARG M))))))))

(defthm
  array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B-1
  (IMPLIES (and (Array2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M)))
		(symbolp name))
	   (array2p name
		    (CAdR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))))))
  :hints
  (("Goal"
    :in-theory
    (disable
     array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B
     array2p-rewrite-linear-1)
    :use
    (array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B
     (:instance
      array2p-rewrite-linear-1
      (name '$arg))))))

(defthm
  array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-C
  (IMPLIES (and (Array2P '$C M)
		(< (* (CAR (DIMENSIONS '$ARG M))
		      (CAR (DIMENSIONS '$ARG M)))
		   *MAXIMUM-POSITIVE-32-BIT-INTEGER*)
		(symbolp name))
	   (array2p name
		    (CAddR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR
			     (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1
			(CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAdR (DIMENSIONS '$ARG M)))))))
  :hints (("Goal"
	   :in-theory (disable array2p-DETERMINANT-INVERSE-LOOP-c)
	   :use (:instance
		 array2p-DETERMINANT-INVERSE-LOOP-c
		 (A (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (B (COMPRESS2 '$ARG
			       (M-1 (CAR (DIMENSIONS '$ARG M)))))
		 (C (COMPRESS2 '$ARG M))
		 (i 0)
		 (j (+ -1 (CAR (DIMENSIONS '$ARG M))))
		 (k 0)
		 (n (+ -1 (CAdR (DIMENSIONS '$ARG M))))))))

(defthm
  array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-C-1
  (IMPLIES (and (Array2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M)))
		(symbolp name))
	   (array2p name
		    (CAddR
		     (DETERMINANT-INVERSE-LOOP
		      (COMPRESS2
		       '$ARG
		       (M-1 (CAR
			     (DIMENSIONS '$ARG M))))
		      (COMPRESS2
		       '$ARG
		       (M-1
			(CAR (DIMENSIONS '$ARG M))))
		      (COMPRESS2 '$ARG M)
		      D
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))
		      0
		      (+ -1
			 (CAR (DIMENSIONS '$ARG M)))))))
  :hints
  (("Goal"
    :in-theory
    (disable
     array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-C
     array2p-rewrite-linear-1)
    :use
    (array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-C
     (:instance
      array2p-rewrite-linear-1
      (name '$arg))))))

(defthm
  array2p-m-/
  (implies (and (array2p name M)
		(equal (first (dimensions name M))
		       (second (dimensions name M))))
		(array2p name (m-/ M)))
  :hints (("Goal"
	   :in-theory
	   (disable
	    array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B-1)
	   :use
	   (:instance
	    array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B-1
	    (D 1)))))

(defthm
  matrixp-m-/
  (implies (and (matrixp (r M)(c M) M)
		(equal (r M)(c M)))
	   (matrixp (r M)(c M)(m-/ M)))
  :hints (("Goal"
	   :in-theory
	   (disable
	    array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B-1)
	   :use
	   (:instance
	    array2p-DETERMINANT-INVERSE-LOOP-COMPRESS2-B-1
	    (D 1)
	    (name '$arg)))))

(in-theory (disable m-binary-*
		    m-=))

(defthm
  Subgoal-7-hack
  (IMPLIES (AND (ARRAY2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M))))
	   (ARRAY2P '$ARG1
		    (M-* M
			 (CADR
			  (DETERMINANT-INVERSE-LOOP
			   (COMPRESS2 '$ARG (M-1 (CAR (DIMENSIONS '$ARG M))))
			   (COMPRESS2 '$ARG (M-1 (CAR (DIMENSIONS '$ARG M))))
			   (COMPRESS2 '$ARG M)
			   1
			   0
			   (+ -1 (CAR (DIMENSIONS '$ARG M)))
			   0
			   (+ -1 (CAR (DIMENSIONS '$ARG M))))))))
  :hints (("Goal"
	   :in-theory (disable ARRAY2P-M-*-1
			       array2p-rewrite-linear-1)
	   :use ((:instance
		  ARRAY2P-M-*-1
		  (name '$arg)
		  (M1 M)
		  (M2 (CADR
		       (DETERMINANT-INVERSE-LOOP
			(COMPRESS2 '$ARG (M-1 (CAR (DIMENSIONS '$ARG M))))
			(COMPRESS2 '$ARG (M-1 (CAR (DIMENSIONS '$ARG M))))
			(COMPRESS2 '$ARG M)
			1
			0
			(+ -1 (CAR (DIMENSIONS '$ARG M)))
			0
			(+ -1 (CAR (DIMENSIONS '$ARG M)))))))
		 (:instance
		  array2p-rewrite-linear-1
		  (name '$arg))))))

(defthm
  Subgoal-3-hack
  (IMPLIES (AND (ARRAY2P '$C M)
		(EQUAL (CAR (DIMENSIONS '$ARG M))
		       (CADR (DIMENSIONS '$ARG M))))
	   (ARRAY2P '$ARG1
		    (M-* (CADR
			  (DETERMINANT-INVERSE-LOOP
			   (COMPRESS2 '$ARG (M-1 (CAR (DIMENSIONS '$ARG M))))
			   (COMPRESS2 '$ARG (M-1 (CAR (DIMENSIONS '$ARG M))))
			   (COMPRESS2 '$ARG M)
			   1
			   0
			   (+ -1 (CAR (DIMENSIONS '$ARG M)))
			   0
			   (+ -1 (CAR (DIMENSIONS '$ARG M)))))
			 M)))
  :hints (("Goal"
	   :in-theory (disable ARRAY2P-M-*-1
			       array2p-rewrite-linear-1)
	   :use ((:instance
		  ARRAY2P-M-*-1
		  (name '$arg)
		  (M2 M)
		  (M1 (CADR
		       (DETERMINANT-INVERSE-LOOP
			(COMPRESS2 '$ARG (M-1 (CAR (DIMENSIONS '$ARG M))))
			(COMPRESS2 '$ARG (M-1 (CAR (DIMENSIONS '$ARG M))))
			(COMPRESS2 '$ARG M)
			1
			0
			(+ -1 (CAR (DIMENSIONS '$ARG M)))
			0
			(+ -1 (CAR (DIMENSIONS '$ARG M)))))))
		 (:instance
		  array2p-rewrite-linear-1
		  (name '$arg))))))

(verify-guards m-singularp)

