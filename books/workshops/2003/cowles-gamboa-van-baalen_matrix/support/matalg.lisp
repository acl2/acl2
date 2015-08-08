; The ACL2 Matrix Algebra Book. Summary of definitions and algebra in matrix.lisp.
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
;  Last modified 17 June 2003.

; ACL2 Version 2.8 alpha (as of May 11 03)
#|
 To certify in
      ACL2 Version 2.8 alpha (as of May 11 03)

(certify-book "matalg"
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

(include-book "alist2")

(local (include-book "matrix"))

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

(defthm
  alist2p-$arg
  (implies (alist2p name  l)
	   (alist2p '$arg l))
  :rule-classes :forward-chaining)

(defthm
  array2p-$arg
  (implies (array2p name  l)
	   (array2p '$arg l))
  :rule-classes :forward-chaining)


(defthm
  not-alist2p-arg$
  (implies (not (alist2p name l))
	   (not (alist2p '$arg l)))
  :rule-classes :forward-chaining)

(defthm
  not-array2p-arg$
  (implies (and (not (array2p name l))
		(symbolp name))
	   (not (array2p '$arg l)))
  :rule-classes :forward-chaining)

(in-theory (disable alist2p array2p aset2 aref2 compress2 header
		    dimensions maximum-length default))

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

(defcong
  ;; m-=-implies-equal-alist2p-2
  m-= equal (alist2p name M) 2
  :hints (("Goal"
	   :use (:theorem
		 (implies (m-= M M-equiv)
			  (iff (alist2p name M)
			       (alist2p name M-equiv)
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

(verify-guards m-1a)

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
  aref2-m-trans
  (equal (aref2 name (m-trans M) i j)
	 (aref2 name M j i))
  :hints (("Goal"
	   :in-theory (enable aref2 header default))))

(defthm
  matrixp-m-trans
  (implies (matrixp m n X)
	   (matrixp n m (m-trans X))))

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

(defcong
  ;; M-=-IMPLIES-M-=-M-TRANS-1
  m-= m-= (m-trans M) 1)

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

(defthm
  matrixp-m-unary--
  (implies (matrixp m n X)
	   (matrixp m n (m-unary-- X))))

(defthm
  idempotency-of-m-unary--_alist2p
  (implies (alist2p name M)
	   (m-= (m-unary-- (m-unary-- M)) M)))

(defthm
  idempotency-of-m-unary--_array2p
  (implies (array2p name M)
	   (m-= (m-unary-- (m-unary-- M)) M)))

(defcong
  ;; M-=-IMPLIES-M-=-M-UNARY---1
  m-= m-= (m-unary-- M) 1)

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

(defthm
  matrixp-s-*
  (implies (matrixp m n X)
	   (matrixp m n (s-* a X))))

(defcong
  ;; M-=-IMPLIES-M-=-S-*-2
  m-= m-= (s-* a M) 2)

(defthm
  associate-scalars-left-s-*
  (implies (alist2p name M)
	   (m-= (s-* a1 (s-* a2 M))
		(s-* (* a1 a2) M))))

(defthm
  m-=-s-*-0
  (implies (alist2p name M)
	   (m-= (s-* 0 M)(m-0 (r M)(c M)))))

(defthm
  m-=-s-*-m-0
  (implies (and (integerp m)
		(integerp n)
		(> m 0)
		(> n 0))
	   (m-= (s-* a (m-0 m n))(m-0 m n))))

(defthm
  m-=-s-*-1
  (implies (alist2p name M)
	   (m-= (s-* 1 M) M)))

(defthm
  m-=-s-*_-1
  (implies (alist2p name M)
	   (m-= (s-* -1 M)(m-unary-- M))))

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
  commutativity-of-m-+
  (equal (m-+ M1 M2)
	 (m-+ M2 M1)))

(defthm
  associativity-of-m-+
  (equal (m-+ (m-+ M1 M2) M3)
	 (m-+ M1 M2 M3))
 :hints (("Goal"
	  :in-theory (disable commutativity-of-m-+))))

(local
 (defthm
   commutativity-2-of-m-+-lemma
   (equal (m-+ (m-+ X Y) Z)
	  (m-+ (m-+ Y X) Z))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory (disable associativity-of-m-+)))))

(defthm
  commutativity-2-of-m-+
  (equal (m-+ X Y Z)
	 (m-+ Y X Z))
  :hints (("Goal"
	   :use commutativity-2-of-m-+-lemma)))

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

(local
 (defthm
   right-m-+-inverse-of-m--_2-lemma
   (implies (and (alist2p name X)
		 (alist2p name Y)
		 (equal (r X)(r Y))
		 (equal (c X)(c Y)))
	    (m-= (m-+ (m-+ X (m-- X)) Y)
		 Y))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory (disable m-binary-+ m-=
				associativity-of-m-+)
	    :use (:instance
		  right-m-+-unicity-of-m-0
		  (M Y))))))

(defthm
  right-m-+-inverse-of-m--_2
  (implies (and (alist2p name X)
		(alist2p name Y)
		(equal (r X)(r Y))
		(equal (c X)(c Y)))
	   (m-= (m-+ X (m-- X) Y)
		Y))
  :hints (("Goal"
	   :use right-m-+-inverse-of-m--_2-lemma)))

(local
 (defthm
   left-m-+-inverse-of-m--_2-lemma
   (implies (and (alist2p name X)
		 (alist2p name Y)
		 (equal (r X)(r Y))
		 (equal (c X)(c Y)))
	    (m-= (m-+ (m-+ (m-- X) X) Y)
		 Y))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory (disable m-binary-+ m-=
				associativity-of-m-+)
	    :use (:instance
		  right-m-+-unicity-of-m-0
		  (M Y))))))

(defthm
  left-m-+-inverse-of-m--_2
  (implies (and (alist2p name X)
		(alist2p name Y)
		(equal (r X)(r Y))
		(equal (c X)(c Y)))
	   (m-= (m-+ (m-- X) X Y)
		Y))
  :hints (("Goal"
	   :use left-m-+-inverse-of-m--_2-lemma)))

(defthm
  uniqueness-of-m-+-inverse
  (implies (and (alist2p name X)
		(alist2p name Y)
		(equal (r X)(r Y))
		(equal (c X)(c Y))
		(m-= (m-+ X Y)
		     (m-0 (r X)(c X))))
	   (m-= X (m-- Y)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable m-binary-+ m-=)
	   :use ((:instance
		  right-m-+-unicity-of-m-0
		  (M X))
		 (:instance
		  right-m-+-unicity-of-m-0
		  (M (m-- Y)))))))

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
  double-m-+-s-*
  (implies (alist2p name M)
	   (m-= (m-+ M M)
		(s-* 2 M)))
  :hints (("Goal"
	   :use (:instance
		 distributivity-of-s-*-over-+
		 (a 1)
		 (b 1)))))

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
  left-nullity-of-m-0-for-m-*
  (implies (and (alist2p name M1)
		(integerp m)
		(> m 0))
	   (m-= (m-* (m-0 m (first (dimensions name M1)))
		     M1)
		(m-0 m (second (dimensions name M1))))))

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
  left-unity-of-m-1-for-m-*
  (implies (alist2p name M1)
	   (m-= (m-* (m-1 (first (dimensions name M1)))
		     M1)
		M1)))

(defthm
  right-unity-of-m-1-for-m-*
  (implies (alist2p name M1)
	   (m-= (m-* M1
		     (m-1 (second (dimensions name M1))))
		M1)))

(defthm
  associativity-of-m-*
  (equal (m-* (m-* M1 M2) M3)
	 (m-* M1 M2 M3)))

(defthm
  left-distributivity-of-m-*-over-m-+
  (m-= (m-* M1 (m-+ M2 M3))
       (m-+ (m-* M1 M2)
	    (m-* M1 M3))))

(defthm
  right-distributivity-of-m-*-over-m-+
  (m-= (m-* (m-+ M1 M2) M3)
       (m-+ (m-* M1 M3)
	    (m-* M2 M3))))

(local
 (defthm
   m-*-m--_left-lemma
   (implies (and (equal (c M1)(r M2))
		 (alist2p name M1)
		 (alist2p name M2))
	    (m-= (m-+ (m-* M1 M2)(m-* (m-- M1) M2))
		 (m-0 (r M1)(c M2))))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory (disable m-= m-binary-+ m-binary-*)
	    :use (:theorem
		  (m-= (m-+ (m-* M1 M2)(m-* (m-- M1) M2))
		       (m-* (m-+ M1 (m-- M1)) M2)))))))

(defthm
  m-*-m--_left
  (implies (and (equal (c M1)(r M2))
		(alist2p name M1)
		(alist2p name M2))
	   (m-= (m-* (m-- M1) M2)
		(m-- (m-* M1 M2))))
  :hints (("Goal"
	   :in-theory (disable m-= m-binary-+ m-binary-*)
	   :use ((:instance
		  uniqueness-of-m-+-inverse
		  (X (m-* (m-- M1) M2))
		  (Y (m-* M1 M2)))
		 m-*-m--_left-lemma))))

(local
 (defthm
   m-*-m--_right-lemma
   (implies (and (equal (c M1)(r M2))
		 (alist2p name M1)
		 (alist2p name M2))
	    (m-= (m-+ (m-* M1 M2)(m-* M1 (m-- M2)))
		 (m-0 (r M1)(c M2))))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory (disable m-= m-binary-+ m-binary-*)
	    :use ((:theorem
		   (m-= (m-+ (m-* M1 M2)(m-* M1 (m-- M2)))
			(m-* M1 (m-+ M2 (m-- M2)))))
		  (:instance
		    right-nullity-of-m-0-for-m-*
		    (p (c M2))))))))

(defthm
  m-*-m--_right
  (implies (and (equal (c M1)(r M2))
		(alist2p name M1)
		(alist2p name M2))
	   (m-= (m-* M1 (m-- M2))
		(m-- (m-* M1 M2))))
  :hints (("Goal"
	   :in-theory (disable m-= m-binary-+ m-binary-*)
	   :use ((:instance
		  uniqueness-of-m-+-inverse
		  (X (m-* M1 (m-- M2)))
		  (Y (m-* M1 M2)))
		 m-*-m--_right-lemma))))

(defthm
  m-=-m-trans-m-1
  (implies (and (integerp n)
		(> n 0))
	   (m-= (m-trans (m-1 n))
		(m-1 n))))

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

(verify-guards determinant-inverse-loop)

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

(defthm
  dimensions-m-/
  (implies (and (alist2p name M)
		(equal (first (dimensions name M))
		       (second (dimensions name M))))
	   (equal (dimensions name (m-/ M))
		  (list (car (dimensions name M))
			(car (dimensions name M))))))

(defthm
  alist2p-m-/
  (implies (and (alist2p name M)
		(equal (first (dimensions name M))
		       (second (dimensions name M))))
	   (alist2p name (m-/ M))))

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

(verify-guards m-singularp)

(in-theory (disable matrixp
		    m-=
		    m-0
		    m-1
		    m-trans
		    m-unary--
		    s-*
		    m-binary-+
		    m-binary-*
		    m-/
		    m-singularp))

(local (in-theory (enable m-singularp)))

(defthm
  uniqueness-of-m-*-inverse
  (implies (and (alist2p name X)
		(not (m-singularp Y))
		(equal (r X)(r Y))
		(equal (c X)(c Y))
		(m-= (m-* X Y)
		     (m-1 (r X))))
	   (m-= X (m-/ Y)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable
		       right-unity-of-m-1-for-m-*
		       left-unity-of-m-1-for-m-*)
	   :use ((:instance
		  M-=-IMPLIES-EQUAL-M-*-1
		  (M1 (m-* X Y))
		  (M1-equiv (m-1 (r X)))
		  (M2 (m-/ Y)))
		 (:instance
		  right-unity-of-m-1-for-m-*
		  (name '$arg)
		  (M1 X))
		 (:instance
		  left-unity-of-m-1-for-m-*
		  (name '$arg)
		  (M1 (m-/ Y)))))))

(defthm
  m-/-m-*-lemma
  (implies (and (not (m-singularp M1))
		(not (m-singularp M2))
		(equal (c M1)(r M2)))
	   (m-= (m-* (m-/ M2)(m-* (m-/ M1) M1) M2)
		(m-1 (r M1))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable
		       ASSOCIATIVITY-OF-M-*
		       left-unity-of-m-1-for-m-*)
	   :use (:instance
		 left-unity-of-m-1-for-m-*
		 (name '$arg)
		 (M1 M2)))))

(defthm
  Subgoal-8-hack
  (IMPLIES (AND (ALIST2P '$C M1)
		(ALIST2P '$C M2)
		(EQUAL (CADR (DIMENSIONS '$ARG M1))
		       (CAR (DIMENSIONS '$ARG M1)))
		(EQUAL (CAR (DIMENSIONS '$ARG M1))
		       (CADR (DIMENSIONS '$ARG M2)))
		(EQUAL (CAR (DIMENSIONS '$ARG M1))
		       (CAR (DIMENSIONS '$ARG M2))))
	   (ALIST2P NAME (M-* (M-/ M2)
			      (M-/ M1))))
  :hints (("Goal"
	   :in-theory (disable ALIST2P-M-*)
	   :use (:instance
		 ALIST2P-M-*
		 (M1 (M-/ M2))
		 (M2 (M-/ M1))
		 (name '$arg)))))

(defthm
  m-/-m-*
  (implies (and (not (m-singularp M1))
		(not (m-singularp M2))
		(not (m-singularp (m-* M1 M2)))
		(equal (c M1)(r M2)))
	   (m-= (m-/ (m-* M1 M2))
		(m-* (m-/ M2)(m-/ M1))))
  :hints (("Goal"
	   :use ((:instance
		  uniqueness-of-m-*-inverse
		  (X (m-* (m-/ M2)(m-/ M1)))
		  (Y (m-* M1 M2)))
		 m-/-m-*-lemma))))

(defthm
  m--_m-0
  (implies (and (integerp m)
		(> m 0)
		(integerp n)
		(> n 0))
	   (m-= (m-- (m-0 m n))
		(m-0 m n)))
  :hints (("Goal"
	   :in-theory (disable m-=-s-*-m-0
			       m-=-s-*_-1)
	   :use ((:instance
		  m-=-s-*-m-0
		  (a -1))
		 (:instance
		  m-=-s-*_-1
		  (M (m-0 m n)))))))

(defthm
  m-=_s-*_m--
  (implies (alist2p name M)
	   (m-= (s-* a (m-- M))
		(m-- (s-* a M))))
  :hints (("Goal"
	   :in-theory (disable
		       associate-scalars-left-s-*)
	   :use ((:instance
		  associate-scalars-left-s-*
		  (a1 -1)
		  (a2 a))
		 (:instance
		  associate-scalars-left-s-*
		  (a1 a)
		  (a2 -1))))))

(defthm
  distributivity-of-m--_over-m-+
  (implies (and (equal (car (dimensions name M1))
		       (car (dimensions name M2)))
		(equal (cadr (dimensions name M1))
		       (cadr (dimensions name M2)))
		(alist2p name M1)
		(alist2p name M2))
	   (m-= (m-- (m-+ M1 M2))
		(m-+ (m-- M1)(m-- M2))))
  :hints (("Goal"
	   :in-theory
	   (disable distributivity-of-s-*-over-m-+)
	   :use (:instance
		 distributivity-of-s-*-over-m-+
		 (a -1)))))

