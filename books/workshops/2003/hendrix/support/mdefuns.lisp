;;;;; Implement low level operations for matrices.  No theorems other than those
;;;;; necessary for guard verification are proven.  See mdefthms.lisp for theorems.
(in-package "ACL2")

(include-book "vector")

;;; Returns true if l is a true-list where each element is a vector
;;; of length n.
(defun vector-list-of-lenp (l n)
  (declare (xargs :verify-guards t))
  (if (consp l)
      (and (mvectorp (car l))
	   (equal (len (car l)) n)
	   (vector-list-of-lenp (cdr l) n))
    (eq l nil)))

;;;; A Matrix is represented as a true-list of true-lists of numbers
;;;; where each list has the same length.  In contrast to traditional
;;;; mathematics, it is possible for a list to contain 0 rows and
;;;; columns in which case it is the empty matrix.  The empty matrix
;;;; is the only matrix with zero rows or columns, all other matrices
;;;; must contain at least one row and column.

;;; Returns true if m is a matrix.
(defun matrixp (m)
  (declare (xargs :verify-guards t))
  (or (eq m nil)
      (and (consp m)
	   (consp (car m))
	   (vector-list-of-lenp m (len (car m))))))

;;; Returns the m-empty.
(defun m-empty ()
  (declare (xargs :verify-guards t))
  nil)

;;; Returns true if m is an atom (this more general definition of
;;; an empty matrix is needed so that termination checking is
;;; easier).
(defun m-emptyp (m)
  (declare (xargs :guard (matrixp m)))
  (endp m))

;;; Return the number of rows in the matrix m.
(defun row-count (m)
  (declare (xargs :guard (matrixp m)))
  (len m))

;;; Return the number of columns in the matrix m.
(defun col-count (m)
  (declare (xargs :guard (matrixp m)))
  (len (car m)))

;;; Returns the top row of the matrix.
(defun row-car (m)
  (declare (xargs :guard (matrixp m)))
  (car m))

;;; Returns a matrix with the top row removed.
(defun row-cdr (m)
  (declare (xargs :guard (matrixp m)))
  (cdr m))

;;; Guard for "consing" a row (vector) to a matrix.
(defmacro row-cons-guard (l m)
  `(and (matrixp ,m)
	(mvectorp ,l)
        (consp ,l)
        (or (m-emptyp ,m)
            (equal (col-count ,m) (len ,l)))))

;;; Adds a new row r to the matrix m.  The existing rows are moved down
;;; one row.  If m is the m-empty, then r is expected to be of
;;; length greater than zero.  Otherwise, r is expected to be the same
;;; length as the number of columns in the matrix.
(defun row-cons (r m)
  (declare (xargs :guard (row-cons-guard r m)))
  (cons r m))

;;; Returns the leftmost column of the matrix.
(defun col-car (m)
  (declare (xargs :guard (matrixp m)))
  (if (or (endp m) (endp (car m)))
      nil
    (cons (caar m) (col-car (cdr m)))))

;;; Returns a matrix with the leftmost column removed.
(defun col-cdr (m)
  (declare (xargs :guard (matrixp m)))
  (if (or (endp m) (endp (cdar m)))
      nil
    (cons (cdar m) (col-cdr (cdr m)))))

;;; Implementation function for col-cons (below).
(defun col-cons-impl (l m)
  (declare (xargs :guard (and (true-listp l)
			      (true-listp m))))
  (if (consp l)
      (cons (cons (car l) (car m)) (col-cons-impl (cdr l) (cdr m)))
    nil))

(defmacro col-cons-guard (l m)
  `(and (matrixp ,m)
	(mvectorp ,l)
        (consp ,l)
	(or (m-emptyp ,m)
	    (equal (row-count ,m) (len ,l)))))

(local
 (defthm vector-list-is-true-list
   (implies (vector-list-of-lenp m i)
	    (true-listp m))
   :rule-classes :forward-chaining))

;;; Adds a new column c to the matrix m.  The existing rows are moved
;;; down one row.  If m is the m-empty, then c is expected to be of
;;; length greater than zero.  Otherwise, c is expected to be the same
;;; length as the number of rows in the matrix.

;;; The implementation using col-cons-impl so that it is guaranteed to
;;; always return something considered not to be the empty matrix even
;;; if the guards are violated.
(defun col-cons (l m)
  (declare (xargs :guard (col-cons-guard l m)))
  (if (consp l)
      (col-cons-impl l m)
    (cons nil nil)))
