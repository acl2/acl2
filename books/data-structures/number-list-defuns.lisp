; number-list-defuns.lisp -- definitions about lists of numbers
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com)
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")
(include-book "list-defuns")
(deflabel number-list-defuns-section)

; ------------------------------------------------------------
; Definitions and Macros
; ------------------------------------------------------------
;                   in
; name              Acl2?  comment
; ------------------------------------------------

; naturalp (macro)   n     recognize a natural number

; excess-natural     n     the least upper bound of a list of naturals
; integer-listp      y     recognize a list of integers
; maxlist            n     find the maximum element of a list of real/rationalps
; minlist            n     find the minimum element of a list of real/rationalps
; natural-listp      n     recognize a list of naturals
; numeric-insert     n     insert a real/rational into a list
; numeric-sort       n     sort a list of real/rationals into ascending order
; numerically-sorted n     recognize a list of sorted real/rationals (ascending order)
; rational-listp     y     recognize a list of rationals
; real-listp         y     recognize a list of reals (ACL2(r) only)
; sum                n     sum of a list of real/rationals

(defmacro real/rational-listp (x)
  #+:non-standard-analysis
  `(real-listp ,x)
  #-:non-standard-analysis
  `(rational-listp ,x))

(defmacro naturalp (x)
  `(and (integerp ,x)
	(<= 0 ,x)))

(defun natural-listp (l)
  "Recognize a list of naturals."
  (declare (xargs :guard t))
  (cond ((atom l) (eq l nil))
	(t (and (naturalp (car l))
		(natural-listp (cdr l))))))

(defun maxlist (l)
  "The largest element of a non-empty list of real/rationals."
  (declare (xargs :guard (and (real/rational-listp l)
			      (consp l))))
  (cond ((endp (cdr l)) (car l))
	(t (max (car l) (maxlist (cdr l))))))

(defun minlist (l)
  "The smallest element of a non-empty list of real/rationals."
  (declare (xargs :guard (and (real/rational-listp l)
			      (consp l))))
  (cond ((endp (cdr l)) (car l))
	(t (min (car l) (minlist (cdr l))))))

(defun sum (l)
  "The sum of the elements of a list of real/rationals."
  (declare (xargs :guard (real/rational-listp l)))
  (cond ((endp l) 0)
	(t (+ (car l) (sum (cdr l))))))

(defun excess-natural (l)
  "The least upper bound of a list of naturals."
  (declare (xargs :guard (natural-listp l)))
  (if (consp l)
      (+ 1 (maxlist l))
      0))

(defun numerically-sorted (l)
  "Recognize a list of real/rationals sorted in ascending order."
  (declare (xargs :guard (real/rational-listp l)))
  (cond ((endp l) t)
	((endp (cdr l)) t)
	(t (and (<= (car l) (cadr l))
		(numerically-sorted (cdr l))))))

(defun numeric-insert (x l)
  "Insert the real/rational x immediately before the first element of
   list L that is larger than x."
  (declare (xargs :guard (and (real/rationalp x)
			      (real/rational-listp l))))
  (cond ((endp l) (list x))
	((< (car l) x) (cons (car l) (numeric-insert x (cdr l))))
	(t (cons x l))))

(defun numeric-sort (l)
  "Sort a list of real/rationals into ascending order."
  (declare (xargs :guard (real/rational-listp l)))
  (cond ((endp l) nil)
	(t (numeric-insert (car l)
			   (numeric-sort (cdr l))))))

; ------------------------------------------------------------
; Type theorems about these functions
; ------------------------------------------------------------

(defthm real/rationalp-maxlist
  (implies (and (real/rational-listp l)
		(consp l))
	   (real/rationalp (maxlist l)))
  :rule-classes (:rewrite :type-prescription))

(defthm real/rationalp-minlist
  (implies (and (real/rational-listp l)
		(consp l))
	   (real/rationalp (minlist l)))
  :rule-classes (:rewrite :type-prescription))

(defthm real/rationalp-sum
  (implies (real/rational-listp l)
	   (real/rationalp (sum l)))
  :rule-classes (:rewrite :type-prescription))

(defthm naturalp-excess-natural
  (implies (natural-listp l)
	   (naturalp (excess-natural l)))
  :rule-classes (:rewrite :type-prescription))

(defthm real/rational-listp-numeric-insert
  (implies (and (real/rationalp x)
		(real/rational-listp l))
	   (real/rational-listp (numeric-insert x l)))
  :rule-classes (:rewrite :type-prescription))

(defthm real/rational-listp-numeric-sort
  (implies (real/rational-listp l)
	   (real/rational-listp (numeric-sort l)))
  :rule-classes (:rewrite :type-prescription))

(deftheory number-list-defuns
  (set-difference-theories (current-theory :here)
			   (current-theory 'number-list-defuns-section)))
