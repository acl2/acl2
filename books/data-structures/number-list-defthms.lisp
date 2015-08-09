; number-list-defthms.lisp -- theorems about lists of numbers
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com)
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")
(include-book "number-list-defuns")
(include-book "deflist")
(deflabel number-list-defthms-section)

(defmacro real/rational-listp (x)
  #+:non-standard-analysis
  `(real-listp ,x)
  #-:non-standard-analysis
  `(rational-listp ,x))

; ------------------------------------------------------------
; Theorems
; ------------------------------------------------------------

(deflist rational-listp (l) rationalp
  (:options :omit-defun))

#+:non-standard-analysis
(deflist real-listp (l) realp
  (:options :omit-defun))

(deflist integer-listp (l) integerp
  (:options :omit-defun))

(deflist natural-listp (l) (lambda (x) (naturalp x))
  (:options :omit-defun))

; ---------- forwardchaining rules ----------

(defthm natural-listp-forward-to-integer-listp
  (implies (natural-listp l)
	   (integer-listp l))
  :rule-classes :forward-chaining)

(defthm integer-listp-forward-to-eqlable-listp
  (implies (integer-listp l)
	   (eqlable-listp l)))

; ---------- LINEAR ----------

(defthm <=maxlist
  (implies (member-equal x l)
	   (<= x (maxlist l)))
  :rule-classes (:rewrite :linear :forward-chaining))

(defthm minlist<=
  (implies (member-equal x l)
	   (<= (minlist l) x))
  :rule-classes (:rewrite :linear :forward-chaining))

; ---------- MEMBER-EQUAL ----------

(defthm member-equal-maxlist
  (implies (and (real/rational-listp l)
		(consp l))
	   (member-equal (maxlist l) l)))

(defthm member-equal-minlist
  (implies (and (real/rational-listp l)
		(consp l))
	   (member-equal (minlist l) l)))

(defthm member-equal-excess-natural
  (implies (natural-listp l)
	   (not (member-equal (excess-natural l) l)))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance <=maxlist (x (excess-natural l)) (l l)))
	   :in-theory (disable <=maxlist))))

(defthm numerically-sorted-numeric-insert
  (implies (and (real/rationalp x)
                (real/rational-listp l)
		(numerically-sorted l))
	   (numerically-sorted (numeric-insert x l)))
  :hints (("Goal" :induct (numeric-insert x l))))

(defthm numerically-sorted-numeric-sort
  (implies (real/rational-listp l)
	   (numerically-sorted (numeric-sort l))))

(deftheory number-list-defthms
  (set-difference-theories
   (current-theory :here)
   (current-theory 'number-list-defthms-section)))
