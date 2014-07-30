; list-defuns.lisp -- definitions in the theory of lists
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com)
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")
(deflabel list-defuns-section)

; * Structure of the Theory 
;
; The functions which occur in the list theory are selected from
; the ACL2 base theory (as defined in axioms.lisp) plus other functions
; which descend from earlier list libraries.
;
; list-defuns.lisp contains the definitions of functions which are not
; in the ACL2 base theory.
;
; list-defthms.lisp contains theorems about the functions in the
; theory. Segregating the theory into two files allows one to load
; only the definitions when one is only interested in running
; simulations.
;
; * General Strategy for Theory Construction
;
; The goal of this theory is to provide useful list-processing functions
; and useful theorems about those functions. We use the term ``function,''
; although some names are defined as macros, and some are introduced
; axiomatically.
;
; * Enabled and Disabled functions
;
; We plan to leave all recursive functions enabled. The theorem prover
; is good at deciding when to open recursive functions. An expert user
; can choose to disable them explicitly.
;
; Non-recursive functions are globally disabled by the book list-defthms.
;
; * Equality
;
; ACL2 (and Common Lisp) support three notions of equality: EQL, EQ and EQUAL.
; One uses EQL or EQ, rather than EQUAL, for efficiency. Many functions
; have three versions, each based on a different equality. MEMBER uses EQL, 
; however MEMBER-EQ and MEMBER-EQUAL are also defined.
;
; We have followed this naming convention. When a function relies on equality.
; the default notion is EQL; -EQ and -EQUAL versions of the function are
; also provided.
;
; In list-defthms, the EQL and EQ versions of all functions are re-written to the
; EQUAL version. All interesting rewrite rules about the list functions are
; expressed in terms of the EQUAL versions of list functions. 
;
; As a result, one can execute using the EQL or EQ versions, but one will reason
; using the EQUAL version.

; ------------------------------------------------------------
; Functions 
; ------------------------------------------------------------

; Function Name               In    Result 
;   (supporting function)     ACL2  Type
; ----------------------      ----  ---- 

; append (binary-append)      Yes   list
; butlast (take)              Yes   list
; firstn                      No    list
; last                        Yes   list
; make-list (make-list-ac)    Yes   list
; member (eql)                Yes   list
;   member-eq                 Yes   list
;   member-equal              Yes   list
; nth-seg                     No    list
; nthcdr                      Yes   list
; put-nth                     No    list
; put-seg                     No    list
; remove (eql)                Yes   list
;   remove-eq                 Yes   list
;   remove-equal              Yes   list
; remove-duplicates (eql)     Yes   list
;   remove-duplicates-eq      Yes   list
;   remove-duplicates-equal   Yes   list
; reverse (revappend)         Yes   list
; subseq (subseq-list)        Yes   list
; update-nth                  Yes   list   
;
; nth                         Yes   ?
;
; consp                       Yes   boolean
; initial-sublistp (eql)      No    boolean
;   initial-sublistp-eq       No    boolean
;   initial-sublistp-equal    No    boolean
; memberp (eql)               No    boolean
;   memberp-eq                No    boolesn
;   memberp-equal             No    boolean
; no-duplicatesp (eql)        Yes   boolean
;   no-duplicatesp-eq         Yes   boolean
;   no-duplicatesp-equal      Yes   boolean
; true-listp                  Yes   boolean
;
; len                         Yes   natural
; occurrences (eql)           No    natural
;   occurrences-eq            No    natural
;   occurrences-equal         No    natural
; position (eql)              Yes   natural V NIL
;   position-eq               Yes   natural V NIL
;   position-equal            Yes   natural V NIL


(defun firstn (n l)
  "The sublist of L consisting of its first N elements."
  (declare (xargs :guard (and (true-listp l)
                              (integerp n)
                              (<= 0 n))))
  (cond ((endp l) nil)
        ((zp n) nil)
        (t (cons (car l)
                 (firstn (1- n) (cdr l))))))

(defun initial-sublistp (l1 l2)
  "Is the first list an initial sublist of the second?"
  (declare (xargs :guard (and (eqlable-listp l1)
			      (eqlable-listp l2))))
  (cond ((endp l1) t)
	((endp l2) nil)
	(t (and (eql (car l1) (car l2))
		(initial-sublistp (cdr l1) (cdr l2))))))

(defun initial-sublistp-eq (l1 l2)
  "Is the first list an initial sublist of the second?"
  (declare (xargs :guard (and (symbol-listp l1)
			      (symbol-listp l2))))
  (cond ((endp l1) t)
	((endp l2) nil)
	(t (and (eq (car l1) (car l2))
		(initial-sublistp-eq (cdr l1) (cdr l2))))))

(defun initial-sublistp-equal (l1 l2)
  "Is the first list an initial sublist of the second?"
  (declare (xargs :guard (and (true-listp l1)
			      (true-listp l2))))
  (cond ((endp l1) t)
	((endp l2) nil)
	(t (and (equal (car l1) (car l2))
		(initial-sublistp-equal (cdr l1) (cdr l2))))))

(defun memberp (x l)
  (DECLARE (XARGS :GUARD
		  (IF (EQLABLEP X)
		      (TRUE-LISTP L)
		      (EQLABLE-LISTP L))))
  (consp (member x l)))

(defun memberp-eq (x l)
  (declare (xargs :guard
		  (if (symbolp x)
		      (true-listp l)
		      (symbol-listp l))))
  (consp (member-eq x l)))

(defun memberp-equal (x l)
  (declare (xargs :guard (true-listp l)))
  (consp (member-equal x l)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defun no-duplicatesp-eq (l)
;   (declare (xargs :guard (symbol-listp l)))
;   (cond ((endp l) t)
;         ((member-eq (car l) (cdr l)) nil)
;         (t (no-duplicatesp-eq (cdr l)))))

(defun nth-seg (i j l)
  "The sublist of L beginning at offset I for length J."
  (declare (xargs :guard (and (integerp i) (<= 0 i)
			      (integerp j) (<= 0 j)
			      (true-listp l))))
  (cond ((endp l) nil)
	((zp i)
	 (cond ((zp j) nil)
	       (t (cons (car l) (nth-seg i (1- j) (cdr l))))))
	(t (nth-seg (1- i) j (cdr l)))))

(defun occurrences-ac (item lst acc)
  (DECLARE (XARGS :GUARD
		  (AND (TRUE-LISTP LST)
		       (OR (EQLABLEP ITEM) (EQLABLE-LISTP LST))
		       (ACL2-NUMBERP ACC))))
  (cond ((endp lst) acc)
	((eql item (car lst)) (occurrences-ac item (cdr lst) (1+ acc)))
	(t (occurrences-ac item (cdr lst) acc))))
	 
(defun occurrences (item lst)
  (declare (xargs :guard (and (true-listp lst)
			      (or (eqlablep item) (eqlable-listp lst)))))
  (occurrences-ac item lst 0))

(defun occurrences-eq-ac (item lst acc)
  (DECLARE (XARGS :GUARD (and (true-listp lst)
			      (or (symbolp item)
				  (symbol-listp lst))
			      (ACL2-NUMBERP ACC))))
  (cond ((endp lst) acc)
	((eq item (car lst)) (occurrences-eq-ac item (cdr lst) (1+ acc)))
	(t (occurrences-eq-ac item (cdr lst) acc))))
	 
(defun occurrences-eq (item lst)
  (declare (xargs :guard (symbol-listp lst)))
  (occurrences-eq-ac item lst 0))

(defun occurrences-equal-ac (item lst acc)
  (DECLARE (XARGS :GUARD
		  (AND (TRUE-LISTP LST)
		       (ACL2-NUMBERP ACC))))
  (cond ((endp lst) acc)
	((equal item (car lst)) (occurrences-equal-ac item (cdr lst) (1+ acc)))
	(t (occurrences-equal-ac item (cdr lst) acc))))
	 
(defun occurrences-equal (item lst)
  (declare (xargs :guard (true-listp lst)))
  (occurrences-equal-ac item lst 0))

(defun put-nth (n v l)
  "The list derived from L by replacing its Nth element with value V."
  (declare (xargs :guard (and (integerp n) (<= 0 n)
			      (true-listp l))))
  (cond ((endp l) nil)
	((zp n) (cons v (cdr l)))
	(t (cons (car l) (put-nth (1- n) v (cdr l))))))

(defun put-seg (i seg l)
  "The list derived from L by replacing its contents beginning
   at location I with the contents of SEG. The length of the resulting
   list equals the length of L."
  (declare (xargs :guard (and (integerp i)
			      (<= 0 i)
			      (true-listp seg)
			      (true-listp l))))
  (cond ((endp l) nil)
	((zp i)
	 (cond ((endp seg) l)
	       (t (cons (car seg) (put-seg i (cdr seg) (cdr l))))))
	(t (cons (car l) (put-seg (1- i) seg (cdr l))))))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
#||
(local ; ACL2 primitive
 (defun remove-eq (x l)
   "The list constructed from L by removing all occurrences of X."
   (declare (xargs :guard (if (symbolp x)
                              (true-listp l)
                            (symbol-listp l))))
   (cond ((endp l) nil)
         ((eq x (car l)) (remove-eq x (cdr l)))
         (t (cons (car l) (remove-eq x (cdr l)))))))

(local ; ACL2 primitive
 (defun remove-equal (x l)
   "The list constructed from L by removing all occurrences of X."
   (declare (xargs :guard (true-listp l)))
   (cond ((endp l) nil)
         ((equal x (car l)) (remove-equal x (cdr l)))
         (t (cons (car l) (remove-equal x (cdr l)))))))
||#

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defun remove-duplicates-eq (l)
;   (declare (xargs :guard (symbol-listp l)))
;   (cond ((endp l) nil)
;         ((member-eq (car l) (cdr l)) (remove-duplicates-eq (cdr l)))
;         (t (cons (car l) (remove-duplicates-eq (cdr l))))))

(deftheory list-defuns
  (set-difference-theories (current-theory :here)
			   (current-theory 'list-defuns-section)))


