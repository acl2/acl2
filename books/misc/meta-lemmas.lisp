; meta-lemmas.lisp  --  meta-lemmas for NTH and MEMBER
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    "meta-lemmas.lisp"
;;;
;;;    This book defines a useful set of meta lemmas.  This book includes the
;;;    meta functions, and the DEFEVALUATOR forms and lemmas. This book
;;;    requires only the Acl2 initialization theory for its certification.
;;;
;;;    Special thanks to Matt Kaufmann of CLInc for getting this one started.
;;;    
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West Sixth Street, Suite 290
;;;    Austin, Texas 78703
;;;    (512) 322-9951
;;;    brock@cli.com
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

;;;****************************************************************************
;;;
;;;    Introduction
;;;
;;;****************************************************************************

(deflabel meta-lemmas
  :doc ":doc-section miscellaneous
  A book of general purpose meta-lemmas.
  ~/
  Note that it may be a good idea to load this book last, so that the lemmas
  in this book will take precedence over all others.
  ~/~/")

(deflabel meta-functions
  :doc ":doc-section meta-lemmas
  Meta-functions used to define the meta-lemmas.
  ~/~/~/")

;;;****************************************************************************
;;;
;;;    The Evaluator.
;;;
;;;    We only have one evaluator, which we'll extend as necessary.
;;;
;;;****************************************************************************

(defevaluator meta-ev meta-ev-list	
  ((car x)
   (cdr x)
   (cons x y)
   (eql x y)
   (if x y z)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
   (member-equal x y)
   (nth x y)
   (true-listp x)))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;  REDUCE-NTH-META-CORRECT 
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun formal-consp (term)
  ":doc-section meta-functions
  The definition of CONSP on formal terms.
  ~/~/
  Note that FORMAL-CONSP is a `formal' predicate returning (QUOTE T)
  or (QUOTE NIL).~/"
  (declare (xargs :guard (pseudo-termp term)))
  (case-match term
    (('QUOTE x) `(QUOTE ,(consp x)))
    (('CONS x y) (declare (ignore x y)) *t*)
    (& *nil*)))
   
(defun formal-true-listp (term)
  ":doc-section meta-functions
  The definition of TRUE-LISTP on formal terms.
  ~/~/
  Note that FORMAL-TRUE-LISTP is a `formal' predicate returning (QUOTE T)
  or (QUOTE NIL).~/"
  (declare (xargs :guard (pseudo-termp term)))
  (case-match term
    (('QUOTE x) `(QUOTE ,(true-listp x)))
    (('CONS x y) (declare (ignore x)) (formal-true-listp y))
    (& *nil*)))

(defun formal-nth (n lst)
  ":doc-section meta-functions
  The definition of (NTH n lst) for integers n and formal terms lst.
  ~/~/~/"
  (declare (xargs :guard (and (integerp n)
                              (<= 0 n)
                              (pseudo-termp lst)
                              (equal (formal-true-listp lst) *t*))
                  :guard-hints
		  (("Goal"
		    :expand (formal-true-listp lst)))))
  (case-match lst
    (('QUOTE x) `(QUOTE ,(nth n x)))
    (& (cond
	((zp n) (fargn lst 1))
	(t (formal-nth (- n 1) (fargn lst 2)))))))

(defun reduce-nth-meta (term)
  ":doc-section meta-functions
  Meta function for NTH.
  ~/~/
  This meta function is designed to quickly rewrite terms of the form
  (NTH n lst) where n is an integer and lst is formally a proper list. ~/"
  (declare (xargs :guard (pseudo-termp term)))
  (case-match term
    (('NTH ('QUOTE n) lst) (if (and (integerp n)
				    (<= 0 n)
				    (equal (formal-true-listp lst) *t*))
			       (formal-nth n lst)
			     term))
    (& term)))

(encapsulate ()

  (local
   (defthm formal-true-listp-implies-true-listp-meta-ev
     (implies
      (and (pseudo-termp term)
	   (alistp a)
	   (equal (formal-true-listp term) *t*))
      (true-listp (meta-ev term a)))
     :hints
     (("Goal"
       :induct (formal-true-listp term)))))

  (local
   (defthm reduce-nth-meta-correct-lemma
     (implies
      (and (integerp n)
	   (>= n 0)
	   (pseudo-termp lst)
	   (equal (formal-true-listp lst) *t*)
	   (alistp a))
      (equal (meta-ev (formal-nth n lst) a)
	     (nth n (meta-ev lst a))))
     :hints
     (("Goal"
       :induct (formal-nth n lst)
       :expand (formal-true-listp lst)))))

  (defthm reduce-nth-meta-correct
    (implies
     (and (pseudo-termp term)
	  (alistp a))
     (equal (meta-ev term a)
	    (meta-ev (reduce-nth-meta term) a)))
    :rule-classes ((:meta :trigger-fns (nth)))
    :doc ":doc-section meta-lemmas
    Meta: Simplify (NTH n lst) for integer n and formal true-listp lst.
    ~/
    This meta lemma was designed to quickly rewrite the terms generated by
    the MV-LET macro.~/~/"))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;   EXPAND-MEMBER-META-CORRECT
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun formal-member (x l)
  ":doc-section meta-functions
  The definition of MEMBER for any x on an EQLABLE-LISTP constant l.
  ~/~/
  This definition reposes the question (MEMBER x l) as a set of nested
  IFs.~/"
  (declare (xargs :guard (and (pseudo-termp x)
			      (eqlable-listp l))))
  (cond
   ((endp l) *nil*)
   (t `(IF (EQL ,x (QUOTE ,(car l)))
	   (QUOTE ,l)
	 ,(formal-member x (cdr l))))))
  
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
(defun expand-member-meta (term)
  ":doc-section meta-functions
  Meta function for MEMBER-EQUAL.
  ~/~/
  This meta function is designed to quickly rewrite (MEMBER-EQUAL x l) to a set
  of nested IFs.  This will happen if l is a EQLABLE-LISTP constant.  Terms of
  this form arise for example in CASE macros.~/"

  (declare (xargs :guard (pseudo-termp term)))

  (case-match term
    (('MEMBER-EQUAL x ('QUOTE l)) (if (eqlable-listp l)
                                      (formal-member x l)
                                    term))
    (& term)))

; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal in documentation).]
(encapsulate ()

  (local
   (defthm pseudo-termp-formal-member
     (implies
      (and (pseudo-termp x)
	   (eqlable-listp l))
      (pseudo-termp (formal-member x l)))))

  (local
   (defthm eqlable-listp-recognizer
     (implies
      (eqlable-listp l)
      (true-listp l))
     :rule-classes :compound-recognizer))

  (local
   (defthm expand-member-meta-correct-lemma
     (implies
      (and (pseudo-termp x)
	   (eqlable-listp l)
	   (alistp a))
      (equal (meta-ev (formal-member x l) a)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
	     (member-equal (meta-ev x a) l)))
     :hints
     (("Goal"
       :induct (formal-member x l)))))

  (defthm expand-member-meta-correct
    (implies
     (and (pseudo-termp term)
	  (alistp a))
     (equal (meta-ev term a)
	    (meta-ev (expand-member-meta term) a)))
    :rule-classes ((:meta :trigger-fns (member)))
    :doc ":doc-section meta-lemmas
    Meta: Rewrite (MEMBER-EQUAL x l) to a set of nested IFs.
    ~/
    If l is an EQLABLE-LISTP constant, then we rewrite (MEMBER-EQUAL x l) to a
    set of nested IFs.  This lemma is used for example to rewrite expressions
    generated by CASE macros for multiple choices, without the necessity of
    ENABLEing MEMBER-EQUAL and EQLABLE-LISTP.~/~/"))


;;;****************************************************************************
;;;
;;;    Theories
;;;
;;;****************************************************************************

(deftheory meta-lemma-theory
  '(reduce-nth-meta-correct expand-member-meta-correct)
  :doc ":doc-section meta-lemmas
  A theory of useful meta-lemmas.
  ~/
  This theory contains the following lemmas:
  ~/~/
  :cite reduce-nth-meta-correct
  :cite expand-member-meta-correct")
