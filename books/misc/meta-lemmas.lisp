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
(include-book "xdoc/top" :dir :system)

;;;****************************************************************************
;;;
;;;    Introduction
;;;
;;;****************************************************************************

(defxdoc meta-lemmas
  :parents (meta)
  :short "A book of general purpose @(see meta) lemmas."
  :long "<p>Note that it may be a good idea to load this book last, so that the
lemmas in this book will take precedence over all others.</p>")

(defxdoc meta-functions
  :parents (meta-lemmas)
  :short "Meta-functions used to define the meta-lemmas.")

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

(defsection formal-consp
  :parents (meta-functions)
  :short "The definition of @(see CONSP) on formal terms."
  :long "<p>Note that FORMAL-CONSP is a `formal' predicate returning @('(QUOTE
T)') or @('(QUOTE NIL)').</p>"

  (defun formal-consp (term)
    (declare (xargs :guard (pseudo-termp term)))
    (case-match term
      (('QUOTE x) `(QUOTE ,(consp x)))
      (('CONS x y) (declare (ignore x y)) *t*)
      (& *nil*))))

(defsection formal-true-listp
  :parents (meta-functions)
  :short "The definition of @(see TRUE-LISTP) on formal terms."
  :long "<p>Note that FORMAL-TRUE-LISTP is a `formal' predicate returning
  @('(QUOTE T)') or @('(QUOTE NIL)').</p>"

  (defun formal-true-listp (term)
    (declare (xargs :guard (pseudo-termp term)))
    (case-match term
      (('QUOTE x) `(QUOTE ,(true-listp x)))
      (('CONS x y) (declare (ignore x)) (formal-true-listp y))
      (& *nil*))))

(defsection formal-nth
  :parents (meta-functions)
  :short "The definition of @('(NTH n lst)') for integers @('n') and formal
  terms @('lst')."

  (defun formal-nth (n lst)
    (declare (xargs :guard (and (integerp n)
                                (<= 0 n)
                                (pseudo-termp lst)
                                (equal (formal-true-listp lst) *t*))
                    :guard-hints (("Goal" :expand (formal-true-listp lst)))))
    (case-match lst
      (('QUOTE x) `(QUOTE ,(nth n x)))
      (& (cond
          ((zp n) (fargn lst 1))
          (t (formal-nth (- n 1) (fargn lst 2))))))))

(defsection reduce-nth-meta
  :parents (meta-functions)
  :short "@(see Meta) function for @(see NTH)."
  :long "<p>This meta function is designed to quickly rewrite terms of the form
@('(NTH n lst)') where n is an integer and lst is formally a proper list.</p>"

  (defun reduce-nth-meta (term)
    (declare (xargs :guard (pseudo-termp term)))
    (case-match term
      (('NTH ('QUOTE n) lst) (if (and (integerp n)
                                      (<= 0 n)
                                      (equal (formal-true-listp lst) *t*))
                                 (formal-nth n lst)
                               term))
      (& term))))

(defsection reduce-nth-meta-correct
  :extension reduce-nth-meta
  :long "<p>This meta lemma was designed to quickly rewrite the terms generated
  by the @(see mv-let) macro.</p>"

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
    :rule-classes ((:meta :trigger-fns (nth)))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;   EXPAND-MEMBER-META-CORRECT
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defsection formal-member
  :parents (meta-functions)
  :short "The definition of @(see MEMBER) for any @('x') on an @(see
  EQLABLE-LISTP) constant @('l')."
  :long "<p>This definition reposes the question @('(MEMBER x l)') as a set of
  nested IFs.</p>"

  (defun formal-member (x l)
    (declare (xargs :guard (and (pseudo-termp x)
                                (eqlable-listp l))))
    (cond
     ((endp l) *nil*)
     (t `(IF (EQL ,x (QUOTE ,(car l)))
             (QUOTE ,l)
             ,(formal-member x (cdr l)))))))

; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]

(defsection expand-member-meta
  :parents (meta-functions)
  :short "Meta function for @(see MEMBER-EQUAL)."
  :long "<p>This meta function is designed to quickly rewrite @('(MEMBER-EQUAL
x l)') to a set of nested IFs.  This will happen if l is a @('EQLABLE-LISTP')
constant.  Terms of this form arise for example in @(see CASE) macros.</p>"

  (defun expand-member-meta (term)
    (declare (xargs :guard (pseudo-termp term)))
    (case-match term
      (('MEMBER-EQUAL x ('QUOTE l)) (if (eqlable-listp l)
                                        (formal-member x l)
                                      term))
      (& term))))

; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal in documentation).]
(defsection expand-member-meta-correct
  :extension expand-member-meta
  :long "<p>This meta rule rewrites @('(MEMBER-EQUAL x l)') to a set of nested
IFs.  If l is an @(see EQLABLE-LISTP) constant, then we rewrite
@('(MEMBER-EQUAL x l)') to a set of nested IFs.  This lemma is used for example
to rewrite expressions generated by @(see CASE) macros for multiple choices,
without the necessity of @(see ENABLE)ing @(see MEMBER-EQUAL) and @(see
EQLABLE-LISTP).</p>"

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
     :hints (("Goal" :induct (formal-member x l)))))

  (defthm expand-member-meta-correct
    (implies (and (pseudo-termp term)
                  (alistp a))
     (equal (meta-ev term a)
	    (meta-ev (expand-member-meta term) a)))
    :rule-classes ((:meta :trigger-fns (member)))))


;;;****************************************************************************
;;;
;;;    Theories
;;;
;;;****************************************************************************

(defsection meta-lemma-theory
  :parents (meta-lemmas)
  :short "A theory of useful meta-lemmas."
  :long "<p>This theory contains the correctness lemmas for @(see
reduce-nth-meta) and @(see expand-member-meta).</p>"

  (deftheory meta-lemma-theory
    '(reduce-nth-meta-correct expand-member-meta-correct)))
