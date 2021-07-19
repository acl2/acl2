; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

; In this file we define the Tau system, a collection of data structures and
; algorithms for reasoning quickly about monadic predicates.  However, we need
; certain basic facilities from the rest of ACL2's sources and we have put them
; all in the following ``prelude.''  See the Essay on the Tau System below for
; a discussion of the tau design.

; Prelude:  General-Purpose Functions Having Nothing Specific to do with Tau

; A ``singleton evg list'' is a singleton list with an evg in it.  A ``neg-evg
; list'' is a duplicate-free list of singleton evg lists, ordered ascending
; almost according to lexorder.  The ``almost'' is due to the fact that we let
; the singleton list containing NIL be the smallest thing in our ordering.  So
; a typical neg-evg list might be ((NIL) (0) (1) (2) (A) (B) (C)).
; Foreshadowing: a neg-evg list represents the evgs ruled out by a tau.  If a
; tau were to contain the neg-evgs above, then the tau would include the
; conjuncts (not (equal x 'NIL)), (not (equal x '0)), ..., and (not (equal x
; 'C)).  We want NIL in the front so that we can rapidly answer the question
; ``does this tau mean the subject is non-NIL?''

; We define the ``almost-lexorder'' function as well as functions for
; determining whether a singleton is a member of a neg-evg list and for
; inserting a singleton into such a list.  These functions are optimized
; exploiting the fact that every item compared is known to be a singleton, so
; instead of using lexorder on (x) and (y) we use it on x and y, i.e., we
; always compare just the cars of the lists.

(defun almost-lexorder-singletons (x y)
  (cond ((eq (car x) nil) t)
        ((eq (car y) nil) nil)
        (t (lexorder (car x) (car y)))))

; We actually don't use almost-lexorder-singletons in the membership and
; insertion functions because we make special cases for nil.

(defun member-nil-neg-evgs (neg-evg-lst)
  (and (consp neg-evg-lst)
       (eq (car (car neg-evg-lst)) nil)))

(defun member-neg-evgs1 (evg neg-evg-lst)

; Evg is non-NIL and neg-evg-lst is a neg-evg list that does not contain (NIL).

  (cond ((endp neg-evg-lst) nil)
        ((lexorder (car (car neg-evg-lst)) evg)
         (or (equal evg (car (car neg-evg-lst)))
             (member-neg-evgs1 evg (cdr neg-evg-lst))))
        (t nil)))

(defun member-neg-evgs (x neg-evg-lst)

; X is a singleton list and neg-evg-lst is a neg-evg list -- a list of
; singletons ordered almost with lexorder but with (nil) as the smallest item
; in the ordering.  We return t if x is a member of neg-evg-lst and nil
; otherwise.

  (cond ((endp neg-evg-lst) nil)
        ((equal (car x) (car (car neg-evg-lst)))
         t)
        ((eq (car x) nil) nil)
        (t (member-neg-evgs1 (car x) (cdr neg-evg-lst)))))

(defun insert-neg-evgs1 (evg x neg-evg-lst)

; X is a singleton evg list containing evg.  Evg is non-nil.  Neg-evg-lst is a
; neg-evg list that does not contain (NIL) and does not contain x.  We insert x
; into neg-evg-lst.

  (cond ((endp neg-evg-lst) (cons x nil))
        ((lexorder (car (car neg-evg-lst)) evg)
         (cons (car neg-evg-lst)
               (insert-neg-evgs1 evg x (cdr neg-evg-lst))))
        (t (cons x neg-evg-lst))))

(defun insert-neg-evgs (x neg-evg-lst)
  (cond ((endp neg-evg-lst) (cons x neg-evg-lst))
        ((eq (car x) nil) (cons x neg-evg-lst))
        ((eq (car (car neg-evg-lst)) nil)
         (cons (car neg-evg-lst)
               (insert-neg-evgs1 (car x) x (cdr neg-evg-lst))))
        (t (insert-neg-evgs1 (car x) x neg-evg-lst))))

; Now we define some other sorting functions.

(defun merge-car-< (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((< (car (car l1)) (car (car l2)))
         (cons (car l1) (merge-car-< (cdr l1) l2)))
        (t (cons (car l2) (merge-car-< l1 (cdr l2))))))

(defun merge-sort-car-< (l)

; Merge-sort, where elements a and b are compared via (car a) < (car b).

  (cond ((null (cdr l)) l)
        (t (merge-car-< (merge-sort-car-< (evens l))
                        (merge-sort-car-< (odds l))))))

(defun merge-cadr-< (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((< (cadr (car l1)) (cadr (car l2)))
         (cons (car l1) (merge-cadr-< (cdr l1) l2)))
        (t (cons (car l2) (merge-cadr-< l1 (cdr l2))))))

(defun merge-sort-cadr-< (l)

; Merge-sort, where elements a and b are compared via (cadr a) < (cadr b).

  (cond ((null (cdr l)) l)
        (t (merge-cadr-< (merge-sort-cadr-< (evens l))
                         (merge-sort-cadr-< (odds l))))))

(defun strip-caddrs (x)
  (declare (xargs :guard (all->=-len x 3)))
  (cond ((endp x) nil)
        (t (cons (caddar x) (strip-caddrs (cdr x))))))

; In forming rules from terms we often strip out individual branches of the
; term, e.g., (implies (and h1 h2) (and c1 (implies h3 c2))) is treated as
; though it were (and (implies (and h1 h2) c1) (implies (and h1 h2 h3) c2)),
; except after distributing the IMPLIES over the concluding ANDs, we do not
; form a term but just traffic in list of pairs (((h1 h2) . c1) ((h1 h2 h3)
; . c2)).  This is called ``unprettyifying.''

(defun unprettyify/add-hyps-to-pairs (hyps lst)

; Each element of lst is a pair of the form (hypsi . concli), where hypsi
; is a list of terms.  We append hyps to hypsi in each pair.

  (cond ((null lst) nil)
        (t (cons (cons (append hyps (caar lst)) (cdar lst))
                 (unprettyify/add-hyps-to-pairs hyps (cdr lst))))))

(defun unprettyify (term)

; This function returns a list of pairs (hyps . concl) such that the
; conjunction of all (implies (and . hyps) concl) is equivalent to
; term.  Hyps is a list of hypotheses, implicitly conjoined.  Concl
; does not begin with an AND (of course, its a macro, but concl
; doesn't begin with an IF that represents an AND) or IMPLIES.
; In addition concl doesn't begin with an open lambda.

; This function is used to extract the :REWRITE rules from a term.
; Lambdas are sort of expanded to expose the conclusion.  They are not
; expanded in the hypotheses, or within an function symbol other than
; the top-level IFs and IMPLIES.  But top-level lambdas (those enclosing
; the entire term) are blown away.

; Thus, if you have a proposed :REWRITE rule
;    (implies (and p q) (let ((x a)) (equal (f x) b)))
; it will be converted to
;    (implies (and p q) (equal (f a) b)).
; The rule
;    (let ((x a)) (implies (and (p x) (q x)) (equal (f x) b))) [1]
; will become
;    (implies (and (p a) (q a)) (equal (f a) b)).              [2]
; But
;    (implies (let ((x a)) (and (p x) (q x)))                  [3]
;             (equal (let ((x a)) (f x)) b))
; stays untouched.  In general, once you've moved the let into a
; hypothesis it is not seen or opened.  Once you move it into the
; equivalence relation of the conclusion it is not seen or opened.
; Note that this processing of lambdas can cause terms to be duplicated
; and simplified more than once (see a in [2] compared to [3]).

  (case-match term
              (('if t1 t2 t3)
               (cond ((equal t2 *nil*)
                      (append (unprettyify (dumb-negate-lit t1))
                              (unprettyify t3)))
                     ((equal t3 *nil*)
                      (append (unprettyify t1)
                              (unprettyify t2)))
                     (t (list (cons nil term)))))
              (('implies t1 t2)
               (unprettyify/add-hyps-to-pairs
                (flatten-ands-in-lit t1)
                (unprettyify t2)))
              ((('lambda vars body) . args)
               (unprettyify (subcor-var vars args body)))
              (& (list (cons nil term)))))

(defun reprettyify (hyps concl wrld)
  (cond ((null hyps)
         (untranslate concl t wrld))
        ((null (cdr hyps))
         `(IMPLIES ,(untranslate (car hyps) t wrld)
                   ,(untranslate concl t wrld)))
        (t `(IMPLIES (AND ,@(untranslate-lst hyps t wrld))
                     ,(untranslate concl t wrld)))))

; Before moving on, we develop the code to translate a type-prescription
; to a term so that we can recognize if a type-prescription can be
; represented as a tau signature rule.

; The next few functions are used to produced the formulas represented by
; type-prescriptions.

(defun convert-returned-vars-to-term-lst (term vars)
  (cond ((null vars) nil)
        (t (cons (mcons-term* 'equal term (car vars))
                 (convert-returned-vars-to-term-lst term (cdr vars))))))

(defun implicate (t1 t2)

; We return a term equivalent to (IMPLIES t1 t2).

  (declare (xargs :guard (and (pseudo-termp t1)
                              (pseudo-termp t2))))
  (cond ((equal t1 *t*) t2)
        ((equal t1 *nil*) *t*)
        ((equal t2 *t*) *t*)
        ((equal t2 *nil*) (dumb-negate-lit t1))
        (t (mcons-term* 'implies t1 t2))))

; We now develop the function that converts a type-set into a term.

(defrec type-set-inverter-rule ((nume . ts) terms . rune) nil)

; A type-set-inverter-rule states that x has type-set ts iff the conjunction of
; terms{X/x} is true.  Thus, for example, if :ts is *ts-integer* then :terms is
; '((INTEGERP X)).

; WARNING:  See the warning in convert-type-set-to-term if you are ever
; tempted to generalize type-set-inverter-rules to allow hypotheses that
; may be FORCEd or CASE-SPLITd!

; A type-set, s, is a disjunction of the individual bits in it.  Thus, to
; create a term whose truth is equivalent to the claim that X has type-set s it
; is sufficient to find any type-set-inverter-rule whose :ts is a subset of s
; and then disjoin the :term of that rule to the result of recursively creating
; the term recognizing s minus :ts.  This assumes one has a rule for each
; single type bit.

; The following is the initial setting of the world global variable
; 'type-set-inverter-rules.  WARNING: EACH TERM IN :TERMS MUST BE IN TRANSLATED
; FORM.  The list is ordered in an important way: the larger type-sets are at
; the front.  This ordering is exploited by convert-type-set-to-term-lst which
; operates by finding the largest recognized type set group and knocks it out
; of the type set.

;; Historical Comment from Ruben Gamboa:
;; I added a rule for realp, non-zero real, non-negative real,
;; non-positive real, positive real, negative real, irrational,
;; negative irrational, positive irrational, and complex.

(defconst *initial-type-set-inverter-rules*
  (list (make type-set-inverter-rule                 ;;; 12 (15) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-complement *ts-cons*)
              :terms '((atom x)))
        (make type-set-inverter-rule                 ;;; 7 (10) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-acl2-number*
              :terms '((acl2-numberp x)))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (8) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-real*
              :terms '((realp x)))
        (make type-set-inverter-rule                 ;;; 6 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-rational*
              :terms '((rationalp x)))
        (make type-set-inverter-rule                 ;;; 6 (9) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-intersection *ts-acl2-number* (ts-complement *ts-zero*))
              :terms '((acl2-numberp x) (not (equal x '0))))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (7) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-intersection *ts-real* (ts-complement *ts-zero*))
              :terms '((realp x) (not (equal x '0))))
        (make type-set-inverter-rule                 ;;; 5 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-intersection *ts-rational* (ts-complement *ts-zero*))
              :terms '((rationalp x) (not (equal x '0))))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (5) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-union *ts-positive-real* *ts-zero*)
              :terms '((realp x) (not (< x '0))))
        (make type-set-inverter-rule                 ;;; 4 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-union *ts-positive-rational* *ts-zero*)
              :terms '((rationalp x) (not (< x '0))))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (4) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-union *ts-negative-real* *ts-zero*)
              :terms '((realp x) (not (< '0 x))))
        (make type-set-inverter-rule                 ;;; 3 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-union *ts-negative-rational* *ts-zero*)
              :terms '((rationalp x) (not (< '0 x))))
        (make type-set-inverter-rule                 ;;; 4 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-integer*
              :terms'((integerp x)))
        (make type-set-inverter-rule                 ;;; 3 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-intersection *ts-integer* (ts-complement *ts-zero*))
              :terms '((integerp x) (not (equal x '0))))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (4) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-positive-real*
              :terms'((realp x) (< '0 x)))
        (make type-set-inverter-rule                 ;;; 3 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-positive-rational*
              :terms'((rationalp x) (< '0 x)))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (3) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-negative-real*
              :terms'((realp x) (< x '0)))
        (make type-set-inverter-rule                 ;;; 2 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-negative-rational*
              :terms'((rationalp x) (< x '0)))
        (make type-set-inverter-rule                 ;;; 3 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-union *ts-positive-integer* *ts-zero*)
              :terms '((integerp x) (not (< x '0))))
        (make type-set-inverter-rule                 ;;; 2 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-union *ts-negative-integer* *ts-zero*)
              :terms '((integerp x) (not (< '0 x))))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (2) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-non-ratio*
              :terms'((realp x) (not (rationalp x))))
        (make type-set-inverter-rule                 ;;; 2 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-ratio*
              :terms'((rationalp x) (not (integerp x))))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (1) bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-negative-non-ratio*
              :terms'((realp x) (not (rationalp x)) (< x '0)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-negative-ratio*
              :terms'((rationalp x) (not (integerp x)) (< x '0)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-negative-integer*
              :terms'((integerp x) (< x '0)))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (1) bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-positive-non-ratio*
              :terms'((realp x) (not (rationalp x)) (< '0 x)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-positive-ratio*
              :terms'((rationalp x) (not (integerp x)) (< '0 x)))
        (make type-set-inverter-rule                 ;;; 2 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-positive-integer*
              :terms'((integerp x) (< '0 x)))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (2) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-complex*
              :terms'((complexp x)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-integer>1*
              :terms'((integerp x) (< '1 x)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-complex-rational*
              :terms'((complex-rationalp x)))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (1) bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-complex-non-rational*
              :terms'((complexp x) (not (complex-rationalp x))))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-zero*
              :terms'((equal x '0)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-one*
              :terms'((equal x '1)))
        (make type-set-inverter-rule                 ;;; 3 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-symbol*
              :terms'((symbolp x)))
        (make type-set-inverter-rule                 ;;;2 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-boolean*
              :terms'((if (equal x 't) 't (equal x 'nil))))
        (make type-set-inverter-rule                 ;;; 2 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-cons*
              :terms'((consp x)))
        (make type-set-inverter-rule                 ;;; 2 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-true-list*
              :terms'((true-listp x)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-improper-cons*
              :terms'((consp x) (not (true-listp x))))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-proper-cons*
              :terms'((consp x) (true-listp x)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-non-t-non-nil-symbol*
              :terms '((symbolp x) (not (equal x 't)) (not (equal x 'nil))))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-t*
              :terms'((equal x 't)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-nil*
              :terms'((equal x 'nil)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-string*
              :terms'((stringp x)))
        (make type-set-inverter-rule                 ;;; 1 bit
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-character*
              :terms'((characterp x)))))

(defun convert-type-set-to-term-lst (ts rules ens lst ttree)

; We map over the list of type-set-inverter rules and each time we find an
; enabled rule whose :ts is a subset of ts, we accumulate its conjoined :terms
; and its :rune, and knock off those bits of ts.  We return (mv lst ttree),
; where lst is a list of terms in the variable X whose disjunction is
; equivalent to ts.

  (cond
   ((null rules) (mv (reverse lst) ttree))
   ((and (enabled-numep (access type-set-inverter-rule (car rules) :nume) ens)
         (ts= (access type-set-inverter-rule (car rules) :ts)
              (ts-intersection
               (access type-set-inverter-rule (car rules) :ts)
               ts)))
    (convert-type-set-to-term-lst
     (ts-intersection
      ts
      (ts-complement (access type-set-inverter-rule (car rules) :ts)))
     (cdr rules)
     ens
     (add-to-set-equal
      (conjoin (access type-set-inverter-rule (car rules) :terms))
      lst)
     (push-lemma (access type-set-inverter-rule (car rules) :rune)
                 ttree)))
   (t (convert-type-set-to-term-lst ts (cdr rules) ens lst ttree))))

(defun convert-type-set-to-term1 (x ts flg ens w ttree)

; X is a term and ts a type-set.  We generate a term that is provably
; equivalent, in w, to "x has type set ts".

; E.g., if x is the term (FN X Y) and ts is *ts-rational* then our output will
; be (RATIONALP (FN X Y)), whether flg is t or nil.  We return (mv term ttree),
; where term is the term and ttree contains the 'lemmas used.  We do not use
; disabled type-set-inverters.

; The only time flg matters is the case that flg is true, term is known to be
; Boolean, and ts is *ts-t*.  In that case we return x instead of the provably
; equivalent (equal x 'T).  If you're trying to explain or show what a type-set
; means, you need to use flg = nil.  But if you're trying to assume or prove
; that x has the given type-set, you may use flg = t.  See the comment where
; flg is used below for an explanation of why this feature matters.

; Note: This function is just a helper function for convert-type-set-to-term.
; That function is called in several places in the ACL2 code and in a couple of
; books.  To save the bother of changing those calls, we named this function
; convert-type-set-to-term1.  Convert-type-set-to-term calls it with flg=nil.
; The only place that this function is called directly (and with flg=t) is
; clausify-type-alist, which is used by clausify-assumption.

; Note:  It would be a major change to make this function force assumptions.
; If the returned ttree contains 'assumption tags then the primary use of
; this function, namely the expression of type-alists in clausal form so that
; assumptions can be attacked as clauses, becomes problematic.  Don't glibly
; generalize type-set-inverter rules to force assumptions.

  (cond ((ts= ts *ts-unknown*) (mv *t* ttree))
        ((and flg
              (ts= ts *ts-t*)
              (ts-booleanp x ens w))

; We commented out this case for Version_3.5 because of a soundness issue that
; no longer exists (because we don't create type-prescription rules for
; subversive functions; see putprop-type-prescription-lst).  We left it
; commented out because we thought it was an unimportant case that hasn't been
; missed.  But, while working with Version_6.4, we encountered a proof in a
; script from Warren Hunt that sped up from 77 seconds to 16 seconds when
; including this case.  That script generated a lot of forced assumptions, and
; this code is responsible for creating the clauses proved in the forcing
; round.  In particular, if a lemma is forced in a context in which one of the
; governing assumptions is (< alpha beta), then that assumption is encoded as
; (equal (< alpha beta) t) in the clause attacked by the forcing round -- if
; those clauses are generated by the code in Version_3.5 through Version_6.4,
; i.e., if flg=nil.  But that means the inequality is hidden until the EQUAL is
; rewritten, delaying, for example, tau.  In the Hunt script, tau can prove the
; clauses generated with flg = t.  So, after Version_6.4 we restored this case,
; conditional on flg.

         (mv x ttree))
        ((ts-complementp ts)
         (mv-let (lst ttree)
                 (convert-type-set-to-term-lst
                  (ts-complement ts)
                  (global-val 'type-set-inverter-rules w)
                  ens nil ttree)
                 (mv (subst-var x 'x
                                (conjoin (dumb-negate-lit-lst lst)))
                     ttree)))
        (t (mv-let (lst ttree)
                   (convert-type-set-to-term-lst
                    ts
                    (global-val 'type-set-inverter-rules w)
                    ens nil ttree)
                   (mv (subst-var x 'x (disjoin lst)) ttree)))))

(defun convert-type-set-to-term (x ts ens w ttree)

; See the comments in the helper function convert-type-set-to-term1.

; Note that this function is independent of the perhaps misleadingly named
; convert-type-set-to-term-lst.  That function applies a list of
; type-set-inverter rules to a type-set, returning a list of disjuncts that
; express it.

  (convert-type-set-to-term1 x ts nil ens w ttree))

(defun convert-type-prescription-to-term (tp ens wrld)

; Tp is a type-prescription.  We generate a term that expresses it relative to
; the supplied ens.  We will usually store this term in the :corollary of tp
; itself; generally the current :corollary field of tp is *t* right now because
; tp was generated by putprop-initial-type-prescriptions.  We return
; the generated corollary term and a ttree citing the type-set-inverter
; rules used.

  (mv-let (concl ttree)
          (convert-type-set-to-term (access type-prescription tp :term)
                                    (access type-prescription tp :basic-ts)
                                    ens wrld nil)
          (mv (implicate (conjoin (access type-prescription tp :hyps))
                         (disjoin
                          (cons concl
                                (convert-returned-vars-to-term-lst
                                 (access type-prescription tp :term)
                                 (access type-prescription tp :vars)))))
              ttree)))

; The function all-runes-in-ttree, defined below, is typically used by each
; event function to recover the supporting runes from a ttree.

(defun all-runes-in-var-to-runes-alist (alist ans)
  (cond ((null alist) ans)
        (t (all-runes-in-var-to-runes-alist
            (cdr alist)
            (union-equal (cdr (car alist)) ans)))))

(defun all-runes-in-var-to-runes-alist-lst (lst ans)
  (cond ((endp lst) ans)
        (t (all-runes-in-var-to-runes-alist-lst
            (cdr lst)
            (all-runes-in-var-to-runes-alist (car lst) ans)))))

(defun union-equal-removing-duplicates (x y)

; Returns the same set as (union-equal x y), but is tail recursive and removes
; any duplicates from x.

  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) y)
        (t (union-equal-removing-duplicates
            (cdr x)
            (add-to-set-equal (car x) y)))))

(defrec summary-data
  ((runes . use-names)
   .
   (by-names . clause-processor-fns))

; The use of nil for the cheap flag helps to ensure that when one writes a
; clause-processor function without taking care to return a summary-data record
; (or nil) as the final, non-stobj argument, the error message will point that
; out.

  nil)

(defmacro make-summary-data (&key runes use-names by-names clause-processor-fns)

; This macro would of course not be necessary for ACL2 developers, who can just
; as well call MAKE directly.  However, make-summary-data provides a documented
; interface that hides the defrec machinery.

  `(make summary-data
         :runes ,runes
         :use-names ,use-names
         :by-names ,by-names
         :clause-processor-fns ,clause-processor-fns))

(mutual-recursion

(defun all-runes-in-elim-sequence-lst (lst ans)
  (cond ((endp lst) ans)
        (t (all-runes-in-elim-sequence-lst
            (cdr lst)
            (all-runes-in-elim-sequence (car lst) ans)))))

(defun all-runes-in-elim-sequence (elim-sequence ans)

; Elim-sequence is a list of elements, each of which is of the form
; (rune rhs lhs alist restricted-vars var-to-runes-alist ttree)
;  0    1   2   3     4               5                  6

  (cond ((null elim-sequence) ans)
        (t (all-runes-in-elim-sequence
            (cdr elim-sequence)
            (all-runes-in-ttree (nth 6 (car elim-sequence))
                                (all-runes-in-var-to-runes-alist
                                 (nth 5 (car elim-sequence))
                                 (add-to-set-equal (nth 0 (car elim-sequence))
                                                   ans)))))))

(defun all-runes-in-ttree-fc-derivation-lst (lst ans)
  (cond ((endp lst) ans)
        (t (all-runes-in-ttree-fc-derivation-lst
            (cdr lst)
            (add-to-set-equal
             (access fc-derivation (car lst) :rune)
             (all-runes-in-ttree (access fc-derivation (car lst) :ttree)
                                 ans))))))

(defun all-runes-in-ttree-find-equational-poly-lst (lst ans)
  (cond ((endp lst) ans)
        (t (all-runes-in-ttree-find-equational-poly-lst
            (cdr lst)
            (let ((val (car lst))) ; Shape: (poly1 . poly2)
              (all-runes-in-ttree
               (access poly (car val) :ttree)
               (all-runes-in-ttree (access poly (cdr val) :ttree)
                                   ans)))))))

(defun all-runes-summary-data-lst (lst ans)

; Lst is a list of tuples of the form (clause-processor-hint summary-data
; . clauses).  We collect the runes from those summary-data fields.

  (cond ((endp lst) ans)
        (t (all-runes-summary-data-lst
            (cdr lst)
            (let ((summary-data (cadr (car lst))))
              (if summary-data
                  (union-equal-removing-duplicates
                   (access summary-data summary-data :runes)
                   ans)
                ans))))))

(defun all-runes-in-ttree (ttree ans)

; Ttree is any ttree produced by this system.  We sweep it collecting into ans
; every rune (or fake rune) in it.

  (cond
   ((endp ttree) ans)
   (t (all-runes-in-ttree
       (cdr ttree)
       (let ((tag (caar ttree))
             (lst (cdar ttree)))
         (case
           tag
           (lemma
; Shape:  rune
            (union-equal lst ans))
           (:by
; Shape: (lmi-lst thm-cl-set constraint-cl k)

; As of this writing, there aren't any runes in an lmi list that are being
; treated as runes.  Imagine proving a lemma that is then supplied in a :use
; hint.  It shouldn't matter, from the point of view of tracking RUNES, whether
; that lemma created a rewrite rule that is currently disabled or whether that
; lemma has :rule-classes nil.

            ans)
           (:bye
; Shape: (name . cl), where name is a "new" name, not the name of something
; used.
            ans)
           (:or
; Shape (parent-cl-id nil-or-branch-number ((user-hint1 . hint-settings1) ...))
; See comment about the :by case above.
            ans)
           (:use
; Shape: ((lmi-lst (hyp1 ...) cl k) . n)

; See comment for the :by case above.

            ans)
           (:cases
; Shape: ((term1 ... termn) . clauses)
            ans)
           (preprocess-ttree
; Shape: ttree
            (all-runes-in-ttree-lst lst ans))
           (assumption
; Shape: assumption record
            ans)
           (pt
; Shape: parent tree - just numbers
            ans)
           (fc-derivation
; Shape: fc-derivation record
            (all-runes-in-ttree-fc-derivation-lst lst ans))
           (find-equational-poly
; Shape: (poly1 . poly2)
            (all-runes-in-ttree-find-equational-poly-lst lst ans))
           (variables
; Shape: var-lst
            ans)
           ((splitter-if-intro
             splitter-case-split
             splitter-immed-forced)
; Shape: rune (Note: objects are a subset 'lemmas objects.)
            ans)
           (elim-sequence
; Shape: ((rune rhs lhs alist restricted-vars var-to-runes-alist ttree) ...)
            (all-runes-in-elim-sequence-lst lst ans))
           ((literal          ;;; Shape: term
             hyp-phrase       ;;;        tilde-@ phrase
             equiv            ;;;        equiv relation
             bullet           ;;;        term
             target           ;;;        term
             cross-fert-flg   ;;;        boolean flg
             delete-lit-flg   ;;;        boolean flg
             clause-id        ;;;        clause-id
             binding-lst      ;;;        alist binding vars to terms
             terms            ;;;        list of terms
             restricted-vars) ;;;        list of vars
            ans)
           ((rw-cache-nil-tag
             rw-cache-any-tag)
; Shape: rw-cache-entry
            ans)
           (var-to-runes-alist
; Shape: (...(var . (rune1 ...))...)
            (all-runes-in-var-to-runes-alist-lst lst ans))
           (ts-ttree
; Shape: ttree
            (all-runes-in-ttree-lst lst ans))
           ((irrelevant-lits
             clause)
; Shape: clause
            ans)
           (hidden-clause
; Shape: t
            ans)
           (abort-cause
; Shape: symbol
            ans)
           (bddnote
; Shape: bddnote

; A bddnote has a ttree in it.  However, whenever a bddnote is put into a given
; ttree, the ttree from that bddnote is also added to the same given ttree.
; So, we don't really think of a bddnote as containing a "ttree" per se, but
; rather, a sort of data structure that is isomorphic to a ttree.

            ans)
           (case-limit
; Shape: t
            ans)
           (sr-limit
; Shape: t
            ans)
           (:clause-processor
; Shape: (clause-processor-hint summary-data . clauses)
            (all-runes-summary-data-lst lst ans))
           (otherwise (er hard 'all-runes-in-ttree
                          "This function must know every possible tag so that ~
                           it can recover the runes used in a ttree.  The ~
                           unknown tag ~x0, associated with the list of ~
                           values ~x1, has just been encountered."
                          tag
                          lst))))))))

(defun all-runes-in-ttree-lst (lst ans)
  (cond ((endp lst) ans)
        (t (all-runes-in-ttree-lst (cdr lst)
                                   (all-runes-in-ttree (car lst) ans)))))
)


; Essay on the Tau System

; This essay touches on a wide variety of topics in the design of the tau
; system.  It is consequently divided into many subsections with the following
; headers.  We recommend scanning this list for subsections of interest; an
; introduction to tau is provided by the first six or so, in order.

; On Tau-Like Terms
; On the Name ``tau''
; On Some Basic Ideas
; On Tau Recognizers -- Part 1
; On the Tau Database and General Design
; On Tau Recognizers -- Part 2
; On Tau Intervals and < versus <=
; On the Tau Data Structure
; On the Built-in Tau and the Abuse of Tau Representation
; On the Additional Restrictions on Tau Fields
; On the Use of ENS by Function Evaluation in the Tau System
; On the Most Basic Implications of Being in an Interval
; On Firing Signature Rules
; On Comparing Bounds
; On the Proof of Correctness of upper-bound-<
; On the Near-Subset Relation for Intervals
; On the Tau Database
; On Closing the Database under Conjunctive Rules
; On Converting Theorems in the World to Tau Rules
; On Tau-Like Terms
; On Loops in Relieving Dependent Hyps in Tau Signature Rules
; On the Tau Msgp Protocol
; On Removal of Ancestor Literals -- The Satriani Hack Prequel
; On the Motivation for Tau-Subrs
; On the Tau Completion Alist (calist)
; On Disjoining Tau
; On the Role of Rewriting in Tau
; On Tau-Clause -- Using Tau to Prove or Mangle Clauses
; On Tau Debugging Features

; On Tau-Like Terms

; The Tau system is a collection of data structures and algorithms for
; reasoning quickly about the things we know to be true about a term.  It was
; motivated by our frustration over the time it took ACL2 to do elementary
; guard-like proofs -- ``proofs'' that could be almost instantaneous in a
; strongly typed language.  A tau is a representation of a set of ``tau
; recognizers'' denoting the function obtained by conjoining the recognizers.
; To say that e has a given tau is to say that the function denoted by the tau
; is true of e.  Informally, ``the'' tau of a term is all the tau-like things
; we know to be true about the term.  The tau recognizers include all the named
; Boolean functions of one argument, their negations, and all the functions
; (lambda (x) (EQUAL x '<evg>)) and (lambda (x) (< x '<evg>)), and their
; negations.

; On the Name ``tau''

; ``Tau'' might stand for ``Types Are Unnecessary'' and if it did the name
; would be ironic because this whole idea is a tribute to type checking!  The
; truth is that ``tau'' doesn't stand for anything!  When we designed this
; system we needed a name for the meta objects denoting the set of monadic
; predicates (``signed tau recognizers'') that we know to hold about a term in
; a given context.

; We were tempted to call such a set a ``type'' of the term but felt that was
; inappropriate because the literature on types is so extensive and we have no
; interest in defending the proposition that our objects are ``types''.  We
; really don't think of them as anything more than sets of recognizers known
; known to be true.  We could not use the words ``sorts'' or ``kinds'' for
; similar reasons.  So we temporarily adopted the name ``recognizer sets''
; abbreviated ``rs.''  But this was an unfortunate acronym for two reasons:
; typically pronounced ``are ess'' it was unclear whether to write ``given an
; rs'' or ``given a rs'' since the former ``sounds right'' when ``rs'' is
; pronounced ``are ess'' but wrong when ``rs'' is read ``recognizer set.''
; Furthermore, is ``rs'' singular or plural?  Did we really want to write
; ``Given a set of rses?''  Nevertheless, we got this idea working, in a
; stand-alone way, under the name rs.  Only when it was integrated into ACL2
; proper did adopt the name ``tau'' for these objects.  We chose ``tau''
; because it had no fixed connotation in the literature, it is short, and it
; started with a pronounced consonant.  We use ``tau'' as both a singular noun
; and a plural one.  We might say ``t1 is a tau'' and we might say that the
; ``tau of x and y are t1 and t2 respectively''.

; On Some Basic Ideas

; We identify certain expressions as primitive ``tau recognizers'' and then
; develop a data structure, tau, to represent conjunctions of these tau
; recognizers.  Speaking precisely in the language of metamathematics, tau
; recognizers and tau are predicates in the semantic sense.  In particular in
; ACL2's terms, they represent not function SYMBOLS or TERMS but FUNCTIONS.
; They can be applied to any single object and yield T or NIL to indicate
; whether the object has the property or not.  For example, we might wish to
; express the property of being a natural number between 1 and 7, or of being
; an alist mapping 32-bit integers to 32-bit integers.  The whole idea of the
; tau system is that by representing primitive tau recognizers as objects and
; allowing the representation of the conjunction and negation of these objects
; we can precompute the implications of some thing having a given property
; independently of whatever thing we might be talking about.

; This leads to another basic idea in the tau system: these precomputed
; relationships between tau properties are stored in a database, so that upon
; learning that an object has one of the properties we can rapidly determine
; all of the tau recognizers it satisfies.

; A third basic idea is that the tau database will not be deduced
; automatically but will be derived from rules proved by the user.  The tau
; system mines rules as they are proved and builds its database.  Several
; forms of theorems are of interest.

; Boolean:
; (booleanp (f v))

; Eval:
; (p 'const)

; Simple:
; (implies (p v) (q v))

; Conjunctive:
; (implies (and (p1 v) (p2 v) ...) (q v))

; Signature [form 1]:
; (implies (and (p1 x1) (p2 x2) ...)
;          (q (f x1 x2 ...)))

; Signature [form 2]:
; (implies (and (p1 x1) (p2 x2) ...)
;          (q (mv-nth 'n (f x1 x2 ...))))

; Big Switch:
; (equal (fn . formals) body), where body is a big switch on some formal.

; MV-NTH Synonym:
; (equal (fn x y) (mv-nth x y))

; where the monadic predicate symbols above, p, q, p1, p2, etc., may be are our
; signed tau recognizers.

; On Tau Recognizers -- Part 1

; So what are the tau recognizers?  They are the following functions:

; (i)   named, monadic Boolean, non-constant functions, both built-in and
;       defined, such as NATP, INTEGERP, CONSP, ALISTP, etc., including
;       user-defined ones, and their negations, e.g., (lambda (x) (NOT (NATP
;       x))); see what we mean by ``non-constant, non-equality'' below.

; (ii)  all functions (lambda (x) (EQUAL x 'evg)) and their negations,
;       where we also accept EQ, EQL, and = in place of EQUAL, and

; (iii) all functions (lambda (x) (< x '<evg>)) or (lambda (x) (< '<evg> x)),
;       for rational <evg>, and their negations, where we also accept > in
;       place of <.  Note that <= and >= are ACL2 macros, not function symbols,
;       so there is no point in accepting them.  When mining ACL2 terms for tau
;       recognizers (i.e., tau-like-term) and encountering (> x y), we act as
;       though we'd just seen (< y x).

; If sign is T or NIL and r is a tau recognizer, then by sign/r we mean r if
; sign is T and the negation of r of sign is NIL.  Think of the positive sign
; being T and the negative sign being NIL.  Thus, (sign/r e) is (NOT (EQUAL e
; 'ABC)) if sign is NIL and r is (lambda (x) (EQUAL x 'ABC)).

; The Non-Constant Non-Equality Premise: No function symbol is defined or
; constrained to be constantly T or constantly NIL, and no function symbol is
; defined or constrained to be equivalent to (EQUAL v 'evg) or (NOT (EQUAL v
; 'evg)).  Thus, we don't expect to handle functions like:

; (defun everywhere-true (x) (declare (ignore x)) T)

; or

; (defun is-loadp (x) (eq x 'LOAD))

; A user wishing to test equality-with-constant should use EQUAL (or one of its
; variants) and the constant, not hide it inside a monadic Boolean function.
; Our code is sound in the presence of such pathological defuns, but it is not
; ``as complete'' as it would be if they were avoided.  These restrictions
; could be dropped by extending the form of Synonym theorems so that the tau
; system understood these symbols.  But equalities like (eq x 'LOAD) are so
; useful it is hard to make sure the rest of the theorem prover is aware of
; them except by leaving them out in the open.

; One implication of the Non-Constant Non-Equality Premise is that we will
; never see (or in any case, take no note of) theorems of the form (fn x) -->
; (equal x 'evg), because such a theorem implies that fn violates the premise.

; (encapsulate ((fn (x) t))
;              (local (defun fn (x) (equal x '23)))
;              (defthm fn-constraint (and (booleanp (fn x))
;                                         (implies (fn x) (equal x '23)))
;                :rule-classes nil))
; (thm (or (equal (fn x) nil)
;          (equal (fn x) (equal x '23)))
;      :hints (("Goal" :use fn-constraint)))

; We discuss how tau recognizers are represented in our code in ``On Tau
; Recognizers -- Part 2'' below.

; On the Tau Database and General Design

; It is possible to turn the tau reasoning engine on or off, by toggling the
; enabled status of the rune for TAU-SYSTEM.

; Our design allows for theorems to enter the tau database in either of two
; ways, explicitly (because they have rule-classes :tau-system) or implicitly
; (because they are of the right syntactic shape).  Non-:tau-system theorems
; are swept up into the database implicitly only when the tau system is in
; ``automatic mode.''

; The two modes just mentioned -- whether tau reasoning is used in proofs
; and whether the tau database is extended implicitly -- are independent.

; The tau system does not track the rules it uses.  This design decision was
; motivated by the desire to make tau reasoning fast.  The tau database does
; not record which tau facts come from which theorems or runes.  It is
; impossible to prevent tau from using a fact in the database unless you
; disable TAU-SYSTEM altogether.  However, there is a facility for regenerating
; the tau database with respect to a given enabled structure.

; Thus, the tau database may be built incrementally as each event is processed
; or may be built in one fell swoop.  In the early implementations of the tau
; system the various modes and features were scattered all over our source
; code.  For example, we found ourselves possibly extending the tau database:
; (a) when :tau-system rules are added by add-x-rule
; (b) when any non-:tau-system rule is added (e.g., by add-rewrite-rule)
; (c) when a defun or constraint added a Boolean type-prescription rule to
;     a monadic function
; (d) when an explicit regenerate event is triggered.

; This became too complicated.  We have therefore moved all the tau database
; extension code into this file and invoke it only two places: in install-event
; and in the regeneration event (which mimics the sequential invocation on
; successive events in the world).

; One odd aspect of this implementation is that add-x-rule, which ``ought'' to
; know how to add every kind of rule class, does NOT add :tau-system rules.
; Instead, it is just a quiet no-op on :tau-system rules and those rules are
; handled by the centralized tau facility developed here.  To do otherwise
; would mean that :tau-system rules must be added both by add-x-rule and by
; regeneration of the tau database.

; Another oddity is that it is difficult to check that certain ``syntactic''
; criteria are met because the criteria are really dependent on previously
; proved and exported theorems.  For example, if p and q are monadic Boolean
; functions,

; (defthm p-implies-q (implies (p x) (q x)) :rule-classes :tau-system)

; is a legal tau rule.  But now imagine that p and p-implies-q are introduced
; inside an encapsulate constraining p.  Then if the encapsulation fails to
; export the fact that p is Boolean, the second pass will fail because
; p-implies-q is not a tau rule.  The ``syntactic'' check that it is a legal
; rule, made in the first pass, is actually not quite enough to ensure
; legality.  We cause a hard error in the second pass when this occurs.  This
; is not unprecedented; see the hard error caused by
; add-type-prescription-rule.  But there is a similar but more common and
; insidious problem arising from regeneration.  Forget about encapsulation;
; let p, q, and p-implies-q just be top-level events.  But imagine we're
; regenerating the tau database under an ens in which the Boolean nature of p
; is disabled.  Then p-implies-q is no longer a legal :tau-system rule even
; though it was legal when checked.  Had p-implies-q just been a :rewrite rule,
; say, and swept into the tau database by auto mode, it would make sense to
; quietly ignore this situation (and not add a tau rule).  But if p-implies-q
; is an explicit :tau-system rule it seems glib to ignore it in the
; reconstruction of the database but harsh to cause a hard error because of
; the disabled status of a :type-prescription rule.  So instead, we collect a
; list of all the explicit :tau-system rules excluded by the user's chosen ens
; and report it at the end of the regeneration process.  We call these ``lost
; tau rules.''

; On Tau Recognizers -- Part 2

; Recall that a tau is a set of tau recognizers representing their conjunction
; and denotes a monadic Boolean function.  We describe how we represent tau
; below.  But a basic idea is that we'll group all the positive recognizer
; symbols into one list representing their conjunction and all the (positive
; versions of the) negative ones in another list representing their
; disjunction.  Thus, we really only represent positive tau recognizers and use
; the sign convention (or the location of the recognizer in some data
; structure) to negate them.

; To make such lists of function symbols easier to search for a given symbol
; we order them and assign each monadic Boolean function symbol a unique
; natural number called its tau index.  The index of each such function will be
; stored on its property list under the property tau-pair, in a pair containing
; the index and function symbol.  Thus, one might find under 'symbolp 'tau-pair
; the pair (7 . SYMBOLP), or whatever the index for symbolp is.

; Note: When constants in this code refer to the indices of specific functions,
; we have a check in check-built-in-constants that insures that the index is
; still correct, since they may shift as Boolean functions are added.

; As noted, we use the notation sign/r to denote a signed tau recognizer, where
; sign = T means the recognizer is positive and sign = NIL means it is
; negative.  Often in our code r is actually a tau-pair.  That is, we might
; write sign/r in a comment but in the code r is (7 . SYMBOLP).  If the
; associated sign were NIL, this would denote (lambda (x) (not (symbolp x))).

; This raises the question of how we represent the unnamed tau recognizers as
; ACL2 objects?  We certainly do not want to represent the function (lambda (x)
; (equal x 'abc)) as the list object '(lambda (x) (equal x 'abc))!  We need a
; succinct and cheap representation for ``equalities with constants'' and
; ``arithmetic inequalities with rationals'' that correspond to the role played
; by tau pairs for those recognizers with symbolic names like SYMBOLP.

; In general our code uses two variables, e.g., sign and r, in tandem to
; represent a signed recognizer sign/r.  We only represent positive
; recognizers, r, and use the sign part of the sign/r notation to handle the
; negatives.

; The equality tau recognizers, (lambda (x) (equal x '<evg>)), are represented
; by a singleton list containing the <evg>, i.e., (<evg>).  This is cheap
; because it is just the cdr of the (QUOTE <evg>) inside the equality term.  It
; is convenient because to apply a named tau recognizer to an evg (to see
; whether it is true or false) we apply the named function to a singleton list
; containing the evg in question, so this notation facilitates that application
; without consing.  We can tell whether an r in the sign/r notation is a
; tau-pair (representing a named recognizer) or a singleton <evg> (representing
; an equality with that <evg>) by testing (cdr r).  If (cdr r) is non-nil, it
; is the function symbol naming the recognizer, otherwise r is a singleton evg.

; The arithmetic inequality tau recognizers, (lambda (x) (< x 'k)) and (lambda
; (x) (< 'k x)), are represented by (k . :lessp-x-k) and (k . :lessp-k-x)
; respectively.  Note that this might look like a tau pair but :lessp-x-k and
; :lessp-k-x are keywords and hence not function symbols.  Note also that
; putting the keyword in the cdr of the cons rather than in the car was a
; deliberate decision, even though it is sort of backward if the keyword is
; thought of the ``function symbol'' and the k is a ``parameter.''  By putting
; the keyword in the cdr we can tell what sort of recognizer r represents by
; using eq tests on the cdr only.

; Thus, the following test can determine what kind of tau recognizer r
; represents.  (Technically, the terms shown in the comments below are
; the BODIES of the (lambda (x) ...) expression r represents.)

; (cond ((eq (cdr r) nil)
;        (let ((evg (car r)))
;          ...                  ; r represents (EQUAL x 'evg), furthermore r
;                               ; is a singleton list containing evg suitable
;                               ; for using ev-fncall-w to apply some monadic
;                               ; function.
;          ))
;       ((eq (cdr r) :lessp-x-k)
;        (let ((k (car r)))
;          ...                  ; r represents (< x 'k), where k is a RATIONALP.
;          ))
;       ((eq (cdr r) :lessp-k-x)
;        (let ((k (car r)))
;          ...                  ; r represents (< 'k x), where k is a RATIONALP.
;          ))
;       (t (let ((p (cdr r))
;                (i (car r)))
;            ...                ; r represents (p x), furthermore, i is the
;                               ; tau index of monadic function symbol p.
;            )))

; Note that tests in CCL show that is sped up (by perhaps 10%) by binding the
; variable symbol discriminator to (cdr r) and using discriminator everywhere
; (cdr r) appears above.

; On Tau Intervals and < versus <=

; The tau data structure is defined below.  But it contains another data
; structure called a tau-interval, which represents a function that bounds its
; argument to an interval between two rationals.  Its argument need not be
; a rational, indeed, its argument need not even be an acl2-numberp.
; For example, every non-numeric ACL2 object x satisfies (-2 < x < 2)!

(defrec tau-interval (domain (lo-rel . lo) . (hi-rel . hi)) t)

; where

; * domain is INTEGERP, RATIONALP, ACL2-NUMBERP, or NIL and indicates the
;   domain of the interval.  That is, it is either the integer line, the
;   rational line, the acl2-numberp line, or the entire ACL2 universe ``line''.
;   (The ACL2 universe ``line'' is not quite a line: the acl2-numbers are laid
;   out linearly as one would expect, and all the non-acl2-numbers are in an
;   equivalence class with 0.)  If the domain is INTEGERP, we impose additional
;   invariants on the other components as described below.

; * lo-rel and hi-rel are T or NIL and indicate whether the corresponding
;   relation is < or <= (T is strict; nil is weak inequality); if the domain
;   is INTEGERP, we always use weak inequalities; and

; * lo and hi are either NIL or rationals and represent the lower and upper
;   bounds, with NIL being the corresponding infinity.  If the domain is INTEGERP,
;   we squeeze the bounds to be integers.  Thus, while it is technically
;   possible to create a tau-interval with
;   (make tau-interval
;         :domain 'INTEGERP
;         :lo 1/2
;         :lo-rel t
;         :hi-rel t
;         :hi 5/2)
;   we prefer to round the bounds up and down (respectively) and weaken the
;   relations, converting 1/2 < x < 5/2 to 1 <= x <= 2.  This adjustment
;   is done with the function squeeze-k.

;   Technically there is no reason to exclude the bounds from being
;   complex-rationals.  <= is a non-strict total order on acl2-numberp.  For
;   example, it is a theorem that if (<= #c(1 2) x) and (<= x #c(1 2)) then x =
;   #c(1 2).  So we could allow the bounds to be complex-rationals and continue
;   more or less as we do here.  However, (a) it gets a little more complicated
;   because in squeezing intervals around integers we'd have to take the
;   realpart of the bounds, e.g., to raise a strict lower bound on an integer
;   we'd use (+ (floor (REALPART lo) 1) 1) instead of (+ (floor lo 1) 1) if lo
;   can be complex, and (b) complex bounds probably never occur!  So the little
;   added complexity probably wouldn't buy us anything.

; Terminology: A ``bound'' is determined by a pair, namely a ``relation''
; (coded as a Boolean flag) and an ``extent'' (coded as either a NIL --
; representing an infinity -- or a rational).  Which infinity nil represents
; depends on whether we're talking about an upper or lower bound.

; We sometimes use the following notation:

;   (defun <? (rel x y)
;     (if (or (null x) (null y))
;        t
;         (if rel
;             (< x y)
;             (<= x y))))

; This function implements the notion of rel being a boolean encoding of strong or
; weak inequality and nil representing the ``appropriate'' infinity.  So for
; example, (<? t 5 7), (<? t nil -1000), (<? t 1000 nil).  When stating theorems
; in our specifications below we tend to use the <? function but to restrict one of
; x or y to being non-nil because our theorems are not meant to allow the user
; to compare infinities.

; We sometimes write (x <? y) meaning (<? rel x y) for some rel.  We sometimes
; even write (lo <? x <? hi) meaning (and (<? lo-rel lo x) (<? hi-rel x hi)).
; Note that this is an abuse of notation!  The two occurrences of the symbol
; ``<?'' denote different relations!

; We sometimes write (rel x y) to mean (<? rel x y).

; Thus, with appropriate interpretation of the flags and infinities, a
; tau-interval denotes the function:

; (lambda (x) (and (,domain x) (,lo-rel ',lo x) (,hi-rel x ',hi)).

; Note that even though we only provide signed < as a tau recognizer, we allow
; either < or <= to be used in bounding an interval.  If we did not allow <= we
; could discard the lo-rel and hi-rel -- they would both always be < -- but
; we'd have to add two signs.  We think <= encourages more reliable thinking.
; The only reason we don't consider signed <= as a tau recognizer above is that
; <= is not a function symbol in ACL2, it is a macro that expands into negative
; <.

; Convention:  When using the (make tau-interval ...) idiom we tend to
; list the parameters in the order shown below:

; (make tau-interval :lo k :lo-rel t :hi-rel nil :hi d)

; because it is suggestive of k < ...  <= d.

; However, when we pass around bounds and relations as arguments, we tend to
; list the relation first (befitting its role of denoting a function symbol)
; and then the bound, thus writing (positive-lower-boundp rel k) rather than
; (positive-lower-boundp k rel).

; Note that the universal tau-interval (where all components are nil)

; (make tau-interval
;       :recog  nil  ; not known to be a number
;       :lo     nil  ; negative infinity
;       :lo-rel nil  ; <=
;       :hi-rel nil  ; <=
;       :hi     nil  ; positive infinity
;       )

; makes absolutely no restriction on the subject.  We use nil to represent this
; tau-interval (and the variants with strict relations) rather than create and
; subsequently test against (nil (nil . nil) . (nil . nil)).  However, we
; exploit the fact that (access tau-interval nil :hi-rel), for example,
; computes to nil.  (Tests show that it is faster to execute (access
; tau-interval x :hi-rel) than (if x (access tau-interval x :hi-rel) nil) even
; when x is nil.)

; If an interval's domain is the integers, we narrow the bounds to integers and
; weaken the relation.  For example, instead of creating

; (lambda (x) (and (integerp x) (< 1/2 x) (< x 5/2)))

; we use

; (lambda (x) (and (integerp x) (<= 1 x) (<= x 2)))

; Aside: This treatment of INTEGERP is an example of a much more general idea
; we're not prepared to implement.  Suppose DIV4P recognizes integers divisible
; by 4.  Then if DIV4P is in the pos-pairs of a tau with interval 1 <= ... <=
; 30, we could shrink the interval to 4 <= ... <= 28.

; To do this we'd need, for selected recognizers, a pair of ``generators:''

; - generate the least y such that y > x and (DIV4P y)
; - generate the greatest y such that y < x and (DIV4P y)

; The infrastructure to support this is tedious.  One would have to prove rules
; characterizing the correctness of such generators and then use such rules to
; build a data structure that would be used when new pos-pairs are added or
; when bounds are changed.  Perhaps somebody would like a project?  End of Aside.

; We use tau-intervals to say everything they can.  This is a strange remark that
; bears explanation.  For example, a tau might say that its subject is a natural
; number (in addition to having many other properties).  Should the interval in that
; tau redundantly be the tau-interval equivalent to NATP,

; (lambda (x) (and (integerp x) (<= 0 x)))

; or should we just store NIL as the tau-interval for this tau on the grounds
; that the NATP property is stored elsewhere?  In short, should the
; tau-interval in a tau be allowed to be redundant?  Our answer is yes: we use
; tau-intervals to say everything they can.  The idea is the linear arithmetic
; facts about the subject will be found in the tau-interval -- even if they are
; pretty unrestrictive like INTEGERP or RATIONALP without any bounds.  We will
; arrange to adjust the tau-interval (shrinking it) whenever we learn anything
; that allows that.

; Perhaps the strangest implication of this decision is that a tau-interval can
; say that its subject is equal to a particular rational constant, by weakly
; bounding the subject above and below by that rational constant.  In the case
; that the constant is 0, one must add that the subject is rationalp.  This all
; follows from a theorem shown among the ``helpful reminders about ACL2
; arithmetic'' below.

; A further implication is that if we are using a tau to represent a
; conjunctive rule and we wish to represent the conjunct (equal e 5) we will
; get the same thing as the tau for (and (equal e 5) (<= 5 e) (<= e 5)).

; Finally, some intervals are contradictory and are never built; we try to
; signal contradiction instead of creating empty intervals like:

; (lambda (x) (and (rationalp x) (< 10 x) (< x 5))).

; However, in the event that we need a canonical empty interval, here is the
; one we use.

(defconst *tau-empty-interval*
  (make tau-interval
        :domain nil
        :lo-rel t
        :lo 0
        :hi-rel t
        :hi 0))

; Because we do not guarantee always to construct the canonical empty interval,
; we test for it with this more general function.  This function recognizes
; *tau-empty-interval* and also has the property that if int is an interval
; that passes this test, then no x is in it.

(defun tau-empty-intervalp (int)
  (and int
       (access tau-interval int :lo)
       (access tau-interval int :hi)
       (if (or (access tau-interval int :lo-rel)
               (access tau-interval int :hi-rel))
           (<= (access tau-interval int :hi)
               (access tau-interval int :lo))
           (<  (access tau-interval int :hi)
               (access tau-interval int :lo)))))

; Here are some helpful reminders about ACL2 arithmetic...  Some of the more
; ``obvious'' lemmas are interesting because of what they DON'T say.  For
; example, some obvious properties of < and <= are missing hypotheses that
; would restrict them to numeric inputs.

;   (er-progn
;
;   ; All of the following could be proved before tau was involved.
;    (in-theory (disable (tau-system)))
;    (include-book "arithmetic-5/top" :dir :system)
;
;   ; Integers are rationals and rationals are (acl2-)numbers.
;   (thm (and (implies (integerp x)
;                      (rationalp x))
;             (implies (rationalp x)
;                      (acl2-numberp x))))
;
;   ; Numbers are partitioned into rationals and complex-rationals.
;   (thm (and (iff (acl2-numberp x)
;                  (or (rationalp x)
;                      (complex-rationalp x)))
;             (implies (rationalp x) (not (complex-rationalp x)))))
;
;   ; < is transitive, whether applied to numbers or not.
;   (thm (implies (and (< x y) (< y z)) (< x z)))
;
;   ; < is anti-symmetric, whether applied to numbers or not.
;   (thm (implies (< x y) (not (< y x))))
;
;   ; Trichotomy holds, but you must know the arguments are both numbers.
;   (thm
;    (implies (and (acl2-numberp x)
;                  (acl2-numberp y))
;             (or (< x y)
;                 (< y x)
;                 (equal x y))))
;
;   ; If something is strictly above or below 0, it must be a number.
;   (thm (implies (or (< x 0) (< 0 x))
;                 (acl2-numberp x)))
;
;   ; Strict lower bounds on integers can be raised and weakened:
;   (thm
;    (implies (and (integerp x)
;                  (rationalp bound))
;             (iff (< bound x)
;                  (<= (+ (floor bound 1) 1) x))))
;
;   ; Weak lower bounds on integers can be raised:
;   (thm
;    (implies (and (integerp x)
;                  (rationalp bound))
;             (iff (<= bound x)
;                  (<= (ceiling bound 1) x))))
;
;   ; Strict upper bounds on integers can be lowered and weakened:
;   (thm
;    (implies (and (integerp x)
;                  (rationalp bound))
;             (iff (<  x bound)
;                  (<= x (- (ceiling bound 1) 1)))))
;
;   ; Weak upper bounds on integers can be lowered:
;   (thm
;    (implies (and (integerp x)
;                  (rationalp bound))
;             (iff (<=  x bound)
;                  (<= x (floor bound 1)))))
;
;   ; The other inequalities are just signed less thans, whether applied to numbers
;   ; or not:
;
;   (thm (and (iff (<= x y) (not (< y x)))
;             (iff (>  x y) (< y x))
;             (iff (>= x y) (not (< x y)))
;             (iff (>= x y) (<= y x))))
;
;   ; Note that the theorem above shows that we can do everything with signed < or
;   ; with < and <=.  These theorems are interesting only because they don't have
;   ; hypotheses about x and y being numbers.
;
;   ; An interval bounded above and below by the same rational contains exactly one
;   ; element, provided either the interval is restricted to numbers or one of the
;   ; bounds is non-0.
;
;   (thm (implies
;         (and (rationalp lo)
;              (rationalp hi)
;              (<= lo x)
;              (<= x hi)
;              (equal lo hi)
;              (or (acl2-numberp x)
;                  (not (equal hi 0))))
;         (equal x hi)))
;
;   ; Stated slightly differently, the recognizer (lambda (x) (equal x 'b)) for a
;   ; rational constant b, is equivalent to the interval recognizer:
;   ; (lambda (x) (and (rationalp x) (<= b x) (<= x b))):
;
;   (thm (implies (rationalp b)
;                 (iff (equal x b)
;                      (and (rationalp x)
;                           (<= b x)
;                           (<= x b)))))
;
;   ; Or, in the even more special case that b is an integer:
;
;   (thm (implies (integerp b)
;                 (iff (equal x b)
;                      (and (integerp x)
;                           (<= b x)
;                           (<= x b)))))
;
;   ; (By the way, one might ask how it is that a complex cannot lie ``between''
;   ; the rational b and the rational b. The reason is that if u+iv <= b and b <=
;   ; u+iv then one can show that u=b and v=0.  This happens because (u+iv <= b) is
;   ; equivalent to (u<b v (u=b & v<= 0)).  If you work out the four cases of the
;   ; conjunction of (u+iv <= b) & (b <= u+iv) you get three impossible ones (where
;   ; b<u and u<b or u=b) and one other which says u=b and v=0.)
;
;   ; I do not anticipate tau using it, but here is how < is completed: first, both
;   ; arguments are coerced to numbers with 0 being the default.  Then, two
;   ; rationals are compared with the traditional <; if either argument is a
;   ; complex-rational, they are compared lexicographically on the real- and
;   ; imagparts.  (On rationals, realpart is the identity and imagpart is always
;   ; 0.)
;
;   (thm
;    (equal (< x y)
;           (let ((x1 (if (acl2-numberp x) x 0))
;                 (y1 (if (acl2-numberp y) y 0)))
;             (if (and (rationalp x)
;                      (rationalp y))
;                 (< x1 y1)
;                 (or (< (realpart x1) (realpart y1))
;                     (and (equal (realpart x1) (realpart y1))
;                          (< (imagpart x1) (imagpart y1)))))))
;    :hints (("Goal" :use completion-of-<)))
;   )

(defun <?-number-v-rational (rel x k)

; This is the logical equivalent of either (< x k) or (<= x k), depending on
; rel and optimized under the assumption that x is an acl2-numberp and k is a
; rational.

; (verify-termination <?-number-v-rational)

; (thm
;  (implies (and (acl2-numberp x)
;                (real/rationalp k))
;          (iff (<?-number-v-rational rel x k)
;               (if rel (< x k) (<= x k))))
;  :hints (("Goal" :use ((:instance completion-of-< (x x) (y k))))))

  (cond ((real/rationalp x)
         (if rel (< x k) (<= x k)))
        (t

; If x is complex and k is rational, they are not equal, so ``<='' devolves to
; just ``<'' and rel is irrelevant.

         (or (< (realpart x) k)
             (and (= (realpart x) k)
                  (< (imagpart x) 0))))))

(defun <?-rational-v-number (rel k x)

; This is the logical equivalent of either (< k x) or (<= k x), depending on
; rel and optimized under the assumption that k is a rational and x is an
; acl2-numberp.

; (verify-termination <?-rational-v-number)

; (thm
;  (implies (and (real/rationalp k)
;                (acl2-numberp x))
;          (iff (<?-rational-v-number rel k x)
;               (if rel (< k x) (<= k x))))
;  :hints (("Goal" :use ((:instance completion-of-< (x k) (y x))))))

  (cond ((real/rationalp x)
         (if rel (< k x) (<= k x)))
        (t

; If x is complex and k is rational, they are not equal, so ``<='' devolves to
; just ``<'' and rel is irrelevant.

         (or (< k (realpart x))
             (and (= k (realpart x))
                  (< 0 (imagpart x)))))))

(defun eval-tau-interval1 (interval x)

; Interval is a tau-interval and x must be an ACL2 numberp.  We return t or nil
; according to whether x satisfies the bounds (but not necessarily the recog)
; of the interval.

  (let ((lo (access tau-interval interval :lo))
        (hi (access tau-interval interval :hi)))
    (and
     (or (null lo) ; represents negative infinity
         (<?-rational-v-number (access tau-interval interval :lo-rel) lo x))
     (or (null hi) ; represents negative infinity
         (<?-number-v-rational (access tau-interval interval :hi-rel) x hi)))))

(defun eval-tau-interval (interval evg)

; Return t or nil indicating whether evg satisfies tau-interval interval.

  (cond
   ((null interval) t)
   (t (case (access tau-interval interval :domain)
        (INTEGERP (and (integerp evg)
                       (eval-tau-interval1 interval evg)))
        (RATIONALP (and (rationalp evg)
                        (eval-tau-interval1 interval evg)))
        (ACL2-NUMBERP (and (acl2-numberp evg)
                           (eval-tau-interval1 interval evg)))
        (otherwise (eval-tau-interval1 interval (fix evg)))))))

(defun decode-tau-interval (interval e skip-domain-flg)
; This function actually returns a list of untranslated terms whose
; conjunction is describes the interval.
  (cond
   ((null interval) nil)
   ((and (eq (access tau-interval interval :domain) nil)
         (eq (access tau-interval interval :lo-rel) nil)
         (eq (access tau-interval interval :lo) nil)
         (eq (access tau-interval interval :hi-rel) nil)
         (eq (access tau-interval interval :hi) nil))
    '(non-canonical-universal-interval))
   (t (let ((lst `(,@(if skip-domain-flg
                         nil
                         (if (access tau-interval interval :domain)
                             `((,(access tau-interval interval :domain) ,e))
                             nil))
                   ,@(if (and (null (access tau-interval interval :lo))
                              (null (access tau-interval interval :lo-rel)))
                         nil
                         `((,(if (access tau-interval interval :lo-rel) '< '<=)
                            ,(if (access tau-interval interval :lo)
                                 (access tau-interval interval :lo)
                                 'non-canonical-neg-infinity)
                            ,e)))
                   ,@(if (and (null (access tau-interval interval :hi))
                              (null (access tau-interval interval :hi-rel)))
                         nil
                         `((,(if (access tau-interval interval :hi-rel) '< '<=)
                            ,e
                            ,(if (access tau-interval interval :hi)
                                 (access tau-interval interval :hi)
                                 'non-canonical-pos-infinity)))))))
        lst))))

; On the Tau Data Structure

; So finally, the tau data structure itself:

(defrec tau
  ((pos-evg . neg-evgs) interval . (pos-pairs . neg-pairs))
  t)

; where the shape of each component is as follows:

; pos-evg:   nil or a singleton list containing an evg
; neg-evgs:  list of singleton lists of evgs, duplicate-free, suitably ordered
; interval:  nil or a tau-interval
; pos-pairs: list of tau-pairs, duplicate-free, ordered descending
; neg-pairs: list of tau-pairs, duplicate-free ordered descending

; Note: The ordering on neg-evgs is ascending ``almost'' lexorder, except that
; NIL is the smallest element.  The ordering on the pairs is descending by tau
; index of the pairs.  There is no reason for the opposite orders except for
; the pre-existence of certain sort functions.  There are additional
; restrictions on these fields so that a tau is kept in a normal form.  See
; below.

; Note: It might be wise to add another slot to tau: :neg-nil.  This would be
; equivalent to having (nil) in :neg-evgs except we'd never delete it as
; subsumed and we wouldn't have to search or eval for it to test whether a tau
; is non-nil.  But unless the tau system is too slow, we won't add this
; optimization.

; Note: For the full hons regression suite (3,117 certified books as of Feb,
; 2013) the longest :neg-evgs seen was 254, the longest :pos-pairs was 30, and
; the longest :neg-pairs was 181.

; Roughly speaking, the fields of a tau contribute conjunctions to its overall
; meaning, which we state below in terms of some object e to which it is applied:

; pos-evg:   e is equal to the given evg [if pos-evg is not nil]
; neg-evgs:  e is equal to none of the listed evgs
; pos-pairs: e satisfies all of the function symbols (actually, tau pairs) listed
; neg-pairs: e satisfies none of the function symbols (actually, tau pairs) listed
; interval:  e falls in the given interval

; Some redundancy is allowed between the interval and the rest of a tau, but
; nowhere else.  For example both the pos-pairs and the interval may say that e
; is an INTEGERP.  The motto on the interval is that everything that can be
; said with the interval is said.  The motto on the rest of tau is that the
; only redundancy is in the interval.  See On the Additional Restrictions on
; Tau Fields.

; Here, for example, is a tau constructed during the computation of

; (tau-term '(if (integerp x)
;                (if (equal x '2)
;                    'hello
;                    (if (equal x '3)
;                        'hello
;                        x))  ; <--- the tau below is the tau of x here
;                'bye)
;          nil nil nil (ens state)(w state))

; in a Version_4.3 boot-strap world.  The tau for the indicated x, constructed
; by repeated tau-assumes and extracted from the resulting alist at the
; location marked above, is:

; ((NIL                                 ; pos-evg
;   .
;   ((2) (3)))                          ; neg-evgs
;  (INTEGERP (NIL) NIL)                 ; interval
;  .
;  (((18 . O-FINP)                      ; pos-pairs
;    (9 . EQLABLEP)
;    (5 . RATIONALP)
;    (4 . INTEGERP)
;    (0 . ACL2-NUMBERP))
;   .
;   ((99 . BAD-ATOM)                    ; neg-pairs
;    (87 . WRITABLE-FILE-LISTP1)
;    (84 . READ-FILE-LISTP1)
;    (81 . WRITTEN-FILE)
;    (78 . READABLE-FILE)
;    (74 . OPEN-CHANNEL1)
;    (54 . KEYWORDP)
;    (47 . ALPHA-CHAR-P)
;    (38 . IMPROPER-CONSP)
;    (37 . PROPER-CONSP)
;    (32 . BOOLEANP)
;    (7 . SYMBOLP)
;    (6 . STRINGP)
;    (3 . CONSP)
;    (2 . COMPLEX-RATIONALP)
;    (1 . CHARACTERP))))

; If you (decode-tau * 'x) you get the body of the lambda expression it represents, which is

; (lambda (x)
;  (AND                                  ; pos-evg [none]
;       (ACL2-NUMBERP X)                 ; pos-pairs
;       (INTEGERP X)
;       (RATIONALP X)
;       (EQLABLEP X)
;       (O-FINP X)
;       (INTEGERP X)                     ; interval [note redundancy]
;       (NOT (EQUAL X '2))               ; neg-evgs
;       (NOT (EQUAL X '3))
;       (NOT (CHARACTERP X))             ; neg-pairs
;       (NOT (COMPLEX-RATIONALP X))
;       (NOT (CONSP X))
;       (NOT (STRINGP X))
;       (NOT (SYMBOLP X))
;       (NOT (BOOLEANP X))
;       (NOT (PROPER-CONSP X))
;       (NOT (IMPROPER-CONSP X))
;       (NOT (ALPHA-CHAR-P X))
;       (NOT (KEYWORDP X))
;       (NOT (OPEN-CHANNEL1 X))
;       (NOT (READABLE-FILE X))
;       (NOT (WRITTEN-FILE X))
;       (NOT (READ-FILE-LISTP1 X))
;       (NOT (WRITABLE-FILE-LISTP1 X))
;       (NOT (BAD-ATOM X))))

; Of course, this will change if additional recognizers or new relations
; between existing recognizers are added to the boot-strap.  But it illustrates
; the structure of an actual tau.

; That is, if we say x has that tau, then we know x is an INTEGERP other than 2
; and 3, and ``everything'' that implies about other tau recognizers.

; Note that the meaning of a tau is the CONJUNCTION of its elements.  We
; sometimes write M[tau] to mean the meaning of tau.

; Note: This interpretation of sets of recognizers is exactly the OPPOSITE of
; type-set!  For example, if we say x has type-set {p q} we mean x either
; satisfies p or satisfies q.  But if that same set is interpreted as a tau, we
; are saying that x satisfies both p and q.  Of course, some tau are
; inconsistent which is why we place additional restrictions (see below) on
; tau.

; We sometimes informally exhibit a tau as a set in notation like this:

; {/=2, /=3, integerp, rationalp, ..., -characterp, ...}

; or obvious variants like

; {nil/2, nil/3, t/integerp, t/rationalp, ..., nil/characterp, ...}.

; and if the interval is interesting we may include elements like 0<= or <=45.

; On the Built-in Tau and the Abuse of Tau Representation

; Below is a well-formed but empty tau.  It says we don't know anything about
; the term to which it is associated.

(defconst *tau-empty*
  (make tau
        :pos-evg nil
        :neg-evgs nil
        :pos-pairs nil
        :neg-pairs nil
        :interval nil))

; Abuse of Tau Representation: Nil is synonymous with *tau-empty* as a
; recognizer set!  That is, applying the tau accessors to nil gives the same
; result as applying them to *tau-empty*.  We actually do this in one place: In
; ok-to-fire-signature-rulep we are supposed to pass in a list of recognizer
; sets in 1:1 correspondence with the formals of a function.  Sometimes we pass
; in nil instead, knowing that every ``element'' of nil is nil and that those
; nils will be treated like *tau-empty*.

; This constant is tested against a lot and we wish to avoid recomputing it
; every time.

(defconst *nil-singleton-evg-list* (cdr *nil*))

(defconst *tau-t* (make tau
                        :pos-evg (cdr *t*)
                        :neg-evgs nil
                        :pos-pairs nil
                        :neg-pairs nil
                        :interval nil))

(defconst *tau-nil* (make tau
                          :pos-evg *nil-singleton-evg-list*
                          :neg-evgs nil
                          :pos-pairs nil
                          :neg-pairs nil
                          :interval nil))

(defconst *tau-non-nil* (make tau
                              :pos-evg nil
                              :neg-evgs (list (cdr *nil*))
                              :pos-pairs nil
                              :neg-pairs nil
                              :interval nil))

; On the Additional Restrictions on Tau Fields

; We enforce restrictions on the tau fields to minimize redundancy and shorten
; the lists involved.  The motto here is ``The only redundancy in a tau is in
; the interval.''

; Restriction 0: No tau should be ``obviously contradictory''.

;  Restriction 0.1:  The intersection of pos-pairs and neg-pairs is empty.

;  Restriction 0.2: When pos-evg is non-nil, no pos-pair evaluates to false on
;  that evg and no neg-pair evaluates to true on it.

; Restriction 1: If pos-evg is non-nil, neg-evgs must be nil.

; Restriction 2: If pos-evg is non-nil, pos-pairs (and neg-pairs) should be as
; short as possible, i.e., not contain recognizers that evaluate to true (false)
; on that evg.  That means when pos-evg is non-nil the only elements in
; pos-pairs and neg-pairs are recognizers that cannot be evaluated.

; Restriction 3: Neg-evgs is duplicate-free and ordered ascending by ``almost''
; lexorder (NIL is the smallest item in our ordering).  Pos-pairs and neg-pairs
; are duplicate-free and ordered by their indices.

; Restriction 4: Neg-evgs should be as short as possible given pos-pairs,
; neg-pairs, and the interval.  It is illegal to have an evg in :neg-evgs such
; that some p in :pos-pairs evaluates to false on evg or some p in :neg-pairs
; evaluates to true on evg or is outside the given interval.  For example, if
; :pos-pairs includes NATP, it is illegal to include (the singleton list
; containing) LOAD in :neg-evgs.  That inequality is implied by :pos-evgs.

; Restriction 5: The interval of a tau has as its domain one of INTEGERP,
; RATIONALP, ACL2-NUMBERP, or NIL; if INTEGERP both relations are nil (<=) and
; both extents are integers (or nil).  Otherwise, extents are rational (or
; nil).  When a tau is an equality with a rational constant, the accompanying
; interval is the singleton interval containing that constant.  Intervals are
; never empty.

; It is sometimes convenient to think in terms of the set comprehending the
; meaning of a tau.  S[tau] = {x | (M[tau] x)}.  Thus, S[{NATP}] = the set of
; all naturals.  If tau has :neg-evgs '((-23)(-24)), :pos-pairs '((1
; . integerp)) and :neg-pairs '((0 . NATP)), then S[tau] is the set of all
; non-natural integers other than -23 and -24.

; A tau is ``obviously contradictory'' if (a) there is a non-nil
; intersection between the pos-pairs and neg-pairs, or if (b) pos-evg is a
; singleton evg and either (b1) the recognizer of some pos-pair evaluates to nil
; on that evg, or (b2) the recognizer of some neg-pair evaluates to t on that
; evg.  If tau is obviously contradictory it is clear that M[tau] is nil.
; However, the converse is not necessarily true.  For example, one might define
; two tau recognizers:

; (defun IS-NATP (x) (NATP x))
; (defun IS-NOT-NATP (x) (not (NATP x)))

; and then the meaning of the recognizer set containing both in pos-pairs is nil
; but the tau is not obviously contradictory.  More complicated examples can be
; constructed involving the evgs and the pairs.  Pragmatically, the user should
; not define predicates as the negations of other predicates nor should
; equality-with-constants be ``hidden'' as predicates.  But we do not enforce
; this and draw no logical conclusions from the fact that a tau is NOT
; obviously contradictory.

; We often return the keyword :contradiction instead of a tau when we have
; detected that tau is obviously contradictory.  That is, if a variable in our
; code is said to be a tau it may be an instance of the tau record class above
; or it may be the symbol :contradiction.  Generally speaking we try to avoid
; even constructing obviously contradictory recognizer sets.

; In order to highlight when :contradiction is being used as a tau, we define
; the following constant.  However, our code assumes the value of this constant
; is a symbol (e.g., we use EQ to test against it).  It is sometimes convenient
; to think of *tau-contradiction* as a recognizer set that contains every
; tau recognizer in both its positive and negative fields.  That's a little
; misleading because the representation of tau do not allow more than one
; :pos-evg, but if it did (e.g., if we had :pos-evgs instead of :pos-evg), the
; canonical *tau-contradiction* contains all the evgs in :pos-evgs and in
; :neg-evgs and has all the recognizers in :pos-pairs and in :neg-pairs.

(defconst *tau-contradiction* :contradiction)

(defconst *contradictory-tau*
  (change tau *tau-empty*
          :interval *tau-empty-interval*))

; The above tau is contradictory on its face: it specifies an empty interval,
; so if (h x) has this tau as its pos-implicants, for example, then (h a)
; implies 0 < a < 0.  A way to create an h with this property is shown in the
; example (sent by Grant Passmore) in add-tau-simple-rule below.

; Note on contradictionp versus :contradiction versus the *contradictory-tau*:
; When a tau is being returned we signal contradictions by using the bogus
; ``tau'' *tau-contradiction*; we could have chosen to return
; *contradictory-tau* instead but that would then require testing for EQUAL
; rather than EQ and we test for *tau-contradiction* quite a lot especially in
; tau-term and tau-assume, which are used a lot during proofs involving big
; terms.  So we wanted to make testing fast.  When we're trafficking in other
; objects, e.g., the property list world, we signal contradictions with the
; familiar (mv contradictionp ...) convention because the contradiction
; detected may be deeply buried in the world.  We do not ever put
; *tau-contradiction* into objects containing tau data structures.  However,
; when we are trafficking in the property list world (meaning we might have
; updated various parts of the tau database, including the pos- or
; neg-implicants of a symbol) we might store the contradictory tau,
; *contradictory-tau*, in the database, as happens when we build the
; pos-implicants, for example, of a predicate that is identically nil.  (See
; the example in add-tau-simple-rule.)

; It would clearly be better to have a single way to denote a contradictory
; tau, e.g., to allow the symbol :contradiction to be treated like a tau but
; tested with eq.  But that would require testing for that symbol in the tau
; accessors which would slow us down.

; We will be more precise about the database later, but Simple rules are used
; to populate the database, storing all the implications of a given
; recognizers truth or falsity.  These implications are just tau representing
; the set of all truths that follow.  For example, under NATP we will store the
; tau of all known recognizers implied by t/NATP, as well as all known
; recognizers implied by nil/NATP.  The database is used to collect known
; truths about a term, by unioning together the sets implied by everything we
; know about the term and then augmenting that set with Conjunctive rules that
; may tell us other things given the particular combination of things we know.

; Conjunctive rules are formulas that tell us that certain combinations of
; recognizers imply other recognizers.  For example, if a Conjunctive rule says
; that p and q imply r, and we have deduced a tau that contains p and contains
; q, then we add r to tau.  This is called ``completing'' the tau.  It happens
; that Conjunctive rules are represented as sets of recognizers, so we use the
; same tau datastructure to represent them but we do not interpret them with M.
; The rule (p & q) --> r is represented by the set C = {-p -q -r}.  To use C as
; a conjunctive rule we ask whether some tau, just derived, contains all but
; one of the elements of C and if so we can add the negation of the omitted
; element of C.

; This brings us to Signature rules of both forms.  Signature rules tells us
; facts about the value of a function given facts about its inputs.  Signature
; rules play the primary role in determining the tau of a term (or of its
; MV-NTH components) given tau assumptions about subterms.

(defrec signature-rule (input-tau-list
                        (vars . dependent-hyps)
                        output-sign output-recog) t)

; Signature rules are hung on some n-ary function symbol.  The formula from
; which such a rule is derived is:

; (implies (and (tau_1 v1) ... (tau_n vn)
;               (dhyp_1 v1 ... vn) ... (dhyp_k v1 ... vn))
;          (tau (fn v1 ... vn)))

; modulo several obvious generalizations of the form and arbitrary ordering and
; mixing of the hypotheses.  The representation of such a formula as a
; signature-rule is:

; :inputs-tau-list  - (tau_1 ... tau_n) -- required tau of corresponding vars
; :vars             - (v1 ... vn) -- the vars used in the conclusion
; :dependent-hyps   - list of terms in vars ((dhyp_1 v1 ... vn) ...)
; :output-sign      - T (positive) or NIL (negative)
; :output-recog     - tau, i.e., tau-pair or singleton evg list

; Foreshadowing: We use this same record for both forms of signature rules.
; Under the SIGNATURE-RULES-FORM-1 property of a function symbol fn we will
; find a list of these records, interpreted in the obvious way about calls of
; fn: if the actuals satisfy their respective tau in :inputs-tau-lst and the
; :dependent-hyps are relieved, then the output of fn satisfies the output-sign
; and output-recog.  Under the SIGNATURE-RULES-FORM-2 property of a fn with
; output arity m we may find a list of length m, each element being a list of
; these same records.  The interpretation of the records in slot i is that the
; ith value returned by fn has the indicated tau.  We will allow both
; properties to exist for a function symbol.  That is, one might prove that (fn
; x y) is a true-list of length 3 and might also characterize the tau of
; (mv-nth '0 (fn x y)), (mv-nth '1 (fn x y)), and (mv-nth '2 (fn x y)).  When
; trying to determine the tau of an (mv-nth 'i (fn a b)) expression we use only
; the rules in the ith slot of the form 2 rules for f.  When trying to
; determine the tau of (fn a b) we use only the form 1 rules for fn.

; Finally, when we are processing terms, either to find their tau or to assume
; them true, we may do a small amount of rewriting.  In particular, we expand
; so-called big switch function calls.  Roughly speaking, a ``big switch''
; function is a nonrec function that is initially controlled entirely by the
; tau of a single formal variable.  For example, (little-switch key x) defined
; to be (symbolp x) if key is 'SYMBOLP, (natp x) if key is 'NATP, and (consp x)
; otherwise, is a big switch function with the variable key as its ``switch
; variable.''

; If fn is a big switch function, then we can partially evaluate a call of that
; function efficiently under some tau assumptions.  In particular, we do not
; need to instantiate the entire body of the definition.  If we know enough
; about the switch actual to navigate past all those tau tests on the switch
; formal, we can reach a ``leaf'' and instantiate just it.  If we cannot
; navigate to a leaf, we do not expand the big switch function at all.

; If a theorem, (EQUAL (fn . formals) body), defines a big switch function we
; make a big switch rule of the form:

(defrec big-switch-rule (formals switch-var switch-var-pos body) nil)

; where switch-var is the switch var and switch-var-pos is its position in
; formals.  That rule will be stored under fn on the property 'big-switch.

(defun tau-simple-implicants (sign pred wrld)
  (getpropc pred (if sign 'pos-implicants 'neg-implicants) nil wrld))

; Obviously Contradictory Recognizer Sets

; We define make-tau which takes the four components of a tau and returns the
; corresponding instance of tau, unless that tau is obviously contradictory, in
; which case we return *tau-contradiction*.  The four arguments are assumed
; individually to be well-formed, e.g., duplicate-free and ordered
; appropriately.

(defun tau-pair-member1 (index pairs)
  (cond ((endp pairs) nil)
        ((>= (car (car pairs)) index)
         (or (equal (car (car pairs)) index)
             (tau-pair-member1 index (cdr pairs))))
        (t nil)))

(defun tau-pair-member (pair pairs)

; This function determines whether (car pair) is a member of (strip-cars
; pairs), but assumes that pairs is ordered descending on the cars, as enforced
; by merge-sort-car->.  Note that it is tempting to think this function
; determines whether pair is a member of pairs, but in fact the cdrs of the
; pairs are totally ignored.  Thus, (tau-pair-member '(1 . A) '((1 . B))) is
; true!

  (tau-pair-member1 (car pair) pairs))

; On the Use of ENS by Function Evaluation in the Tau System

; The following function is used throughout the tau system to determine whether
; a recognizer will accept (recognize) a given constant or not.  In an earlier
; incarnation of the function, it was not sensitive to the enabled status of the
; executable-counterpart of the tau recognizer fn.

; One argument for making the tau system respect the current enabled structure
; is that some authors disable :executable-counterparts in their proofs and if
; tau does not respect the disabling, it is behaving contrary to the author's
; wishes.  This happens in the file Proof-Of-Equiv-From-M-Corr.lisp of
; community book books/workshops/1999/embedded/Proof-Of-Contribution/ by
; P.G. Bertoli and P. Traverso (which is a chapter in the ACL2 Case Studies
; book), where the authors execute (in-theory (current-theory 'ground-zero))
; near the top of the book, thus disabling almost everything.  The hypothesis
; (rel-prime-moduli '(11 13 15 17 19)) is used frequently and proofs break if
; it is evaluated.  This particular book is not a very good argument for
; respecting ens, since the script could probably have been developed without
; this Draconian disabling.  A better reason to make tau respect ens is that
; some executable-counterparts could be so inefficient to compute that the user
; would prefer that they never be run.  But tau would run them and lose.  In
; fact, in that earlier incarnation just mentioned, tau did run them and did
; lose.  See the example below.

; On the other side, however, is the tau system convention that if a recognizer
; in the pos-pairs of a tau accepts a given evg, then that evg is not included
; in the neg-evgs.  For example, suppose we want to construct the tau that
; denotes (lambda (v) (and (not (equal v 23)) (foop v))).  But suppose that
; (foop 23) is false.  Then there is no point in including the ``(not (equal v
; 23))'' since is implied by the (foop v).  Indeed, we'd represent this tau as
; the set {foop}.  Suppose that tau were stored as the positive implicants of
; some recognizer in the database.  Now imagine the user disables the
; executable-counterpart of foop.  Are we to recompute the normal form of all
; the stored taus?  We just can't bear the thought!

; So we have adopted a slightly inelegant approach: Tau is sensitive to the
; enabled status of the executable-counterparts of the tau recognizers it needs
; to evaluate but suffers unnecessary incompleteness as a result.  For example,
; one might build a tau in the database that contains foop and that (at the
; time it was built) also records that 23 is not in the tau.  But then one
; disables foop and thereafter it is unknown whether 23 is in the tau or not.

; The second occurrence of a local LEMMA4 in the community book
; unicode/utf8-decode.lisp provides an interesting test of the available
; strategies for dealing with expensive calls of ev-fncall-w-tau-recog.

; If the tau-system is disabled, that LEMMA4 takes only about 0.06 seconds to
; prove (on a 2.6 GHz Intel Core i7 with 16 GB 1600 MHz DDR3 Macbook Pro).  But
; if tau-system is enabled and no special steps are taken, it takes 5.91
; seconds.  The problem is that the tau recognizer TEST-UTF8-COMBINE4 is
; evaluated several times by the tau system as it computes the tau for various
; terms, and TEST-UTF8-COMBINE4 is very expensive to compute.  Tau evaluates
; this user-defined predicate a total of 11 times in all, on 0, NIL, and T.

; This raises two problems: how do you discover the source of this slowdown,
; and what do you do about it after discovering it?  It was discovered by
; noticing the time difference for the utf8-decode book in two successive
; regressions and then using the Allegro profiler to identify the *1* function
; for TEST-UTF8-COMBINE4 as the culprit.  Once that was confirmed, experiments
; were done to determine all the calls of ev-fncall-w-tau-recognizer in the
; entire book (just to see if it got excessive).  It turns out it is called a
; total of 102,004 times to evaluate 96 different tau recognizers on these
; constants: (-1 244 240 237 224 1 4 3 2 0 T NIL).  A total of 480 distinct (fn
; 'evg) are involved and about 5.8 seconds is consumed in these.

; But by far the most expensive calls are the 11 calls of TEST-UTF8-COMBINE4:

; (evg val n secs)

; (0   T   7 0.180351)
; (T   T   2 1.152991)
; (NIL T   2 1.163224)

; E.g., TEST-UTF8-COMBINE4 is called 7 times on 0 and the first call took
; 0.180351 seconds.  Note how expensive T and NIL are.

; After the defun of ev-fncall-w-tau-recog, below, we include a comment that
; shows the raw Lisp code used to accumulate such information.  This is
; preserved here for future reference and may be advertised to some users
; suffering slowdowns.  NOTE: After these notes were written, we implemented
; the time-tracker mechanism as a way of diagnosing such slowdowns.

; There are four mechanisms in tau for dealing with this.  Mechanism A is to do
; nothing and suffer the slowdown.  Mechanism B is to disable the tau-system!
; Mechanism C is to prove the ``mechanism-c-lemma,'' characterizing the value
; of the expensive recognizer on the constants in question, provided one can
; determine what those constants are.  Mechanism D is to disable the expensive
; recognizer and perhaps lose some completeness.

; Mechanism             LEMMA4 Proof Time Reported in Summary
; A [do nothing]                 5.91 seconds
; B [disable tau]                0.07 seconds
; C [build in expensive calls]   0.07 seconds
; D [disable expensive calls]    0.07 seconds

; Here is the lemma used in Mechanism C:
; (local (defthm mechanism-c-lemma
;          (and (test-utf8-combine4 0)
;               (test-utf8-combine4 nil)
;               (test-utf8-combine4 t))
;          :rule-classes :tau-system))
; Time:  2.50 seconds (prove: 2.50, print: 0.00, other: 0.00)

; This lemma stores the value of the recognizer on its property list and it is
; looked up instead of computed.

; Note that while the lemma allows the fast proof of LEMMA4, the lemma itself
; takes 2.5 seconds to prove.

(defun ev-fncall-w-tau-recog (fn evg-lst ens wrld)

; Fn is a monadic Boolean function symbol known to tau and evg-lst is a
; singleton list containing an evg.  We apply fn to evg-lst and return the
; value, T or NIL, or we return :UNEVALABLE.  We check the unevalable-but-known
; property of fn first.  By checking it first we allow the user to prove a
; :tau-system rule that short-circuits long but successful calculations, if the
; user is clever enough to realize that slowdowns are due to repeated
; evaluations of such functions.

; Warning: If this function is changed to call itself recursively, reconsider
; the setf expression in the comment after this defun.

  (cond
   ((enabled-xfnp fn ens wrld)
    (let* ((ubk (getpropc fn 'unevalable-but-known nil wrld))
           (temp (if ubk
                     (assoc-equal (car evg-lst) ubk)
                     nil)))
      (cond
       (temp (cdr temp)) ; previously stored T or NIL
       (t
        (mv-let (erp val)
                (ev-fncall-w fn evg-lst wrld nil nil t t nil)

; The arguments to ev-fncall-w above, after wrld, are user-stobj-alist (= nil),
; safe-mode (= nil), gc-off (= t), hard-error-returns-nilp (= t), and aok (=
; nil).  These are the same arguments used in the call of ev-fncall-w in
; sublis-var!.

                (cond
                 (erp :UNEVALABLE)
                 (val t)
                 (t nil)))))))
   (t :UNEVALABLE)))

; Some Implementor-Level Performance Investigation Tools
;
;   ; Ev-fncall-w-tau-recog, above, is used to evaluate tau predicates on
;   ; constants.  Of course, if the tau predicate in question is complicated this
;   ; evaluation can be slow.  Tau Eval rules can be used to store pre-computed
;   ; results and speed up subsequent evaluations.  But what predicates and what
;   ; constants need to be pre-computed and stored?
;
;   ; In this comment we drop some raw Lisp code used to collect every call of
;   ; ev-fncall-w-tau-recog.  Data is stored in a simple alist and so if the number
;   ; of distinct recognizers grows large, this data collection will slow down the
;   ; proof.  After collecting the data, one can learn what recognizers were
;   ; called, what constants they were called on, how many times each recognizer
;   ; was called on each constant, and how long the first (and only computed) call
;   ; of each recognizer took.
;
;   ; When you are ready to collect the data for a proof or proofs, do this to
;   ; exit the ACL2 loop and enter raw Lisp.
;
;   (value :q)
;
;   ; Next, save the current definition of ev-fncall-w-tau-recog in
;   ; ev-fncall-w-tau-recog1.
;
;   ; Warning:  This setf hack works only if ev-fncall-w-tau-recog is not
;   ; recursively defined and our sources don't already use the symbol
;   ; ev-fncall-w-tau-recog1.
;
;   (setf (symbol-function 'ev-fncall-w-tau-recog1)
;         (symbol-function 'ev-fncall-w-tau-recog))
;
;   ; Now declare the collection site.  The setq after this defvar is useful if
;   ; you run multiple tests and want to clear the site.
;
;   (defvar ev-fncall-w-tau-recog-alist nil)
;   (setq ev-fncall-w-tau-recog-alist nil)
;
;   ; Now redefine the raw Lisp version of  ev-fncall-w-tau-recog to
;   ; collect the data:
;
;   (defun ev-fncall-w-tau-recog (fn evg-lst ens wrld)
;     (let ((fn-alist (assoc-eq fn ev-fncall-w-tau-recog-alist)))
;       (cond
;        (fn-alist
;         (let ((evg-val-cnt-time (assoc-equal (car evg-lst) (cdr fn-alist))))
;           (cond
;            (evg-val-cnt-time
;             (setf (caddr evg-val-cnt-time) (+ 1 (caddr evg-val-cnt-time)))
;             (cadr evg-val-cnt-time))
;            (t
;             (let* ((start-time (get-internal-run-time))
;                    (val (ev-fncall-w-tau-recog1 fn evg-lst ens wrld))
;                    (total-time (- (get-internal-run-time) start-time)))
;               (setf (cdr fn-alist)
;                     (cons (list (car evg-lst) val 1 total-time) (cdr fn-alist)))
;               val)))))
;        (t (let* ((start-time (get-internal-run-time))
;                  (val (ev-fncall-w-tau-recog1 fn evg-lst ens wrld))
;                  (total-time (- (get-internal-run-time) start-time)))
;             (setq ev-fncall-w-tau-recog-alist
;                   (cons (cons fn (list (list (car evg-lst) val 1 total-time)))
;                         ev-fncall-w-tau-recog-alist))
;             val)))))
;
;   ; Return to the loop and run your proof(s).
;   (lp)
;
;   ; <your proof event(s) here>
;
;   ; Exit ACL2 and re-enter raw Lisp:
;   (value :q)
;
;   ; The collected data is stored in  ev-fncall-w-tau-recog-alist.  But this
;   ; list can be big so we tend to investigate its size before just printing it.
;
;   ; For the record, every element of ev-fncall-w-tau-recog-alist is a
;   ; fn-dot-alist, e.g., (fn . alist), and alist is a list of 4-tuples, each of
;   ; the form (const val count time), where
;
;   ; (nth 0 fourtuple) -- evg that fn is applied to
;   ; (nth 1 fourtuple) -- val of fn on evg
;   ; (nth 2 fourtuple) -- number of times fn applied to evg
;   ; (nth 3 fourtuple) -- time it took to eval (fn evg) once
;
;   ; Time, above, is measured in CLTL internal time units, where the Common Lisp
;   ; global internal-time-units-per-second says how many of these units are in
;   ; one second.
;
;   ; Some typical expressions for investigating the evaluation of recognizers on
;   ; constants:
;
;   ; Number of distinct tau recogs evaluated:
;   (len ev-fncall-w-tau-recog-alist)
;
;   ; Total amount of time, in seconds, devoted to ev-fncall-w-tau-recog
;   ; if every call were computed from the definition of the recognizers.
;   (list (float
;          (/ (loop for fn-dot-alist in ev-fncall-w-tau-recog-alist
;                   sum
;                   (loop for fourtuple in (cdr fn-dot-alist)
;                         sum (* (nth 2 fourtuple)
;                                (nth 3 fourtuple))))
;             internal-time-units-per-second))
;         'seconds)
;
;   ; Number of distinct constants concerned:
;   (len (loop for fn-dot-alist in ev-fncall-w-tau-recog-alist
;              with ans
;              do (setq ans (union-equal (loop for fourtuple in (cdr fn-dot-alist)
;                                              collect (nth 0 fourtuple))
;                                        ans))
;              finally (return ans)))
;   ; To see the constants themselves, just drop the len above.
;
;   ; Number of calls of ev-fncall-tau-recog
;   (loop for fn-dot-alist in ev-fncall-w-tau-recog-alist
;         sum (loop for fourtuple in (cdr fn-dot-alist) sum (nth 3 fourtuple)))
;
;   ; Display of all the data, sorted to show most expensive calls first:
;   ; Time is measured in internal-time-units and internal-time-units-per-second
;   ; says how big those units are.
;   (loop for x in
;         (cons '(time (fn evg) = val (count))
;               (merge-sort-car->
;                (loop for fn-dot-alist in ev-fncall-w-tau-recog-alist
;                      append
;                      (let ((fn (car fn-dot-alist)))
;                        (loop for fourtuple in (cdr fn-dot-alist)
;                              collect (list (nth 3 fourtuple)
;                                            (list fn (nth 0 fourtuple))
;                                            '= (nth 1 fourtuple)
;                                            (list (nth 2 fourtuple))))))))
;         do (print x))
;
;   ; Sort the list of recognizers by total time spent in each.
;   (merge-sort-car->
;    (loop for fn-dot-alist in ev-fncall-w-tau-recog-alist
;          collect
;          (list (loop for fourtuple in (cdr fn-dot-alist)
;                      sum (* (nth 2 fourtuple) (nth 3 fourtuple)))
;                (car fn-dot-alist))))
;
; End of Some Implementor-Level Performance Investigation Tools

(defun bad-val-or-unknowns (bad-val pairs evg-lst ens wrld)

; Bad-val is t or nil.  If bad-val is t, understand it to mean that we are
; looking for a true or non-nil value.  If bad-val is nil, we are looking for a
; false or nil value.  Pairs is a list of tau-pairs, (i . pred).  Evg-lst is a
; SINGLETON list containing one evg!  We determine whether there is a pred in
; pairs that evals to bad-val on this evg.  If so we return T.  If all eval to
; something other than the bad-val, we return NIL.  If some cannot be evaled
; and none eval to the bad-val, we return the list of unevalable tau pairs.

  (cond
   ((endp pairs) nil)
   (t
    (let ((val (ev-fncall-w-tau-recog (cdr (car pairs)) evg-lst ens wrld)))
      (cond
       ((eq val :UNEVALABLE)
        (let ((rest (bad-val-or-unknowns bad-val (cdr pairs) evg-lst ens wrld)))
          (cond ((eq rest t) t)
                (t (cons (car pairs) rest)))))
       (bad-val
        (if val
            t
            (bad-val-or-unknowns bad-val (cdr pairs) evg-lst ens wrld)))
       (t (if val
              (bad-val-or-unknowns bad-val (cdr pairs) evg-lst ens wrld)
              t)))))))

(defun exists-bad-valp (bad-val pairs evg-lst ens wrld)

; Bad-val is t or nil.  If bad-val is t, understand it to mean that we are
; looking for a true or non-nil value.  If bad-val is nil, we are looking for a
; false or nil value.  Pairs is a list of tau-pairs, (i . pred).  Evg-lst is a
; SINGLETON list containing one evg!  We determine whether there is a pred in
; pairs that evals to bad-val on this evg.  If so, we return T.  If not we
; return NIL.  Note that preds in pairs that cannot be evaluated are skipped.
; They are not considered ``good'' or ``bad''.  What we said is what we mean:
; we're looking for a pred that evals to bad-val!

  (cond
   ((endp pairs) nil)
   (t
    (let ((val (ev-fncall-w-tau-recog (cdr (car pairs)) evg-lst ens wrld)))
      (cond
       ((eq val :UNEVALABLE)
        (exists-bad-valp bad-val (cdr pairs) evg-lst ens wrld))
       (bad-val
        (if val
            t
            (exists-bad-valp bad-val (cdr pairs) evg-lst ens wrld)))
       (t (if val
              (exists-bad-valp bad-val (cdr pairs) evg-lst ens wrld)
              t)))))))

(defun all-eval-valp (good-val pairs evg-lst ens wrld)

; Good-val is t or nil.  If good-val is t, understand it to mean that we are
; looking for a true or non-nil value.  If good-val is nil, we are looking for
; a false or nil value.  Pairs is a list of tau-pairs, (i . pred).  Evg-lst is
; a SINGLETON list containing one evg!  We determine whether every pred in
; pairs evals to good-val on this evg.  If so, we return T.  If not we return
; NIL.  If a pred in pairs cannot be evaled, it means it did not eval to
; good-val!

  (cond
   ((endp pairs) t)
   (t
    (let ((val (ev-fncall-w-tau-recog (cdr (car pairs)) evg-lst ens wrld)))
      (cond
       ((eq val :UNEVALABLE) nil)
       (good-val
        (if val
            (all-eval-valp val (cdr pairs) evg-lst ens wrld)
            nil))
       (t (if val
              nil
              (all-eval-valp val (cdr pairs) evg-lst ens wrld))))))))

(defun delete-bad-vals (neg-evgs pos-pairs neg-pairs ens wrld)

; We copy neg-evgs deleting those that falsify some element of pos-pairs or
; satisfy some element of neg-pairs.  We return (mv changedp result).  Changedp
; is t if the result is different from neg-evgs; else changedp is nil.

  (cond
   ((endp neg-evgs) (mv nil nil))
   (t (mv-let
       (changedp result)
       (delete-bad-vals (cdr neg-evgs) pos-pairs neg-pairs ens wrld)
       (cond
        ((exists-bad-valp nil pos-pairs (car neg-evgs) ens wrld)
         (mv t result))
        ((exists-bad-valp t neg-pairs (car neg-evgs) ens wrld)
         (mv t result))
        ((null changedp)
         (mv nil neg-evgs))
        (t (mv t (cons (car neg-evgs) result))))))))

(defun delete-bad-vals1 (neg-evgs sign tau-pair ens wrld)

; Despite the name, this function is not a subroutine of delete-bad-vals.
; Instead, it is a minor extension of it, equivalent to

; (delete-bad-vals neg-evgs
;                  (if sign (list tau-pair) nil)
;                  (if sign nil (list tau-pair))
;                  ens wrld)

; but avoids the consing of (list tau-pair).

; We sweep neg-evgs (a list of singleton lists containing evgs) and delete
; those that are bad in the sense of being redundant wrt to a particular
; signed recognizer.  We return (mv changedp result).

  (cond ((endp neg-evgs) (mv nil nil))
        (t (let ((val (ev-fncall-w-tau-recog (cdr tau-pair)
                                             (car neg-evgs)
                                             ens
                                             wrld)))
             (mv-let
              (changedp result)
              (delete-bad-vals1 (cdr neg-evgs) sign tau-pair ens wrld)
              (cond
               ((eq val :UNEVALABLE)
                (if changedp
                    (mv t (cons (car neg-evgs) result))
                    (mv nil neg-evgs)))
               (val (if sign
                        (if changedp
                            (mv t (cons (car neg-evgs) result))
                            (mv nil neg-evgs))
                        (mv t result)))
               (t (if sign
                      (mv t result)
                      (if changedp
                          (mv t (cons (car neg-evgs) result))
                          (mv nil neg-evgs))))))))))

(defun tau-pairs-subsetp (pairs1 pairs2)

; Provided both arguments are duplicate-free ordered descending tau-pair lists
; we determine whether (subsetp-equal pairs1 pairs2).

  (cond ((endp pairs1) t)
        ((endp pairs2) nil)
        ((>= (car (car pairs1)) (car (car pairs2)))
         (if (equal (car (car pairs1)) (car (car pairs2)))
             (tau-pairs-subsetp (cdr pairs1) (cdr pairs2))
             nil))
        (t (tau-pairs-subsetp pairs1 (cdr pairs2)))))

(defun tau-pairs-near-subsetp (pairs1 pairs2 e)

; Pairs1 and pairs2 are duplicate-free ordered descending tau-pair lists.  We
; determine whether there is exactly one element of pairs1 not in pairs2.  We
; return t if pairs1 is a subset of pairs2, nil if more than one element of
; pairs1 fails to be pairs2, and the missing tau-pair otherwise.

; Optimization Note: Pairs1 cannot be a near subset of pairs2 if the index of
; the second pair in pairs1 is greater than the index of the first pair in
; pairs2 the first time this function is entered (or more generally when e =
; nil).  But this optimization (coded by renaming this function to be the
; workhorse, tau-pairs-near-subsetp1, and adding a top-level function to check
; for the short-cut) only saved about one half of one percent of the total
; number of calls of the workhorse over a test involving about 380 million
; calls.  So we don't implement this optimization.

  (cond ((endp pairs1) (if e e t))
        ((endp pairs2)
         (if e nil (if (endp (cdr pairs1)) (car pairs1) nil)))
        ((>= (car (car pairs1)) (car (car pairs2)))
         (if (equal (car (car pairs1)) (car (car pairs2)))
             (tau-pairs-near-subsetp (cdr pairs1) (cdr pairs2) e)
             (if e
                 nil
                 (tau-pairs-near-subsetp (cdr pairs1) pairs2 (car pairs1)))))
        (t (tau-pairs-near-subsetp pairs1 (cdr pairs2) e))))

(defun tau-pairs-intersectionp (pairs1 pairs2)

; The two arguments are lists of tau-pairs, ordered descending.  We determine
; whether there is an element in both lists.  We key only on the indices and
; ignore the cdrs.  Thus, we say there is an intersection between ((1 . a)) and
; ((1 . b)).

  (cond
   ((endp pairs1) nil)
   ((endp pairs2) nil)
   ((>= (car (car pairs1)) (car (car pairs2)))
    (if (equal (car (car pairs1)) (car (car pairs2)))
        t
        (tau-pairs-intersectionp (cdr pairs1) pairs2)))
   (t (tau-pairs-intersectionp pairs1 (cdr pairs2)))))

(defun insert-tau-pair (pair pairs)

; Pair is a tau-pair and pairs is a list of tau-pairs, ordered descending.  We
; insert pair into pairs or else return t if it is already there.

  (cond ((endp pairs) (cons pair pairs))
        ((>= (car (car pairs)) (car pair))
         (if (eql (car (car pairs)) (car pair))
             t
             (let ((rest (insert-tau-pair pair (cdr pairs))))
               (if (eq rest t)
                   t
                   (cons (car pairs) rest)))))
        (t (cons pair pairs))))

; On the Most Basic Implications of Being in an Interval

; Suppose x is in an interval (lo <? x <? hi).  Suppose k is some rational.  What
; does the interval tell us about (x <? k)?

; Below are four theorems, labeled A, B, C, and D.  A tells us that (< x k) is
; true and B tells us that it is false.  C tells us that (<= x k) is true, and
; D tells us that it is false.  Of course, the tests comparing x to the
; endpoints of its interval are really just tests on the strengths of the
; applicable relations:

; test in       test in
; theorem       code

; (< x hi)      hi-rel = t
; (<= x hi)     hi-rel = nil
; (< lo x)      lo-rel = t
; (<= lo x)     lo-rel = nil

; Furthermore, the first conjuncts in the hypotheses for B and C

; test in theorem                          test ``in'' code

; (or (< lo x) (<= lo x))                  (or lo-rel (not lo-rel)) = t
; (or (< x hi) (<= x hi))                  (or hi-rel (not hi-rel)) = t

; are propositionally and so may be ignored.

; (thm (and
;       (implies (or (and (<  x hi) (<= hi k))   ; A
;                    (and (<= x hi) (<  hi k)))
;                (< x k))
;
;      (implies (and (or (< lo x) (<= lo x))     ; B
;                    (<= k lo))
;               (not (< x k)))
;
;      (implies (and (or (<  x hi) (<= x hi))    ; C
;                    (<= hi k))
;               (<= x k))
;
;      (implies (or (and (< lo x) (<= k lo))     ; D
;                   (and (<= lo x) (< k lo)))
;               (not (<= x k)))))

; These four theorems could be coded this way to determine that (<? rel x k) is
; known true, known false, or unknown given the interval:

; (if rel
;     (cond ((if hi-rel (<= hi k) (< hi k)) t)   ; A
;           ((<= k lo) nil)                      ; B
;           (t '?))
;     (cond ((<= hi k) t)                        ; C
;           ((if lo-rel (<= k lo) (< k lo)) nil) ; D
;           (t '?)))

; However, this analysis ignores the infinities.  If x has no upper bound
; (hi=nil), it will be impossible to show that k is an upper bound, i.e., that
; either (< x k) or (<= x k) is true.  Similarly, if x has no lower bound
; (lo=nil), it will be impossible to show that k is a lower bound, i.e., that
; (<= k x) or (< k x) is true, i.e., that (< x k) or (<= x k) is false.  Thus,
; we must return ?  on any branch that involves testing an infinity.

(defun interval-decider (lo-rel lo hi-rel hi rel k)

; Lo-rel, lo, hi-rel and hi are the bounds on an interval containing some
; unknown x.  Either or both of lo and hi may be nil denoting their respective
; infinities.  K is a rational and rel and k code the inequality (<? rel x k),
; i.e., (< x k) or (<= x k), depending on rel.  The question is: if we know
; that x is in the given interval, what do we know about (<? rel x k)?  The
; possible answers are: t, nil, or ?.

; Derivation of the following code is given in the comment just above.  Proof
; of its soundness is given below.

  (if rel
      (cond ((and hi (if hi-rel (<= hi k) (< hi k))) t)   ; A
            ((and lo (<= k lo)) nil)                      ; B
            (t '?))
      (cond ((and hi (<= hi k)) t)                        ; C
            ((and lo (if lo-rel (<= k lo) (< k lo))) nil) ; D
            (t '?))))

; We can use the decider to handle (<? rel k x) instead of (<? rel x k) by
; calling it with (not rel) instead of rel and swapping the sense of the answer
; with (signate nil ans) below.

(defun signate (sign x)

; Sign is a flag indicating positive or negative parity and x is a ``truth
; value'' in a 3-way system in which ? plays the role of the unknown truth
; value.  This is like ``negate,'' from which the name is derived, except (a)
; we negate if sign is negative (nil) and don't if sign is positive (t), and
; (b) we only ``negate'' the definite truth values T and NIL.

; 3-way truth table:

; sign\x |  T     NIL    ?
; --------------------------
;  T     |  T     NIL    ?
; NIL    | NIL     T     ?

; Apologies to the zoologists for abusing their word, which means ``having definite
; color markings.''

  (if sign x (if (eq x '?) '? (not x))))

; We can prove interval-decider sound as follows:

;   (verify-termination interval-decider)
;   (verify-termination signate)
;
;   (tau-status :system nil)
;
;   (defun <? (rel x y)
;     (if (or (null x) (null y))
;        t
;         (if rel
;             (< x y)
;             (<= x y))))
;
;   (thm
;    (implies (and (rationalp k)
;                  (not (equal x nil))  x can't be an infinity
;                  (<? lo-rel lo x)
;                  (<? hi-rel x hi)
;                  (not (equal (interval-decider lo-rel lo hi-rel hi rel k) '?)))
;             (equal (<? rel x k)
;                    (interval-decider lo-rel lo hi-rel hi rel k))))
;
;   ; Here is the theorem that shows how to use interval-decider to decide
;   ; (<? rel k x) instead of (<? rel x k).
;
;   (thm
;    (implies (and (rationalp k)
;                  (not (equal x nil))  x can't be an infinity
;                  (<? lo-rel lo x)
;                  (<? hi-rel x hi)
;                  (not (equal (interval-decider lo-rel lo hi-rel hi (not rel) k) '?)))
;             (equal (<? rel k x)
;                    (signate nil (interval-decider lo-rel lo hi-rel hi (not rel) k)))))
;
;   ; Alternatively, the two theorems below show how interval-decider is used to
;   ; decide signed :lessp-x-k or signed :lessp-k-x recognizers.  Note that
;   ; since < is Boolean, (signate sign (< x k)) is just (< x k) or (NOT (< x k))
;   ; depending on sign.
;
;   (thm
;    (implies (and (rationalp k)
;                  (not (equal x nil))  x can't be an infinity
;                  (<? lo-rel lo x)
;                  (<? hi-rel x hi)
;                  (not (equal (interval-decider lo-rel lo hi-rel hi t k) '?)))
;             (equal (signate sign (< x k))  ; sign/(k . :lessp-x-k)
;                    (signate sign
;                             (interval-decider lo-rel lo hi-rel hi t k)))))
;
;   (thm
;    (implies (and (rationalp k)
;                  (not (equal x nil))  x can't be an infinity
;                  (<? lo-rel lo x)
;                  (<? hi-rel x hi)
;                  (not (equal (interval-decider lo-rel lo hi-rel hi nil k) '?)))
;             (equal (signate sign (< k x)) ; sign/(k . :lessp-k-x)
;                    (signate (not sign)
;                             (interval-decider lo-rel lo hi-rel hi nil k)))))
;
;   ; Note that to use interval-decider on sign/(k . :lessp-x-k) you call it
;   ; with rel = t and then just interpret the non-? answers via sign as usual.
;   ; To use it on sign/(k . :lessp-k-x) you call it with rel = nil and then
;   ; interpret the non-? answers with via (not sign).

(defun reduce-sign/recog (tau sign recog ens wrld)

; Tau is a tau.  Sign is t or nil indicating positive or negative.  Recog is
; the concrete representation of a tau recognizer.  See tau-like-term for a
; table.  Note that the discriminator, (cdr recog), is always defined and is
; one of (i) a tau recognizer symbol, (ii) nil, (iii) :lessp-x-k, or (iv)
; :lessp-k-x.

; We return T, NIL, or ? to indicate what (tau x) directly implies about
; (sign/recog x).  If tau implies sign/recog is true, we return T.  If it
; implies it is nil, we return nil.  Otherwise, we return ?.

; By ``direct'' we mean this function only uses the immediate information in
; tau, plus evaluation on constants.  For example, if tau were {NATP EVENP}
; then it could determine that NATP is true, that nil/NATP is false, and that
; =17 is false, for example.  But it doesn't determine a value for INTEGERP
; because the fact that NATP implies INTEGERP should be (will be) already
; incorporated into any tau that contains NATP.

; This function is used in tau-term and tau-assume: If while walking through
; IFs we encounter (sign/recog x) in a test, which way should we go?

  (let ((discriminator (cdr recog)))
    (cond
     ((eq tau *tau-contradiction*) t)
     ((eq discriminator nil)
      (cond
       (sign ; sign/recog is a positive equality on the evg in recog.
        (cond
         ((access tau tau :pos-evg)
          (equal recog (access tau tau :pos-evg)))
         ((member-neg-evgs recog (access tau tau :neg-evgs))
          nil)
         ((not (eval-tau-interval (access tau tau :interval) (car recog)))
          nil)

; There is nothing else we can try.  We are trying to determine whether X = evg
; is true or false under tau and all that is left to investigate is whether one
; of the tau-pairs decides this question.  But we assume that no pred implies
; the truth of an equality-with-constant.  Note that if (q x) --> x='evg then
; either (q x) is always false or else (q x) <--> x='evg.  This trivial
; observation is confirmed by:

; (encapsulate ((q (x) t))
;              (local (defun q (x) (equal x '23)))
;              (defthm q-constraint (and (booleanp (q x))
;                                        (implies (q x) (equal x '23)))
;                :rule-classes nil))
; (thm (or (equal (q x) nil)
;          (equal (q x) (equal x '23)))
;      :hints (("Goal" :use q-constraint)))

; The case for (not (q x)) --> x='evg is symmetric.  But we assume no pred is
; defined to be constantly t or nil and none hides an equality-with-constant.

; On the other hand, it is possible for the preds to imply the negation of an
; equality-with-constant.  For example, if pos-pairs contains integerp
; and evg is 'ABC, then (integerp x) --> X/='ABC is true and hence X='ABC is
; false.

         ((exists-bad-valp nil (access tau tau :pos-pairs) recog ens wrld)
          nil)
         ((exists-bad-valp t (access tau tau :neg-pairs) recog ens wrld)
          nil)
         (t '?)))
       (t ; sign/recog is a negative equality on the evg in recog
        (cond ((access tau tau :pos-evg)
               (not (equal recog (access tau tau :pos-evg))))
              ((member-neg-evgs recog (access tau tau :neg-evgs))
               t)
              ((not (eval-tau-interval (access tau tau :interval) (car recog)))
               t)
              ((exists-bad-valp nil (access tau tau :pos-pairs) recog ens wrld)
               t)
              ((exists-bad-valp t (access tau tau :neg-pairs) recog ens wrld)
               t)
              (t '?)))))
     ((eq discriminator :lessp-x-k)
      (let ((k (car recog))
            (interval (access tau tau :interval)))
        (cond
         ((null interval)
          (cond ((tau-pair-member *tau-acl2-numberp-pair* (access tau tau :neg-pairs))
                 (signate sign (< 0 k)))
                (t '?)))
         (t (let ((ans (interval-decider
                        (access tau-interval interval :lo-rel)
                        (access tau-interval interval :lo)
                        (access tau-interval interval :hi-rel)
                        (access tau-interval interval :hi)
                        t
                        k)))
              (signate sign ans))))))
     ((eq discriminator :lessp-k-x)
      (let ((k (car recog))
            (interval (access tau tau :interval)))
        (cond
         ((null interval)
          (cond ((tau-pair-member *tau-acl2-numberp-pair* (access tau tau :neg-pairs))
                 (signate sign (< k 0)))
                (t '?)))
         (t (let ((ans (interval-decider
                        (access tau-interval interval :lo-rel)
                        (access tau-interval interval :lo)
                        (access tau-interval interval :hi-rel)
                        (access tau-interval interval :hi)
                        nil
                        k)))
              (signate (not sign) ans))))))
     (t ; recog is a tau-pair and discriminator is the predicate symbol
      (cond
       ((access tau tau :pos-evg) ; tau is X='evg
        (let ((val (ev-fncall-w-tau-recog discriminator (access tau tau :pos-evg)
                                          ens
                                          wrld)))
          (cond
           ((eq val :UNEVALABLE)
            (cond
             ((tau-pair-member recog
                               (if sign
                                   (access tau tau :pos-pairs)
                                   (access tau tau :neg-pairs)))
              t)
             ((tau-pair-member recog
                               (if sign
                                   (access tau tau :neg-pairs)
                                   (access tau tau :pos-pairs)))
              nil)
             (t '?)))
           (sign (if val t nil))
           (t (if val nil t)))))
       ((tau-pair-member recog
                         (if sign
                             (access tau tau :pos-pairs)
                             (access tau tau :neg-pairs)))
        t)
       ((tau-pair-member recog
                         (if sign
                             (access tau tau :neg-pairs)
                             (access tau tau :pos-pairs)))
        nil)
       (t '?))))))

; Before running these tests, add the defuns and macros for ptrans and mktau
; from the section ``On Tau Debugging Features'' below.  They can't be defined
; at this point because they use some functions not yet defined.
;
;   (logic)
;
;   (defun predicted (expr val)
;     (if (equal expr val) 'Passed 'Failed!))
;
;   ; Every element of the following list should be PASSED.
;
;   (list
;   (let ((tau (mktau t (natp x) (evenp x) (not (equal x 20)))))
;     (predicted (reduce-sign/recog tau t *tau-natp-pair*
;                                   (ens state) (w state))
;                t))
;
;   (let ((tau (mktau t (natp x) (evenp x) (not (equal x 20)))))
;     (predicted (reduce-sign/recog tau nil *tau-natp-pair*
;                                   (ens state) (w state))
;                nil))
;
;   (let ((tau (mktau t (natp x) (evenp x) (not (equal x 20)))))
;     (predicted (reduce-sign/recog tau t '(16 . nil)
;                                   (ens state) (w state))
;                '?))
;
;   (let ((tau (mktau t (natp x) (evenp x) (not (equal x 20)))))
;     (predicted (reduce-sign/recog tau t '(15 . nil)
;                                   (ens state) (w state))
;                NIL))
;
;   (let ((tau (mktau t (natp x) (evenp x) (not (equal x 20)))))
;     (predicted (reduce-sign/recog tau nil '(15 . nil)
;                                   (ens state) (w state))
;                T))
;   (let ((tau (mktau t (natp x) (evenp x) (not (equal x 20)))))
;     (predicted (reduce-sign/recog tau nil '(20 . nil)
;                                   (ens state) (w state))
;                T))
;   (let ((tau (mktau t (natp x) (evenp x) (not (equal x 20)))))
;     (predicted (reduce-sign/recog tau t '(20 . nil)
;                                   (ens state) (w state))
;                NIL))
;   (let ((tau (mktau t (natp x) (evenp x))))
;     (predicted (reduce-sign/recog tau t '(17 . nil)
;                                   (ens state) (w state))
;                NIL))
;
;   ; If (10 <= x <= 20) then (x =17) may or may not be true.
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(17 . nil)
;                                   (ens state) (w state))
;                '?))
;
;   ; If (10 <= x <= 20) then (x/=17) may or may not be true
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau nil '(17 . nil)
;                                   (ens state) (w state))
;                '?))
;
;   ; If (10 <= x <= 20) then (x =21) is false
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(21 . nil)
;                                   (ens state) (w state))
;                nil))
;
;   ; If (10 <= x <= 20) then (x/=21) is true
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau nil '(21 . nil)
;                                   (ens state) (w state))
;                t))
;
;   ; If (10 <= x <= 20) then (x ='ABC) is false
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(abc . nil)
;                                   (ens state) (w state))
;                nil))
;
;   ; If (10 <= x <= 20) then (x/='ABC) is true
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau nil '(abc . nil)
;                                   (ens state) (w state))
;                t))
;
;   ; If (10 <= x <= 20) then (x =20) may or may not be true
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(20 . nil)
;                                   (ens state) (w state))
;                '?))
;
;   ; If (10 <= x <= 20) then (x/=20) may or may not be true
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau nil '(20 . nil)
;                                   (ens state) (w state))
;                '?))
;
;   ; If (10 <= x < 20) then (x =20) is false
;   (let ((tau (mktau t (<= 10 x) (< x 20))))
;     (predicted (reduce-sign/recog tau t '(20 . nil)
;                                   (ens state) (w state))
;                nil))
;
;   ; If (10 <= x < 20) then (x/=20) is true
;   (let ((tau (mktau t (<= 10 x) (< x 20))))
;     (predicted (reduce-sign/recog tau nil '(20 . nil)
;                                   (ens state) (w state))
;                t))
;
;   ; If (10 <= x <= 20) then (x =9) is false
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(9 . nil)
;                                   (ens state) (w state))
;                nil))
;
;   ; If (10 <= x <= 20) then (x < 9) is false
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(9 . :lessp-x-k)
;                                   (ens state) (w state))
;                nil))
;
;   ; If (10 <= x <= 20) then (x < 15) is unknown
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(15 . :lessp-x-k)
;                                   (ens state) (w state))
;                '?))
;
;   ; If (10 <= x <= 20) then (x < 24) is true
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(24 . :lessp-x-k)
;                                   (ens state) (w state))
;                t))
;
;   ; If (10 <= x <= 20) then (x < 21) is true
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(21 . :lessp-x-k)
;                                   (ens state) (w state))
;                t))
;
;   ; If (10 <= x <= 20) then (x < 20) is unknown
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(20 . :lessp-x-k)
;                                   (ens state) (w state))
;                '?))
;
;   ; If (10 <= x <= 20) then (x < 10) is false
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(10 . :lessp-x-k)
;                                   (ens state) (w state))
;                nil))
;
;   ; If (10 <= x <= 20) then (5 < x) is true
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(5 . :lessp-k-x)
;                                   (ens state) (w state))
;                t))
;
;   ; If (10 <= x <= 20) then (25 < x) is false
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(25 . :lessp-k-x)
;                                   (ens state) (w state))
;                nil))
;
;   ; If (10 <= x <= 20) then (15 < x) is unknown
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau t '(15 . :lessp-k-x)
;                                   (ens state) (w state))
;                '?))
;
;   ; If (10 <= x <= 20) then (5 <= x) is true
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau nil '(5 . :lessp-x-k)
;                                   (ens state) (w state))
;                t))
;
;   ; If (10 <= x <= 20) then (25 <= x) is false
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau nil '(25 . :lessp-x-k)
;                                   (ens state) (w state))
;                nil))
;
;   ; If (10 <= x <= 20) then (15 <= x) is unknown
;   (let ((tau (mktau t (<= 10 x) (<= x 20))))
;     (predicted (reduce-sign/recog tau nil '(15 . :lessp-x-k)
;                                   (ens state) (w state))
;                '?))
;
;   ; If (10 <= x <= infinity) then (x <= 15) is unknown
;   (let ((tau (mktau t (<= 10 x))))
;     (predicted (reduce-sign/recog tau nil '(15 . :lessp-k-x)
;                                   (ens state) (w state))
;                '?))
;
;   ; If (10 <= x <= infinity) then (x <= 15) is true
;   (let ((tau (mktau t (<= x 10))))
;     (predicted (reduce-sign/recog tau nil '(15 . :lessp-k-x)
;                                   (ens state) (w state))
;                t))
;
;   ; If (10 <= x <= infinity) then (x = 'abc) is false
;   (let ((tau (mktau t (<= 10 x))))
;     (predicted (reduce-sign/recog tau t '(abc . nil)
;                                   (ens state) (w state))
;                nil))
;
;   ; If (10 <= x <= infinity) then (x = 20) is unknown
;   (let ((tau (mktau t (<= 10 x))))
;     (predicted (reduce-sign/recog tau t '(20 . nil)
;                                   (ens state) (w state))
;                '?))
;
;   ; If (10 <= x <= infinity) then (acl2-numberp x) is true
;   (let ((tau (mktau t (<= 10 x))))
;     (predicted (reduce-sign/recog tau t *tau-acl2-numberp-pair*
;                                   (ens state) (w state))
;                t))
;   ; If (not (acl2-numberp x)), then (< x 30) is true.
;   (let ((tau (mktau t (not (acl2-numberp x)))))
;     (predicted (reduce-sign/recog tau t '(30 . :lessp-x-k)
;                                   (ens state) (w state))
;                t))
;
;   ; If (not (acl2-numberp x)), then (< x -30) is false
;   (let ((tau (mktau t (not (acl2-numberp x)))))
;     (predicted (reduce-sign/recog tau t '(-30 . :lessp-x-k)
;                                   (ens state) (w state))
;                nil))
;
;   ; If (< x -30) then (acl2-numberp x) is true
;   (let ((tau (mktau t (< x -30))))
;     (predicted (reduce-sign/recog tau t *tau-acl2-numberp-pair*
;                                   (ens state) (w state))
;                t))
;
;   ; If 0 <= x <= 0 and (acl2-numberp x) then x is 0
;   (let ((tau (mktau t (<= 0 x) (<= x 0) (acl2-numberp x))))
;     (predicted (reduce-sign/recog tau t '(0 . nil)
;                                   (ens state) (w state))
;                t))
;
;   ; Here I repeat the above for other permutations of the order in which the
;   ; hyps are processed:
;
;   (let ((tau (mktau t (<= x 0) (<= 0 x) (acl2-numberp x))))
;     (predicted (reduce-sign/recog tau t '(0 . nil)
;                                   (ens state) (w state))
;                t))
;
;   (let ((tau (mktau t (<= x 0) (acl2-numberp x) (<= 0 x))))
;     (predicted (reduce-sign/recog tau t '(0 . nil)
;                                   (ens state) (w state))
;                t))
;
;   (let ((tau (mktau t  (<= 0 x) (acl2-numberp x) (<= x 0))))
;     (predicted (reduce-sign/recog tau t '(0 . nil)
;                                   (ens state) (w state))
;                t))
;
;   (let ((tau (mktau t (acl2-numberp x) (<= x 0) (<= 0 x))))
;     (predicted (reduce-sign/recog tau t '(0 . nil)
;                                   (ens state) (w state))
;                t))
;
;   (let ((tau (mktau t (acl2-numberp x) (<= 0 x) (<= x 0))))
;     (predicted (reduce-sign/recog tau t '(0 . nil)
;                                   (ens state) (w state))
;                t))
;
;   ; IF (0 <= x <= 0) then (x=0) is unknown.
;   (let ((tau (mktau t (<= 0 x) (<= x 0))))
;     (predicted (reduce-sign/recog tau t '(0 . nil)
;                                   (ens state) (w state))
;                '?))
;
;   ; IF (1/2 <= x <= 1/2) then (x=1/2) is t
;   (let ((tau (mktau t (<= 1/2 x) (<= x 1/2))))
;     (predicted (reduce-sign/recog tau t '(1/2 . nil)
;                                   (ens state) (w state))
;                t))
;
;   ; IF (#c(1 2) <= x <= #c(1 2)) then (x=#c(1 2)) is '? -- because we can't handle
;   ;  complex bounds!
;   (let ((tau (mktau t (<= #c(1 2) x) (<= x #c(1 2)))))
;     (predicted (reduce-sign/recog tau t '(#c(1 2) . nil)
;                                   (ens state) (w state))
;                '?))
;   )

; -----------------------------------------------------------------

; On Firing Signature Rules

; Consider a term like (fn a).  Suppose tau1 is the tau for a.  Suppose the
; signature for fn is fn: tau2 --> tau3.  To fire this rule we will need to
; determine whether S[tau1] \subset S[tau2].

; To think about this, ignore the concrete structure of a tau, including the
; signs of things; think a tau as a set of recognizers (!).  The meaning of a
; recognizer set is the conjunction of its elements -- so bigger sets of
; recognizers comprehend smaller sets of objects.  In particular, S[tau1]
; \subset S[tau2] if tau2 \subset tau1.  (Of course, it is possible for S[tau1]
; to be a subset of S[tau2] under other conditions, but this one is
; sufficient.)

; Let tau1 = {p1 ... pn} and tau2 = {q1 ... qk}.  We want to know whether
; S[tau1] \subset S[tau2], which is equivalent to M[tau1] --> M[tau2], which is

; (implies (and (p1 x) ... (pn x)) (and (q1 x) ... (qk x))).

; Note that one way to prove this conjecture would be to show that each qi is
; some pj.

; Because of the concrete structure of tau we need only compare them
; component-wise.  For example, if q is among the :neg-pairs of one we need to
; search for it only among the :neg-pairs of the other.  This holds for the
; four components pos-evg, neg-evgs, pos-pairs, and neg-pairs.  We have to
; handle intervals specially.

(defun every-neg-evg-in-tau-p1
  (neg-evgs1 neg-evgs2 pos-pairs2 neg-pairs2 interval2 ens wrld)

; Neither neg-evgs1 nor neg-evgs2 contains (NIL).  This function is just an
; efficient way of checking that every element of neg-evgs1 is (a) in
; neg-evgs2, or (b) subsumed by the tau-interval interval2, (c) subsumed by an
; element of pos-pairs2, or (d) subsumed by an element of neg-pairs2.  For
; example, if an element of neg-evgs1 is /=7 then it might be subsumed in
; another tau by with an explicit /=7 in it, or by an interval not including 7,
; or by some sign/recognizer in the other tau being false on it.  We could do
; this by mapping over neg-evgs1 and just check member-neg-evgs and the other
; checks each element.  But that method is quadratic in the lengths of the two
; neg-evgs, since member-neg-evgs would repeatedly search neg-evgs2.  Instead,
; we exploit the fact that both neg-evgs are ``almost'' lexordered ascending.

  (cond
   ((endp neg-evgs1) t)
   ((endp neg-evgs2)
    (and (or (not (eval-tau-interval interval2 (car (car neg-evgs1))))
             (exists-bad-valp nil pos-pairs2 (car neg-evgs1) ens wrld)
             (exists-bad-valp t   neg-pairs2 (car neg-evgs1) ens wrld))
         (every-neg-evg-in-tau-p1 (cdr neg-evgs1)
                                  nil
                                  pos-pairs2 neg-pairs2
                                  interval2 ens wrld)))
   ((lexorder (car (car neg-evgs1)) (car (car neg-evgs2)))
    (cond ((equal (car (car neg-evgs1)) (car (car neg-evgs2)))
           (every-neg-evg-in-tau-p1 (cdr neg-evgs1)
                                    (cdr neg-evgs2)
                                    pos-pairs2 neg-pairs2
                                    interval2 ens wrld))
          (t (and (or (not (eval-tau-interval interval2 (car (car neg-evgs1))))
                      (exists-bad-valp nil pos-pairs2
                                       (car neg-evgs1) ens wrld)
                      (exists-bad-valp t neg-pairs2
                                       (car neg-evgs1) ens wrld))
                  (every-neg-evg-in-tau-p1 (cdr neg-evgs1)
                                           neg-evgs2
                                           pos-pairs2 neg-pairs2
                                           interval2 ens wrld)))))
   (t (every-neg-evg-in-tau-p1 neg-evgs1
                               (cdr neg-evgs2)
                               pos-pairs2 neg-pairs2
                               interval2 ens wrld))))

(defun every-neg-evg-in-tau-p (neg-evgs tau ens wrld)

; Think of M[neg-evgs] as a conjunction of negative equalities with constants.
; We wish to know whether M[tau] --> M[neg-evgs].  We answer t if so, and nil if
; we do not know.

  (cond
   ((endp neg-evgs) t)
   ((access tau tau :pos-evg)

; If tau says x is some specific evg, then M[neg-evgs] is true as long as evg
; isn't among the neg-evgs.  I.e., x=5 --> (x/=7 & x/='ABC).  One might wonder
; whether we need to look into the :pos or :neg-pairs of tau, which might
; contain some unevalable predicates, e.g., that P is also true of 5.  But that
; cannot help us establish an inequality.

    (not (member-neg-evgs (access tau tau :pos-evg) neg-evgs)))

; The following is essentially every-neg-evg-in-tau-p1 unrolled for the (NIL)
; case possibly at the front of the two relevant neg-evgs.

   (t (let ((neg-evgs1 neg-evgs)
            (neg-evgs2 (access tau tau :neg-evgs))
            (pos-pairs2 (access tau tau :pos-pairs))
            (neg-pairs2 (access tau tau :neg-pairs))
            (interval2 (access tau tau :interval)))
        (cond
         ((eq (car (car neg-evgs1)) nil)
          (cond
           ((endp neg-evgs2)
            (and (or (not (eval-tau-interval interval2 nil))
                     (exists-bad-valp nil pos-pairs2
                                      *nil-singleton-evg-list*
                                      ens wrld)
                     (exists-bad-valp t neg-pairs2
                                      *nil-singleton-evg-list*
                                      ens wrld))
                 (every-neg-evg-in-tau-p1 (cdr neg-evgs1)
                                          nil
                                          pos-pairs2 neg-pairs2
                                          interval2 ens wrld)))
           ((eq (car (car neg-evgs2)) nil)
            (every-neg-evg-in-tau-p1 (cdr neg-evgs1)
                                     (cdr neg-evgs2)
                                     pos-pairs2 neg-pairs2
                                     interval2 ens wrld))
           (t (and (or (not (eval-tau-interval interval2 nil))
                       (exists-bad-valp nil pos-pairs2
                                        *nil-singleton-evg-list*
                                        ens wrld)
                       (exists-bad-valp t neg-pairs2
                                        *nil-singleton-evg-list*
                                        ens wrld))
                   (every-neg-evg-in-tau-p1 (cdr neg-evgs1)
                                            neg-evgs2
                                            pos-pairs2 neg-pairs2
                                            interval2 ens wrld)))))
         ((and (consp neg-evgs2)
               (eq (car (car neg-evgs2)) nil))
          (every-neg-evg-in-tau-p1 neg-evgs1
                                   (cdr neg-evgs2)
                                   pos-pairs2 neg-pairs2
                                   interval2 ens wrld))
         (t (every-neg-evg-in-tau-p1 neg-evgs1
                                     neg-evgs2
                                     pos-pairs2 neg-pairs2
                                     interval2 ens wrld)))))))

; We will return to the issue of firing signature rules after we've dealt with
; intervals.

; On Comparing Bounds

; We now define four functions for comparing bounds:
; lower-bound-<=
; lower-bound->
; upper-bound->=
; upper-bound-<

; All four take the specification of two bounds, a-rel a and b-rel b, which are
; each upper or lower bounds of two intervals over the same domain and decide
; whether the first bound is in the given relation to the second one.  For
; example, (upper-bound-< a-rel a b-rel b) decides whether the upper bound
; a-rel a is strictly below the upper bound b-rel b.

; These functions are complicated by the fact that they compare bounds not
; merely numbers (we must take into account the strengths of the
; inequalities), that the domains are the same, that for INTEGERP domain the
; bounds are in our normal form (rel = nil and extent is an integer or NIL), and
; that a and/or b may be NIL, indicating the appropriate infinity.
; Nevertheless, the functions are very simple.  We first define all four and
; then we exhibit a big comment specifying one of them and proving it correct.

; The two lower-bound functions are actually the negations of each other, as
; are the two upper-bound functions.

; (lower-bound-<= a-rel a b-rel b) <--> (not (lower-bound-> a-rel a b-rel b))

; (upper-bound->= a-rel a b-rel b) <--> (not (upper-bound-< a-rel a b-rel b))

; a is NIL or a rational and b is NIL or a rational.

; Why define all four if two of them are the negations of the other two?  The
; answer is the same as to the question, ``why define ``>='' if it is just the
; negation of ``<''?  Answer: it clarifies thinking if one doesn't introduce
; negations.  We sometimes need ``>='' and sometimes need ``<''.

; Specification of Bound Comparisons

; We specify all four in terms of (implicit) intervals A and B because all
; our applications involve intervals and we find it clearer to think about
; relations on intervals than on bounds.  The (upper or lower, as appropriate)
; bounds on A are given by a-rel and a, and those on B are b-rel and b.  For
; brevity in our comments, we use LA(x) to mean that x satisfies the lower
; bound on A.  For example, if A's lower bound is given by arel=t and a = 5,
; then LA(x) means (< 5 x).  Similar conventions are made for LB(x), UA(x), and
; UB(x).

; We assume that the domains of both A and B are the same.  We furthermore
; assume that if the domain is INTEGERP, then a-rel and b-rel are both nil (<=)
; and that a and b are integers if they are non-nil.

; We describe the meaning of each of our four functions in three ways: an
; informal English sentence, a formula, and a picture.  In the pictures we use
; parentheses to mark the bounds of each interval.  But we do not mean to
; suggest that the intervals are open at that end.

; LOWER-BOUND-<=

;  Informally: lower bound of A is weakly below the lower bound of B, by which
;  we mean that anything satisfying the lower bound of B will also satisfy that
;  for A

;  Formally:   [all x : LB(x) ---> LA(x)]

;  Picture:    A   B
;              (---(---...


; UPPER-BOUND->=

;  Informally: upper bound of A is weakly above the upper bound of B by which
;  we mean that anything satisfying the upper bound of B will also satisfy the
;  upper bound of A

;  Formally:  [all x : UB(x) ---> UA(x)]

;  Picture:         B   A
;             ...---)---)

; LOWER-BOUND->

;  Informally: lower bound of A is strictly above the lower bound of B, by
;  which we mean not only that anything satisfying the lower bound of A
;  satisfies the lower bound of B but also that there is an element of the
;  domain which satisfies the lower bound of B but not that of A

;  Formally:  [all x : LA(x) ---> LB(x)] & [exists z : dom(z) & LB(z) & -LA(z)]

;  Picture:    B   A
;              (-z-(---...

;
; UPPER-BOUND-<

;  Informally: Upper bound of A is strictly below the upper bound of B, by
;  which we mean not only that anything satisfying the upper bound of A
;  satisfies the upper bound of B but also that there is a z in the domain that
;  satisfies the upper bound of B but not that of A

;  Formally:  [all x : UA(x) ---> UB(x)] & [exists z : dom(z) & UB(z) & -UA(z)]

;  Picture:         A   B
;             ...---)-z-)

(defun lower-bound-<= (a-rel a b-rel b)

; See Specification of Bound Comparisons, above.

  (declare (xargs :guard (and (booleanp a-rel)
                              (or (null a) (rationalp a))
                              (booleanp b-rel)
                              (or (null b) (rationalp b)))))
  (if (null a)
      t
      (if (null b)
          nil
          (if (and a-rel (not b-rel))
              (< a b)
              (<= a b)))))

; Note that if (and a-rel (not b-rel)) then the ``a'' bound is ``a < ...'' and
; the ``b'' bound is ``b <= ...''.  Thus, if a=b, the b interval extends further.

(defun upper-bound->= (a-rel a b-rel b)

; See Specification of Bound Comparisons, above.

  (declare (xargs :guard (and (booleanp a-rel)
                              (or (null a) (rationalp a))
                              (booleanp b-rel)
                              (or (null b) (rationalp b)))))
  (if (null a)
      t
      (if (null b)
          nil
          (if (and a-rel (not b-rel))
              (< b a)
              (<= b a)))))

(defun lower-bound-> (a-rel a b-rel b)

; See Specification of Bound Comparisons, above.

  (declare (xargs :guard (and (booleanp a-rel)
                              (or (null a) (rationalp a))
                              (booleanp b-rel)
                              (or (null b) (rationalp b)))))
  (if (null a)
      nil
      (if (null b)
          t
          (if (and a-rel (not b-rel))
              (>= a b)
              (> a b)))))

(defun upper-bound-< (a-rel a b-rel b)

; See Specification of Bound Comparisons, above.

  (declare (xargs :guard (and (booleanp a-rel)
                              (or (null a) (rationalp a))
                              (booleanp b-rel)
                              (or (null b) (rationalp b)))))
  (if (null a)
      nil
      (if (null b)
          t
          (if (and a-rel (not b-rel))
              (<= a b)
              (< a b)))))

; On the Proof of Correctness of upper-bound-<

; (verify-termination lower-bound-<=)
; (verify-termination lower-bound->)
; (verify-termination upper-bound->=)
; (verify-termination upper-bound-<)

; (include-book "arithmetic-5/top" :dir :system)

; (defun <? (rel x y)
;   (if (or (null x) (null y))
;       t
;       (if rel
;           (< x y)
;           (<= x y))))

; (tau-status :system nil)

; First we prove the noted equivalences between the four relations:

; (thm (implies (and (or (rationalp a) (null a))
;                    (or (rationalp b) (null b)))
;               (iff (lower-bound-<= a-rel a b-rel b)
;                    (not (lower-bound-> a-rel a b-rel b)))))

; (thm (implies (and (or (rationalp a) (null a))
;                    (or (rationalp b) (null b)))
;               (iff (upper-bound->= a-rel a b-rel b)
;                    (not (upper-bound-< a-rel a b-rel b)))))

; We will prove that upper-bound-< is correct wrt our specification.

; Theorem:  Correctness of upper-bound-<.

; Suppose you have two intervals, A and B, over the same domain and suppose
; that a-rel a and b-rel b specify the bounds, respectively. Either or both of
; a and b may be NIL, denoting positive infinities.  If either is non-NIL, it
; is a rational.  Furthermore, if the domain in question is INTEGERP, both
; a-rel and b-rel are nil (<=) and a and b are integers unless they are NIL
; (infinity).

; We are to return T iff

; The picture:
;  Picture:         A   B
;             ...---)-z-)

; [i]                        & [ii]
; [all x : UA(x) ---> UB(x)] & [exists z : dom(z) & UB(z) & -UA(z)]

; Proof Sketch: Step 1.  We first deal with the two infinities.  Step 2.  Then
; we show, for rational a and b, that if we return T, conjuncts [i] and [ii]
; above both hold.  Step 3.  Then we show, for rational a and b, that if we
; return nil, at least one of the conjuncts fails to hold.

; Step 1: Suppose a is positive infinity.  Then upper-bound-< returns nil.  To
; see that this is correct, case split on whether b is positive infinity.  Then
; there can be no z such that UB(z) but such that -UA(z), so [ii] fails.  If b
; is finite, then [i] fails: let x be b+1 and observe that UA(x) holds but
; UB(x) requires (<? b-rel (+ b 1) b) which is nil.

; If on the other hand, a is finite but b is infinite, upper-bound-< returns t.
; But observe that UB(x) holds for everything, so [i] is true.  And [ii] is
; shown true by letting z be a+1, something in the domain such that UB(z) holds
; but (<? a-rel (+ a 1) a) does not.

; So henceforth we may assume both a and b are finite rationals.

; Step 2.  Next we show that if the code returns T then [i] and [ii] both hold.
; Consider the cases.  If (and a-rel (not b-rel)) is true and we return T, then
; (<= a b).  Thus, [i] is shown by:

; (thm (implies (and (rationalp a)
;                    (rationalp b)
;                    (and a-rel (not b-rel))
;                    (<= a b))
;               (implies (<? a-rel x a) (<? b-rel x b))))

; Furthermore, given (and a-rel (not b-rel)) we know the domain is not just
; INTEGERP, so it includes all the rationals.  Our existential witness for z is
; the rational given in the let binding below:

; (thm (let ((z (+ a (/ (- b a) 2))))
;        (implies (and (rationalp a)
;                      (rationalp b)
;                      (and a-rel (not b-rel))
;                      (<= a b))
;                 (and (rationalp z)
;                      (<? b-rel z b)
;                      (not (<? a-rel z a))))))

; On the other hand, if (and a-rel (not b-rel)) is false, and we return T
; then (< a b).  We can prove [i] with

; (thm (implies (and (rationalp a)
;                    (rationalp b)
;                    (not (and a-rel (not b-rel)))
;                    (< a b))
;               (implies (<? a-rel x a) (<? b-rel x b))))

; But to prove [ii] we must consider whether the domain is INTEGERP or not.  If
; it is INTEGERP, we know a-rel = b-rel = nil and that a and b are integers.
; Thus, [ii] becomes the formula below, with our existential witness being the
; integer shown:

; (thm (let ((z (+ a 1)))
;        (implies (and (integerp a)
;                      (integerp b)
;                      (null a-rel)
;                      (null b-rel)
;                      (< a b))
;                 (and (integerp z)
;                      (<? b-rel z b)
;                      (not (<? a-rel z a))))))

; If on the other hand, the domain is not INTEGERP, then it includes all the
; rationals and we can prove:

; (thm (let ((z (+ a (/ (- b a) 2))))
;        (implies (and (rationalp a)
;                      (rationalp b)
;                      (not (and a-rel (not b-rel)))
;                      (< a b))
;                 (and (rationalp z)
;                      (<? b-rel z b)
;                      (not (<? a-rel z a))))))

; That finishes Step 2.

; Step 3.  Finally, we show that if we return NIL, one of [i] or [ii] fails.
; Again, we consider whether (and a-rel (not b-rel)) holds.  If it does and we
; return NIL then we know (NOT (<= a b)) and we observe that [i] fails for the
; case where x = (+ b (/ (- a b) 2)):

; (thm (implies (and (rationalp a)
;                    (rationalp b)
;                    (and a-rel (not b-rel))
;                    (not (<= a b)))
;               (let ((x (+ b (/ (- a b) 2))))
;                 (not (implies (<? a-rel x a) (<? b-rel x b))))))

; On the other hand, if (and a-rel (not b-rel)) is nil and we return NIL, we
; know (NOT (< a b)) and we can prove that [ii] is false by proving that EVERY
; z satisfying (<? b-rel z b) satisfies (<? a-rel z a):

;  (thm (implies (and (rationalp a)
;                     (rationalp b)
;                     (not (and a-rel (not b-rel)))
;                     (not (< a b)))
;                (implies (<? b-rel z b) (<? a-rel z b))))

; Q.E.D.

(defun tau-subintervalp (interval1 interval2)

; We determine whether every element of interval1 is an element of interval2.

  (let ((dom1 (access tau-interval interval1 :domain))
        (dom2 (access tau-interval interval2 :domain)))
; We first determine whether the domain of interval1 is a subset of the domain of interval2.
    (and (case dom1
           (INTEGERP
            ; Every dom2 includes all the integers.
            t)
           (RATIONALP
            ; Every dom2 except INTEGERP includes all the rationals.
            (not (eq dom2 'INTEGERP)))
           (ACL2-NUMBERP
            ; Only ACL2-NUMBERP or NIL includes all the ACL2 numbers.
            (or (eq dom2 'acl2-numberp) (null dom2)))
           (otherwise
            ; Only NIL includes all the ACL2 objects.
            (null dom2)))

; Below we check that interval2 extends weakly further left and right (lower
; and upper) than interval1.  However, the predicates lower-bound-<= and
; upper-bound->= have onerous preconditions: the two bounds provided must
; govern two intervals, A and B, with the same domain and if that domain is
; INTEGERP, then both relations are weak (<=) and both extents are integers.
; Now in the case below, the two intervals may or may not have the same domain.
; If they do, all is well.  But if they don't, then we can imagine that the
; more restrictive domain, which necessarily must be dom1, is replaced by the
; less restrictive one, dom2, which necessarily won't be INTEGERP and which
; must include the integers and, more generally, the rationals.  So if that
; imaginary extension of interval1 to dom2 is in interval2, so is interval1.

         (lower-bound-<= (access tau-interval interval2 :lo-rel)
                         (access tau-interval interval2 :lo)
                         (access tau-interval interval1 :lo-rel)
                         (access tau-interval interval1 :lo))
         (upper-bound->= (access tau-interval interval2 :hi-rel)
                         (access tau-interval interval2 :hi)
                         (access tau-interval interval1 :hi-rel)
                         (access tau-interval interval1 :hi)))))

(defun tau-implies (tau1 tau2 ens wrld)
; If we return non-nil, then  M[tau1] --> M[tau2].
  (cond
   ((eq tau1 *tau-contradiction*) t)
   ((eq tau2 *tau-contradiction*) nil)
   ((access tau tau2 :pos-evg)
    (if (access tau tau1 :pos-evg)
        (equal (access tau tau2 :pos-evg)
               (access tau tau1 :pos-evg))
        nil))
   ((access tau tau1 :pos-evg)

; M[Tau1] is an equality to some evg and M[tau2] is a conjunction of negative
; equalities, positive and negative recognizers, and an interval.  M[tau1]
; makes M[tau2] true if every element of tau2 is satisfied by the evg in
; question.

    (and (not (member-neg-evgs (access tau tau1 :pos-evg)
                               (access tau tau2 :neg-evgs)))
         (all-eval-valp t (access tau tau2 :pos-pairs)
                        (access tau tau1 :pos-evg)
                        ens wrld)
         (all-eval-valp nil (access tau tau2 :neg-pairs)
                        (access tau tau1 :pos-evg)
                        ens wrld)
         (eval-tau-interval (access tau tau2 :interval)
                            (car (access tau tau1 :pos-evg)))))
   (t

; Every neg evg in tau2 must be implied by tau1, every symbolic recognizer of
; tau2 must be among the same-signed recognizers of tau1 (tau1 is stronger and
; so may contain additional conjuncts), and the interval of tau1 must be
; contained in that of tau2.  Note that we're generally interested in ``is each
; component of tau2 smaller than the corresponding component of tau1'' but in
; the case of the intervals the roles are reversed and tau1's must be the
; smaller interval.

      (and (every-neg-evg-in-tau-p (access tau tau2 :neg-evgs)
                                   tau1 ens wrld)
           (tau-pairs-subsetp (access tau tau2 :pos-pairs)
                              (access tau tau1 :pos-pairs))
           (tau-pairs-subsetp (access tau tau2 :neg-pairs)
                              (access tau tau1 :neg-pairs))
           (tau-subintervalp (access tau tau1 :interval)
                             (access tau tau2 :interval))))))

(defun empty-tau-intervalp (lo-rel lo hi-rel hi)

; We return t if the arguments describe an empty interval.

  (cond ((null lo) nil)
        ((null hi) nil)
        ((or lo-rel hi-rel) (<= hi lo))
        (t (< hi lo))))

(defun singleton-tau-intervalp (lo-rel lo hi-rel hi)

; A well-formed interval contains exactly one element iff both relations are <=
; and the two endpoints are non-nil and equal.

; Caution:  The name ``singleton interval'' is misleading!  If the domain is
; NIL and the ``singleton interval'' is 0 <= ... <= 0, then it contains ALL
; non-numbers!

  (and lo
       (equal lo hi)
       (not lo-rel)
       (not hi-rel)))

; We are in the process of defining add-to-tau1, which adds a signed recognizer to a
; tau.  When we add an equal-to-constant, we might need to add an identity interval.

(defun make-identity-interval (interval evg)

; We make the interval containing exactly evg, if such an interval can be
; expressed.  We reuse interval if it already says what we want.

  (let ((dom (cond ((integerp evg) 'integerp)
                   ((rationalp evg) 'rationalp)

; If we allowed bounds to be complex-rationals then we could handle the acl2-numberp
; case for an identity interval, e.g., x = #c(3 5) <--> #c(3 5) <= x <= #c(3 5).
; But to make things simpler we've prohibited complex bounds so we cannot
; express an equality-with-complex-rational as an interval.

                  ;((acl2-numberp evg) 'acl2-numberp)

                   (t nil))))
    (cond ((null dom) nil)
          ((and (eq dom (access tau-interval interval :domain))
                (eql evg (access tau-interval interval :lo))
                (eq nil (access tau-interval interval :lo-rel))
                (eql evg (access tau-interval interval :hi))
                (eq nil (access tau-interval interval :hi-rel)))
; We use EQL above instead of = because the interval bounds might be NIL.
           interval)
          (t (make tau-interval
                   :domain dom
                   :lo evg
                   :lo-rel nil
                   :hi-rel nil
                   :hi evg)))))

(defun identity-intervalp (int)

; If this function returns t then int is an identity interval and (access
; tau-interval int :lo) is the object identified.  To be an identity, an
; interval must have the domain INTEGERP or RATIONALP, the relations must be
; weak (<=), and lo and hi must be non-nil and equal.

  (and (or (eq (access tau-interval int :domain) 'INTEGERP)
           (eq (access tau-interval int :domain) 'RATIONALP))
       (null (access tau-interval int :lo-rel))
       (null (access tau-interval int :hi-rel))
       (access tau-interval int :lo)
       (eql (access tau-interval int :lo)
            (access tau-interval int :hi))))

; Suppose we wish to add to a tau the fact that x is not some particular evg.
; Then we add the negatively signed version of the recognizer (evg . nil).  We
; will first check that the evg in question is not already ruled out by the
; other components.  Then we add it to the neg-evgs.  But what about the
; interval?

; The most general rule is this:

; If the domain is ACL2-NUMBERP and the excepted evg is equal to one of the
; endpoints (meaning the evg is the bound and the corresponding rel is weak),
; we can strengthen the rel.  For example, the interval over the ACL2-NUMBERPs
; such that 5 <= x < 10, when conjoined with x /= 5, produces 5 < x < 10.  (Of
; course, INTEGERP intervals are a special case discussed below.)  The
; following theorem justifies this for ACL2-NUMBERP intervals and the lo bound
; and the symmetric theorem holds for the hi bound.  Since it holds for
; ACL2-NUMBERP, it holds for RATIONALP and INTEGERP intervals too.  However, it
; does not hold for unrestricted intervals.  For example, if the domain is
; unrestricted and 0 <= x < 10, and we add x/=0, we cannot change the lower
; bound to 0 < x < 10, since x='NAN is in the original interval and satisfies
; x/=0 but is not in the changed interval.

; For the defun of <? above:

; (thm (implies (and (rationalp lo)
;                    (rationalp hi)
;                    (<? (or lo-rel hi-rel) lo hi) ; non-empty
;                    (not lo-rel)
;                    )
;               (iff (and (acl2-numberp x)
;                         (<? lo-rel lo x)
;                         (<? hi-rel x hi)
;                         (not (equal x lo)))
;                    (and (acl2-numberp x)
;                         (<? t lo x)
;                         (<? hi-rel x hi)))))

; There is an easy-to-fall-for fallacy near here: ``If the domain is
; unrestricted but the tau excludes 0, then the domain ACL2-NUMBERP may be
; added.''  This is based on the valid observation that both (< 0 x) and (< x
; 0) imply (acl2-numberp x).  So if we knew lo < x < hi but x /= 0 then don't
; we know (< 0 x) or (< x 0)?  No!  For example, lo might be -5 and hi might be
; +5.  Now let x be 'NAN.  Then -5 < 'NAN < +5 and 'NAN /= 0, but (acl2-numberp
; 'NAN) is false.

; The special case for INTEGERP intervals should be handled specially.

; If the domain of interval is INTEGERP and the evg is one of the endpoints, we
; can shrink the interval to exclude it.  Recall that the relations for
; INTEGERP intervals are always weak.  Adding x/=5 to the interval over the
; integers 5 <= x <= 10 will turn the interval into 6 <= x <= 10.  (One can see
; this as first 5 < x <= 10 and then shrinking to 6 <= x <= 10, but we'll do it
; in one step.)

; But the INTEGERP case should go on to confirm that the NEW endpoint is not
; excluded.

; For example, the tau:
;   ((integerp x) & 0 <= x <= 10 & x/=2 & x/=1)
; can't be represented any other way.  But if we add x/=0, we
; should produce:
;   ((integerp x) & 3 <= x <= 10)
; and not the more verbose:
;   ((integerp x) & 1 <= x <= 10 & x/=2 & x/=1)
; That is, when shrinking an INTEGERP interval in a tau, continue
; shrinking past all excluded endpoints.

(defun delete-consecutive-integers-upward (k neg-evgs)

; K is a new lower bound on an INTEGERP interval associated with a tau
; containing neg-evgs.  We assume neg-evgs is a duplicate-free ordered
; ascending list of singleton integer evgs.  We remove from neg-evgs every
; element less than k and then all consecutively larger elements of neg-evgs
; until finding the first integer not in neg-evgs.  We return (mv k'
; neg-evgs'), where k' is the first consecutive integer at or above k not in
; neg-evgs and the neg-evgs' is the tail of neg-evgs containing all elements
; larger than k'.  Note that k' may be k and neg-evgs' may be neg-evgs.

; For example, suppose a tau has the INTEGERP interval 0 <= ... <= 20 and the
; neg-evgs ((3) (6) (7) (10) (17)), meaning the elements described are those
; integers between 5 and 20 other than 3, 6, 7, 10, and 17.  Suppose that we
; learn that the new lower bound of the interval is 6 (or, equivalently for an
; INTEGERP interval, that the lower bound is 5 < ...).  Then in fact the new
; lower bound is 8 and the new neg-evgs are just ((10) (17)).  3 is below the
; new lower bound, so it is deleted.  6 is the new lower bound, but it is
; excluded, so we move to 7 and find the same thing, finally identifying 8.
; This function would return 8 and ((10) (17)) on this example.

  (cond ((endp neg-evgs) (mv k nil))
        ((< (car (car neg-evgs)) k)
         (delete-consecutive-integers-upward k (cdr neg-evgs)))
        ((eql (car (car neg-evgs)) k)
         (delete-consecutive-integers-upward (+ k 1) (cdr neg-evgs)))
        (t (mv k neg-evgs))))


; (delete-consecutive-integers-upward 6 '((3) (6) (7) (10) (17)))
; = (mv 8 '((10) (17)))

(defun delete-consecutive-integers-downward (k neg-evgs)

; K is a new upper bound on an INTEGERP interval associated with a tau
; containing neg-evgs.  We assume neg-evgs is a duplicate-free ordered
; ascending list of singleton integer evgs.  We remove from neg-evgs every
; element that is greater than k and every consecutively smaller integer until
; finding one not in neg-evgs.  We return (mv k' neg-evgs') where k' is the
; first consecutive integer at or below k no in neg-evgs and neg-evgs' is the
; initial sublist of neg-evgs containing all elements smaller than k'.  It is
; possible that k' is just k and neg-evgs' is neg-evgs.

; For example, suppose a tau has the INTEGERP interval 0 <= ... <= 20 and the
; neg-evgs ((3) (4) (7) (8) (17)) and the new upper bound, k, is to be 8.  Then
; in fact we get a new upper bound k' of 6 and the neg-evgs' of ((3) (4))
; because the 17 is thrown out as being above the new bound, the stated new
; bound of 8 is excluded, as is the next lower one, 7, and we're left with the
; bound of 6.

  (cond ((endp neg-evgs) (mv k neg-evgs))
        ((> (car (car neg-evgs)) k)
         (mv k nil))
        ((eql (car (car neg-evgs)) k)
         (mv (- k 1) nil))
        (t (mv-let
            (k1 neg-evgs1)
            (delete-consecutive-integers-downward k (cdr neg-evgs))
            (cond ((eql (car (car neg-evgs)) k1)
                   (mv (- k1 1) neg-evgs1))
                  (t (mv k1 (cons (car neg-evgs) neg-evgs1))))))))

; (delete-consecutive-integers-downward 8 '((3)(4)(7)(8)(17)))
; = (mv 6 '((3) (4)))

(defun collect-<?-x-k (rel k neg-evgs)

; Provided the assumptions below are satisfied, we collect those x in neg-evgs
; such that (<? rel x k).  More precisely, rel denotes < (rel = t) or <= (rel =
; nil), and k is a rational; together they define the upper bound on an
; interval.  Neg-evgs is a list of singletons.  We assume it is lexordered,
; ascending, and duplicate-free.  It may or may not contain non-numbers
; (depending on the domain of the interval, which we don't know here because we
; don't see that much advantage in knowing.)  We collect those elements of
; neg-evgs that satisfy rel and k, i.e., those that fit within the upper bound
; of the interval.  Note that if k were nil, representing positive infinity,
; and the inequalities above were extended in the obvious way, this function
; would just return neg-evgs, so there is no reason to support k = nil; just
; don't use the function in that case.

; Important Note: lexorder does NOT extend <=.  For example, (< 'abc 3) but it
; is not the case that (lexorder 'abc 3), because lexorder puts all numbers
; first.  Worse, lexorder does not even extend <= on the acl2-numbers!  For
; example, (< #c(5 -1) 5) but not (lexorder #c(5 -1) 5), because lexorder puts
; rationals before complex-rationals.  Thus, it is difficult to exploit the
; lexordering of neg-evgs here until we encounter the first non-acl2-numberp,
; at which point we know that all remaining elements are coerced to 0 by <.

  (cond ((endp neg-evgs) nil)
        ((acl2-numberp (car (car neg-evgs)))
         (if (<?-number-v-rational rel (car (car neg-evgs)) k)
             (cons (car neg-evgs)
                   (collect-<?-x-k rel k (cdr neg-evgs)))
             (collect-<?-x-k rel k (cdr neg-evgs))))
; All remaining elements of neg-evgs are non-numeric.  They are all coerced to
; 0 by rel.  So we keep them all if 0 is acceptable and throw them all away
; otherwise:
        ((if rel (< 0 k) (<= 0 k))
         neg-evgs)
        (t nil)))

(defun collect-<?-k-x (rel k neg-evgs)

; Provided the assumptions described in collect-<?-x-k are satisfied, we
; collect those x in neg-evgs such that (<? rel k x).  See collect-<?-x-k for
; details.

  (cond ((endp neg-evgs) nil)
        ((acl2-numberp (car (car neg-evgs)))
         (if (<?-rational-v-number rel k (car (car neg-evgs)))
             (cons (car neg-evgs)
                   (collect-<?-k-x rel k (cdr neg-evgs)))
             (collect-<?-k-x rel k (cdr neg-evgs))))
; All remaining elements of neg-evgs are non-numeric.  They are all coerced to
; 0 by rel.  So we keep them all if 0 is acceptable and throw them all away
; otherwise:
        ((if rel (< k 0) (<= k 0))
         neg-evgs)
        (t nil)))

(defun adjust-upper-bound-with-neg-evgs (domain rel k neg-evgs)

; Suppose we have an interval over domain with upper bound specified by rel and k
; (i.e., the upper bound on x is given by (< x k) or (<= x k), depending on
; whether rel is t or nil.  If the domain is INTEGERP we additionally assume
; that rel is nil (<=) and k is an integer.  If k is among the neg-evgs, we
; adjust the bound downward (possibly strengthening the relation) and eliminate
; unnecessary elements of neg-evgs, i.e., all those above the bound.  We return
; (mv rel' k' neg-evgs').

  (if (eq domain 'INTEGERP)
      (mv-let (k1 neg-evgs1)
        (delete-consecutive-integers-downward k neg-evgs)
        (mv nil k1 neg-evgs1))

; If we're over a more general domain, we strengthen the relation if it is weak
; and the specified endpoint is excluded by neg-evgs, and then we return the
; specified bound k, the new relation, and everything satisfying that relation
; in neg-evgs.  Notice that the specified endpoint is never to be found in the
; final neg-evgs: if the relation was strong, the specified endpoint need not
; be in neg-evgs because it is ruled out by the relation; if the relation was
; weak but the specified endpoint was already ruled out, then the relation is
; strengthened and the new relation (rather than the new neg-evgs) rules out
; the endpoint; if the endpoint was not in neg-evgs in the first place, then of
; course it is still not in it.

; There used to be a bug here!  The bug had us strengthen x <= 0 to x < 0 when
; 0 was in the neg-evgs.  I.e., if the interval was the non-positives but 0 is
; explicitly excluded, then the interval became the negatives.  But this is
; only correct for intervals over numbers!  If the domain is unrestricted then
; x <= 0 and x/=0 doesn't imply x < 0 because x might be a non-number.  Since
; the neg-evgs can't possibly include all non-numbers, we can't strengthen the
; relation.  In fact, if the domain is unrestricted and we've got x <= 0 then
; we can't do anything whether 0 is excluded or not so we return without
; changing anything. The bug fix was to add the next three lines (the if test
; and mv return).

    (if (and (null domain)
             (eql k 0))
        (mv rel k neg-evgs)
      (let ((new-rel (or rel (if (assoc-equal k neg-evgs) t nil))))
        (mv new-rel
            k
            (collect-<?-x-k new-rel k neg-evgs))))))

(defun adjust-lower-bound-with-neg-evgs (domain rel k neg-evgs)

; Suppose we have an interval over domain with lower bound specified by rel and
; k (i.e., the lower bound on x is given by (< k x) or (<= k x), depending on
; whether rel is t or nil.  If the domain is INTEGERP we additionally assume
; that rel is nil (<=) and k is an integer.  If k is among the neg-evgs, we
; adjust the bound upward (possibly strengthening the relation) and eliminate
; unnecessary elements of neg-evgs, i.e., all those below the bound.  We return
; (mv rel' k' neg-evgs').

  (if (eq domain 'INTEGERP)
      (mv-let (k1 neg-evgs1)
        (delete-consecutive-integers-upward k neg-evgs)
        (mv nil k1 neg-evgs1))

; If we're over a more general domain, we strengthen the relation if it is weak
; and the specified endpoint is excluded by neg-evgs, and then we return the
; specified bound k, the new relation, and everything satisfying that relation
; in neg-evgs.  Notice that the specified endpoint is never to be found in the
; final neg-evgs: if the relation was strong, the specified endpoint need not
; be in neg-evgs because it is ruled out by the relation; if the relation was
; weak but the specified endpoint was already ruled out, then the relation is
; strengthened and the new relation (rather than the new neg-evgs) rules out
; the endpoint; if the endpoint was not in neg-evgs in the first place, then of
; course it is still not in it.

; There used to be a bug here.  See the corresponding comment in
; adjust-upper-bound-with-neg-evgs.

    (if (and (null domain)
             (eql k 0))
        (mv rel k neg-evgs)
      (let ((new-rel (or rel (if (assoc-equal k neg-evgs) t nil))))
        (mv new-rel
            k
            (collect-<?-k-x new-rel k neg-evgs))))))

(defun squeeze-k (upper-boundp rel k)

; K is either NIL (the appropriate infinity) or a rational.  Consider some
; interval with INTEGERP domain bounded (above or below as per upper-boundp) by
; rel and k.  If k is non-nil, we squeeze the given bound as per:

; Table A:
; upper-boundp  rel   meaning    squeezed        k'
; t             t     (<  x k)   (<= x k')       (- (ceiling k 1) 1)
; t             nil   (<= x k)   (<= x k')       (floor k 1)
; nil           t     (<  k x)   (<= k' x)       (+ (floor k 1) 1)
; nil           nil   (<= k x)   (<= k' x)       (ceiling k 1)

; Programming Note: When k is a non-integer rational,
; (- (ceiling k 1) 1) = (floor k 1), and thus
; (+ (floor k 1) 1)   = (ceiling k 1)
; so the table would be:

; Table B: Non-Integer Rational k:
; upper-boundp  rel   meaning    squeezed        k'
; t             t     (<  x k)   (<= x k')       (floor k 1)
; t             nil   (<= x k)   (<= x k')       (floor k 1)
; nil           t     (<  k x)   (<= k' x)       (ceiling k
; nil           nil   (<= k x)   (<= k' x)       (ceiling k 1)

; But when k is an integer, the table is:

; Table C: Integer k:
; upper-boundp  rel   meaning    squeezed        k'
; t             t     (<  x k)   (<= x k')       (- k 1)
; t             nil   (<= x k)   (<= x k')       k
; nil           t     (<  k x)   (<= k' x)       (+ k 1)
; nil           nil   (<= k x)   (<= k' x)       k

; We actually code Tables B and C and test which to use with (integerp k),
; because we believe it is faster than Table A because whenever k is an integer
; we avoid calls of floor or ceiling.

  (declare (xargs :guard (and (booleanp upper-boundp)
                              (booleanp rel)
                              (or (null k) (rationalp k)))))
  (if k
      (if (integerp k)
          (if rel
              (if upper-boundp (- k 1) (+ k 1))
              k)
          (if upper-boundp
              (floor k 1)
              (ceiling k 1)))
      nil))

(defun set-tau-pos-evg (tau recog ens wrld)

; Recog must be (evg . nil), the recognizer for an equality with evg.  We
; change tau to recog, filtering :pos-pairs and :neg-pairs appropriately (and
; possibly returning *tau-contradiction*), and setting the :interval to the
; identity interval (or nil if evg is not rational).

  (let ((evg (car recog))
        (new-pos-pairs
         (bad-val-or-unknowns nil
                              (access tau tau :pos-pairs)
                              recog ens wrld)))
    (cond
     ((eq new-pos-pairs t)
; There is a pos-pair that evals to nil on this new evg.
      *tau-contradiction*)
     (t
      (let ((new-neg-pairs
             (bad-val-or-unknowns t
                                  (access tau tau :neg-pairs)
                                  recog ens wrld)))
        (cond
         ((eq new-neg-pairs t)
; There is a neg-pair that evals to t on this new evg.
          *tau-contradiction*)
         (t (make tau
                  :pos-evg recog
                  :neg-evgs nil
                  :pos-pairs new-pos-pairs
                  :neg-pairs new-neg-pairs
                  :interval (make-identity-interval
                             (access tau tau :interval)
                             evg)))))))))

(defun positive-lower-boundp (lo-rel lo)
  (and lo
       (if lo-rel
           (<= 0 lo)
           (<  0 lo))))

(defun nonnegative-lower-boundp (lo)
  (and lo (<= 0 lo)))

(defun negative-upper-boundp (hi-rel hi)
  (and hi
       (if hi-rel
           (<= hi 0)
           (<  hi 0))))

(defun tighten-bound (tau domain upper-boundp rel k ens wrld)

; This function tightens the domain and/or an upper or lower bound on the
; interval in a tau, adjusting the tau's :neg-evgs appropriately.  However, as
; a precondition, we insist that the new domain is either (a) implied by some
; recognizer already in the :pos-pairs or :neg-pairs of tau or (b) implied by
; the existing bounds on the interval, or (c) implied by the new upper-boundp,
; rel, and k.  We return the new tau.  K may be nil (denoting the appropriate
; infinity) or a rational.  It will be adjusted to an integer if the relevant
; domain is INTEGERP.

; Note that using k=nil or domain=nil is a way of saying ``no change of this
; parameter'' since they place no new restrictions and we'll use the existing
; parameter.

; Programming note: We don't explicitly filter :neg-evgs for the new domain, we
; just filter it for the new upper-bound, rel, and k.  This is correct because
; of our precondition.  If condition (a) holds, we know that every element of
; tau's :neg-evgs already satisfies the existing (stronger) recognizer and
; hence must satisfy domain.  (For example, perhaps we are adding domain =
; INTEGERP in response to add-to-tau1 t/POSP.  In adding t/POSP, we will filter
; out of :neg-evgs all those elements that are not POSP, and so we will have
; filtered out all non-INTEGERPs before calling tighten-bound to add INTEGERP
; to the interval.)  Alternatively, if condition (b) holds, the pre-existing
; bounds on the interval imply the domain and hence :neg-evgs are already
; appropriately filtered.  Finally, if condition (c) holds, there may be
; illegal elements of :neg-evgs but they will be removed here when we enforce
; upper-boundp, rel, k.  (For example, we may be adding domain = ACL2-NUMBERP
; in response to adding lower-bound 0 <.  In this case, we'll remove from
; :neg-evgs all non-numeric elements because they fail 0 <.)

; Reminder: This is not all that must be done when adjusting a bound in a tau!
; For example, if the interval is bounded above 0, we could add ACL2-NUMBERP
; (or perhaps POSP), but we don't make ``non-local'' inferences here.  That is
; saved for add-to-tau.

  (if (eq tau *tau-contradiction*)
      *tau-contradiction*
      (let* ((interval (access tau tau :interval))
             (neg-evgs (access tau tau :neg-evgs))
             (domain0 (access tau-interval interval :domain))
             (lo0 (access tau-interval interval :lo))
             (lo-rel0 (access tau-interval interval :lo-rel))
             (hi0 (access tau-interval interval :hi))
             (hi-rel0 (access tau-interval interval :hi-rel)))
; Select the more restrictive of the two domains.
        (let ((domain
               (cond ((eq domain nil) domain0)
                     ((or (eq domain0 'integerp)
                          (eq  domain 'integerp))
                      'integerp)
                     ((or (eq domain0 'rationalp)
                          (eq  domain 'rationalp))
                      'rationalp)
                     ((or domain0
                          domain)
                      'acl2-numberp)
                     (t nil))))

; If the more restrictive domain is INTEGERP and is different from the initial
; domain, squeeze both the initial lower and upper bounds of the interval.

          (mv-let
           (lo-rel lo hi-rel hi)
           (if (and (not (eq domain domain0))
                    (eq domain 'INTEGERP))
               (mv nil (squeeze-k nil lo-rel0 lo0) nil (squeeze-k t hi-rel0 hi0))
               (mv lo-rel0 lo0 hi-rel0 hi0))

; If the more restrictive domain is INTEGERP, squeeze the new bound.

           (mv-let
            (rel k)
            (if (eq domain 'INTEGERP)
                (mv nil (squeeze-k upper-boundp rel k))
                (mv rel k))

; Now we set lo, lo-rel, hi-rel, and hi to the most restrictive bounds we have.

            (mv-let
             (lo-rel lo)
             (if (and (not upper-boundp)
                      (lower-bound-> rel k lo-rel lo))
                 (mv rel k)
                 (mv lo-rel lo))
             (mv-let
              (hi-rel hi)
              (if (and upper-boundp
                       (upper-bound-< rel k hi-rel hi))
                  (mv rel k)
                  (mv hi-rel hi))

; Note that we might have changed either or both of the bounds.  For example,
; if we changed the domain to INTEGERP, we might have moved both bounds.  In
; addition, one of the bounds might have been pulled toward the other by
; upper-boundp, rel, and k.  But regardless of how we obtained them, the best
; bounds we have, based entirely on the domain, the bounds of the original
; interval, and the rel,k adjustment, are now lo-rel, lo, hi-rel, and hi.
; However, it is possible that we can do further adjustment via the neg-evgs,
; and we might have to adjust either or both of the bounds.

              (mv-let
               (new-lo-rel new-lo new-neg-evgs)
               (if (and (equal lo-rel lo-rel0)
                        (equal lo lo0))
                   (mv lo-rel lo neg-evgs)
                   (adjust-lower-bound-with-neg-evgs domain lo-rel lo neg-evgs))
               (mv-let
                (new-hi-rel new-hi new-neg-evgs)
                (if (and (equal hi-rel hi-rel0)
                         (equal hi hi0))
                    (mv hi-rel hi new-neg-evgs)
                    (adjust-upper-bound-with-neg-evgs domain hi-rel hi
                                                      new-neg-evgs))

; So now the new, best bounds are given by new-lo-rel, new-lo, new-hi-rel, and
; new-hi, and the neg-evgs by new-neg-evgs.  Next we bind new-domain to
; ACL2-NUMBERP if it was completely unrestricted and the interval does not
; include 0; otherwise it is domain, as before.

                (let ((new-domain
                       (if (and (null domain)
                                (or (positive-lower-boundp new-lo-rel new-lo)
                                    (negative-upper-boundp new-hi-rel new-hi)))
                           'acl2-numberp
                           domain)))

; Even if the domain has been changed to ACL2-NUMBERP, we need not further
; filter the :neg-evgs: they will have been filtered by the adjustments to
; accommodate the interval bounds which are away from 0.  It remains only to
; see if this interval is empty or a singleton.

                  (cond
                   ((and (eq  new-domain domain0)
                         (eq  new-lo-rel lo-rel0)
                         (eql new-lo lo0)
                         (eq  new-hi-rel hi-rel0)
                         (eql new-hi hi0))
                    tau)
                   ((empty-tau-intervalp new-lo-rel new-lo new-hi-rel new-hi)
                    *tau-contradiction*)
                   ((and new-domain
                         (singleton-tau-intervalp new-lo-rel new-lo new-hi-rel new-hi))

; If the interval is a singleton, e.g., k <= x <= k, then if the domain is
; non-nil, we know the tau is the identity.  (In this case we will also know
; that the domain is either INTEGERP or RATIONALP as per the type of k.)  The
; only case in which a singleton interval does not convert to a constant is if
; k=0 and the new-domain is nil.  Furthermore, if k/=0, then domain is never
; nil.

                    (set-tau-pos-evg tau (cons new-hi nil) ens wrld))
                   (t (change tau tau
                              :interval (make tau-interval
                                              :domain new-domain
                                              :lo new-lo
                                              :lo-rel new-lo-rel
                                              :hi-rel new-hi-rel
                                              :hi new-hi)
                              :neg-evgs new-neg-evgs))))))))))))))

(defun add-to-tau1 (sign recog tau ens wrld)

; Recog is a tau-pair, singleton evg list, or one of the inequality
; recognizers, (k . :lessp-x-k) or (k . :lessp-k-x).  Tau is a tau object or
; *tau-contradiction* or *contradictory-tau* and is not obviously contradictory
; unless it is one of those two special values.  We add sign/recog to tau --
; WITHOUT any propagation of implicants.  We clean up the new tau as much as
; possible, e.g., delete pos- or neg-pairs evaluable under pos-evg changes and
; delete negative evgs made redundant by pos- or neg-pairs, etc.  We return the
; modified tau or *tau-contradiction*.

; Note that adding NATP, for example, to a tau will set the domain of the tau's
; interval to INTEGERP and the lower bound to at least 0.  But INTEGERP is not
; added to the tau's :pos-pairs.  The domain of a tau's interval is implied by
; the recognizers in the tau but is not necessarily among them.  We use the
; domain to do things like adjust the bounds, not to decide whether a given
; recognizer is true.  To add sign/recog AND ITS IMPLICANTS to tau, use
; add-to-tau, not add-to-tau1.

; The motivation of our cleaning up is to keep tau small.  Our basic
; assumption is that we'll query taus more often than we build them, and
; smaller taus generally allow faster queries since queries involve search.

  (let ((discriminator (cdr recog)))
    (cond
     ((or (eq tau *tau-contradiction*)
          (equal tau *contradictory-tau*))
      *tau-contradiction*)
     ((eq discriminator nil)
      (cond
       (sign

; We are adding a positive evg equality to tau.

        (cond
         ((access tau tau :pos-evg)
          (if (equal recog (access tau tau :pos-evg))
              tau
            *tau-contradiction*))
         ((member-neg-evgs recog (access tau tau :neg-evgs))
          *tau-contradiction*)
         ((not (eval-tau-interval (access tau tau :interval) (car recog)))
; The evg falls outside the tau interval.
          *tau-contradiction*)
         (t (let ((new-pos-pairs
                   (bad-val-or-unknowns nil
                                        (access tau tau :pos-pairs)
                                        recog ens wrld)))
              (cond
               ((eq new-pos-pairs t)

; There is a pos-pair that evals to nil on this new evg.
                *tau-contradiction*)
               (t
                (let ((new-neg-pairs
                       (bad-val-or-unknowns t
                                            (access tau tau :neg-pairs)
                                            recog ens wrld)))
                  (cond
                   ((eq new-neg-pairs t)
; There is a neg-pair that evals to t on this new evg.
                    *tau-contradiction*)
                   (t (make tau
                            :pos-evg recog
                            :neg-evgs nil
                            :pos-pairs new-pos-pairs
                            :neg-pairs new-neg-pairs
                            :interval (make-identity-interval
                                       (access tau tau :interval)
                                       (car recog))))))))))))
       (t

; We are adding an evg to :neg-evgs.

        (cond
         ((access tau tau :pos-evg)
          (if (equal recog (access tau tau :pos-evg))
              *tau-contradiction*
            tau))
         ((member-neg-evgs recog (access tau tau :neg-evgs))
          tau)
         ((not (eval-tau-interval (access tau tau :interval) (car recog)))
          tau)
         ((exists-bad-valp nil (access tau tau :pos-pairs) recog ens wrld)
          tau)
         ((exists-bad-valp t (access tau tau :neg-pairs) recog ens wrld)
          tau)
         (t

; Recog, which is a negative equality, /= evg, where evg is (car recog), is not
; ruled out by any existing component of tau.  Thus, we will add it to tau and
; clean up.  Adding a negative equality cannot change either :pos-pairs or
; :neg-pairs (without violating our rule that no recognizer is just a hidden
; equality-to-constant).  Nor will it change the (empty) :pos-evg field.  But
; it might change the interval!  For example, if we have an INTEGERP interval
; with 0 <= x <= 10 and we know x/=8 and x/=9, and we add x/=10, we get the
; interval 0 <= x <= 7 and must eliminate the now redundant elements of
; neg-evgs.  If the interval is merely RATIONALP and we exclude 10, we'd
; strengthen the upper bound to x < 10.  Note that the neg-evgs and the
; interval must be consistent initially, so neg-evgs contains no element
; outside the interval.  So the only way a new neg-evg can affect the interval
; is if the evg is ``equal to one of the endpoints,'' which means that the evg
; is a rational, one of the bounding relations is weak (<=), and the evg is
; equal to the bound used in that weak relation.

          (let ((interval (access tau tau :interval)))
            (cond

; There used to be a bug here!  In general a weak relation on an interval can
; be strengthened if a new negative equality excludes the existing bound.
; E.g., if we know x <= 1/2 and we get the new fact x /= 1/2 we can change it
; to x < 1/2.  (We have already dealt with strengthening integral bounds).
; But this strengthening is only legal if either (a) the domain of the
; interval is numeric or (b) the new constant is non-0.  E.g., if we have an
; rational interval bounded above with <= 0 and we get /= 0, we can change the
; bound to < 0, or if we have an unrestricted domain bounded above by <= k and
; we get /= k, we can change the bound to < k only if k/=0.  In particular, if
; the domain is unrestricted and the interval is bounded above by <= 0 and we
; get /=0 it is unsound to change the bound to < 0, since all non-numbers are
; in the interval and are <= 0 but not < 0.  The fix to this bug was to add
; the disjunction below as a new conjunct to the test.

             ((and (or (access tau-interval interval :domain) ; numeric
                       (not (eql (car recog) 0)))
                   interval
                   (rationalp (car recog)))
              (cond
               ((and (null (access tau-interval interval :lo-rel))
                     (eql (access tau-interval interval :lo) (car recog)))

; The excluded evg is equal to the weak lower bound so we strengthen the
; lower bound from evg <= ... to evg < ..., with the appropriate tightening.

                (tighten-bound tau
                               nil         ; new domain = ``no change''
                               nil         ; upper-boundp
                               t           ; = new :lo-rel (strengthened)
                               (car recog) ; = new :lo
                               ens wrld))
               ((and (null (access tau-interval interval :hi-rel))
                     (eql (access tau-interval interval :hi) (car recog)))
; The excluded evg is equal to the weak upper bound.
                (tighten-bound tau
                               nil         ; new domain = ``no change''
                               t           ; upper-boundp
                               t           ; = new :hi-rel (strengthened)
                               (car recog) ; = new :hi
                               ens wrld))
; In the two t cases below, we're just adding the /= evg to the :neg-evgs either
; because the excluded evg is neither the lower nor the upper bound of the interval
; or because there is no interval.
               (t (change tau tau
                          :neg-evgs
                          (insert-neg-evgs recog
                                           (access tau tau :neg-evgs))))))
             (t (change tau tau
                        :neg-evgs
                        (insert-neg-evgs recog
                                         (access tau tau :neg-evgs)))))))))))

; So that completes the code for adding a signed equality-to-constant (positive
; or negative).

     ((or (eq discriminator :lessp-x-k)
          (eq discriminator :lessp-k-x))

      (let ((k (car recog)))

; Shift from recognizer notation to interval notation
; recog        sign        lower          upper
; :lessp-x-k    t                         (< x k)
; :lessp-x-k    nil         (<= k x)
; :lessp-k-x    t           (<  k x)
; :lessp-k-x    nil                       (<= x k)

        (mv-let
          (upper-boundp rel)
          (if (eq discriminator :lessp-x-k)
              (if sign
                  (mv t   t)
                (mv nil nil))
            (if sign
                (mv nil t)
              (mv t   nil)))
          (tighten-bound tau
                         nil ; new domain = ``no change''
                         upper-boundp
                         rel
                         k
                         ens wrld))))

; That completes the code for adding a signed :lessp-x-k or :lessp-k-x.

     (t ; recog is (i . fn)
      (cond
       ((access tau tau :pos-evg)

; tau is a :pos-evg.  Then if sign/fn is true on the evg, we don't change
; anything; if sign/fn is false on the evg, we return *tau-contradiction*; else
; sign/fn is unevaluable and we add fn to :pos-pairs or :neg-pairs.

        (let ((val (ev-fncall-w-tau-recog discriminator
                                          (access tau tau :pos-evg)
                                          ens
                                          wrld)))
          (cond
           ((eq val :UNEVALABLE)

; Recog is unevaluable on evg.  We add it to the appropriate pairs list.  But
; we must make sure it is not already there and not in the other list!

            (cond
             (sign
              (let ((new-pos-pairs
                     (insert-tau-pair recog
                                      (access tau tau :pos-pairs))))
                (cond
                 ((eq new-pos-pairs t)
                  tau)
                 ((tau-pair-member recog
                                   (access tau tau :neg-pairs))
                  *tau-contradiction*)
                 (t
                  (change tau tau :pos-pairs new-pos-pairs)))))
             (t
              (let ((new-neg-pairs
                     (insert-tau-pair recog
                                      (access tau tau :neg-pairs))))
                (cond
                 ((eq new-neg-pairs t)
                  tau)
                 ((tau-pair-member recog
                                   (access tau tau :pos-pairs))
                  *tau-contradiction*)
                 (t
                  (change tau tau :neg-pairs new-neg-pairs)))))))
           ((eq val sign) ; same as (iff val sign), as val and sign are Boolean
; recog evals as expected; don't bother to store
            tau)
           (t
; recog evals to false; signal contradiction
            *tau-contradiction*))))
       ((tau-pair-member recog
                         (if sign
                             (access tau tau :pos-pairs)
                           (access tau tau :neg-pairs)))

; If recog is already in the appropriate pairs list, there is nothing to

        tau)
       ((tau-pair-member recog
                         (if sign
                             (access tau tau :neg-pairs)
                           (access tau tau :pos-pairs)))

; If recog is in the other pairs list, we have a contradiction.

        *tau-contradiction*)

; Note that we do not have to check the :interval of tau to see whether it
; approves the addition of sign/recog since the only part of the interval that
; matters directly is the domain and that is reflected in the :pos-pairs of
; tau.  Of course, it may be that sign/recog implies, via the database, a
; contradictory relationship with tau's :interval, but we must start to add it
; to find out.

       (t

; Otherwise, it is ok to add recog to the appropriate pairs list.  But it may
; make it possible to delete some of the :neg-evgs in tau.  Suppose one of
; those :neg-evgs asserts that X is not 'ABC.  Suppose that recog asserts that
; X is INTEGERP.  Then we don't need that particular element of :neg-evgs any
; more.  Note that we might worry that the assertion of sign/recog makes one of
; our :neg-evgs false, but that would violate the Non-Constant Non-Equality
; Premise.

        (mv-let
          (changedp new-neg-evgs)
          (delete-bad-vals1 (access tau tau :neg-evgs)
                            sign
                            recog
                            ens
                            wrld)
          (let ((tau1
                 (if sign
                     (if changedp
                         (change tau tau
                                 :neg-evgs new-neg-evgs
                                 :pos-pairs (insert-tau-pair
                                             recog
                                             (access tau tau :pos-pairs)))
                       (change tau tau
                               :pos-pairs (insert-tau-pair
                                           recog
                                           (access tau tau :pos-pairs))))
                   (if changedp
                       (change tau tau
                               :neg-evgs new-neg-evgs
                               :neg-pairs (insert-tau-pair
                                           recog
                                           (access tau tau :neg-pairs)))
                     (change tau tau
                             :neg-pairs (insert-tau-pair
                                         recog
                                         (access tau tau :neg-pairs)))))))

; Tau1 now has the recog in :pos-pairs or :neg-pairs as per sign and the
; :neg-evgs of tau1 is consistent with the new recog (and all the old ones).
; But the interval is not yet updated.  We will call tighten-bound on tau1 to
; do that.  Note in every call of tighten-bound below, the new domain is either
; (a) implied by the recognizers in tau1 or (b) implied by the existing bounds,
; or (c) implied by the new bounds.

; Here is how the interval can change.  Note that we are only concerned with
; the interval here, not with adding additional recognizers to :pos-pairs or
; :neg-pairs.  See the Note 1 below.

; sign/recog        effect (do both if two things are listed)
; t/NATP            INTEGERP domain and 0 <= ...
; t/POSP            INTEGERP domain and 0 <  ...
; t/INTEGERP        INTEGERP domain
; t/RATIONALP       RATIONALP domain
; t/ACL2-NUMBERP    ACL2-NUMBERP domain
; t/MINUSP          ACL2-NUMBERP domain and ... < 0
; nil/MINUSP        0 <= ...

; Certain negatively signed recogs can cause changes if we know certain
; conditions:

; sign/recog        condition          effect
; nil/NATP          INTEGERP domain    ... < 0
; nil/POSP          INTEGERP domain    ... <= 0
; nil/ACL2-NUMBERP  NIL domain         0 <= ... <= 0
; nil/ACL2-NUMBERP  non-NIL domain     contradiction [See Note 2 below]
; nil/RATIONALP     RATIONALP domain   contradiction [See Note 2 below]
; nil/RATIONALP     INTEGERP domain    contradiction [See Note 2 below]
; nil/INTEGERP      INTEGERP domain    contradiction [See Note 2 below]

; Note 1:  The effects listed above merely concern the interval.  If add-to-tau1
; added additional recognizers to :pos-pairs or :neg-pairs it would violate
; its contract not to add implicants.  For example, it may be tempting to
; include:

; nil/NATP          0 <= ...           nil/INTEGERP
; nil/POSP          0 < ...            nil/INTEGERP

; E.g., if we've added the negation of NATP or POSP and we know, from the
; interval, that the sign is ok, then we could add the negation of INTEGERP.
; But that would violate the contract and make it impossible to construct tau
; that just represent arbitrary non-contradictory sets of recognizers as needed
; for conjunctive rules.

; Note 2: Since the tau is not necessarily closed, it is possible to have a
; restricted domain without having that predicate in the :pos-pairs.  For
; example, t/NATP sets the domain to INTEGERP and without this rule we would
; not detect a contradiction from then adding nil/RATIONALP.  One might think
; that there is no way to get a RATIONALP domain except to explicitly add
; t/RATIONALP, so one could argue that the second rule noted above:

; nil/RATIONALP     RATIONALP domain   contradiction [See Note 2 below]

; is unnecessary because we will detect the contradiction in :pos-pairs.
; But it is possible to get a RATIONALP domain without adding t/RATIONALP!
; Just form the tau for (equal e 1/2).  It gives a tau with :pos-evg
; 1/2 and the singleton RATIONALP interval on 1/2.

            (cond
             (sign
              (case discriminator
                (NATP (tighten-bound tau1 'INTEGERP nil nil 0 ens wrld))
                (POSP (tighten-bound tau1 'INTEGERP nil t 0 ens wrld))
                (INTEGERP (tighten-bound tau1 'INTEGERP nil nil nil ens wrld))
                (RATIONALP (tighten-bound tau1 'RATIONALP nil nil nil ens wrld))
                (ACL2-NUMBERP (tighten-bound tau1 'ACL2-NUMBERP nil nil nil ens wrld))
                (MINUSP (tighten-bound tau1 'ACL2-NUMBERP t t 0 ens wrld))
                (otherwise tau1)))
             (t
              (let ((domain
                     (access tau-interval (access tau tau1 :interval) :domain)))
                (case discriminator
                  (ACL2-NUMBERP
; If we are adding nil/ACL2-NUMBERP and the interval has a non-nil domain, then
; it contradicts nil/ACL2-NUMBERP.  Otherwise, we change the interval to be 0
; <= ... <= 0 with the unrestricted domain.  To set this interval we
; do two successive tighten-bounds, first (innermost) on the lower bound
; bound and then on the upper.
                   (cond
                    ((eq domain nil)
; Args to tighten-bound: tau domain upper-boundp rel k wrld.
                     (tighten-bound
                      (tighten-bound tau1 nil nil nil 0 ens wrld)
                      nil t nil 0 ens wrld))
                    (t *tau-contradiction*)))
                  (RATIONALP
                   (if (or (eq domain 'RATIONALP)
                           (eq domain 'INTEGERP))
                       *tau-contradiction*
                     tau1))
                  (INTEGERP
                   (if (eq domain 'INTEGERP)
                       *tau-contradiction*
                     tau1))
                  (MINUSP (tighten-bound tau1 nil nil nil 0 ens wrld))
                  (NATP
                   (cond
                    ((eq domain 'INTEGERP)
                     (tighten-bound tau1 'INTEGERP t t 0 ens wrld))
                    (t tau1)))
                  (POSP
                   (cond
                    ((eq domain 'INTEGERP)
                     (tighten-bound tau1 nil t nil 0 ens wrld))
                    (t tau1)))
                  (otherwise tau1)))))))))))))

(defun add-recogs-to-tau1 (sign recog-lst tau ens wrld)

; Recog-lst is a list of recognizers, all of which have the same sign.  We add
; each to tau and return tau', where tau' might be *tau-contradiction*.  Note:
; In fact, each recog in recog-lst is the same ``kind'', either each is a
; singleton evg list (because recog-lst was the :neg-evgs of some recognizer
; set) or is a tau-pair (from a :pos-pairs or :neg-pairs).  But we don't
; exploit this uniformity.

  (cond ((endp recog-lst) tau)
        (t (let ((tau (add-to-tau1 sign (car recog-lst) tau ens wrld)))
             (cond ((eq tau *tau-contradiction*)
                    *tau-contradiction*)
                   (t (add-recogs-to-tau1 sign (cdr recog-lst) tau ens wrld)))))))

; The two recognizers (k . :lessp-x-k) and (k . :lessp-k-x) define either upper
; or lower bounds, depending on the sign.

; token        sign        lower          upper
; :lessp-x-k    t                         (< x k)
; :lessp-x-k    nil         (<= k x)
; :lessp-k-x    t           (< k x)
; :lessp-k-x    nil                       (<= x k)

(defun tau-interval-endpoint-to-sign-k-token (upper-boundp rel k)

; We return (mv sign k token) where the bound described by upper-boundp, k, and
; rel is sign/(k . token).  However, the latter is well-formed only if k is
; rational.  This avoids consing up the concrete representation of the
; recognizer, (cons k token), though sometimes we immediately just cons it up
; anyway.

  (if upper-boundp
      (if rel
          (mv t   k :lessp-x-k)      ; (< x k)
          (mv nil k :lessp-k-x))     ; (<= x k)
      (if rel
          (mv t   k :lessp-k-x)      ; (< k x)
          (mv nil k :lessp-x-k))))   ; (<= k x)

(defun tau-union (tau1 tau2 ens wrld)

; We add every sign/recog in tau1 to tau2 using add-to-tau1.  We return tau2'.
; Tau2' may be *tau-contradiction*.  This function does not add implicants
; because we assume both tau1 and tau2 are already closed under simple
; implication.

  (let ((tau2
         (if (access tau tau1 :pos-evg)
             (add-to-tau1 t (access tau tau1 :pos-evg) tau2 ens wrld)
             tau2)))
    (let ((tau2
           (if (eq tau2 *tau-contradiction*)
               *tau-contradiction*
               (add-recogs-to-tau1 nil (access tau tau1 :neg-evgs)
                                   tau2 ens wrld))))
      (let ((tau2
             (if (eq tau2 *tau-contradiction*)
                 *tau-contradiction*
                 (add-recogs-to-tau1 t (access tau tau1 :pos-pairs)
                                     tau2 ens wrld))))
        (let ((tau2
               (if (eq tau2 *tau-contradiction*)
                   *tau-contradiction*
                   (add-recogs-to-tau1 nil (access tau tau1 :neg-pairs)
                                       tau2 ens wrld))))

          (if (eq tau2 *tau-contradiction*)
              *tau-contradiction*

; To add the interval of tau1 to tau2, we need not add the domain recognizer
; because it would be implied by the recognizers and bounds in tau1 and we'll
; add all those.

              (let ((interval (access tau tau1 :interval)))
                (mv-let
                 (sign1 recog1)
                 (if (and interval
                          (access tau-interval interval :lo))
                     (mv-let (sign k token)
                             (tau-interval-endpoint-to-sign-k-token
                              nil
                              (access tau-interval interval :lo-rel)
                              (access tau-interval interval :lo))
                             (mv sign (cons k token)))
                     (mv nil nil))
                 (mv-let
                  (sign2 recog2)
                  (if (and interval
                           (access tau-interval interval :hi))
                      (mv-let (sign k token)
                              (tau-interval-endpoint-to-sign-k-token
                               t
                               (access tau-interval interval :hi-rel)
                               (access tau-interval interval :hi))
                              (mv sign (cons k token)))
                      (mv nil nil))

; If recog1 is non-nil, then sign1/recog1 represents the lower bound of the
; interval in tau1.  If recog2 is non-nil, then sign2/recog2 represents the
; upper bound of the interval in tau1.  We add both to tau2.

                  (let ((tau2 (if recog1
                                  (add-to-tau1 sign1 recog1 tau2 ens wrld)
                                  tau2)))
                    (if (eq tau2 *tau-contradiction*)
                        *tau-contradiction*
                        (let ((tau2 (if recog2
                                        (add-to-tau1 sign2 recog2 tau2 ens wrld)
                                        tau2)))
                          tau2))))))))))))

; The next two functions are used to implement the deduction that if a tau
; includes all the rationals between between lo and hi but excludes each of the
; the integers in that range, then the tau is non-INTEGERP.

(defun all-integers-in-range-excludedp1 (lo hi neg-evgs)

; Lo and hi are integers and neg-evgs is a :neg-evgs list from a tau except
; that the leading (NIL), if any, has been stripped off, i.e., neg-evgs is a
; duplicate-free ``ordered ascending according to lexorder'' (see ; Prelude:
; General-Purpose Functions Having Nothing Specific to do with Tau) of
; singleton evgs not including (NIL).  We check that every integer i such that
; lo <= i <= hi that (list i) is an element of neg-evgs.  We know that the
; ordering is such that (NIL), if present, precedes all rationals, all
; rationals precede all complex-rationals, and all complex-rationals precede
; everything else.  Integers and non-integer rationals are mixed by magnitude
; with negatives first.  Thus, if we are looking for the integers from -3 to
; 2, say, we can cdr our way through neg-evgs until we find them all or hit a
; rational bigger than hi or hit a non-rational.

  (cond ((> lo hi) t)
        ((endp neg-evgs) nil)
        ((equal lo (car (car neg-evgs)))
         (all-integers-in-range-excludedp1 (+ 1 lo) hi (cdr neg-evgs)))
        ((or (not (rationalp (car (car neg-evgs))))
             (> (car (car neg-evgs)) hi))
         nil)
        (t (all-integers-in-range-excludedp1 lo hi (cdr neg-evgs)))))


(defun all-integers-in-range-excludedp (lo-rel lo hi-rel hi neg-evgs)

; Lo and hi are rationals that bound an interval.  Neg-evgs is the :neg-evgs of
; a tau.  We check that every integer between lo and hi is excluded -- which
; means for each i from lo to hi inclusive, (list i) is a member of neg-evgs.
; We can delete the NIL that might be at the front of neg-evgs.  Furthermore,
; if the number of integers between lo and hi inclusive is greater than the
; length of the exclusions, we know some integer is not excluded.  Otherwise,
; we check each one.

; We were once afraid that this deduction will be expensive.  For example, what
; if lo is 0 and hi is (expt 2 32)?  However, we'll only check as many elements
; of neg-evgs as the formula has excluded.  So we have hopes this won't kill
; us!

  (let* ((ilo (squeeze-k nil lo-rel lo))
         (ihi (squeeze-k t   hi-rel hi))
         (lst (if (and (consp neg-evgs)
                       (eq nil (car (car neg-evgs))))
                  (cdr neg-evgs)
                  neg-evgs))
         (k (+ 1 (- ihi ilo))))

; After squeezing the rational extents, the relations are weak (<=), so we
; check every integer between ilo and ihi, inclusive.

    (cond ((> k (len lst))
           nil)
          (t (all-integers-in-range-excludedp1 ilo ihi lst)))))

(defun add-to-tau (sign recog tau ens wrld)

; Recog is a tau-pair or singleton evg list.  Tau is a tau object, not
; *tau-contradiction*.  We add sign/recog and its implicants to tau.  We assume
; tau is a complete tau and we return a complete tau', where tau' may be
; *tau-contradiction*.

  (let ((tau1
         (let ((discriminator (cdr recog)))
           (cond
            ((or (eq discriminator nil)
                 (eq discriminator :lessp-x-k)
                 (eq discriminator :lessp-k-x))
             (add-to-tau1 sign recog tau ens wrld))
            (t (tau-union (tau-simple-implicants sign discriminator wrld)

; One might think we could just use tau here, instead of the add-to-tau1
; expression below.  However, we use the presence of certain recognizers to
; prevent recursive looping.  For example, if the interval in the tau1 that we
; are creating is below 0, we add MINUSP and its implicants -- IF MINUSP isn't
; already there.  This is done with a full-blown add-to-tau call further below.
; But we do not wish to depend upon the order in which the recognizers in the
; implicants are added, and if MINUSP is added later than others, we might
; loop.  So here we immediately add the recognizer we were asked to add, and
; then we add all the implicants.  The implicants will include sign/recog,
; which will be redundant.

                          (add-to-tau1 sign recog tau ens wrld)
                          ens wrld))))))

; We have added sign/recog to tau using add-to-tau1.  We now inspect tau1 for
; certain further deductions we can make, related to the interval in tau.

    (cond
     ((eq tau1 *tau-contradiction*) *tau-contradiction*)
     (t
      (let* ((interval (access tau tau1 :interval))
             (domain (access tau-interval interval :domain))
             (lo-rel (access tau-interval interval :lo-rel))
             (lo (access tau-interval interval :lo))
             (hi-rel (access tau-interval interval :hi-rel))
             (hi (access tau-interval interval :hi))
             (pos-pairs (access tau tau1 :pos-pairs))
             (neg-pairs (access tau tau1 :neg-pairs)))
        (cond
         ((or (null interval)
              (and (null lo) (null hi))
              (access tau tau1 :pos-evg))

; If tau1 has an unrestricted interval (regardless of the domain) there's
; nothing more we can deduce from it because everything below is based on
; properties of the bounds.  In addition, if tau1 recognizes a constant, we
; don't add anything more to it.

          tau1)

; We now consider deductions we can make relating the pos-pairs and neg-pairs
; to the interval bounds.  We first consider deducing positive recogs and then
; negative recogs.  In all cases when we add a recog to tau1 we do so with a
; full blown recursive call, so that we might fire more than one of these rules
; before we're done.  We protect our recursive calls with explicit checks
; confirming that the recog isn't already present.  We assume that if a tau is
; not that for a constant, then adding a recognizer that is not explicitly
; present will change the tau so the recognizer is explicitly present.

; The bounds on the interval may allow us to deduce certain other recognizers.
; The implication tree of the recognizers in question is:

; posp --> natp--->
;                  \
;                    -->  acl2-numberp
;                  /
; minusp ---------

; The implicants of each imply all the others along the branches above.  So we
; just look for the strongest ones.

; domain and bound             effect (if not already there)

; any      &  ... < 0           t/MINUS
; INTEGERP & 0 <  ...           t/POSP
; INTEGERP & 0 <= ...           t/NATP
; INTEGERP                      t/INTEGERP     ; See Note
; RATIONALP                     t/RATIONALP    ; See Note
; ACL2-NUMBERP                  t/ACL2-NUMBERP

; Note: We don't think these cases can occur but signal a hard error if they
; do.

         ((and hi
               (if hi-rel (<= hi 0) (< hi 0))
               (not
                (tau-pair-member *tau-minusp-pair* pos-pairs)))

; If the interval is bounded strictly below 0, we can add MINUSP and its
; implicants (if MINUSP is not already there).  Among the implicants will be
; ACL2-NUMBERP.  It is through this mechanism that tau knows that (< x 0) -->
; (ACL2-NUMBERP x).  Even though an interval with a negative upper bound will
; have an ACL2-NUMBERP domain, the tau won't have ACL2-NUMBERP in it until we
; add it.

          (add-to-tau t *tau-minusp-pair* tau1 ens wrld))
         ((and (eq domain 'INTEGERP)
;              (null lo-rel) ; is guaranteed with INTEGERP domain
               lo
               (< 0 lo)
               (not
                (tau-pair-member *tau-posp-pair* pos-pairs)))
; If the interval is over the positive integers, we add POSP and its implicants
; (if POSP is not already there).
          (add-to-tau t *tau-posp-pair* tau1 ens wrld))
         ((and (eq domain 'INTEGERP)
               lo
               (<= 0 lo)
               (not
                (tau-pair-member *tau-natp-pair* pos-pairs)))
; If the interval is over the non-negative integers, we can add NATP and its
; implicants (if NATP is not already there).
          (add-to-tau t *tau-natp-pair* tau1 ens wrld))
         ((or (and (eq domain 'INTEGERP)
                   (not (tau-pair-member *tau-integerp-pair* pos-pairs)))
              (and (eq domain 'RATIONALP)
                   (not (tau-pair-member *tau-rationalp-pair* pos-pairs))))
          (er hard 'add-to-tau
              "It was thought impossible for a tau to have an :interval with ~
               domain ~x0 without that recognizer being in its :pos-pairs, ~
               but it happened with ~x1.  One way this might have happened is ~
               if the initial tau was ``incomplete,'' e.g., had NATP in it ~
               but not its implicants.  But add-to-tau is supposed to be ~
               called on complete taus and guarantees the completeness of its ~
               result."
              domain tau1))
         ((and (eq domain 'ACL2-NUMBERP)
               (not
                (tau-pair-member *tau-acl2-numberp-pair* pos-pairs)))
; If an interval is over the numbers, we add ACL2-NUMBERP and all its
; implicants (if ACL2-NUMBERP is not already there).  (The primitives for
; constructing intervals use the bounds to infer the ACL2-NUMBERP domain when
; possible.)
          (add-to-tau t *tau-acl2-numberp-pair* tau1 ens wrld))

; Now we consider some negative deductions:

; sign/recog        condition          effect
; nil/NATP          0 <= ...           nil/INTEGERP
; nil/POSP          0 < ...            nil/INTEGERP
; t/RATIONALP       lo <? ... <? hi    nil/INTEGERP
;                   and every integer
;                   in range is excluded

         ((and (tau-pair-member *tau-natp-pair* neg-pairs)
               lo
               (<= 0 lo)
               (not (tau-pair-member *tau-integerp-pair* neg-pairs)))

; If tau1 includes nil/NATP but the interval tells us the subject is
; nonnegative, we add nil/INTEGERP (if it is not already there).

          (add-to-tau nil *tau-integerp-pair* tau1 ens wrld))
         ((and (tau-pair-member *tau-posp-pair* neg-pairs)
               lo
               (< 0 lo)
               (not (tau-pair-member *tau-integerp-pair* neg-pairs)))

; If tau1 includes nil/POSP but the interval tells us the subject is positive,
; we add nil/INTEGERP (if it is not already there).

          (add-to-tau nil *tau-integerp-pair* tau1 ens wrld))
         ((and (tau-pair-member *tau-rationalp-pair* pos-pairs)
               lo
               hi
               (not (tau-pair-member *tau-integerp-pair* neg-pairs))
               (all-integers-in-range-excludedp lo-rel lo hi-rel hi
                                                (access tau tau1 :neg-evgs)))

; If tau1 includes t/RATIONALP and there is a finite interval from lo to hi but
; every integer in that interval is excluded by the neg-evgs, then we add
; nil/INTEGERP (if it is not already there).

          (add-to-tau nil *tau-integerp-pair* tau1 ens wrld))
         (t
; Otherwise we can't deduce any new recognizers from this interval and return the
; simply extended tau1.
          tau1)))))))

; Now we define the notion of one tau being a ``near subset'' of another.  Set1
; is a near subset of set2 if there is exactly one element of set1 that is not
; in set2.  For example, {A -C} is a near subset of {A -C D E F G} because the
; only element of the first set not in the second is B.  The concept is used in
; firing conjunctive rules.  The conjunctive rule (A & B) --> C is stored as
; the tau {A B -C}.  If we ever encounter a tau such that some conjunctive rule
; is a near subset of it, we can assert the negation of the missing element.
; For example, given the conjunctive rule {A B -C} and tau {A -C D E F G}, we
; can assert -B, to get {A -B -C D E F G}.  Think of the conjunctive rule being
; stated in the contrapositive: (A & -C) --> -B, and the tau as describing some
; object with properties A and -C (among others).  Then the object also has
; property -B.

; Note that if we regard the objects in our sets as terms, we really want to
; know whether the conjunction of the terms in set2 imply all (subset) or all
; but one (near-subset) of the terms in set1.  Typically, set2 describes the
; context we're in and set1 represents a bunch of hypotheses we'd like to
; relieve.  For all the elements but the interval bounds, we just look for
; membership, but for the bounds we look for implication.

; Our functions for checking this property (across various data structures like
; almost lexordered lists, tau-pairs, tau, etc) all follow the convention that
; they return t if every element of the former is in the latter (i.e., the
; subset relation holds), nil if more than one element fails to occur, and the
; unique missing element otherwise.  We are careful that the sets to which we
; apply this concept never contain nil as an element.

(defun pos-evg-near-subsetp (pos-evg1 pos-evg2)

; This is an odd little function that plays the role for the :pos-evg slot of
; tau that tau-pairs-near-subsetp plays for :pos-pairs and
; :neg-pairs.  By defining it explicitly we allow tau-near-subsetp to be defined
; as a composition across the five components.

; The :pos-evg slot of a tau is either nil or represents a singleton set
; containing the :pos-evg.  So think of s1 and s2 as the sets corresponding to
; the given pos-evg1 and pos-evg2.  Then we determine whether s1 is a
; near-subset of s2: If s1 is a subset of s2, we return t, if exactly one
; element of s1 fails to be an element of s2, we return that missing element,
; otherwise we return nil.  However, since s1 contains at most one element, we
; never return nil!

  (if pos-evg1
      (if pos-evg2
          (if (equal pos-evg1 pos-evg2)
              t
              pos-evg1)
          pos-evg1)
      t))

(defun neg-evgs-near-subsetp
  (neg-evgs1 neg-evgs2 e pos-pairs2 neg-pairs2 interval2 ens wrld)

; This is analogous to tau-pairs-near-subsetp, but for the neg-evgs components.

; We wish to check the near-subset relation between the neg-evgs of two tau,
; tau1 and tau2.  (Recall that lst1 is a near-subset of lst2 if there is
; exactly one element of lst1 that is not in lst2.  Our convention is that
; ``near-subset'' functions return t to indicate that every element of the one
; is in the other, nil to indicate that more than one element is missing, and
; otherwise returns the missing element.)  However, suppose x /= 23 is in tau1
; by being in its neg-evgs, while it is not in the neg-evgs of tau2 because
; that evg is ruled out by some pair.  For example, tau1 might be the integers
; except 23, while tau2 might be the even integers.  If the assumption that x =
; 23 allows us to falsify some pos-pair in tau2, then x = 23 isn't really
; missing from tau2, it is swept up by the pos-pairs.  Neg-pairs are, of
; course, symmetric.  But this concept is just that codified in
; exists-bad-valp.  Similar remarks apply to the interval of tau2 ruling out an
; evg.

; If every element of neg-evgs1 is either in neg-evgs2 or else is subsumed by
; some pair in the interval, pos-pairs2, or neg-pairs2, we return t.  If more
; than one element of neg-evgs1 fails to have that property (i.e., is in
; neg-evgs2 or is subsumed by the pairs), we return nil.  Otherwise, we return
; the missing element.

  (cond
   ((endp neg-evgs1) (if e e t))
   ((endp neg-evgs2)
    (cond
     ((or (not (eval-tau-interval interval2 (car (car neg-evgs1))))
          (exists-bad-valp nil pos-pairs2 (car neg-evgs1) ens wrld)
          (exists-bad-valp t   neg-pairs2 (car neg-evgs1) ens wrld))
      (neg-evgs-near-subsetp (cdr neg-evgs1)
                             nil
                             e
                             pos-pairs2 neg-pairs2
                             interval2 ens wrld))

; Otherwise, we know (car neg-evgs1) really is missing and so we fail if we've
; already seen a missing element and we continue with (car neg-evgs1) as our
; candidate unique witness if we haven't.

     (t (if e
            nil
            (neg-evgs-near-subsetp (cdr neg-evgs1)
                                   nil
                                   (car neg-evgs1)
                                   pos-pairs2 neg-pairs2
                                   interval2 ens wrld)))))
   ((almost-lexorder-singletons (car neg-evgs1) (car neg-evgs2))
    (if (equal (car neg-evgs1) (car neg-evgs2))
        (neg-evgs-near-subsetp (cdr neg-evgs1)
                               (cdr neg-evgs2)
                               e
                               pos-pairs2 neg-pairs2
                               interval2 ens wrld)

; At this point, we've discovered that (car neg-evgs1) is missing from
; neg-evgs2.  But we can't treat it as missing until we make sure it
; isn't subsumed by one of the pairs or the interval.

        (cond
         ((or (not (eval-tau-interval interval2 (car (car neg-evgs1))))
              (exists-bad-valp nil pos-pairs2 (car neg-evgs1) ens wrld)
              (exists-bad-valp t   neg-pairs2 (car neg-evgs1) ens wrld))

; So the ``missing'' element is actually subsumed elsewhere tau2 and we can
; treat it as found.

          (neg-evgs-near-subsetp (cdr neg-evgs1)
                                 (cdr neg-evgs2)
                                 e
                                 pos-pairs2 neg-pairs2
                                 interval2 ens wrld))
         (t

; Otherwise, it really is missing and we either fail or make this the candidate
; unique witness.

          (if e
              nil
              (neg-evgs-near-subsetp (cdr neg-evgs1)
                                     neg-evgs2
                                     (car neg-evgs1)
                                     pos-pairs2 neg-pairs2
                                     interval2 ens wrld))))))
   (t (neg-evgs-near-subsetp neg-evgs1 (cdr neg-evgs2)
                             e
                             pos-pairs2 neg-pairs2
                             interval2 ens wrld))))

; On the Near-Subset Relation for Intervals

; We now develop the code for checking the near-subset relation for intervals.
; However, it is useful to recap why we care about near-subsets.

; Each conjunctive rule is stored as a tau: the rule p1 & ... & pn --> q is
; stored as the tau p1 & ... & pn & -q.  Suppose we have some facts about x,
; expressed as a tau for x, and wish to try to fire a conjunctive rule.  If
; each of the conjuncts in the rule tau are in the factual tau, then we have a
; contradiction.  But if all but one of the conjuncts of the rule are among the
; facts, then we may add the negation of the missing predicate to the facts.
; For example, if we know p1 & ... & pn then we can add q.  More interestingly,
; if we know p1 & ... pn-1 & -q, we can add -pn.  So it is important to be able
; to determine if all but one of the conjuncts of a tau are in another tau.  We
; call this relation ``near subset.''  We will check the near-subset relation
; essentially component-wise, comparing pos-pairs to pos-pairs, neg-evgs to
; neg-evgs, etc.

; But what does it mean to be a near subset if intervals are involved?  Think
; of an interval coding at most two more recognizers, zero or one chosen from
; group LO below and zero or one chosen from group HI:

; LO: (lambda (x) (<= 'lo x))
;     (lambda (x) (<  'lo x))
; HI: (lambda (x) (<= x 'hi))
;     (lambda (x) (<  x 'hi))

; Of course, if there is no upper or lower bound (i.e., the interval is somehow
; infinite) it just means that no recognizer is chosen.

; Now, consider the conjunctive rule: (integerp x) & 0 <= x <= 100 --> (Q x)
; coded as a tau-like object:

; Rule:  (integerp x) & (<= 0 x) & (<= x 100) & -(Q x)

; and a set of known facts:

; Facts:  (integerp x) & (<= x 100) & -(Q x)

; we see that the Rule is a near-subset of the Facts.  One Rule hypothesis is
; missing: (<= 0 x).  That means we can augment the facts with its negation: (<
; x 0).

; Now what if we have even stronger Facts than the Rule requires?

; Rule:  (integerp x) & (<= 0 x) & (<= x 100) & -(Q x)
; Facts: (integerp x) & (<= x 75) & -(Q x)

; Clearly, if x is below 75, it is below 100.  So we can add (< x 0) here too.

; Finally, what if a fact actually contradicts the missing hypothesis?
; Suppose we have:

; Rule:  (integerp x) & (<= 0 x) & (<= x 100) & -(Q x)
; Facts: (integerp x) & (< x -100) & -(Q x)

; Again, the Rule is a near subset of the Facts.  In particular, we know
; (integerp x), we know (<= x 100) -- indeed, x is negative, and we know -(Q
; x).  The missing hypothesis is (<= 0 x).

; But this hypothesis is actually contradicted by (< x -100).  So we shouldn't
; add its negation.  Why?  What if we did?  What if we added the "new" fact (<
; x 0).  We haven't helped.  We already know (< x -100).

; So we need to be able to compare the inequality hypotheses of a rule with
; some inequality facts and determine whether (a) all the hypotheses are true
; according to the facts -- in which case we have a contradiction since
; conjunctive rules are stored the way they are, or (b) there is exactly one
; hypothesis missing from the facts and it is not contradicted by the facts --
; in which case we can add its negation to the facts, or (c) multiple
; hypotheses are missing and we do nothing.

; So now we need to be able to answer the question: given a single inequality
; fact can we determine whether a single inequality hypothesis is true? Is
; false? Is unknown?

; We next define tau-interval-endpoint-implication which takes a ``fact,'' A, a
; ``hypothesis,'' B, and decides whether the hypothesis is true given A, false
; given A, or undecided.  Below is a macro definition used solely to justify
; the definition of this function.

; The macro contains a table with columns labeled (A x), (B x), C, and Z.  The
; meaning of each row in this table is:

; ``Thm:  C <--> [forall x : (A x) --> (B x)]

;   Proof: C --> ((A x) --> (B x)) is obvious.  The other direction is proved by
;   first instantiating the universal x with Z and then proving ((A Z) --> (B Z))
;   --> C.  Q.E.D.''

; The commented-out code below actually checks these entries.

;   (tau-status :system nil)
;   (include-book "arithmetic-5/top" :dir :system)
;
;   (defun generate-ABC-thms (lst)
;     (cond ((endp lst) nil)
;           (t (let ((A (nth 0 (car lst)))
;                    (B (nth 1 (car lst)))
;                    (C (nth 2 (car lst)))
;                    (Z (nth 3 (car lst))))
;                (cons `(implies (and (rationalp k)
;                                     (rationalp d))
;                                (and
;                                 (implies ,C (implies ,A ,B))
;                                 (implies (let ((x ,Z))
;                                            (implies ,A ,B))
;                                          ,C)))
;                      (generate-ABC-thms (cdr lst)))))))
;
;   (defmacro confirm-ABC-table nil
;     `(thm
;       (and
;        ,@(generate-ABC-thms
;   ;           fact        question
;   ;           (A x)       (B x)         C              Z
;           '(((<  k x)    (<  d x)    (<= d k)    (+ k (/ (- d k) 2))) ;  1
;             ((<  k x)    (<= d x)    (<= d k)    (+ k (/ (- d k) 2))) ;  2
;             ((<  k x)    (<= x d)    NIL         (+ (max k d) 1))             ;  3
;             ((<  k x)    (<  x d)    NIL         (+ (max k d) 1))             ;  4
;
;             ((<= k x)    (<  d x)    (<  d k)    (+ k (/ (- d k) 2))) ;  5
;             ((<= k x)    (<= d x)    (<= d k)    (+ k (/ (- d k) 2))) ;  6
;             ((<= k x)    (<= x d)    NIL         (+ (max k d) 1))             ;  7
;             ((<= k x)    (<  x d)    NIL         (+ (max k d) 1))             ;  8
;
;             ((<= x k)    (<  d x)    NIL         (- (min k d) 1))             ;  9
;             ((<= x k)    (<= d x)    NIL         (- (min k d) 1))             ; 10
;             ((<= x k)    (<= x d)    (<= k d)    (+ d (/ (- k d) 2))) ; 11
;             ((<= x k)    (<  x d)    (<  k d)    (+ d (/ (- k d) 2))) ; 12
;
;             ((<  x k)    (<  d x)    NIL         (- (min k d) 1))             ; 13
;             ((<  x k)    (<= d x)    NIL         (- (min k d) 1))             ; 14
;             ((<  x k)    (<= x d)    (<= k d)    (+ d (/ (- k d) 2))) ; 15
;             ((<  x k)    (<  x d)    (<= k d)    (+ d (/ (- k d) 2)))))))); 16
;
;   (confirm-ABC-table)

; The success of confirm-ABC-table means that the entries in the above table
; are correct.  Thus, we know that

; [forall x : (A x) --> (B x)]

; is a theorem if the condition in column C is true.

; For example, consider a function call (fn a) and imagine that we know that
; the actual, a, has tau A.  But imagine that the signature of fn requires B.
; Then if C is true, the signature requirement is satisfied.  Alternatively, we
; might have a Conjunctive Rule, which when applied to the term a, produces the
; literal (B a).  If we know (A a) then we know (B a) holds, provided C is
; true.

; We are also interested in the situation in which (A x) means that (B x) is
; false.  That can be investigated by considering:

; [forall x : (A x) --> -(B x)].

; For every (B x), -(B x) is also in the table, just a few rows away.  Here is
; a rearrangement of the table in which we've deleted the Z column (the proofs)
; and included, in the C' column, the C condition for the negation of each B
; with the same A.  The final line number is the line in the table that
; justifies -(B x).

; The ABC Table
; [forall x : A -->  B] is true if C
; [forall x : A --> -B] is true if C'

;             A           B           C        C'
;  1      (<  k x)    (<  d x)    (<= d k)     NIL      ;  3
;  2      (<  k x)    (<= d x)    (<= d k)     NIL      ;  4
;  3      (<  k x)    (<= x d)    NIL          (<= d k) ;  1
;  4      (<  k x)    (<  x d)    NIL          (<= d k) ;  2

;  5      (<= k x)    (<  d x)    (<  d k)     NIL      ;  7
;  6      (<= k x)    (<= d x)    (<= d k)     NIL      ;  8
;  7      (<= k x)    (<= x d)    NIL          (<  d k) ;  5
;  8      (<= k x)    (<  x d)    NIL          (<= d k) ;  6

;  9      (<= x k)    (<  d x)    NIL          (<= k d) ; 11
; 10      (<= x k)    (<= d x)    NIL          (<  k d) ; 12
; 11      (<= x k)    (<= x d)    (<= k d)     NIL      ;  9
; 12      (<= x k)    (<  x d)    (<  k d)     NIL      ; 10

; 13      (<  x k)    (<  d x)    NIL          (<= k d) ; 15
; 14      (<  x k)    (<= d x)    NIL          (<= k d) ; 16
; 15      (<  x k)    (<= x d)    (<= k d)     NIL      ; 13
; 16      (<  x k)    (<  x d)    (<= k d)     NIL      ; 14

; For example, suppose we have a lower bound, A: (< 20 a), among our facts.
; Suppose the rule has the hypothesis B: (<= 15 a).  We want to know whether
; the hypothesis, B, follows from the fact A.  These two choices of A and B
; correspond to line 2 in the table, with k = 20 and d = 15.  So we ask
; question C, (<= 15 20).  The answer is T, so we know that the hypothesis B is
; satisfied.  However, if B were (<= 25 a), then C would become (<= 25 20) and
; we could not relieve B.

; Note that every row contains a NIL in C or C'.  So if we index into the table
; for a given A and B and find a non-NIL comparison term in C, then the table
; might tell us that B is true (if C evaluates to true), but cannot tell us
; that B is false (because C' will be NIL).

; If on the other hand we index into the table for a given A and B and find a
; NIL in C, the table cannot tell us that B is true but it MIGHT be able to
; tell us that it is false, by checking the condition in the C' column.

; For example, consider A: (<= x 20) and B: (< 25 x).  This is line 9.  Here, C
; = NIL, so the table cannot tell us that B is true.  However, looking at the
; C' column we see the test (<= 20 25), which is true.  So we know B is false.

; Finally notice that the A in lines 1-8 are lower bounds and those in lines
; 9-16 are upper bounds.  Similarly, every block of B has two lower bound cases
; (e.g., lines 1 and 2 in the first block) and two upper bound cases (lines 3
; and 4).  A lower bound can sometimes establish that another lower bound
; holds; a lower bound can never establish that an upper bound holds but can
; sometimes show that an upper bound is false.  The situation is symmetric with
; respect to upper bounds.  These remarks only apply to finite (i.e., rational)
; bounds; if the bound in the conclusion is infinite, of course the implication
; holds.

(defun tau-interval-endpoint-implication (ap arel k bp brel d)

; Ap and bp should be named ``a-upper-boundp'' and ``b-upper-boundp''
; respectively.

; This function takes the interval-level descriptions of the endpoints of two
; intervals.  The first three formals, ap, k, and arel, describe one bound of
; an interval and the next three, bp, d, and brel, describe another.  We call
; these two bounds A and B respectively.  The coding is

; p     rel      A             B
; t      t     (<  x k)      (<  x d)
; t      nil   (<= x k)      (<= x d)
; nil    t     (<  k x)      (<  d x)
; nil    nil   (<= k x)      (<= d x)

; We return t if [forall x : A --> B].  We return nil if [forall x : A --> -B].
; We return ? otherwise.  We simply implement the ABC Table above, except we
; first interpret those k and/or d representing infinities.  If d is NIL then B
; is true (because d represents either negative or positive infinity depending
; on whether it is a lower or upper bound).  If k is NIL, then A is true and
; thus implies nothing useful.  Thus the structure of the code below is: (if k
; (if d <ABC Table> t) (if d '? t)).  While implementing the table we show the
; relevant blocks from the table, rearranging the lines to show the order of
; the tests.

; Finally, a literal translation of the table, say for lines 16 and 15 below would
; ask whether brel is t or nil and test (<= k d) for the one and (<= k d) for
; the other.  But since the two tests are identical, we exploit (if x y y) = y by
; commenting out the (if x ... y) parts.


  (if k
      (if d
          (if ap
              (if arel
;            A            B        C             C'
; 16      (<  x k)    (<  x d)  |  (<= k d)     NIL
; 15      (<  x k)    (<= x d)  |  (<= k d)     NIL
; 13      (<  x k)    (<  d x)  |  NIL          (<= k d)
; 14      (<  x k)    (<= d x)  |  NIL          (<= k d)

                  (if bp
;                     (if brel
                      (if (<= k d) t '?)
;                         (if (<= k d) t '?))
;                     (if brel
                      (if (<= k d) nil '?)
;                         (if (<= k d) nil '?))
                      )


; 12      (<= x k)    (<  x d)  |  (<  k d)     NIL
; 11      (<= x k)    (<= x d)  |  (<= k d)     NIL
;  9      (<= x k)    (<  d x)  |  NIL          (<= k d)
; 10      (<= x k)    (<= d x)  |  NIL          (<  k d)

                  (if bp
                      (if brel
                          (if (<  k d) t '?)
                          (if (<= k d) t '?))
                      (if brel
                          (if (<= k d) nil '?)
                          (if (<  k d) nil '?))))

              (if arel

;  4      (<  k x)    (<  x d)  |  NIL          (<= d k)
;  3      (<  k x)    (<= x d)  |  NIL          (<= d k)
;  1      (<  k x)    (<  d x)  |  (<= d k)     NIL
;  2      (<  k x)    (<= d x)  |  (<= d k)     NIL

                  (if bp
;                     (if brel
                      (if (<= d k) nil '?)
;                         (if (<= d k) nil '?))
;                     (if brel
                      (if (<= d k) t '?)
;                         (if (<= d k) t '?))
                      )

;  8      (<= k x)    (<  x d)  |  NIL          (<= d k)
;  7      (<= k x)    (<= x d)  |  NIL          (<  d k)
;  5      (<= k x)    (<  d x)  |  (<  d k)     NIL
;  6      (<= k x)    (<= d x)  |  (<= d k)     NIL

                  (if bp
                      (if brel
                          (if (<= d k) nil '?)
                          (if (<  d k) nil '?))
                      (if brel
                          (if (<  d k) t '?)
                          (if (<= d k) t '?)))))
          t)
      (if d '? t)))

; Independently of tau we can prove that when the above function
; returns t, then A --> B, and when it returns nil, then A --> -B.

; (tau-status :system nil)
; (verify-termination tau-interval-endpoint-implication)

; In the defun below, p indicates whether rel,k is an upper
; or lower bound on x.

; (defun <?? (p rel k x)
;   (if p
;       (if rel
;           (if k (< x k) t)
;           (if k (<= x k) t))
;       (if rel
;           (if k (< k x) t)
;           (if k (<= k x) t))))
;
; (thm
;  (implies
;   (equal (tau-interval-endpoint-implication ap arel k bp brel d)
;          t)
;   (implies (<?? ap arel k x)
;            (<?? bp brel d x))))
;
; (thm
;  (implies
;   (equal (tau-interval-endpoint-implication ap arel k bp brel d)
;          nil)
;   (implies (<?? ap arel k x)
;            (not (<?? bp brel d x)))))

(defun tau-interval-near-subsetp (interval1 interval2)

; This is loosely analogous to tau-pairs-near-subsetp, but for the interval
; components.  This function returns (mv sign k rel), where rel = T means
; both bounds of interval1 are implied by those of interval2, rel=NIL means
; neither bound is implied (or one is definitely false), and otherwise rel is
; :lessp-x-k or :lessp-k-x and sign, k, and rel represent the missing element.

; Recall that one set is a near subset of another if all but one element of the
; first is a member of (is implied by) the second.  Here we're not interested
; in membership but in implication.  For example, the lower bound 0 < ...  is
; implied by the lower bound 100 < ...

; We ignore the domain of interval1 and just try to establish the bounds of
; interval1 from those of interval2.  Why?  We assume that interval1 comes from
; some tau, say tau1, which corresponds to a theorem in the sense that we code
; conjunctive rules as tau.  The domain in the interval of tau1 is implied
; either by other recognizers in tau1 or by the bounds themselves.  Thus, if we
; have a tau representing a conjunctive rule and we were to add the domain in
; as a conjunct, we could remove it from the theorem.  I.e., the domain really
; is irrelevant to conjunctive rule firings.

; So we may think of an interval as representing just (at most) two conjuncts,
; two imaginary ``tau-pairs'', one recognizing (<? lo x) and the other
; recognizing (<? x hi).  These recognizers exist only if their respective
; bounds are non-nil.  So we just need to check whether (<? lo x), if present
; in interval1, is implied by interval2, and similarly for (<? x hi).  If we
; find exactly one missing, we return ``it.''

; (Unlike the near-subset comparison for neg-evgs, this function can confine its
; attention to the intervals of the two taus in question:  only an inequality can
; establish an inequality.)

; Our convention for other ``near-subset'' functions is that they return t (to
; indicate that every element of the first is in the other), nil (to indicate
; that more than one element is missing), or the missing element.  That would
; be inefficient here because the missing ``tau pair'' is represented by three
; objects that we'd have to cons up, e.g., a missing upper bound (<= ... k) is
; represented as a negatively signed (k . :lessp-k-x).  So this function
; ``accumulates'' and returns three things, the missing sign, k, and token.  If
; the returned token is t is means we found all of interval1 in interval2.  If
; the returned token is nil both bounds were missing.

; Also unlike the others, an interval can actually say more than just
; that a bound is ``missing'', it can say the bound is false.  We
; treat the discovery of a false bound as we would the discovery that
; multiple elements are missing, so as to avoid the application of
; the rule.

; In terms of tau-interval-endpoint-implication, the endpoints of interval1
; provide our Bs, the endpoints of interval2 provide our As, and we are trying
; to decide the questions A --> B and A --> -B for each combination.  If any B
; comes back false or multiple Bs come back unknown, we quit with NIL (which
; might always be interpreted by our caller to mean ``multiple recognizers are
; unknown'' but, when discovered meant ``one recognizer is simply false and so
; you can't productively assume its negation''), if every B comes back true, we
; report T (meaning all the hypotheses are true), and otherwise, exactly one B
; is unknown and we return ``it.''  But what we actually return is (mv
; missing-sign missing-k missing-token) where if missing-token is t or nil we
; mean ``all found'' or ``multiple missing'' (or ``one false''), and otherwise
; missing-token is :lessp-x-k or :lessp-k-x and missing-sign and missing-k are
; the other pieces of the missing sign/recog.

; In the following we use ``A lo'' to mean the lower bound of interval2, ``B
; lo'' to mean the lower bound of interval1, etc.  We use ``A lo --> B lo'' to
; mean the question: ``does A lo imply B lo (t), the negation of B lo (nil), or
; is it unknown (?)?''

  (let ((b-lo-rel (access tau-interval interval1 :lo-rel))
        (b-lo-d (access tau-interval interval1 :lo))
        (b-hi-rel (access tau-interval interval1 :hi-rel))
        (b-hi-d (access tau-interval interval1 :hi))

        (a-lo-rel (access tau-interval interval2 :lo-rel))
        (a-lo-k (access tau-interval interval2 :lo))
        (a-hi-rel (access tau-interval interval2 :hi-rel))
        (a-hi-k (access tau-interval interval2 :hi)))

; We first ask ``A hi --> B hi''.  If that returns t, we ask ``A lo --> B lo''.
; If that returns t, we're done and return t (in a triple).  If either test
; returns nil, we return nil (in a triple).  But if ``A lo --> B lo'' returns
; ?, we have to try ``A hi --> B lo'' because it might report that B lo is
; false.  (For example, A might be [15 <= ... <= 20] and B might be [30 <=
; ... ...].  (<= 15 x) does not establish that (<= 30 x), so we get ? on the
; ``A lo --> B lo'' comparison.  But we get NIL on ``A hi --> B lo'' because
; (<= x 20) means (<= 30 x) is false.)  Similar remarks apply if ``A hi --> B
; hi'' returns ?.

    (let ((temp (tau-interval-endpoint-implication ; (A hi --> B hi)
                 t a-hi-rel a-hi-k
                 t b-hi-rel b-hi-d)))
      (cond
       ((eq temp t)
        (let ((temp (tau-interval-endpoint-implication ; (A lo --> B lo)
                     nil a-lo-rel a-lo-k
                     nil b-lo-rel b-lo-d)))
          (cond
           ((eq temp t)
            (mv nil nil t))
           ((eq temp nil)
            (mv nil nil nil))
           (t (let ((temp (tau-interval-endpoint-implication ; (A hi --> B lo)
                           t   a-hi-rel a-hi-k
                           nil b-lo-rel b-lo-d)))
                (cond
                 ((eq temp t)
                  (mv nil nil
                      (er hard 'tau-interval-near-subsetp
                          "``A hi --> B lo'' returned T after ``A lo --> B ~
                          lo'' returned unknown.  This is not supposed to ~
                          happen!  The only way an upper bound like ``A hi'' ~
                          can imply a lower bound like ``B lo'' is if the ~
                          lower bound is negative infinity (i.e., the bound ~
                          is vacuous), in which case ``A lo --> B lo'' would ~
                          have succeeded.  A is this tau-interval ~x0 and B ~
                          is this one ~x1."
                          interval2
                          interval1)))
                 ((eq temp nil)
                  (mv nil nil nil))
                 (t
; B-lo-d cannot be nil, and so must be a rational, since B lo is missing.
; (If the bound were nil, it would be trivially true.)  So the resulting
; (k . token) is a well-formed inequality recognizer.
                  (tau-interval-endpoint-to-sign-k-token
                   nil b-lo-rel b-lo-d))))))))
       ((eq temp nil)
        (mv nil nil nil))
       (t (let ((temp (tau-interval-endpoint-implication ; (A lo --> B hi)
                       nil a-lo-rel a-lo-k
                       t   b-hi-rel b-hi-d)))
            (cond
             ((eq temp t)
              (mv nil nil
                  (er hard 'tau-interval-near-subsetp
                      "``A lo --> B hi'' returned T after ``A hi --> B hi'' ~
                       returned unknown (?).  This is not supposed to happen! ~
                       The only way a lower bound like ``A lo'' can imply an ~
                       upper bound like ``B hi'' is if the upper bound is ~
                       positive infinity (i.e., the bound is vacuous), in ~
                       which case ``A hi --> B hi'' would have succeeded.  A ~
                       is this tau-interval ~x0 and B is this one ~x1."
                      interval2
                      interval1)))
             ((eq temp nil)
              (mv nil nil nil))
             (t (let ((temp (tau-interval-endpoint-implication ; (A lo --> B lo)
                             nil a-lo-rel a-lo-k
                             nil b-lo-rel b-lo-d)))
                  (cond
                   ((eq temp t)
; B-hi-d cannot be nil and so must be rational, as explain for b-lo-d above.
                    (tau-interval-endpoint-to-sign-k-token t b-hi-rel b-hi-d))
                   ((eq temp nil)
                    (mv nil nil nil))
                   (t (let ((temp ; (A hi --> B lo)
                             (tau-interval-endpoint-implication
                              t   a-hi-rel a-hi-k
                              nil b-lo-rel b-lo-d)))
                        (cond
                         ((eq temp t)
                          (mv nil nil
                              (er hard 'tau-interval-near-subsetp
                                  "``A hi --> B lo'' returned T after ``A lo ~
                                  --> B lo'' returned unknown.  This is not ~
                                  supposed to happen!  The only way an upper ~
                                  bound like ``A hi'' can imply a lower bound ~
                                  like ``B lo'' is if the lower bound is ~
                                  negative infinity (i.e., the bound is ~
                                  vacuous), in which case ``A lo --> B lo'' ~
                                  would have succeeded.  A is this ~
                                  tau-interval ~x0 and B is this one ~x1."
                                  interval2
                                  interval1)))
                         (t
; We only asked ``A hi --> B lo'' to detect the possible hard error.  The only
; expected answer is NIL or ?.  And in both cases we fail because we already have
; B hi missing and now we've got B lo either missing or false.

                          (mv nil nil nil)))))))))))))))

(defun tau-near-subsetp (tau1 tau2 ens wrld)

; Think of tau1 and tau2 simply as sets of recognizers.  If tau1 is a subset of
; tau2, we signal a contradiction.  If more than one element of tau1 is not in
; tau2, we return nil; otherwise, we return the sign and recog of the missing
; element.  We return (mv contradictionp sign recog), where the last two are
; nil when contradictionp is t.

; Some of the possibilities below don't really make sense -- we'd never be
; presented with a Conjunctive rule tau1 consisting of a :pos-evg.  But we
; behave as per the spec above just to keep the interface clean.  The main
; thing to remember is that we need only look for :neg-evgs, :pos-pairs,
; neg-pairs, and :interval bounds of tau1 in the corresponding components of
; tau2.

; Imagine computing the five component-wise near-subsetp answers.  For each
; obtain a signed answer, sign1/temp1, sign2/temp2, etc, where if tempi = t,
; subset holds, if tempi=nil, two or more elements failed to be included, and
; otherwise tempi is the missing element.

; If any tempi is nil, we fail: (mv nil nil nil).  If all are t, we signal
; contradiction: (mv t nil nil).  If exactly one tempi is the missing element
; and other tempi are t, we won: (mv nil signi tempi) for the i that was
; witnessed.  Otherwise, we fail.

; Efficiency considerations: By cascading the (null tempi) checks we avoid even
; computing tempi for those i beyond the first failure.  Furthermore, if any
; tempi is nil, temp4 is nil.  And we don't actually have to remember most
; signi because we know that for temp1 and temp3, the signs are positive (t),
; and for temp2 and temp4, the signs are negative (nil).

  (let* ((temp1 (pos-evg-near-subsetp
                 (access tau tau1 :pos-evg)
                 (access tau tau2 :pos-evg)))
         (temp2 (cond ((null temp1) nil)
                      (t (neg-evgs-near-subsetp
                          (access tau tau1 :neg-evgs)
                          (access tau tau2 :neg-evgs)
                          nil
                          (access tau tau2 :pos-pairs)
                          (access tau tau2 :neg-pairs)
                          (access tau tau2 :interval)
                          ens wrld))))
         (temp3 (cond ((null temp2) nil)
                      (t (tau-pairs-near-subsetp
                          (access tau tau1 :pos-pairs)
                          (access tau tau2 :pos-pairs)
                          nil))))
         (temp4 (cond ((null temp3) nil)
                      (t (tau-pairs-near-subsetp
                          (access tau tau1 :neg-pairs)
                          (access tau tau2 :neg-pairs)
                          nil)))))
; Recall that ``near-subset'' for intervals has a different interface:
    (mv-let
     (sign5 k5 temp5)
     (cond
      ((null temp4) (mv nil nil nil))
      (t (tau-interval-near-subsetp (access tau tau1 :interval)
                                    (access tau tau2 :interval))))

; Observe that if any tempi is nil, temp5 is nil.  If temp5 is not nil and not
; t, then it is either :lessp-x-k or :lessp-k-x and sign5/(k5 . temp5) is the
; single missing, not contradicted, endpoint of the interval in tau2.

     (cond
      ((null temp5) (mv nil nil nil))

; Remember: temp1 and temp3 have positive (t) sign and temp2 and temp4 have
; negative (nil) sign.  Temp5 has sign5.

      (t (if (eq temp1 t)
             (if (eq temp2 t)
                 (if (eq temp3 t)
                     (if (eq temp4 t)
                         (if (eq temp5 t)
                             (mv t nil nil)
                             (mv nil sign5 (cons k5 temp5)))
                         (if (eq temp5 t)
                             (mv nil nil temp4)
                             (mv nil nil nil)))
                     (if (and (eq temp4 t)
                              (eq temp5 t))
                         (mv nil t temp3)
                         (mv nil nil nil)))
                 (if (and (eq temp3 t)
                          (eq temp4 t)
                          (eq temp5 t))
                     (mv nil nil temp2)
                     (mv nil nil nil)))
             (if (and (eq temp2 t)
                      (eq temp3 t)
                      (eq temp4 t)
                      (eq temp5 t))
                 (mv nil t temp1)
                 (mv nil nil nil))))))))

; Here is a test that yields a contradiction (all elements are found).  If you
; change the 25 to a 24, that becomes the missing element.  If you additionally
; change 23 to 22, it fails because there are two missing elements.

; (tau-near-subsetp
;   (mktau nil (not (equal x 23)) (not (equal x 25)) (integerp x))
;   (mktau t (not (equal x 20)) (not (equal x 44)) (integerp x) (evenp x))
;   (ens state) (w state))

; Here there is one missing element, (11 . :lessp-x-k).  If you change the 7 to a 4
; both parts are missing so we fail.   If you add to the (<= 7 x) the additional
; restriction that (<= x 10), we get a contradiction.

; (tau-near-subsetp
;   (mktau nil (<= 5 x) (< x 11))
;   (mktau t (<= 7 x))
;   (ens state) (w state))

; -----------------------------------------------------------------
; On the Tau Database

; We build a database from certain kinds of theorems, as shown below.  In the
; forms shown, p, q, p1, p2, ..., are all understood to be tau recognizers (and
; thus may be (fn x), (EQUAL x 'evg), (< x 'rational), or (< 'rational x),
; and/or their negations.

; Simple:
; (implies (p v) (q v))

; Conjunctive:
; (implies (and (p1 v) (p2 v) ...) (q v))

; Signature [form 1]
; (implies (and (p1 x1) (p2 x2) ...)
;          (q (f x1 x2 ...)))

; Signature [form 2]
; (implies (and (p1 x1) (p2 x2) ...)
;          (q (mv-nth 'n (f x1 x2 ...))))

; Big Switch
; (equal (fn . formals) body), where body is a big switch on some formal.

; MV-NTH Synonym:
; (equal (fn x y) (mv-nth x y))

; The database will maintain the following properties on certain
; function symbols fn.

; property                   value

; tau-pair                   (i . fn), means fn is known to tau database

; tau-pair-saved             (i . fn), means fn has in the past been known
;                                      and will have this index whenever known

; pos-implicants             tau:  for every sign/recog in tau, it is known
;                            that (fn x) --> (sign/recog x)

; neg-implicants             tau: for every sign/recog in tau, it is known
;                            that -(fn x) --> (sign/recog x)

; unevalable-but-known       ((evg . bool) ...): means that
;                            (fn 'evg) = bool, even though fn has
;                            been detected to be unevaluable on 'evg.
;                            This alist is populated from Simple Rule form
;                            theorems proved about fn, i.e.,
;                            (equal x 'evg) --> sign/(fn x).
;
; signature-rules-form-1     (sig-rule1 ... sig-rulen):  see defrec for
;                            signature-rule

; signature-rules-form-2     ((sig-rule1,1 ... sig-rule1,n1)
;                             (sig-rule2,1 ... sig-rule2,n2)
;                             ...)
;                            where each slot corresponds to a slot in
;                            the MV returned by fn and each sig-rule is
;                            as described in defrec signature-rule

; big-switch                 see defrec for big-switch-rule; indicates
;                            that fn is a big switch function

; tau-bounders-form-1        (bc1 ... bcn), a list of tau bounder-correctness
;                            records, all of which have fn as their :subject-fn.

; tau-bounders-form-2        ((bc1,1 ... bc1,n1)
;                             (bc2,1 ... bc2,n2)
;                             ...)
;                             where each slot corresponds to a slot in the
;                             MV returned by fn and each bc is a bounder
;                             correctness record with :subject-fn fn.

; global-value               we use the global-value property of the following
;                            symbol                GLOBAL-VALUE

;                            tau-next-index         n
;                            tau-conjunctive-rules  (conj-rule1 ... conj-rulek),
;                                                   where each conj-rulei is
;                                                   just a tau
;                            tau-runes              (rune1 rune2 ...)
;                            tau-mv-nth-synonyms    (fn1 ... fnk)
;                            tau-lost-runes         (rune1 rune2 ...)

; The first three properties are called ``tau recognizer properties'' and the
; other fn specific properties are called ``tau function properties.''  A
; recognizer symbol may have both kinds of properties, e.g., it may be
; unevalable-but-known and may be a big-switch.

; Closure of Simple Rules under Contraposition and Transitivity

; We now turn to implementing the closure operations.  We close the simple
; rules under contraposition and transitivity.  The function tau-put, given for
; example, (p x) --> (q x), will store it by adding q to the pos-implicants of
; p.  Since q is just a signed tau recognizer and the pos-implicants of p is
; just a tau, tau-put uses add-to-tau1 to store q in the pos-implicants of p.

; The driver and main function of simple rule storage is tau-put*, which (i)
; uses tau-put to handle (p x) --> (q x), then (ii) uses tau-put to handle the
; contrapositive -(q x) --> -(p x), then (iii) calls itself recursively to
; propagate the addition of q to pos-implicants of p, and then (iv) calls
; itself recursively again to propagate the addition of -p to neg-implicants of
; q.

; This note concerns how tau-put handles p-->q, for arbitrary signed tau
; recognizers.  It may update the tau database or not, depending on the
; formula.  It may also signal that a contradiction has been detected.  But
; things may get complicated when p and/or q is either an
; equality-with-constant or one of the two inequalities-with-constants,
; :lessp-x-k or :lessp-k-x.

; For example, x='A --> (p x) usually tells us nothing because (a) if we ever
; compute that a term has the tau {'A} then we will use evaluation to determine
; what other tau predicates it satisfies, and (b) most predicates are evalable
; and so (p 'A) either evaluates to T or to NIL.  So tau-put uses evaluation to
; determine whether there is anything to store.  If (p 'A) computes to T,
; tau-put stores nothing; in the case where it computes to NIL, tau-put signals
; a contradiction.  But there is a third case: x='A --> (p x) could be provable
; but (p 'A) might not be evalable.  In this third case, tau-put would add (p
; 'A) = T to the UNEVALABLE-BUT-KNOWN property of p.

; Tau-put's treatment of p-->q is asymmetric. Even though p-->q and its
; contrapositive, -q-->-p are logically equivalent, we may do something in
; response to the one and do nothing in response to the other.  For example, (p
; x) --> (q x) causes updates to p's pos-implicants and its contrapositive
; causes updates to q's neg-implicants.  But there is only one thing we can
; learn from x='A --> (p x) and that is, at most, that p is unevalable but true
; on 'A.  There is no point in attempting to store that fact for both x='A -->
; (p x) and its contrapositive -(p x) --> x/='A.  So tau-put does not always
; act on every version of every formula.

; To make sure we cover all the cases, we build a table of possibilities and
; describe the appropriate action by tau-put.

; How we build the Tau-Put Table

; We consider all the formulas of the form p-->q, where p and q are any of the
; signed tau recognizers.  For each choice of p and q, we determine what we can
; learn (i.e., store in the database) from the discovery that p-->q is a
; theorem.  To make it easier to think about, we let p take on the following
; four forms (handling both signs explicitly later below).
;
; (p x)    ; p represents some arbitrary monadic Boolean function symbol
; (= x a)  ; = represents EQUAL and a stands for an arbitrary quoted constant
; (< x i)  ; i represents an arbitrary quoted rational constant
; (< i x)  ; i represents an arbitrary quoted rational constant

; Similarly, we let q take on

; (q x)
; (= x b)
; (< x j)
; (< j x)

; where b and j are constants analogous to a and i above.  For each choice of p
; and each choice of q, we will consider

;  p -->  q
;  p --> -q
; -p -->  q
; -p --> -q

; This methodology produces a ``contrapositive variant'' for each formula but
; assures that we cover all the cases.  For example, formulas 1 and 4 of the
; table below are contrapositive variants of each other.  In the table this is
; noted this way:

; 1 ( 4)   (p x) -->  (q x)
; 4 ( 1)  -(p x) --> -(q x)

; because if we take the contrapositive of either and swap the roles of the
; symbols p and q we get the other formula.  More interestingly, formulas 8 and
; 17 are contrapositive variants, where here we also swap the roles of a and b.

; 8 (17)  -(p x) --> -(= x b)
;17 ( 8)   (= x a) -->  (q x)

; The contrapositive variants noted in the table below were mechanically
; identified, so you may assume it is a complete and accurate identification.

; Why is this notion relevant?  First, contrapositives are, of course,
; equivalent formulas.  Furthermore, p, q, a, b, and i, and j merely represent
; arbitrary examples of symbols or terms of certain syntactic classes.  If our
; analysis calls for the same action on a formula as on its contrapositive,
; then there is no point in coding tau-put to recognize and act on both forms.
; So for example, our reaction to formula 8 above is to try to evaluate the
; function symbol bound to the pattern variable P on the constant bound to the
; pattern variable b and if it is unevalable we store the fact that the
; function is unevalable but true on that constant.  This is the same thing
; we'd do on formula 17, where we'd name the function and constant q and a but
; then carry out the same actions.  So we do not do anything on formulas of
; form 17 because we know we will deal with the contrapositive sometime.

; On the other hand, if our analysis calls for different actions on the
; different forms, then the fact that one is the contrapositive variant of
; another is irrelevant.  (Note that 22, 23, 42, 43, 62 and 63 are their own
; contrapositive variants and are marked with ( *).)

; We indicate actions in the table as follows:

; code    action                                                        update?

; S       store the obvious add-to-tau1 into the database              yes
; U       may tell us some fn is unevalable but known                   maybe
; V       violates Non-Constant Non-Equality                            no
; N       no action     (mv Nil nil wrld)                               no
; T       contradiction (mv T   nil wrld)                               no
; W       wait for contrapositive                                       no
; if ...  describes one of two outcomes, either N or T                  no

; Apology: It may seem odd to use N to code for no action (e.g., the formula is
; trivially true) and T to code for contradiction, but those action codes make
; it easier to reconcile the table entries with the code because no action (N)
; is coded as (mv Nil ...) and contradiction (T) is coded as (mv T ...).

; We sometimes use an if in the table.  For example, x=a --> x=b is either
; trivial (N) or contradictory (T), depending on whether constants a and b are
; equal.  But sometimes we use arithmetic inequalities in these tests.  For
; example, x=a --> x < j is trivial if a < j but contradictory otherwise.
; However, when coding these comparisons remember that while i and j are known
; to be rational constants, a and b are not and the proper interpretation of
; ``a<j'' is (< (fix a) j).

; We had to think about some of the actions and so put justifying notes or
; references to proofs or demonstrations of unsatisfiability in brackets.  For
; example,

; 23 ( *)  -(= x a) -->  (= x b)    T [demo: let x=(cons a b)]

; means that the formula is unprovable in a consistent theory, as can be
; demonstrated by proving the negation of an instance:
; (thm (let ((x (cons a b)))
;        (not (implies (not (equal x a)) (equal x b)))))

; Some other lines have notes like ``[pf 5]'' referencing proofs (enumerated by
; the line number of the formula in question) presented at the end of the
; table.  In these demonstrations and proofs, A, B, I, and J are not
; instantiable!  They're constants!

;-----------------------------------------------------------------

; Tau-Put Table of Actions for Storing Simple Tau Rules

;-----------------------------------------------------------------
;  1 ( 4)   (p x) -->  (q x)        S -- add  q to pos-imps p
;  2 ( 2)   (p x) --> -(q x)        S -- add -q to pos-imps p
;  3 ( 3)  -(p x) -->  (q x)        S -- add  q to neg-imps p
;  4 ( 1)  -(p x) --> -(q x)        S -- add -q to neg-imps p

;  5 (20)   (p x) -->  (= x b)      V [pf 5] -- ignore
;  6 (18)   (p x) --> -(= x b)      U -- store if -(p b) unevalable
;  7 (19)  -(p x) -->  (= x b)      V [cf 5] -- ignore
;  8 (17)  -(p x) --> -(= x b)      U -- store if (p b) unevalable

;  9 (36)   (p x) -->  (< x j)      S -- add  (< x j) to pos-imps p
; 10 (34)   (p x) --> -(< x j)      S -- add -(< x j) to pos-imps p
; 11 (35)  -(p x) -->  (< x j)      S -- add  (< x j) to neg-imps p
; 12 (33)  -(p x) --> -(< x j)      S -- add -(< x j) to neg-imps p

; 13 (52)   (p x) -->  (< j x)      S -- add  (< j x) to pos-imps p
; 14 (50)   (p x) --> -(< j x)      S -- add -(< j x) to pos-imps p
; 15 (51)  -(p x) -->  (< j x)      S -- add  (< j x) to neg-imps p
; 16 (49)  -(p x) --> -(< j x)      S -- add -(< j x) to neg-imps p

;-----------------------------------------------------------------
; 17 ( 8)   (= x a) -->  (q x)      W -- wait for ( 8)
; 18 ( 6)   (= x a) --> -(q x)      W -- wait for ( 6)
; 19 ( 7)  -(= x a) -->  (q x)      W -- wait for ( 7)
; 20 ( 5)  -(= x a) --> -(q x)      W -- wait for ( 5)

; 21 (24)   (= x a) -->  (= x b)    if a=b, N else T
; 22 ( *)   (= x a) --> -(= x b)    if a=b, T else N
; 23 ( *)  -(= x a) -->  (= x b)    T [demo: let x=(cons a b)]
; 24 (21)  -(= x a) --> -(= x b)    W -- wait for (21)

; 25 (40)   (= x a) -->  (< x j)    if a<j, N else T
; 26 (38)   (= x a) --> -(< x j)    if j<=a, N else T
; 27 (39)  -(= x a) -->  (< x j)    T [demo: let x = (+ (max a j) 1)]
; 28 (37)  -(= x a) --> -(< x j)    T [demo: let x = (- (min a j) 1)]

; 29 (56)   (= x a) -->  (< j x)    if j<a, N else T
; 30 (54)   (= x a) --> -(< j x)    if a<=j, N else T
; 31 (55)  -(= x a) -->  (< j x)    T [demo: let x = (- (min a j) 1)]
; 32 (53)  -(= x a) --> -(< j x)    T [demo: let x = (+ (max a j) 1)]

;-----------------------------------------------------------------
; 33 (12)   (< x i) -->  (q x)      W -- wait for (12)
; 34 (10)   (< x i) --> -(q x)      W -- wait for (10)
; 35 (11)  -(< x i) -->  (q x)      W -- wait for (11)
; 36 ( 9)  -(< x i) --> -(q x)      W -- wait for ( 9)

; 37 (28)   (< x i) -->  (= x b)    W -- wait for (28)
; 38 (26)   (< x i) --> -(= x b)    W -- wait for (26)
; 39 (27)  -(< x i) -->  (= x b)    W -- wait for (27)
; 40 (25)  -(< x i) --> -(= x b)    W -- wait for (25)

; 41 (44)   (< x i) -->  (< x j)    if i<=j, N else T [pf 41]
; 42 ( *)   (< x i) --> -(< x j)    T [demo: let x = (- (min i j) 1)]
; 43 ( *)  -(< x i) -->  (< x j)    T [demo: let x = (+ (max i j) 1)]
; 44 (41)  -(< x i) --> -(< x j)    W -- wait for (41)

; 45 (60)   (< x i) -->  (< j x)    T [demo: let x = (- (min i j) 1)]
; 46 (58)   (< x i) --> -(< j x)    if i<=j, N else T [pf 46]
; 47 (59)  -(< x i) -->  (< j x)    if j<i, N else T [pf 47]
; 48 (57)  -(< x i) --> -(< j x)    T [demo: let x = (+ (max i j) 1)]

;-----------------------------------------------------------------
; 49 (16)   (< i x) -->  (q x)      W -- wait for (16)
; 50 (14)   (< i x) --> -(q x)      W -- wait for (14)
; 51 (15)  -(< i x) -->  (q x)      W -- wait for (15)
; 52 (13)  -(< i x) --> -(q x)      W -- wait for (13)

; 53 (32)   (< i x) -->  (= x b)    W -- wait for (32)
; 54 (30)   (< i x) --> -(= x b)    W -- wait for (30)
; 55 (31)  -(< i x) -->  (= x b)    W -- wait for (31)
; 56 (29)  -(< i x) --> -(= x b)    W -- wait for (29)

; 57 (48)   (< i x) -->  (< x j)    W -- wait for (48)
; 58 (46)   (< i x) --> -(< x j)    W -- wait for (46)
; 59 (47)  -(< i x) -->  (< x j)    W -- wait for (47)
; 60 (45)  -(< i x) --> -(< x j)    W -- wait for (45)

; 61 (64)   (< i x) -->  (< j x)    if j<=i, N else T [pf 61]
; 62 ( *)   (< i x) --> -(< j x)    T [demo: let x = (+ (max i j) 1)]
; 63 ( *)  -(< i x) -->  (< j x)    T [demo: let x = (- (min i j) 1)]
; 64 (61)  -(< i x) --> -(< j x)    W -- wait for (61)
;-----------------------------------------------------------------

; Proofs cited above:

; First,
; (include-book "arithmetic-5/top" :dir :system)
; (tau-status :system nil)

; Proof 5:  We prove that if formula 5, (p x) -->  (= x b), is a theorem
; then p is either a constant function or an equality with a constant.

; We assume p and b are constrained as in formula 5 and prove

; [forall x1 : (p x1) = nil] or [forall x2 : (p x2) = (equal x2 (b))].

; (encapsulate ((p (x) t)
;               (b () t))
;   (local (defun p (x) (declare (ignore x)) nil))
;   (local (defun b () nil))
;   (defthm booleanp-p (booleanp (p x)) :rule-classes :type-prescription)
;   (defthm formula-5 (implies (p x) (equal x (b)))
;     :rule-classes nil))

; (defstub x1 () t)
; (defstub x2 () t)

; (thm (or (equal (p (x1)) nil)
;          (equal (p (x2)) (equal (x2) (b))))
;      :hints (("Goal" :use ((:instance formula-5 (x (x1)))
;                            (:instance formula-5 (x (x2)))))))

; (ubt! 3)

; Proof 41: We prove that 41 is a theorem iff i<=j is a theorem.
; Case: thm 41 |= i<=j:
; (thm (implies (let ((x (+ j (/ (- i j) 2))))
;                 (implies (< x i) (< x j)))
;               (<= i j)))
; Case: i<=j |= thm 41:
; (thm (implies (<= i j)
;               (implies (< x i) (< x j))))

; Proof 46: We prove that 46 is a theorem iff i<=j is a theorem.
; Case: thm 46 |= i<=j:
; (thm (implies (let ((x (+ i (/ (- j i) 2))))
;                 (implies (< x i) (not (< j x))))
;               (<= i j)))
; Case: i<=j |= thm 46:
; (thm (implies (<= i j)
;               (implies (< x i) (not (< j x)))))

; Proof 47: We prove that 47 is a theorem iff j<i is a theorem.
; Case: thm 47 |= j<i:
; (thm (implies (let ((x (+ i (/ (- j i) 2))))
;                 (implies (not (< x i)) (< j x)))
;               (< j i)))
;
; Case: j<=i |= thm 47:
; (thm (implies (< j i)
;               (implies (not (< x i)) (< j x))))

; Proof 61: We prove that 61 is a theorem iff j<=i is a theorem.
; Case: thm 61 |= j<=i:
; (thm (implies (let ((x (+ j (/ (- i j) 2))))
;                 (implies (< i x) (< j x)))
;               (<= j i)))
; Case: j<=i |= thm 61:
; (thm (implies (<= j i)
;               (implies (< i x) (< j x))))

; -----------------------------------------------------------------

; A coding question: The table above guides our coding of tau-put below.  But
; when we say ``signal contradiction'' we mean we are logically justified in
; signaling a contradiction.  We are also logically justified in just ignoring
; the situation: if the theory is inconsistent, it is still sound to not report
; it!  For example, consider lines 21--24.

; 21 (24)   (= x a) -->  (= x b)    if a=b, N else T
; 22 ( *)   (= x a) --> -(= x b)    if a=b, T else N
; 23 ( *)  -(= x a) -->  (= x b)    T [demo: let x=(cons a b)]
; 24 (21)  -(= x a) --> -(= x b)    W -- wait for (21)

; We get to these lines if both p and q are signed equalities -- conditions we
; check by observing that (cdr p-recog) and (cdr q-recog) are both nil.  Lines
; 21 and 22 would have us test whether the two constant arguments of the
; equalities are equal, and either do nothing or signal a contradiction.  Line
; 23 would have us signal a contradiction.  And line 24 would have us do
; nothing.  To determine which action to take, we have to test the signs and
; the constants.  But just doing nothing in all four cases is sound and faster.
; On the other hand, the situation will probably never arise since the user is
; not likely to prove any formula of these forms so the efficiency is of little
; concern.  Really, how likely is it that we'll see theorems like (implies
; (equal x 23) (equal x 27)) or (implies (equal x 23) (equal x 23)) proved as
; rules?

; Is the danger of bugs in our code worth the extra robustness of testing for
; explicit contradictions?

; After some consideration of this issue, we decided to code the table
; precisely, if only to document the analysis and make the case analysis
; uniform.

; Now, regarding the order in which we enumerate the cases.  The table suggests
; that we look first for recognizer function applications, then equalities,
; then the two inequalities.  But recall the concrete representation of tau
; recognizers as shown in tau-like-term and consider programming the necessary
; tests.  Efficiency suggests we test for equality first, then the two
; inequalities, and handle function applications as the final case.  The basic
; decoding of a concrete tau recognizer, recog, is as follows:

; Tests in order tried          term represented by recog     evg var name

; (eq (cdr recog) nil)         `(EQUAL X ',(car recog))       a or b
; (eq (cdr recog) :lessp-x-k)  `(< X ',(car recog))           i or j
; (eq (cdr recog) :lessp-k-x)  `(< ',(car recog) X)           i or j
; otherwise                    `(,(cdr recog) X)              p or q

; Note that as we try the tests we bind variables a, b, i, and j to the
; corresponding evgs and we bind p and q to the corresponding function symbols
; to make our code match the names used in our table.

; Note: while our table shows ``terms'' like (= x a) the corresponding term is
; `(EQUAL x ',a).  That is the variable a in our code corresponds to the evg of
; quoted constant denoted by a in our table.

(defun tau-put (p-sign p-recog q-sign q-recog ens wrld)

; Each of p-recog and q-recog is a concrete tau recognizer with the
; corresponding sign.

; Think of the two signs and two recognizers as representing signed recognizers
; p and q.  This function is called on every simple tau rule, p --> q.  It will
; also be called on the contrapositive.  We implement the actions listed in the
; Tau-Put Table and we reproduce lines from that table to document what we're
; doing.  We test the cases on p and then on q in the order tried above, thus
; first considering (EQUAL x ...), then (< x ...), then (< ... x), and finally
; (fn x).

; We return (mv contradictionp changedp wrld') and this is a No-Change Loser on
; wrld.

; The actions recorded in the table and their implementations are:
; S   store stuff?         (mv contradictionp changedp wrld') -- as appropriate
; U   unevalable?          (mv contradictionp changedp wrld') -- as appropriate
; V   violation            (mv nil nil wrld)
; N   no action            (mv nil nil wrld)
; T   signal contradiction (mv t   nil wrld)
; W   wait -- ignore       (mv nil nil wrld)
; T   contradiction        (mv t   nil wrld)

  (let ((p-discriminator (cdr p-recog)))
    (cond
     ((eq p-discriminator nil)
      (let ((a (car p-recog)) ; p-recog represents (EQUAL x 'a)
            (q-discriminator (cdr q-recog)))
        (cond
         ((eq q-discriminator nil)
          (let ((b (car q-recog)))

; 21 (24)   (= x a) -->  (= x b)    if a=b, N else T
; 22 ( *)   (= x a) --> -(= x b)    if a=b, T else N
; 23 ( *)  -(= x a) -->  (= x b)    T [demo: let x=(cons a b)]
; 24 (21)  -(= x a) --> -(= x b)    W -- wait for (21)

            (if p-sign
                (if q-sign
                    (mv (if (equal a b) nil t) nil wrld)
                    (mv (if (equal a b) t nil) nil wrld))
                (if q-sign
                    (mv t   nil wrld)
                    (mv nil nil wrld)))))
         ((eq q-discriminator :lessp-x-k)
          (let ((j (car q-recog)))

; 25 (40)   (= x a) -->  (< x j)    if a<j, N else T
; 26 (38)   (= x a) --> -(< x j)    if j<=a, N else T
; 27 (39)  -(= x a) -->  (< x j)    T [demo: let x = (+ (max a j) 1)]
; 28 (37)  -(= x a) --> -(< x j)    T [demo: let x = (- (min a j) 1)]

            (if p-sign
                (if q-sign
                    (mv (if (< (fix a) j) nil t) nil wrld)
                    (mv (if (<= j (fix a)) nil t) nil wrld))
                (mv t nil wrld))))
         ((eq q-discriminator :lessp-k-x)
          (let ((j (car q-recog)))

; 29 (56)   (= x a) -->  (< j x)    if j<a, N else T
; 30 (54)   (= x a) --> -(< j x)    if a<=j, N else T
; 31 (55)  -(= x a) -->  (< j x)    T [demo: let x = (- (min a j) 1)]
; 32 (53)  -(= x a) --> -(< j x)    T [demo: let x = (+ (max a j) 1)]

            (if p-sign
                (if q-sign
                    (mv (if (< j (fix a)) nil t) nil wrld)
                    (mv (if (<= (fix a) j) nil t) nil wrld))
                (mv t nil wrld))))
         (t
;       (let ((q q-discriminator))

; 17 ( 8)   (= x a) -->  (q x)      W -- wait for ( 8)
; 18 ( 6)   (= x a) --> -(q x)      W -- wait for ( 6)
; 19 ( 7)  -(= x a) -->  (q x)      W -- wait for ( 7)
; 20 ( 5)  -(= x a) --> -(q x)      W -- wait for ( 5)

          (mv nil nil wrld) ;)
          ))))

     ((eq p-discriminator :lessp-x-k)
      (let ((i (car p-recog)) ; p-recog represents (< x i)
            (q-discriminator (cdr q-recog)))
        (cond
         ((eq q-discriminator nil)
;       (let ((b (car q-recog)))

; 37 (28)   (< x i) -->  (= x b)    W -- wait for (28)
; 38 (26)   (< x i) --> -(= x b)    W -- wait for (26)
; 39 (27)  -(< x i) -->  (= x b)    W -- wait for (27)
; 40 (25)  -(< x i) --> -(= x b)    W -- wait for (25)

          (mv nil nil wrld) ;)
          )
         ((eq q-discriminator :lessp-x-k)
          (let ((j (car q-recog)))

; 41 (44)   (< x i) -->  (< x j)    if i<=j, N else T [pf 41]
; 42 ( *)   (< x i) --> -(< x j)    T [demo: let x = (- (min i j) 1)]
; 43 ( *)  -(< x i) -->  (< x j)    T [demo: let x = (+ (max i j) 1)]
; 44 (41)  -(< x i) --> -(< x j)    W -- wait for (41)

            (if p-sign
                (if q-sign
                    (mv (if (<= i j) nil t) nil wrld)
                    (mv t nil wrld))
                (if q-sign
                    (mv t nil wrld)
                    (mv nil nil wrld)))))
         ((eq q-discriminator :lessp-k-x)
          (let ((j (car q-recog)))

; 45 (60)   (< x i) -->  (< j x)    T [demo: let x = (- (min i j) 1)]
; 46 (58)   (< x i) --> -(< j x)    if i<=j, N else T [pf 46]
; 47 (59)  -(< x i) -->  (< j x)    if j<i, N else T [pf 47]
; 48 (57)  -(< x i) --> -(< j x)    T [demo: let x = (+ (max i j) 1)]

            (if p-sign
                (if q-sign
                    (mv t nil wrld)
                    (mv (if (<= i j) nil t) nil wrld))
                (if q-sign
                    (mv (if (< j i) nil t) nil wrld)
                    (mv t nil wrld)))))
         (t
;       (let ((q q-discriminator))

; 33 (12)   (< x i) -->  (q x)      W -- wait for (12)
; 34 (10)   (< x i) --> -(q x)      W -- wait for (10)
; 35 (11)  -(< x i) -->  (q x)      W -- wait for (11)
; 36 ( 9)  -(< x i) --> -(q x)      W -- wait for ( 9)

          (mv nil nil wrld) ;)
          ))))

     ((eq p-discriminator :lessp-k-x)
      (let ((i (car p-recog)) ; p-recog represents (< i x)
            (q-discriminator (cdr q-recog)))
        (cond
         ((eq q-discriminator nil)
;       (let ((b (car q-recog)))

; 53 (32)   (< i x) -->  (= x b)    W -- wait for (32)
; 54 (30)   (< i x) --> -(= x b)    W -- wait for (30)
; 55 (31)  -(< i x) -->  (= x b)    W -- wait for (31)
; 56 (29)  -(< i x) --> -(= x b)    W -- wait for (29)

          (mv nil nil wrld) ;)
          )
         ((eq q-discriminator :lessp-x-k)
;       (let ((j (car q-recog)))

; 57 (48)   (< i x) -->  (< x j)    W -- wait for (48)
; 58 (46)   (< i x) --> -(< x j)    W -- wait for (46)
; 59 (47)  -(< i x) -->  (< x j)    W -- wait for (47)
; 60 (45)  -(< i x) --> -(< x j)    W -- wait for (45)

          (mv nil nil wrld) ;)
          )
         ((eq q-discriminator :lessp-k-x)
          (let ((j (car q-recog)))

; 61 (64)   (< i x) -->  (< j x)    if j<=i, N else T [pf 61]
; 62 ( *)   (< i x) --> -(< j x)    T [demo: let x = (+ (max i j) 1)]
; 63 ( *)  -(< i x) -->  (< j x)    T [demo: let x = (- (min i j) 1)]
; 64 (61)  -(< i x) --> -(< j x)    W -- wait for (61)

            (if p-sign
                (if q-sign
                    (mv (if (<= j i) nil t) nil wrld)
                    (mv t nil wrld))
                (if q-sign
                    (mv t nil wrld)
                    (mv nil nil wrld)))))
         (t
;       (let ((q q-discriminator))

; 49 (16)   (< i x) -->  (q x)      W -- wait for (16)
; 50 (14)   (< i x) --> -(q x)      W -- wait for (14)
; 51 (15)  -(< i x) -->  (q x)      W -- wait for (15)
; 52 (13)  -(< i x) --> -(q x)      W -- wait for (13)

          (mv nil nil wrld) ;)
          ))))

     (t
      (let ((p p-discriminator) ; p-recog represents (p x)
            (q-discriminator (cdr q-recog)))
        (cond
         ((eq q-discriminator nil)
          (let ((b (car q-recog)))

;  5 (20)   (p x) -->  (= x b)      V [pf 5] -- ignore
;  6 (18)   (p x) --> -(= x b)      U -- store if -(p b) unevalable
;  7 (19)  -(p x) -->  (= x b)      V [cf 5] -- ignore
;  8 (17)  -(p x) --> -(= x b)      U -- store if (p b) unevalable

            (if p-sign
                (if q-sign
                    (mv nil nil wrld)

; Recall: q-recog here is (b), a singleton list containing b.  Formula 6 is
; equivalent to x=b --> -(p x).  The code below for handling line 6 could be
; easily combined with the code for handling line 8.  But that would break the
; correspondence between lines of the table and if-then-else clauses here.

                    (let ((val (ev-fncall-w-tau-recog p q-recog ens wrld)))
                      (cond
                       ((eq val :UNEVALABLE)
                        (mv nil t
                            (putprop p
                                     'unevalable-but-known
                                     (cons (cons b nil) ; records that (p 'b) = nil
                                           (getpropc p
                                                     'unevalable-but-known
                                                     nil
                                                     wrld))
                                     wrld)))
                       ((eq val nil)
                        (mv nil nil wrld))
                       (t (mv t nil wrld)))))
                (if q-sign
                    (mv nil nil wrld)
                    (let ((val (ev-fncall-w-tau-recog p q-recog ens wrld)))
                      (cond
                       ((eq val :UNEVALABLE)
                        (mv nil t
                            (putprop p
                                     'unevalable-but-known
                                     (cons (cons b t) ; records that (p 'b) = t
                                           (getpropc p
                                                     'unevalable-but-known
                                                     nil
                                                     wrld))
                                     wrld)))
                       ((eq val nil)
                        (mv t nil wrld))
                       (t (mv nil nil wrld))))))))

         (t

; Else, q is an inequality or function application and we do the
; same thing on all of them.

;  9 (36)   (p x) -->  (< x j)      S -- add  (< x j) to pos-imps p
; 10 (34)   (p x) --> -(< x j)      S -- add -(< x j) to pos-imps p
; 11 (35)  -(p x) -->  (< x j)      S -- add  (< x j) to neg-imps p
; 12 (33)  -(p x) --> -(< x j)      S -- add -(< x j) to neg-imps p

; 13 (52)   (p x) -->  (< j x)      S -- add  (< j x) to pos-imps p
; 14 (50)   (p x) --> -(< j x)      S -- add -(< j x) to pos-imps p
; 15 (51)  -(p x) -->  (< j x)      S -- add  (< j x) to neg-imps p
; 16 (49)  -(p x) --> -(< j x)      S -- add -(< j x) to neg-imps P

;  1 ( 4)   (p x) -->  (q x)        S -- add  q to pos-imps p
;  2 ( 2)   (p x) --> -(q x)        S -- add -q to pos-imps p
;  3 ( 3)  -(p x) -->  (q x)        S -- add  q to neg-imps p
;  4 ( 1)  -(p x) --> -(q x)        S -- add -q to neg-imps p

          (let* ((old-tau
                  (tau-simple-implicants p-sign p-discriminator wrld))
                 (new-tau
                  (add-to-tau1 q-sign q-recog old-tau ens wrld)))
            (cond
             ((eq new-tau *tau-contradiction*)
              (mv t
                  t
                  (putprop p-discriminator
                           (if p-sign 'pos-implicants 'neg-implicants)
                           *contradictory-tau*
                           wrld)))
             ((equal old-tau new-tau)
              (mv nil nil wrld))
             (t (mv nil
                    t
                    (putprop p-discriminator
                             (if p-sign 'pos-implicants 'neg-implicants)
                             new-tau
                             wrld))))))))))))

(mutual-recursion

(defun tau-put* (p-sign p-recog q-sign q-recog ens wrld)

; Let p be p-sign/p-recog and q be q-sign/q-recog.  We store q as an implicant
; of p, then store the contrapositive version, and then close both additions
; under transitivity.  More precisely, we first do two simple stores: q as an
; implicant of p, followed by NOT/p as an implicant of NOT/q.  Then, for every
; element, r, of the implicants of q, we store r as an implicant of p.  Then,
; for every element, r, of the implicants of NOT/p, we store r as an implicant
; of NOT/q.  We return (mv contradictionp changedp wrld').  Wrld' is always
; either wrld unchanged (changedp=nil) or wrld extended appropriately.

; Note: It is possible for p-->q NOT to change the world but for -q --> -p to
; change the world.  For example, (x=2) --> (evenp x) does nothing, but -(evenp
; x) --> (x /= 2) adds the inequality to the implicants of not/evenp.
; (Remember, we are storing a user-supplied theorem to that effect.)

  (mv-let
   (contradictionp changedp1 wrld)
   (tau-put p-sign p-recog q-sign q-recog ens wrld)
   (cond
    (contradictionp (mv t nil wrld))
    (t
     (mv-let
      (contradictionp changedp2 wrld)
      (tau-put (not q-sign) q-recog (not p-sign) p-recog ens wrld)
      (cond
       (contradictionp (mv t (or changedp1 changedp2) wrld))
       ((and (not changedp1) (not changedp2))
        (mv nil nil wrld))

; At this point we know something changed, so we pursue the implicants.  But it
; could be that we can avoid one implicant chase or the other due to the
; no-change flags.  But every exit from this function below will indicate that
; wrld has changed because it changed above.

       (t
        (let ((q-discriminator (cdr q-recog)))
          (mv-let
           (contradictionp changedp wrld)
           (if (and changedp1
                    q-discriminator
                    (not (eq q-discriminator :lessp-k-x))
                    (not (eq q-discriminator :lessp-x-k)))

; q is a function call and we added q to the implicants of p.  So we have to
; add all the implicants of q to the implicants of p.  However, if adding q to
; the implicants of p didn't really change p (and provided the database was
; already closed), then we don't have to do anything.  Also, if q-recog is not
; a tau-pair but is a singleton evg list, we don't chase it's implicants.

               (tau-put*-tau
                p-sign p-recog
                (tau-simple-implicants q-sign q-discriminator wrld)
                ens wrld)
               (mv nil t wrld))
           (declare (ignore changedp)) ; always t!
           (let ((p-discriminator (cdr p-recog)))
             (cond
              (contradictionp (mv t t wrld))
              ((and changedp2
                    p-discriminator
                    (not (eq p-discriminator :lessp-k-x))
                    (not (eq p-discriminator :lessp-x-k)))

; This is the symmetric case, which we do only if we really changed the
; implicants of q and p is function call.

               (tau-put*-tau
                (not q-sign) q-recog
                (tau-simple-implicants (not p-sign) p-discriminator wrld)
                ens wrld))
              (t (mv nil t wrld)))))))))))))

(defun tau-put*-tau (p-sign p-recog tau ens wrld)

; We map over every r-sign/r-recog in tau and do

; (tau-put* p-sign p-recog r-sign r-recog ...).

; Technically we return (mv contradictionp changedp wrld').  But actually the
; returned changedp flag is always t and we don't bother keeping track of that
; because we don't call this function except when the input wrld has changed.

; While abstractly tau is a set of recognizers that we might map over,
; concretely it is a tau with five quite different components: pos-evg,
; neg-evgs, pos-pairs, neg-pairs, and an interval.  It is clear how to map over
; the two -pairs.  But is there any point in mapping over the others?  Yes!
; For example, consider pos-evg.  Adding that to p-sign/p-recog could have
; wonderful effects.  More likely, adding each of the neg-evgs could populate
; unevalable-but-known fields.  Thus, we really do map over every part of tau.

  (mv-let
   (contradictionp changedp wrld)
   (if (access tau tau :pos-evg)
       (tau-put* p-sign p-recog t (access tau tau :pos-evg)
                 ens wrld)
       (mv nil t wrld))
   (declare (ignore changedp)) ; always t
   (cond
    (contradictionp (mv t t wrld))
    (t
     (mv-let
      (contradictionp changedp wrld)
      (tau-put*-recogs p-sign p-recog
                       nil
                       (access tau tau :neg-evgs)
                       ens wrld)
      (declare (ignore changedp)) ; always t
      (cond
       (contradictionp (mv t t wrld))
       (t
        (mv-let
         (contradictionp changedp wrld)
         (tau-put*-recogs p-sign p-recog
                          t
                          (access tau tau :pos-pairs)
                          ens wrld)
         (declare (ignore changedp))
         (cond
          (contradictionp (mv t t wrld))
          (t
           (mv-let
            (contradictionp changedp wrld)
            (tau-put*-recogs p-sign p-recog
                             nil
                             (access tau tau :neg-pairs)
                             ens wrld)
            (declare (ignore changedp))
            (cond
             (contradictionp (mv t t wrld))
             (t (tau-put*-interval-endpoints
                 p-sign p-recog
                 (access tau tau :interval)
                 ens wrld))))))))))))))

(defun tau-put*-interval-endpoints (p-sign p-recog r-interval ens wrld)

; We store the implication from p-sign/p-recog to the endpoints of r-interval
; and return (mv contradictionp changedp wrld), except changedp is always t
; because we know the world changed before we called this function.

  (cond
   ((null r-interval)
    (mv nil t wrld))
   (t (mv-let
       (lo-sign lo-recog)
       (if (access tau-interval r-interval :lo)
           (mv-let
            (sign k token)
            (tau-interval-endpoint-to-sign-k-token
             nil ; upper-boundp
             (access tau-interval r-interval :lo-rel)
             (access tau-interval r-interval :lo))
            (mv sign (cons k token)))
           (mv nil nil))
       (mv-let
        (hi-sign hi-recog)
        (if (access tau-interval r-interval :hi)
            (mv-let
             (sign k token)
             (tau-interval-endpoint-to-sign-k-token
              t ; upper-boundp
              (access tau-interval r-interval :hi-rel)
              (access tau-interval r-interval :hi))
             (mv sign (cons k token)))
            (mv nil nil))
        (if lo-recog
            (mv-let (contradictionp changedp wrld)
                    (tau-put* p-sign p-recog lo-sign lo-recog ens wrld)
                    (declare (ignore changedp))
                    (cond
                     (contradictionp (mv t t wrld))
                     (t (if hi-recog
                            (tau-put* p-sign p-recog hi-sign hi-recog ens wrld)
                            (mv nil t wrld)))))
            (if hi-recog
                (tau-put* p-sign p-recog hi-sign hi-recog ens wrld)
                (mv nil t wrld))))))))

(defun tau-put*-recogs (p-sign p-recog r-sign r-recogs ens wrld)

; In our usage of this function r-recogs is always either a list of tau-pairs
; (namely, :pos-pairs or :neg-pairs) or a list of singleton evg lists
; (:neg-evgs).  But in any case, each element of r-recogs is the atom
; of a recognizer.  The sign of all the atoms in r-recogs is r-sign.

; For every r-sign/r-recog in r-sign/r-recogs (slight abuse of notation), we

; (tau-put* p-sign p-recog r-sign r-recog ...).

; We return (mv contradictionp changedp wrld), but in fact changedp is always
; t as explained in tau-put*-tau.


  (cond
   ((endp r-recogs) (mv nil t wrld))
   (t (mv-let
       (contradictionp changedp wrld)
       (tau-put* p-sign p-recog r-sign (car r-recogs) ens wrld)
       (declare (ignore changedp))
       (cond
        (contradictionp (mv t t wrld))
        (t (tau-put*-recogs p-sign p-recog r-sign (cdr r-recogs) ens wrld)))))))

)

; On Closing the Database under Conjunctive Rules

; At one point we considered closing the database under the conjunctive rules,
; in so far as we could.  We knew that we had to keep conjunctive rules around
; anyway and use them at query time because at query time we are given a list
; of knowns and must consider what the conjunctive rules tell us about that
; particular combination of recognizers.  But it seemed like possibly a good
; idea to also use the rules on the database itself.  But that is very
; complicated.  Suppose we have a db closed under everything (including
; conjunctive rules).  Then we add p-->q.  This will touch the implicants of p
; (to add q and all the things q implies), -q (to add -p and all the things -p
; implies), and for every r in the implicants of q, -r (to add -p), and for
; every s in the implicants of -p, -s (to add q), and so on.  Every one of
; those implicant lists has to be closed again under conjunctive rules.  So we
; would need to track all the recs we change, not just whether we changed
; anything.

; Furthermore, if a conjunctive rule is added, we have to close every implicant
; list in the world again.

; Finally, how common will it be for the user to have told us that (a & b) -->
; c, and then told us that p --> a and p --> b?  Certainly it will happen,
; e.g., if p is added after the primitive types a, b, and c, have been defined.

; It turns out that this happens a lot.  For example, in the Rockwell benchmark
; used to test early versions of this (in which all :type-prescription and
; :forward-chaining rules were interpreted as :tau-system rules) we mapped over
; all the tau recognizers and asked how often does a conjunctive rule fire on
; the implicants (positive and negative).  The answer was that of 11,940
; implicants stored in the database, 4,640 of them could be extended with
; conjunctive rules.

; -----------------------------------------------------------------
; On Converting Theorems in the World to Tau Rules

; We populate the database by processing certain theorems.  However, we do
; this both when an event is first processed (in install-event) and also when
; the tau database is regenerated (regenerate-tau-database).  We call this
; ``visiting'' the event; obviously, there is a first visit.  That is,
; sometimes when we visit an event we've already processed it once.

; Recall also that theorems are added to the tau database either because they
; are explicitly labeled :tau-system rules or because we are in automatic mode
; and the theorems are of the appropriate form.  This is also done when we
; visit an event, rather than in the core code for each event.  This is a
; deliberate design decision to bring all the tau database updates into one
; place so we can implement regenerate-tau-database more robustly.

; The following code deals with recognizing the shapes of theorems that can be
; represented as tau rules and adding those rules to the database.  We
; ultimately define the function for visiting an event (tuple) and adding its
; rules.

; Tau Boolean rules tell us that a function symbol is a monadic Boolean and
; thus should be tracked by the tau system.  These rules cause the function
; symbol to get a tau-pair and cause its pos- and neg-implicants to be
; appropriately set.  However, when in automatic mode, tau also automatically
; recognize monadic Boolean functions introduced by defun (or
; mutual-recursion).  For that reason, we first define the function that visits
; a function symbol after its introduction and sets up its tau properties.
; We'll then use that function to add Boolean tau rules.

(defconst *non-tau-monadic-boolean-functions*
  '(NOT DEBUGGER-ENABLEDP))

#+:non-standard-analysis
(defun classicalp (fn wrld)

; WARNING: This function is expected to return t for fn = :?, in support of
; measures (:? v1 ... vk), since classicalp is called by
; get-non-classical-fns-from-list in support of get-non-classical-fns-aux.

  (getpropc fn 'classicalp

; We guarantee a 'classicalp property of nil for all non-classical
; functions.  We make no claims about the existence of a 'classicalp
; property for classical functions; in fact, as of Version_2.5 our
; intention is to put no 'classicalp property for classical functions.

           t wrld))

;; Historical Comment from Ruben Gamboa:
;; This function tests whether a list of names is made up purely
;; of classical function names (i.e., not descended from the
;; non-standard function symbols)

#+:non-standard-analysis
(defun classical-fn-list-p (names wrld)
  (cond ((null names) t)
        ((not (classicalp (car names) wrld))
         nil)
        (t (classical-fn-list-p (cdr names) wrld))))

(defun monadic-boolean-fnp (fn ens wrld)

; Fn is known to be a function symbol.  We return (mv t ttree) if fn is a
; monadic Boolean function and (mv nil nil) otherwise.  Ttree is from the proof
; that fn is Boolean.

  (cond ((and

; We exclude all non-classical functions from consideration by tau.  It is not clear
; that this is necessary but it's a safe thing to do until we've thought more about it.

          #+:non-standard-analysis
          (classicalp fn wrld)

          (equal (arity fn wrld) 1)
          (member-eq (symbol-class fn wrld)
                     '(:ideal :common-lisp-compliant))
          (not
           (member-eq fn *non-tau-monadic-boolean-functions*)))

         (mv-let (ts ttree)
                 (type-set (fcons-term* fn '(V)) nil nil nil
                           ens wrld
                           nil nil nil)

; The type-set check below intentionally rejects the constant T and constant
; NIL functions.

                 (cond ((ts= ts *ts-boolean*)
                        (mv t ttree))
                       (t (mv nil nil)))))
        (t (mv nil nil))))

(defun putprop-if-different (sym prop val wrld)

; Wrld must be the ACL2 logical world, not some user-defined world.  We store
; val as the property prop of sym unless it is already stored there.

; The following theorem (proved after calling verify-termination on the two
; putprop-xxx functions) specifies the relationship between this function and
; putprop-unless.

;   (thm (equal (putprop-if-different sym prop val wrld)
;               (let ((exception (getpropc sym prop *acl2-property-unbound*
;                                          wrld)))
;                 (putprop-unless sym prop val exception wrld))))

  (if (equal (getpropc sym prop *acl2-property-unbound* wrld)
             val)
      wrld
      (putprop sym prop val wrld)))

(defun tau-visit-function-introduction (fn wrld)

; This function makes fn almost virgin wrt to the tau system.  Those functions
; in *primitive-monadic-booleans* as explained below.  For all other functions
; fn, the only tau property of fn that is preserved is its tau-pair-saved
; property (if any), which is the tau-pair fn will be assigned if it is ever
; again classified as a tau recognizer.

; This function is called when we are regenerating the tau database by
; scanning the world and we encounter a function introduction, i.e., a FORMALs
; property.  But the monadic primitives, like CONSP and SYMBOLP, are known to
; be Boolean and are so initialized when we begin regenerating the world, in an
; imitation of what happens during boot-strap.  We do not want our encounter
; with their subsequent FORMALS binding to erase those tau properties.

  (cond
   ((member-eq fn *primitive-monadic-booleans*)
    wrld)
   (t (putprop-if-different
       fn 'TAU-PAIR *acl2-property-unbound*
       (putprop-if-different
        fn 'TAU-POS-IMPLICANTS *acl2-property-unbound*
        (putprop-if-different
         fn 'TAU-NEG-IMPLICANTS *acl2-property-unbound*
         (putprop-if-different
          fn 'UNEVALABLE-BUT-KNOWN *acl2-property-unbound*
          (putprop-if-different
           fn 'SIGNATURE-RULES-FORM-1 *acl2-property-unbound*
           (putprop-if-different
            fn 'SIGNATURE-RULES-FORM-2 *acl2-property-unbound*
            (putprop-if-different
             fn 'BIG-SWITCH *acl2-property-unbound*
             wrld))))))))))

(defun tau-visit-function-introductions (fns wrld)
  (cond ((endp fns) wrld)
        (t (tau-visit-function-introductions
            (cdr fns)
            (tau-visit-function-introduction (car fns) wrld)))))

(defun putprop-tau-pair (fn wrld)

; Assign and store a ``new'' tau-pair to fn, updating the global value of
; tau-next-index as necessary.  We return the updated world.

; However, if fn has ever had a tau-pair, we re-assign the same pair to it.
; This is an attempt to minimize the differences between regenerations of tau
; databases under different enabled structures.

  (let ((old-pair (getpropc fn 'tau-pair-saved nil wrld)))
    (if old-pair
        (putprop fn 'tau-pair old-pair wrld)
        (let* ((nexti (global-val 'tau-next-index wrld))
               (new-pair (cons nexti fn)))
          (putprop fn 'tau-pair new-pair
                   (putprop fn 'tau-pair-saved new-pair
                            (global-set 'tau-next-index (+ 1 nexti) wrld)))))))

(defun initialize-tau-pred (fn wrld)

; Fn is known to be a monadic Boolean function symbol.  We initialize the tau
; properties of fn as a monadic Boolean, i.e., give it a tau-pair and set up
; its pos- and neg-implicants.  It is assumed that all of fn's tau properties
; have previously been cleared.  We considered adding the appropriate :domain
; for the intervals associated with the arithmetic primitive monadic Booleans
; (cf.  *primitive-monadic-booleans*) upon which this is called.  For example,
; when fn is INTEGERP we could add an unrestricted interval over that :domain.
; But we don't see any point because the :domain of the interval is irrelevant
; for anything except local bounds adjustments.  When the pos-implicants of
; INTEGERP are added to some tau, the addition of the tau-pair for INTEGERP
; will trigger the setting of the :domain in that new tau; the setting of the
; :domain in the :pos-implicants is ignored.

  (let* ((wrld1 (putprop-tau-pair fn wrld))
         (tau-pair (getpropc fn 'tau-pair nil wrld1))
         (wrld2 (putprop fn 'pos-implicants
                         (make tau
                               :pos-evg nil
                               :neg-evgs nil
                               :pos-pairs (list tau-pair)
                               :neg-pairs nil
                               :interval nil)
                         wrld1))
         (wrld3 (putprop fn 'neg-implicants
                         (make tau
                               :pos-evg nil
                               :neg-evgs nil
                               :pos-pairs nil
                               :neg-pairs (list tau-pair)
                               :interval nil)
                         wrld2)))
    wrld3))

(defun initialize-tau-preds (fns wrld)
  (cond ((endp fns) wrld)
        (t (initialize-tau-preds (cdr fns)
                                 (initialize-tau-pred (car fns) wrld)))))

(defun tau-boolean-formp (hyps concl wrld)

; We return t or nil to indicate whether (IMPLIES (AND . hyps) concl) is of the
; form (booleanp (f v)), where f is a function symbol and v is a variable
; symbol.  Hyps is a list of translated terms and concl is a translated term
; (so it suffices to check merely that f and v are symbols).

  (declare (ignore wrld))
  (and (null hyps)
       (case-match concl
         (('BOOLEANP (f v))
          (and (symbolp f)
               (symbolp v)))
         (& nil))))

(defun tau-eval-formp (hyps concl wrld)
  (and (null hyps)
       (mv-let (sign atm)
               (strip-not concl)
               (declare (ignore sign))
               (and (not (variablep atm))
                    (not (fquotep atm))
                    (symbolp (ffn-symb atm))
                    (getpropc (ffn-symb atm) 'tau-pair nil wrld)
                    (quotep (fargn atm 1))))))

(defun rune-< (x y)
  (cond
   ((eq (car x) (car y))
    (or (symbol< (cadr x) (cadr y))
        (and (eq (cadr x) (cadr y))
             (cond ((null (cddr x))
                    (cddr y))
                   ((null (cddr y))
                    nil)
                   (t (< (cddr x) (cddr y)))))))
   ((symbol< (car x) (car y))
    t)
   (t
    nil)))

(defun merge-runes-strict (l1 l2)
  (cond ((endp l1) l2)
        ((endp l2) l1)
        ((equal (car l1) (car l2))
         (cons (car l1) (merge-runes-strict (cdr l1) (cdr l2))))
        ((rune-< (car l1) (car l2))
         (cons (car l1) (merge-runes-strict (cdr l1) l2)))
        (t (cons (car l2) (merge-runes-strict l1 (cdr l2))))))

(defun merge-sort-runes-strict (lst)
  (cond ((endp (cdr lst))
         lst)
        (t (let ((n (floor (length lst) 2)))
             (merge-runes-strict (merge-sort-runes-strict (take n lst))
                                 (merge-sort-runes-strict (nthcdr n lst)))))))

(defun get-tau-runes (wrld)
  (merge-sort-runes-strict (global-val 'tau-runes wrld)))

(defun set-tau-runes (flg val wrld)

; This function updates the global-value of tau-runes, adding val to its
; current value.  Flg should be 'list or nil indicating whether val is a list
; of runes or a single rune.

; Note: We formerly used union-equal and add-to-set-equal below rather than
; append and cons (respectively), even though we never visit the same rule
; twice, because some rules split into many (hyps . concl) pairs and each pair
; has the same rune.  For example, if a function foo has a :type-prescription
; rule that says the result is a symbol other than T or NIL, it turns into the
; conjunction of (symbolp v), (not (equal v 'T)), (not (equal v 'NIL)) and each
; is added with the same rune.  However, we found in July 2019 that the
; evaluation of (include-book "centaur/sv/top" :dir :system) sped up from just
; over 84 seconds to just under 70 seconds, cutting about 17% off the time,
; when using append and cons rather than union-equal and (especially)
; add-to-set-equal.

  (let ((runes0 (global-val 'tau-runes wrld)))
    (global-set 'tau-runes
                (cond ((eq flg 'list)
                       (append val runes0))
                      (t (cons val runes0)))
                wrld)))

(defun add-tau-boolean-rule (rune hyps concl wrld)

; To add a new tau Boolean rule, in which hyps is nil and concl is (BOOLEANP
; (fn v)), we make f a tau recognizer by giving it a (possibly new) tau pair
; and initializing its pos- and neg-implicants.  We also add rune to tau-runes.
; However, we must first check that fn is not already known to be a tau
; predicate so that we don't re-initialize its tau properties and wipe out
; existing ones.  Sol Swords constructed a script in which proving that NATP
; was BOOLEANP inadvertently wiped out the bootstrap properties of NATP because
; we failed to detect that we already knew NATP was BOOLEANP.

  (declare (ignore hyps))
  (let ((fn (ffn-symb (fargn concl 1))))
    (cond
     ((getpropc fn 'tau-pair nil wrld)

; We still add rune to the global-value of tau-runes even though the rune
; doesn't otherwise change our world.  The reason is simply that we think the
; user may expect to see it there if he or she proves a tau rule.

      (set-tau-runes nil rune wrld))
     (t (initialize-tau-pred fn
                             (set-tau-runes nil rune wrld))))))

(defun add-tau-eval-rule (rune hyps concl wrld)
  (declare (ignore hyps))
  (mv-let (sign atm)
          (strip-not concl)
          (let ((fn (ffn-symb atm))
                (evg (cadr (fargn atm 1))))
            (putprop fn 'unevalable-but-known
                     (cons (cons evg (if sign nil t))
                           (getpropc fn 'unevalable-but-known nil wrld))
                     (set-tau-runes nil rune wrld)))))

; On Tau-Like Terms

; We need to recognize terms that are suitable applications of signed tau
; recognizers.  We call these ``tau-like'' terms.  Technically, a term is
; ``tau-like'' if it is either (pred e) or (NOT (pred e)) where pred is a tau
; recognizer.  Recall that to be a tau recognizer, pred must be a function
; symbol with a tau-pair or be one of the built-in variants of EQUAL or <.  If
; a term is tau-like, then the ``subject'' of that tau-like term is e.

; For later work we need to identify when a list of terms are all tau-like (and
; perhaps about a common subject or about various subjects but all of which are
; variable symbols).  Our code is simpler if we elaborate the tau-like check
; with certain criteria on the subject.

; criteria          meaning
; :VARIOUS-ANY      subjects may vary and may be any term
; :SAME-ANY         subjects must all be the same but may be any term
; :VARIOUS-VAR      subjects may vary but must all be variable symbols
; :SAME-VAR         subjects must all be the same variable symbol
; term              subjects must be term

; The way we enforce a criterion across a list of terms is to change certain
; of the keyword criteria into term criteria as we go.  For example, to check
; that a list of terms satisfy :VARIOUS-ANY we check that criterion for each
; term, but to check that a list of terms satisfies :SAME-ANY or :SAME-VAR we
; shift the criterion from the input one to whatever subject we find in the
; first term we check.

(defun tau-like-subject-criterion (criterion x)

; Criterion is one of the criteria above and x is a term that is the subject of
; a tau-like term.  We return nil if x does not meet criterion; else we return
; the next criterion to use in checking subsequent allegedly tau-like terms with
; this same criterion.  Thus, this function is both a predicate indicating
; whether x meets the criterion, and a function used to select the next
; criterion when mapping across a list of terms.

  (case criterion
    (:VARIOUS-ANY :VARIOUS-ANY)
    (:SAME-ANY    x)
    (:VARIOUS-VAR (if (variablep x) :VARIOUS-VAR nil))
    (:SAME-VAR (if (variablep x) x nil))
    (otherwise (if (equal criterion x) criterion nil))))

(defun tau-like-term (term criterion wrld)

; If term is tau-like we return (mv sign recog e criterion'), else we return all
; nils.  If recog is non-nil, then it is the internal representation of a tau recognizer:

; tau recognizer       concrete          notes
; form                 representation

; (fn x)               (index . fn)      fn is a symbol with given tau pair

; (equiv x 'evg)       (evg   . nil)     equiv is EQUAL, EQ, EQL, or =
; (equiv 'evg x)

; (< x 'k)             (k . :lessp-x-k)  k is a rational
; (> 'k x)

; (< 'k x)             (k . :lessp-k-x)  k is a rational
; (> x 'k)

; (IF (equiv x '0)     (index . BITP)    opened form of BITP recog
;     T                                  (We also handle the case where the
;     (equiv x '1))                      equiv-terms are swapped.)

; To be ``tau-like'' term must be a possibly negated term of one of the forms
; above The returned sign is T if term is positive; sign is nil for negated
; terms.  The returned e is the subject of the term and meets the input
; criterion.  Criterion' is the NEXT criterion to use when mapping across a
; list of terms to determine if they are all tau-like in the given sense.

; Warning: This function could treat (IFF x NIL) like (NOT x).  It could treat
; (IFF x T) or even (IFF x 123) like (NOT (NOT x)).  It could do lots of
; rewriting to comprehend tau-like meaning in various forms of terms.  But it
; doesn't.  Furthermore, if you change this function to give special treatment
; to IFF, be sure to reconsider tau-like-propositionp and
; expand-tau-like-proposition where also consider looking into IFF and EQUAL.

; Keep this function in sync with tau-big-switch-var

  (let ((equiv-fns '(EQUAL EQ EQL =))
        (inequality-fns '(< >)))
    (mv-let
     (sign atm)
     (if (ffn-symb-p term 'NOT)
         (mv nil (fargn term 1))
         (mv t term))
     (case-match atm
       ((fn e)
        (cond
         ((symbolp fn)
          (let ((tau-pair (getpropc fn 'tau-pair nil wrld)))
            (cond
             (tau-pair
              (let ((next-criterion (tau-like-subject-criterion criterion e)))
                (cond (next-criterion
                       (mv sign tau-pair e next-criterion))
                      (t (mv nil nil nil nil)))))
             (t (mv nil nil nil nil)))))
         (t (mv nil nil nil nil))))
       ((g e ('quote . singleton-evg))

; This matches both the equal-to-constant and arithmetic inequality cases.  We have
; to decide which, if either, case we're in.  Below, we look for the commuted case.

        (cond ((member-eq g equiv-fns)
               (let ((next-criterion (tau-like-subject-criterion criterion e)))
                 (cond (next-criterion
                        (mv sign singleton-evg e next-criterion))
                       (t (mv nil nil nil nil)))))
              ((member-eq g inequality-fns)
               (let ((next-criterion (tau-like-subject-criterion criterion e))
                     (k (car singleton-evg)))
                 (cond ((and next-criterion
                             (rationalp k))
                        (mv sign
                            (if (eq g '<)
                                (cons k :lessp-x-k)
                                (cons k :lessp-k-x))
                            e next-criterion))
                       (t (mv nil nil nil nil)))))
              (t (mv nil nil nil nil))))
       ((g ('quote . singleton-evg) e)
        (cond ((member-eq g equiv-fns)
               (let ((next-criterion (tau-like-subject-criterion criterion e)))
                 (cond (next-criterion
                        (mv sign singleton-evg e next-criterion))
                       (t (mv nil nil nil nil)))))
              ((member-eq g inequality-fns)
               (let ((next-criterion (tau-like-subject-criterion criterion e))
                     (k (car singleton-evg)))
                 (cond ((and next-criterion
                             (rationalp k))
                        (mv sign
                            (if (eq g '<)
                                (cons k :lessp-k-x)
                                (cons k :lessp-x-k))
                            e next-criterion))
                       (t (mv nil nil nil nil)))))
              (t (mv nil nil nil nil))))
       (('IF (g e ''0) ''t (g e ''1))
        (cond ((member-eq g equiv-fns)
               (let ((next-criterion (tau-like-subject-criterion criterion e)))
                 (cond (next-criterion
                        (mv sign *tau-bitp-pair* e next-criterion))
                       (t (mv nil nil nil nil)))))
              (t (mv nil nil nil nil))))
       (('IF (g e ''1) ''t (g e ''0))
        (cond ((member-eq g equiv-fns)
               (let ((next-criterion (tau-like-subject-criterion criterion e)))
                 (cond (next-criterion
                        (mv sign *tau-bitp-pair* e next-criterion))
                       (t (mv nil nil nil nil)))))
              (t (mv nil nil nil nil))))
       (& (mv nil nil nil nil))))))

(defun tau-like-term-listp (lst criterion wrld)

; A list of terms is ``tau-like'' if every term in it is tau-like, and the
; subject of each term meets a certain criterion.  If lst is tau-like in the
; given sense, we return a non-nil answer; else we return nil.  In the
; successful case, the non-nil answer is the common subject of all the terms,
; if the initial criterion is :SAME-ANY, :SAME-VAR, or itself the designated
; subject term.  Otherwise, the non-nil result is just the criterion checked.
; Since the list might be empty, the resulting non-nil answer could be any of
; the legal criterion.

  (cond ((endp lst) criterion)
        (t (mv-let (sign recog e next-criterion)
                   (tau-like-term (car lst) criterion wrld)
                   (declare (ignore sign e))
                   (cond ((null recog) nil)
                         (t (tau-like-term-listp (cdr lst)
                                                 next-criterion wrld)))))))


; Recognizing Simple and Conjunctive Rules

; Simple rules are actually a special case of conjunctive rules.  We define
; the two acceptors first and then the two adders.

(defun tau-conjunctive-formp (hyps concl wrld)

; Hyps and concl are the corresponding components of the pairs generated by
; unprettyify on some theorem: hyps is a list of terms and concl is a term.  We
; return t or nil to indicate whether (implies (and . hyps) concl) is suitable
; as a tau Conjunctive rule.  It must be of the

; Subtype Form:
; (implies (and (tau-like1 v) (tau-like2 v) ...)
;          (tau-likek v))
; where each tau-likei is a recognizer about a common variable symbol v.

; Warning: Given the way this function is defined, (hyps . concl) can be BOTH a
; Conjunctive rule and a Simple Rule!  If (hyps . concl) meets the criteria for
; a Conjunctive rule, then it is actually stored as a Simple rule if hyps is of
; length 1.  Do not change this functionality lightly.

  (let ((hyp-subject (and hyps (tau-like-term-listp hyps :same-var wrld))))
    (cond
     (hyp-subject

; Since hyps is non-empty, if hyp-subject is non-nil it is the common,
; variablep subject of all the hyps.  We check that the conclusion is a
; tau-like term with that same subject.

      (mv-let (sign recog e criterion)
              (tau-like-term concl hyp-subject wrld)
              (declare (ignore sign e criterion))
              (if recog
                  t
                  nil)))
     (t nil))))

(defun tau-simple-formp (hyps concl wrld)

; Return t or nil to indicate whether (implies (and . hyps) concl) is a Simple
; Subtype rule.  This means it has the form (implies (tau-like1 v) (tau-like2
; v)) for two signed tau recognizers and a common variable symbol v.

  (and (tau-conjunctive-formp hyps concl wrld)
       (null (cdr hyps))))

(defun add-tau-simple-rule (rune hyps concl ens wrld)

; To add a simple subtype rule we extend the implicants in the database,
; maintaining closure.  We know that hyps and concl satisfy tau-simple-formp,
; so we can ignore the subject of the recogs.  (We know the subject of the hyp
; and the concl is some common variable.)  We use the criterion :VARIOUS-ANY in
; the tau-like-term calls below because it doesn't do any checks.

  (mv-let (p-sign p-recog e criterion)
          (tau-like-term (car hyps) :various-any wrld)
          (declare (ignore e criterion))
          (mv-let (q-sign q-recog e criterion)
                  (tau-like-term concl :various-any wrld)
                  (declare (ignore e criterion))
                  (mv-let (contradictionp changedp wrld)
                          (tau-put* p-sign p-recog q-sign q-recog ens wrld)
                          (declare (ignore contradictionp changedp))

; Consider the following example (sent June 8, 2017 by Grant Passmore).

;   (defun f (x) (> x 0))
;   (defun g (x) (< x 0))
;   (defun h (x) (and (f x) (g x)))

; When ACL2 admits h, it puts us in this case, i.e., where contradictionp is
; true but it sets the POS-IMPLICANTS of h to the *contradictory-tau* so that
; subsequent proofs in which (h x) is assumed are fast.  Indeed, we can
; prove

; (thm (not (h x))
;      :hints (("Goal" :in-theory '(not (:e tau-system)))))

; with just tau reasoning.  (This wouldn't be the case if we didn't
; record the contradiction discovered when h was defined.)

; Furthermore, if the user proves a theorem like:

; (defthm h-implies-consp
;   (implies (h x) (consp x)))

; no work is done to add CONSP (and all its implicants) to those of h, since we
; recognize that h is contradictory (i.e., already implies everything).

                          (set-tau-runes nil rune wrld)))))

(defun convert-tau-like-terms-to-tau (complete-flg terms ens wrld)

; We convert a list of tau-like terms, terms, to a tau.  If the complete-flg is
; t, the resulting tau is ``complete'' in that it includes the implicants.  Otherwise,
; it just includes the tau representations of the terms themselves.

  (cond
   ((endp terms) *tau-empty*)
   (t (mv-let
       (sign recog e criterion)
       (tau-like-term (car terms) :various-any wrld)
       (declare (ignore e criterion))
       (let ((tau1 (convert-tau-like-terms-to-tau complete-flg (cdr terms) ens wrld)))
         (if complete-flg
             (add-to-tau sign recog
                         tau1
                         ens wrld)
             (add-to-tau1 sign recog
                          tau1
                          ens
                          wrld)))))))

(defun add-tau-conjunctive-rule (rune hyps concl ens wrld)

; A conjunctive rule (implies (and (p1 x) ... (pk x)) (q x)) is stored as {p1
; ... pk -q}.  The idea is that if we detect that we know all but one of the
; elements of such a set, we can assert the remaining element.  This is
; actually stored as a tau so that it is easier to search for each
; ``kind'' of recog in it.  But we are not interested in the semantics of such
; tau, i.e., M[tau] is irrelevant for conjunctive rules; we're just exploiting
; the data structure.

  (let ((tau (convert-tau-like-terms-to-tau
              nil
              (append hyps (list (case-match concl
                                   (('NOT p) p)
                                   (& `(NOT ,concl)))))

; Note that I move the negated conclusion into the hyps to produce the list
; that is converted to a tau.  I avoid dumb-negate-lit simply because it does
; more than just add or strip a NOT.

              ens wrld)))

; If we get a contradiction it is because hyps --> concl is a tau-detectable
; tautology and we just ignore it.

    (if (equal tau *tau-contradiction*)
        wrld
        (set-tau-runes nil rune
                       (global-set 'tau-conjunctive-rules
                                   (cons tau
                                         (global-val 'tau-conjunctive-rules
                                                     wrld))
                                   wrld)))))

; We now turn to signature rules.

; On Loops in Relieving Dependent Hyps in Tau Signature Rules

; We allow signature rules with non-tau-like hypotheses.  These hyps are saved
; in the :dependent-hyps field of signature-rule records.  If the tau-like hyps
; in :input-tau-list are relieved then ok-to-fire-signature-rulep next attempts
; to relieve each dependent one by instantiating it and applying type-set
; (which also invokes a little linear arithmetic).  At one point
; ok-to-fire-signature-rulep also recursively applied tau-term, and asked
; whether the resulting tau contained nil among its :neg-evgs (meaning the hyp
; is non-nil).  But the recursive use of tau-term caused infinite backchaining.
; The loop was first detected in the regression:

; cd books/workshops/2006/cowles-gamboa-euclid/Euclid/
; (defpkg "GAUSS-INT"
;         (union-eq *acl2-exports*
;                   *common-lisp-symbols-from-main-lisp-package*))
; (ld "ed5aa.lisp" :ld-pre-eval-print t)

; The command above will fail with a stack overflow at in the [GAUSS-INT::] event
; SQ-ABS-<-SQ-ABS-*

; However, here is a simpler example that loops:

; (encapsulate ((q (x) t)(p (x) t) (mum (x) t) (bar (x) t))
;              (local (defun q (x) (equal x t)))
;              (local (defun p (x) (equal x t)))
;              (local (defun mum (x) (cons x x)))
;              (local (defun bar (x) (cons x x)))
;              (defthm p-sig
;                (implies (consp x) (equal (p x) nil)))
;              (defthm q-sig
;                (implies (consp x) (equal (q x) nil)))
;              (defthm bar-sig
;                (implies (q (mum x)) (consp (bar x)))
;                :rule-classes :tau-system)
;              (defthm mum-sig
;                (implies (p (bar x)) (consp (mum x)))
;                :rule-classes :tau-system))
;
; (thm (consp (mum a)))

; Note that both bar-sig and mum-sig contain non-tau hyps, i.e., dependent
; hyps.  In trying to compute the signature of (mum a) using mum-sig we compute
; the tau of (bar a), but in computing the tau of (bar a) with bar-sig we
; compute the tau of (mum a).  The p-sig and q-sig rules are present so that we
; can bury (bar x) and (mum x) in the dependent hyps and still dive down to
; them when computing the tau of the dependent hyps.

; To stop this loop we took Draconian action: we simply eliminated use of
; tau-term in ok-to-fire-signature-rulep.  Perhaps there is a smarter way?

(defun partition-signature-hyps-into-tau-alist-and-others
  (hyps alist others ens wrld)

; We partition hyps into two lists: the tau-like terms about variables and the
; others.  To represent the first partition, we build an alist pairing each
; variable with its associated tau (except the tau is not closed under the
; database, it just contains the recognizers explicitly listed for that
; variable).  The other hyps are merely assembled into a list in the same order
; as they appear in hyps.  Hyps0 and concl0 are the components of the
; unprettyified theorem from which this rule is being constructed and are used
; only for error reporting.  We return (mv contradictionp tau-alist others).
; Contradictionp is t when we find a contradiction among the hyps.  For
; example,
; (implies (and (stringp x) (not (stringp x))) (true-listp (foo x y)))
; is a theorem but tells us absolutely nothing about the type of foo.
; If this function signals contradictionp, no signature rule should be
; built.

  (cond
   ((endp hyps) (mv nil alist others))
   (t (mv-let (contradictionp alist others)
              (partition-signature-hyps-into-tau-alist-and-others
               (cdr hyps) alist others ens wrld)
              (cond
               (contradictionp
                (mv contradictionp nil nil))
               (t
                (mv-let (sign recog v criterion)
                        (tau-like-term (car hyps) :various-var wrld)
                        (declare (ignore criterion))
                        (cond
                         (recog
                          (let ((old-tau
                                 (or (cdr (assoc-eq v alist)) *tau-empty*)))
                            (let ((new-tau
                                   (add-to-tau1 sign recog old-tau ens wrld)))
; Note: We use add-to-tau1 because we are not interested in the implicants.
                              (cond
                               ((eq new-tau *tau-contradiction*)
                                (mv t nil nil))
                               (t (mv nil (put-assoc-eq v new-tau alist) others))))))
                         (t (mv nil alist (cons (car hyps) others)))))))))))

(defun tau-boolean-signature-formp (hyps concl)

; The tau system cannot handle disjunctions and is thus incapable of coding
; (or (equal e 'T) (equal e 'NIL)) as a signature.  But this is a very special
; case: (BOOLEANP e), and many function have that as a type-prescription rule.
; So we recognize as form 1 signatures expressions of the form:

; (IF (EQUAL (fn v1 ... vn) 'T)
;     T
;     (EQUAL (fn v1 ... vn) 'NIL))

; and variants.  We recognize variants because the user might have written an
; OR which actually translates into the IF above with the true-branch replaced
; by a repetition of the test, even though the conversion of type-prescription
; rules to terms does short-cuts that and puts a T there.

; Warning: All variants MUST have the property that (fargn (fargn concl 1) 1) is
; the term (fn v1 ... vn).

  (cond
   ((null hyps)
    (let ((e (case-match concl
;  Note this position:       *
               (('IF ('EQUAL e ''T) ''T ('EQUAL e ''NIL)) e)
               (('IF ('EQUAL e ''T) ('EQUAL e ''T) ('EQUAL e ''NIL)) e)
               (('IF ('EQUAL e ''NIL) ''T ('EQUAL e ''T)) e)
               (('IF ('EQUAL e ''NIL) ('EQUAL e ''NIL) ('EQUAL e ''T)) e)
;  Note this position:       *

               (& nil))))
      (and e
           (nvariablep e)
           (not (fquotep e))
           (symbolp (ffn-symb e))
           (symbol-listp (fargs e))
           (no-duplicatesp-eq (fargs e)))))
   (t nil)))

(defun tau-signature-formp (hyps concl wrld)

; We return 1 or 2 or nil to indicate whether (implies (and . hyps) concl) is
; suitable as a tau signature rule of the indicated form.  To be of form 1, it
; must be of the

; Signature Form 1:
; (implies (and (tau-like1_1 v1) ... (tau-like1_k v1)
;               ...
;               (tau-liken_1 vn) ... (tau-liken_j vn)
;               (dhyp_1 v1 ... vn) ... (dhyp_k v1 ... vn))
;          (tau-like (fn v1 ... vn)))

; That is, we get to make an arbitrary number of non-nil tau-like hypotheses
; about distinct variables v1, ..., vn, and we get to make an arbitrary number
; of non-nil non-tau-like hypotheses about any of the variables, and then
; assert a tau-like conclusion about (fn v1 ... vn).  No free vars are allowed.

; We recognize (OR (EQUAL (fn v1 ... vn) T) (EQUAL (fn v1 ... vn) NIL)) as
; synonymous with (BOOLEANP (fn v1 ... vn)) and thus as a form 1 signature rule.

; To be of form 2 it must be of the form:

; Signature Form 2
; (implies (and (tau-like1_1 v1) ... (tau-like1_k v1)
;               ...
;               (tau-liken_1 vn) ... (tau-liken_j vn)
;               (dhyp_1 v1 ... vn) ... (dhyp_k v1 ... vn))
;          (tau-like (mv-nth 'i (fn v1 ... vn)))

; Note that the hypotheses are of the same form as in form 1.  Note also that
; the hyps are thus unconstrained except for the free-var restriction: any list
; of hyps can be partitioned into those that are tau-like and those that are
; not!

  (cond

; We exclude all non-classical functions from consideration by tau.  We could just check that
; the fn being signed and the dependent hyps are classical, since we know that all tau predicates
; are classical.  However, it is simplest to check that every function in the formula is
; classical.

   #+:non-standard-analysis
   ((not (classical-fn-list-p
          (all-fnnames1 nil concl
                        (all-fnnames1 t hyps nil))
          wrld))
    nil)
   ((member-equal *nil* hyps)

; We first confirm that hyps is not identically nil.  While we handle this
; case correctly -- it would be a dependent hyp and would never be relieved --
; it almost certainly indicates a misunderstanding on the part of the user.

    nil)
   ((tau-boolean-signature-formp hyps concl)
    1)
   (t
    (mv-let (sign recog e criterion)
            (tau-like-term concl :same-any wrld)
            (declare (ignore sign criterion))
            (cond
             ((or (null recog)
                  (variablep e)
                  (fquotep e))
              nil)

; The conclusion is a tau-like term applied to something.  We now check that
; the something is either (mv-nth 'i (fn x1 ... xn)) or (fn x1 ... xn), where
; fn is a function symbol and the xi are distinct variables and that there are
; no free vars among the hyps.

             ((or (eq (ffn-symb e) 'mv-nth)
                  (member-eq (ffn-symb e)
                             (global-val 'tau-mv-nth-synonyms wrld)))

; Notice that this simple check for mv-nth or a synonym precludes us having a
; useful signature rule about MV-NTH itself.  It is hard to imagine a useful
; rule about (MV-NTH X1 X2)!

              (cond
               ((and (quotep (fargn e 1))
                     (natp (cadr (fargn e 1))))
                (let ((e (fargn e 2)))
                  (cond
                   ((and (nvariablep e)
                         (not (fquotep e))
                         (symbolp (ffn-symb e))
                         (symbol-listp (fargs e))      ; faster than arglistp
                         (no-duplicatesp-eq (fargs e)) ; for a list of terms.
                         (not (ffnnamep-lst (ffn-symb e) hyps))
                         (subsetp (all-vars1-lst hyps nil) (fargs e)))
                    2)
                   (t nil))))
               (t nil)))
             ((and (symbolp (ffn-symb e))
                   (nvariablep e)
                   (not (fquotep e))
                   (symbolp (ffn-symb e))
                   (symbol-listp (fargs e))      ; faster than arglistp
                   (no-duplicatesp-eq (fargs e)) ; for a list of terms.
                   (not (ffnnamep-lst (ffn-symb e) hyps))
                   (subsetp (all-vars1-lst hyps nil) (fargs e)))
              1)
             (t nil))))))

(defun replace-vars-by-bindings (vars alist)

; Given a list of vars and an alist mapping vars to objects, we return the
; result of replacing each var in the list by its image under the alist.

  (cond ((endp vars) nil)
        (t (cons (or (cdr (assoc-eq (car vars) alist))
                     *tau-empty*)
                 (replace-vars-by-bindings (cdr vars) alist)))))

(defun add-tau-signature-rule (rune form hyps concl ens wrld)

; Form is either 1 or 2 and indicates which form of signature rule we can
; construct from (implies (and . hyp) concl).  We update the database
; appropriately.  Look at the comment in tau-signature-formp for a description
; of the two forms.

  (let ((concl (if (tau-boolean-signature-formp hyps concl)
                   `(BOOLEANP ,(fargn (fargn concl 1) 1))
                   concl)))
    (mv-let
     (sign recog e criterion)
     (tau-like-term concl :various-any wrld)
     (declare (ignore criterion))
     (let* ((temp recog)
            (recog (if temp recog *tau-booleanp-pair*))
            (sign (if temp sign t))
            (e (if temp e (fargn concl 1))))
       (let* ((fn (if (eql form 1) (ffn-symb e) (ffn-symb (fargn e 2))))
              (i (if (eql form 1) nil (cadr (fargn e 1))))
              (vars (fargs (if (eql form 1) e (fargn e 2)))))
         (mv-let (contradictionp alist others)
                 (partition-signature-hyps-into-tau-alist-and-others
                  hyps nil nil ens wrld)
                 (cond
                  (contradictionp

; The hyps are contradictory, so there is no useful signature rule to store.

                   wrld)
                  (t
                   (let ((rule
                          (make signature-rule
                                :input-tau-list (replace-vars-by-bindings vars alist)
                                :vars vars
                                :dependent-hyps others
                                :output-sign sign
                                :output-recog recog)))

; It is easy to imagine that the same signature gets stored in two different
; theorems, as happens in the Rockwell work where types are mechanically
; generated and there is some redundancy.  So we check.

                     (cond
                      ((eql form 1)
                       (let ((sigs (getpropc fn 'signature-rules-form-1 nil
                                             wrld)))
                         (if (member-equal rule sigs)
                             wrld
                             (set-tau-runes nil rune
                                            (putprop fn
                                                     'signature-rules-form-1
                                                     (cons rule sigs)
                                                     wrld)))))
                      (t (let ((sigs (getpropc fn 'signature-rules-form-2 nil
                                               wrld)))
                           (if (member-equal rule (nth i sigs))
                               wrld
                               (set-tau-runes
                                nil rune
                                (putprop fn
                                         'signature-rules-form-2
                                         (update-nth i
                                                     (cons rule (nth i sigs))
                                                     sigs)
                                         wrld)))))))))))))))

; Now we turn our attention to recognizing big switch functions.

; We say a variable v is a ``switch'' (or ``flag'') in a term
; iff

; (a) the term is of the form (IF x y z), where x is a recognizer term, v is
;     the only variable free in x, and v is a switch for both y and z, or

; (b) v is not free in the term.

; Note that any variable that does not occur freely in term is (pathologically)
; a switch for the term.  But let's confine our attention to variables that
; occur freely in term.

; If v occurs freely in term and is a switch for term, then term must begin
; with an IF and the test must be a recognizer on v.  Thus, at most one
; variable occurring freely in term is a switch for term.

; We say an unconditional equation defines a ``big switch function'' if the
; equation is of the form

; (equal (fn v1 ... vk) body)

; where fn is a function symbol, fn is not a tau recognizer, the vi are
; distinct variables, the free vars of body are a subset of the vi, and one of
; the vi is free in body and is the switch for body, and body does not call fn.
; The largest subterms of body that do not contain the switch var are called
; the ``leaves'' of the switch.

; Note that it is possible for a big switch equation to define a function fn
; about which we also have signatures.  In this case, the tau mechanism will
; ignore the big switch definition.  That is, the presence of a signature in
; tau overrides the possibility of expanding the function.

(defun switch-varp (v term wrld)
  (case-match term
    (('IF x y z)
     (mv-let (sign recog e criterion)
             (tau-like-term x :various-any wrld)
             (declare (ignore sign criterion))
             (cond
              ((and recog
                    (eq v e)
                    (switch-varp v y wrld)
                    (switch-varp v z wrld))
               t)
              (t (not (occur v term))))))
    (& (not (occur v term)))))

(defun tau-big-switch-equationp (term wrld)
  (case-match term

    (('EQUAL (fn . vars) ('IF test x y))
     (let* ((test-vars (all-vars test))
            (v (car test-vars))
            (body-vars (all-vars1 y (all-vars1 x test-vars))))
       (and

; We exclude all non-classical functions from consideration by tau.  We could
; just check that the fn being signed and the dependent hyps are classical,
; since we know that all tau predicates are classical.  However, it is simplest
; to check that every function in the formula is classical.

        #+:non-standard-analysis
        (classical-fn-list-p
         (all-fnnames1 nil term nil)
         wrld)

        (symbolp fn)
        (not (equal fn 'quote))
        (not (getpropc fn 'tau-pair nil wrld))
        (not (getpropc fn 'big-switch nil wrld))
        (symbol-listp vars)
        (no-duplicatesp vars)
        test-vars
        (null (cdr test-vars))
        (subsetp-eq body-vars vars)
        (mv-let (sign recog e criterion)
                (tau-like-term test :various-any wrld)
                (declare (ignore sign criterion))
                (and recog (eq e v)))
        (not (ffnnamep fn (fargn term 2)))
        (switch-varp v x wrld)
        (switch-varp v y wrld))))
    (& nil)))

(defun tau-big-switch-var (term)

; Given that term is recognized by tau-big-switch-equationp, return the switch
; var.  Note that this function recapitulates some of the checks in
; tau-like-term.  Keep the two functions in sync.

; We know term = (EQUAL (fn . vars) (IF test x y)) and that test is recognized
; by tau-like-term.  We return the subject of test.

  (mv-let (sign test)
          (strip-not (fargn (fargn term 2) 1))
          (declare (ignore sign))

; Test is now (recog v) or (equal a1 a2) or (< a1 a2). If we're in the recog
; case, v is the switch var; otherwise either a1 or a2 is a quoted evg and the
; other one is the switch var.

          (cond ((null (cdr (fargs test))) (fargn test 1))
                ((quotep (fargn test 1)) (fargn test 2))
                (t (fargn test 1)))))

(defun tau-big-switch-formp (hyps concl wrld)
  (and (null hyps)
       (tau-big-switch-equationp concl wrld)))

(defun add-tau-big-switch-rule (rune hyps concl wrld)

; We know that hyps is nil and concl satisfies the big switch equation
; criterion: (EQUAL (fn . formals) body).

  (declare (ignore hyps))
  (let* ((fn (ffn-symb (fargn concl 1)))
         (formals (fargs (fargn concl 1)))
         (body (fargn concl 2))
         (switch-var (tau-big-switch-var concl))
         (switch-var-pos (- (length formals)
                            (length (member-eq switch-var formals)))))
    (set-tau-runes nil rune
                   (putprop fn
                            'big-switch
                            (MAKE big-switch-rule
                                  :formals formals
                                  :switch-var switch-var
                                  :switch-var-pos switch-var-pos
                                  :body body)
                            wrld))))

(defun tau-mv-nth-synonym-formp (hyps concl)
  (and (null hyps)
       (case-match concl
         (('EQUAL (fn x y) ('MV-NTH x y))
          (and (not (flambdap fn))
               (variablep x)
               (variablep y)
               (not (eq x y))))
         (('EQUAL ('MV-NTH x y) (fn x y))
          (and (not (flambdap fn))
               (variablep x)
               (variablep y)
               (not (eq x y))))
         (& nil))))

(defun add-tau-mv-nth-synonym-rule (rune hyps concl wrld)
  (declare (ignore hyps))
  (let* ((fn (if (eq (ffn-symb (fargn concl 1)) 'MV-NTH)
                 (ffn-symb (fargn concl 2))
                 (ffn-symb (fargn concl 1))))
         (fns (global-val 'tau-mv-nth-synonyms wrld)))
    (cond ((member-eq fn fns)
           wrld)
          (t (set-tau-runes nil rune
                            (global-set 'tau-mv-nth-synonyms
                                        (cons fn fns)
                                        wrld))))))

; A bounder correctness theorem is parsed into the following
; record:

(defrec bounder-correctness
  ((subject-fn . acceptable-domains)
   .
   (bounder-fn . bounder-args))
  t)

; Here, subject-fn is the function symbol whose value is constrained to the
; interval computed by bounder-fn.  Both are function symbols.
; Acceptable-domains codes the domain requirements on the arguments to
; subject-fn; it is a list of elements in 1:1 correspondence with the actuals
; of subject-fn: each element is a list of interval domain recognizers,
; indicating that the corresponding actual must lie in an interval over one of
; the listed domains or that no restriction is made.  The last field of a
; bounder-correctness record is a list of numbers, in 1:1 correspondence with
; the arguments of bounder-fn, indicating which actual interval is to be passed
; to bounder-fn in each position.

; For example, here is a bounder correctness theorem for the function fn:

;  (implies (and (tau-intervalp int1)
;                (tau-intervalp int3)
;                (or (equal (tau-interval-dom int1) 'integerp)
;                    (equal (tau-interval-dom int1) 'rationalp))
;                (equal (tau-interval-dom int3) 'integerp)
;                (in-tau-intervalp x int1)
;                (in-tau-intervalp z int3))
;           (and (tau-intervalp (bounder int3 int1))
;                (in-tau-intervalp (fn x y z) (bounder int3 int1))))

; and here is the corresponding bounder-correctness record which
; represents this theorem:

; (make bounder-correctness
;       :subject-fn         'fn
;       :acceptable-domains '((INTEGERP RATIONALP)
;                             (INTEGERP RATIONALP ACL2-NUMBERP NIL)
;                             (INTEGERP))
;       :bounder-fn         'bounder
;       :bounder-args       '(2 0))

; If tau-term sees a call of fn, it determines the tau of the arguments (or at
; least those with non-T acceptable-domains) and checks that each tau contains
; an interval with an acceptable domain.  If so, it collects the intervals of
; the tau in the positions listed in :bounder-args (in the order listed) and
; applies bounder to that list of arguments to get an interval known to contain
; the fn term.

(defun all-cars-nil (pairs)
  (cond ((endp pairs) t)
        (t (and (null (car (car pairs)))
                (all-cars-nil (cdr pairs))))))

(defun find-subject-bounder-link-term (pairs pairs0)

; Pairs is a list of (hyp . concl) pairs.  To be sensible, every hyp must be
; nil; i.e., pairs is obtained by unprettyifying a conjunction and so is
; essentially a list of conjuncts except each is embedded in (nil . conjunct).
; Pairs0 is initially pairs.  We find the first conjunct of the form
; (IN-TAU-INTERVALP subject-term bounder-term) such that (TAU-INTERVALP bounder-term)
; is also among the conjuncts.  (Thus, we search pairs for the first pattern
; and when we find a candidate, we check the full list, pairs0, for the
; second.)  We return either the IN-TAU-INTERVALP term we found or nil.

  (cond
   ((endp pairs) nil)
   ((and (null (car (car pairs)))
         (ffn-symb-p (cdr (car pairs)) 'in-tau-intervalp)
         (member-equal (cons nil (cons 'tau-intervalp
                                       (cddr (cdr (car pairs)))))
                       pairs0))
    (cdr (car pairs)))
   (t (find-subject-bounder-link-term (cdr pairs) pairs0))))

(defun tau-bounder-doms-extraction (term ivars ivar)
  (case-match term
    (('EQUAL ('TAU-INTERVAL-DOM v) ('QUOTE evg))
     (cond ((and (if ivar
                     (eq v ivar)
                     (member-eq v ivars))
                 (member-eq evg '(INTEGERP RATIONALP ACL2-NUMBERP NIL)))
            (mv v (list evg)))
           (t (mv nil nil))))
    (('IF ('EQUAL ('TAU-INTERVAL-DOM v) ('QUOTE evg))
          ('EQUAL ('TAU-INTERVAL-DOM v) ('QUOTE evg))
          else-term)
     (cond ((and (if ivar
                     (eq v ivar)
                     (member-eq v ivars))
                 (member-eq evg '(INTEGERP RATIONALP ACL2-NUMBERP NIL)))
            (mv-let (ivar doms)
                    (tau-bounder-doms-extraction else-term
                                                 ivars
                                                 v)
                    (cond (ivar
                           (mv ivar (add-to-set-eq evg doms)))
                          (t (mv nil nil)))))
           (t (mv nil nil))))
    (& (mv nil nil))))

(defun tau-bounder-hyp-extraction
  (hyps svars ivars missing-ivars1 missing-ivars2
        ivar-to-doms-alist
        ivar-to-svar-pos-alist
        svar-to-ivar-alist)
  (cond
   ((endp hyps)
    (cond
     ((and (null missing-ivars1)
           (null missing-ivars2))

; If both lists of missing ivars are empty then we know that for each ivar, (a)
; we have an INTERVALP hyp, (b) we have an (IN-TAU-INTERVALP svar ivar) hyp, and
; (c) ivar is paired with a unique svar position in ivar-to-svar-pos-alist.

      (mv t ivar-to-doms-alist ivar-to-svar-pos-alist svar-to-ivar-alist))
     (t (mv nil nil nil nil))))
   ((or (variablep (car hyps))
        (fquotep (car hyps)))
    (mv nil nil nil nil))
   ((eq (ffn-symb (car hyps)) 'TAU-INTERVALP)
    (let ((ivar (fargn (car hyps) 1)))
      (cond ((member-eq ivar missing-ivars1)

; The hyp is (TAU-INTERVALP ivar), so we can ``check off'' ivar from the
; ones we're looking for.

             (tau-bounder-hyp-extraction
              (cdr hyps)
              svars ivars
              (remove1-eq ivar missing-ivars1)
              missing-ivars2
              ivar-to-doms-alist
              ivar-to-svar-pos-alist
              svar-to-ivar-alist))
            (t (mv nil nil nil nil)))))
   ((eq (ffn-symb (car hyps)) 'IN-TAU-INTERVALP)
    (let ((svar (fargn (car hyps) 1))
          (ivar (fargn (car hyps) 2)))
      (cond
       ((and (member-eq svar svars)
             (member-eq ivar missing-ivars2)
             (not (assoc-eq svar svar-to-ivar-alist)))

; The hyp is (IN-TAU-INTERVALP svar ivar).  Since we know that no such hyp for ivar
; has been seen before -- ivar is not among the missing in-tau-intervalp-vars -- we
; also know there is no correspondent for it in the ivar-to-svar-pos-alist.
; Since we know that svar is not already mapped to another ivar, we know this
; mapping will be unique.  So we ``check off'' ivar and record the position of
; the svar it tracks and the correspondence between svar and ivar.

        (let ((n (- (len svars)
                    (len (member-eq svar svars)))))
          (tau-bounder-hyp-extraction
           (cdr hyps)
           svars ivars
           missing-ivars1
           (remove1-eq ivar missing-ivars2)
           ivar-to-doms-alist
           (cons (cons ivar n) ivar-to-svar-pos-alist)
           (cons (cons svar ivar) svar-to-ivar-alist))))
       (t (mv nil nil nil nil)))))
   (t (mv-let (ivar doms)
              (tau-bounder-doms-extraction (car hyps) ivars nil)
              (cond
               ((and ivar
                     (not (assoc-eq ivar ivar-to-doms-alist)))
                (tau-bounder-hyp-extraction
                 (cdr hyps)
                 svars ivars
                 missing-ivars1
                 missing-ivars2
                 (cons (cons ivar doms) ivar-to-doms-alist)
                 ivar-to-svar-pos-alist
                 svar-to-ivar-alist))
               (t (mv nil nil nil nil)))))))

(defconst *all-interval-domains*
  '(INTEGERP RATIONALP ACL2-NUMBERP NIL))

(defun acceptable-domains-for-bounder
  (svars svar-to-ivar-alist ivar-to-doms-alist)
  (cond
   ((endp svars) nil)
   (t (let ((temp (assoc-eq (car svars) svar-to-ivar-alist)))
        (cons (cond ((null temp) *all-interval-domains*)
                    (t (let* ((ivar (cdr temp))
                              (temp (assoc-eq ivar ivar-to-doms-alist)))
                         (cond ((null temp) *all-interval-domains*)
                               (t (cdr temp))))))
              (acceptable-domains-for-bounder
               (cdr svars)
               svar-to-ivar-alist
               ivar-to-doms-alist))))))

(defun bounder-args (ivars ivar-to-svar-pos-alist)
  (cond
   ((endp ivars) nil)
   (t (cons (cdr (assoc-eq (car ivars) ivar-to-svar-pos-alist))
            (bounder-args (cdr ivars) ivar-to-svar-pos-alist)))))

(defun tau-bounder-formp (term wrld)

; This function, while a peer of the other tau form recognizers, e.g.,
; tau-boolean-formp, tau-simple-formp, etc., is actually quite odd.  Unlike
; those other functions, it takes the whole term, not (hyps . concl) pairs
; stripped out of the term.  Also, unlike those other functions which truly
; just recognize the desired forms, this function returns some additional
; information gleaned while parsing the term.

; This function returns (mv form j bc) where form is nil, 1, or 2, where nil
; means term is NOT of the form of a bounder correctness rule, 1 means it is of
; form 1, and 2 means it is of form 2.  If form is 1, then j is nil and bc is
; the corresponding bounder-correctness record.  If form is 2, then j is the
; slot in the MV tuple returned by the :subject-fn of bc, which is the
; corresponding bounder-correctness record.

; To be of form 1, term must be:
; (implies (and (tau-intervalp i1)
;               ...
;               (tau-intervalp ik)
;               (or (equal (tau-interval-dom i1) 'dom1,1)
;                   ...
;                   (equal (tau-interval-dom i1) 'dom1,n1))
;               ...
;               (or (equal (tau-interval-dom ik) 'domk,1)
;                   ...
;                   (equal (tau-interval-dom ik) 'domk,nk))
;               (in-tau-intervalp x1 i1)
;               ...
;               (in-tau-intervalp xk ik))
;          (and (tau-intervalp (bounder-fn i1 ... ik))
;               (in-tau-intervalp (fn x1 ... xk y1 ...)
;                                 (bounder-fn i1 ... ik))
;               ...))

; except we don't care about the order in which the hyps, the conclusion, or
; their individual parts (including the variables presented as actuals to the
; calls of fn and bounder-fn) occur, and not every interval i has to have a
; domain restriction.

; Form 2 is just like form 1 above except the (fn x1 ... xk y1 ...) is
; (mv-nth 'j (fn x1 ... xk y1 ...)).

  (cond
   ((ffn-symb-p term 'implies)
    (let* ((hyp-pairs (unprettyify (fargn term 1)))
           (concl-pairs (unprettyify (fargn term 2)))
           (link-term (find-subject-bounder-link-term concl-pairs concl-pairs)))

; Note: link-term is the (IN-TAU-INTERVALP x bounder) where the conclusion also
; contains (TAU-INTERVALP bounder).  So next we do a few simple checks to see if it
; is plausible that this is a bounder rule of either form and then we split the
; two forms and check their pieces more carefully.

      (cond
       ((and link-term
             (all-cars-nil hyp-pairs)
             (nvariablep (fargn link-term 1))
             (not (fquotep (fargn link-term 1)))
             (nvariablep (fargn link-term 2))
             (not (fquotep (fargn link-term 2)))
             (symbolp (ffn-symb (fargn link-term 2)))
             (symbol-listp (fargs (fargn link-term 2)))
             (no-duplicatesp-eq (fargs (fargn link-term 2))))

; So we know that the hyp-pairs is a list of conjuncts paired with nil (in the
; cars), and that we found a link-term in the conclusion and that it is of the
; form (IN-TAU-INTERVALP (g ...) (bounder-fn i1 ... ik)) where the i are distinct
; variable symbols.  By looking at g we can decide if this is plausibly form 1
; or form 2.

        (cond
         ((or (eq (ffn-symb (fargn link-term 1)) 'mv-nth)
              (member-eq (ffn-symb (fargn link-term 1))
                         (global-val 'tau-mv-nth-synonyms wrld)))
          (cond
           ((and (quotep (fargn (fargn link-term 1) 1))
                 (natp (cadr (fargn (fargn link-term 1) 1))))

; We are in the plausibly Form 2 case.  We know nothing about subject-term
; below but we know bounder-fn below is a function symbol and the ivars are
; distinct variable symbols.

            (let ((j (cadr (fargn (fargn link-term 1) 1)))
                  (subject-term (fargn (fargn link-term 1) 2))
                  (bounder-fn (ffn-symb (fargn link-term 2)))
                  (ivars (fargs (fargn link-term 2))))
              (cond
               ((and (nvariablep subject-term)
                     (not (fquotep subject-term))
                     (symbolp (ffn-symb subject-term))
                     (symbol-listp (fargs subject-term))
                     (no-duplicatesp-eq (fargs subject-term))
                     (not (intersectp-eq (fargs subject-term) ivars)))
                (let ((fn (ffn-symb subject-term))
                      (svars (fargs subject-term))
                      (hyps (strip-cdrs hyp-pairs)))

; Let subject and bounder be the terms (fn . svars) and (bounder-fn . ivars).
; We know that the conclusion contains (TAU-INTERVALP bounder) and also
; (IN-TAU-INTERVALP (MV-NTH 'j subject) bounder).  Furthermore, we know that both
; fn and bounder-fn are function symbols, that they are applied to distinct
; variable symbols, svars and ivars, respectively, and that those variable
; symbols do not overlap.  Finally, hyps is a list of hypothesis terms
; implicitly conjoined.

; Next, every hyp in hyps has to be of one of the following forms: (TAU-INTERVALP
; ivar), (IN-TAU-INTERVALP svar ivar), or the IF form of a disjunction of (EQUAL
; (TAU-INTERVAL-DOM ivar) 'dom).  Furthermore, we MUST have an INTERVALP hyp and an
; IN-TAU-INTERVALP hyp for EVERY bounder-var, and a unique svar must be paired to
; each ivar by those IN-TAU-INTERVALP hyps.

                  (mv-let
                   (flg ivar-to-doms-alist ivar-to-svar-pos-alist svar-to-ivar-alist)
                   (tau-bounder-hyp-extraction
                    hyps svars ivars
                    ivars ; initial missing (TAU-INTERVALP ivar) ivars
                    ivars ; initial missing (IN-TAU-INTERVALP * ivar) ivars
                    nil   ; initial alist mapping ivars to domains
                    nil   ; initial alist mapping ivars to svar positions
                    nil   ; initial alist mapping svars to ivars
                    )
                   (cond
                    (flg
                     (mv 2 ; Form 2
                         j ; mv-nth slot concerned
                         (make bounder-correctness
                               :subject-fn fn
                               :acceptable-domains (acceptable-domains-for-bounder
                                                    svars
                                                    svar-to-ivar-alist
                                                    ivar-to-doms-alist)
                               :bounder-fn bounder-fn
                               :bounder-args (bounder-args ivars
                                                           ivar-to-svar-pos-alist))))
                    (t (mv nil nil nil))))))
               (t (mv nil nil nil)))))
           (t (mv nil nil nil))))
         (t

; We are in the plausibly Form 1 case.  We know nothing about subject-term
; below but we know bounder-fn below is a function symbol and the ivars are
; distinct variable symbols.

          (let ((j nil)
                (subject-term (fargn link-term 1))
                (bounder-fn (ffn-symb (fargn link-term 2)))
                (ivars (fargs (fargn link-term 2))))
            (cond
             ((and (nvariablep subject-term)
                   (not (fquotep subject-term))
                   (symbolp (ffn-symb subject-term))
                   (symbol-listp (fargs subject-term))
                   (no-duplicatesp-eq (fargs subject-term))
                   (not (intersectp-eq (fargs subject-term) ivars)))
              (let ((fn (ffn-symb subject-term))
                    (svars (fargs subject-term))
                    (hyps (strip-cdrs hyp-pairs)))

; Let subject and bounder be the terms (fn . svars) and (bounder-fn . ivars).
; We know that the conclusion contains (TAU-INTERVALP bounder) and also
; (IN-TAU-INTERVALP subject bounder).  Furthermore, we know that both
; fn and bounder-fn are function symbols, that they are applied to distinct
; variable symbols, svars and ivars, respectively, and that those variable
; symbols do not overlap.  Finally, hyps is a list of hypothesis terms
; implicitly conjoined.

; Next, every hyp in hyps has to be of one of the following forms: (TAU-INTERVALP
; ivar), (IN-TAU-INTERVALP svar ivar), or the IF form of a disjunction of (EQUAL
; (TAU-INTERVAL-DOM ivar) 'dom).  Furthermore, we MUST have an INTERVALP hyp and an
; IN-TAU-INTERVALP hyp for EVERY bounder-var, and a unique svar must be paired to
; each ivar by those IN-TAU-INTERVALP hyps.

                (mv-let
                 (flg ivar-to-doms-alist ivar-to-svar-pos-alist svar-to-ivar-alist)
                 (tau-bounder-hyp-extraction
                  hyps svars ivars
                  ivars ; initial missing (TAU-INTERVALP ivar) ivars
                  ivars ; initial missing (IN-TAU-INTERVALP * ivar) ivars
                  nil   ; initial alist mapping ivars to domains
                  nil   ; initial alist mapping ivars to svar positions
                  nil   ; initial alist mapping svars to ivars
                  )
                 (cond
                  (flg
                   (mv 1 ; Form 1
                       j ; mv-nth slot concerned = nil
                       (make bounder-correctness
                             :subject-fn fn
                             :acceptable-domains (acceptable-domains-for-bounder
                                                  svars
                                                  svar-to-ivar-alist
                                                  ivar-to-doms-alist)
                             :bounder-fn bounder-fn
                             :bounder-args (bounder-args ivars
                                                         ivar-to-svar-pos-alist))))
                  (t (mv nil nil nil))))))
             (t (mv nil nil nil)))))))
       (t (mv nil nil nil)))))
   (t (mv nil nil nil))))

; In the following code we develop the idea of adding a bounder-correctness
; record to a list of such records, except that we eliminate subsumed records.
; A bounder-correctness record bc1 is subsumed by another, bc2, if the
; subject-fn, bounder-fn, and bounder-args are all identical and the successive
; acceptable domains of bc1 are subsets of the corresponding domains of bc2.
; For example, bc1 might have :acceptable-domains of ((INTEGERP) (RATIONALP))
; while bc2 might have :acceptable-domains of ((INTEGERP RATIONALP) (INTEGERP
; RATIONALP)).  Given that everything else is the same, it is obvious that bc2
; applies more often.

; The reason we need such a function is that when developing a book of bounder
; theorems we frequently encounter many lemmas (and also many corollaries of
; each bounder correctness theorem) that are less complete than the final
; bounder correctness theorem for a function.

(defun pairwise-subsetp-eq (doms-lst1 doms-lst2)
  (cond ((endp doms-lst1) t)
        ((subsetp-eq (car doms-lst1) (car doms-lst2))
         (pairwise-subsetp-eq (cdr doms-lst1) (cdr doms-lst2)))
        (t nil)))

(defun bounder-subsumedp (bc1 bc2)

; Bc1 and bc2 are two bounder-correctness records.  We determine whether bc1 is
; subsumed by bc2.  The only way one bounder subsumes another is if the
; successive acceptable domains of bc1 are subsets of the corresponding ones of
; bc2.  All other fields have to be the same.  Since we assume that both bc1
; and bc2 are about the same subject-fn, we delay that test to the end because
; it will most likely be true.  We check the bounder-fn and bounder-arg fields
; first because they're fast checks.

  (and (eq (access bounder-correctness bc1 :bounder-fn)
           (access bounder-correctness bc2 :bounder-fn))
       (equal (access bounder-correctness bc1 :bounder-args)
              (access bounder-correctness bc2 :bounder-args))
       (pairwise-subsetp-eq
        (access bounder-correctness bc1 :acceptable-domains)
        (access bounder-correctness bc2 :acceptable-domains))
       (eq (access bounder-correctness bc1 :subject-fn)
           (access bounder-correctness bc2 :subject-fn))))

(defun bounder-subsumedp-by-some (bc bounders)
  (cond ((endp bounders) nil)
        ((bounder-subsumedp bc (car bounders)) t)
        (t (bounder-subsumedp-by-some bc (cdr bounders)))))

(defun delete-some-subsumed-bounders (bc bounders)
  (cond ((endp bounders) nil)
        ((bounder-subsumedp (car bounders) bc)
         (delete-some-subsumed-bounders bc (cdr bounders)))
        (t
         (cons (car bounders)
               (delete-some-subsumed-bounders bc (cdr bounders))))))

(defun add-bounder-to-bounders (bc bounders)
  (cond ((bounder-subsumedp-by-some bc bounders) bounders)
        (t (cons bc (delete-some-subsumed-bounders bc bounders)))))

(defun add-tau-bounder-rule (rune form j bc wrld)

; Form is 1 or 2, j is the slot that a form 2 rule occupies, and bc is the
; bounder-correctness record representing a bounder correctness theorem.  We
; store it under the 'tau-bounders-form-1 or -2 property of the subject-fn and
; add rune to the tau runes.

; Note that when we add a new bounder-correctness rule we may delete some old
; ones or not actually add anything (if the new rule is subsumed).  So we
; actually ``add'' the rule to the appropriate list of bounders and then see if
; changed anything before modifying the world.

  (let ((subject-fn (access bounder-correctness bc :subject-fn)))
    (cond
     ((equal form 1)
      (let* ((bounders0 (getpropc subject-fn 'tau-bounders-form-1 nil wrld))
             (bounders1 (add-bounder-to-bounders bc bounders0)))
        (if (equal bounders0 bounders1)
            wrld
            (set-tau-runes nil rune
                           (putprop subject-fn
                                    'tau-bounders-form-1
                                    bounders1
                                    wrld)))))
     (t
      (let* ((slots (getpropc subject-fn 'tau-bounders-form-2 nil wrld))
             (bounders0 (nth j slots))
             (bounders1 (add-bounder-to-bounders bc bounders0)))
        (if (equal bounders0 bounders1)
            wrld
            (set-tau-runes nil rune
                           (putprop subject-fn
                                    'tau-bounders-form-2
                                    (update-nth j bounders1 slots)
                                    wrld))))))))


; Now we define the functions for checking and adding tau rules.

; The following function strips FORCE and CASE-SPLIT off of the hyps so that
; they don't trick us into missing tau rules.

(defun strip-force-and-case-split (lst)
  (cond ((endp lst) nil)
        (t (let* ((hyp (car lst))
                  (rest (strip-force-and-case-split (cdr lst))))
             (case-match hyp
               (('force hyp) (cons hyp rest))
               (('case-split hyp) (cons hyp rest))
               (& (cons hyp rest)))))))

(defun strip-force-and-case-split-in-hyps-of-pairs (pairs)
  (cond ((endp pairs) nil)
        (t (cons (cons (strip-force-and-case-split (car (car pairs)))
                       (cdr (car pairs)))
                 (strip-force-and-case-split-in-hyps-of-pairs (cdr pairs))))))

; Note for future improvement: When we check whether a rule (of any class) is
; suitable as a tau-system rule, we call a number of functions to prepare the
; rule for the check.  In particular, we call (in order)

;  remove-guard-holders
;  unprettyify
;  strip-force-and-case-split-in-hyps-of-pairs
;  split-on-conjoined-disjunctions-in-hyps-of-pairs

; to get a list of (hyps . concl) pairs that we then inspect for suitability
; under the tau constraints.  This is done in three places.  The places are
; shown below and the notation ``fn < gn'' should be read as ``fn is called by
; gn'':

; chk-acceptable-tau-rule < chk-acceptable-x-rules (on :tau-system rules only)

; add-tau-rule <
;  tau-visit-defthm1 < tau-visit-defthm < TAU-VISIT-EVENT < [see below]

; tau-rules-from-type-prescriptions <
;   tau-visit-defuns1 < tau-visit-defuns < tau-visit-defun < TAU-VISIT-EVENT
;                                        < TAU-VISIT-EVENT

; Note that add-tau-rule and tau-rules-from-type-prescriptions are essentially
; only called from TAU-VISIT-EVENT, which is called by install-event (and
; during regenerate-tau-database, which is so rare we will ignore it).  Recall
; that while one might expect add-tau-rule to be called by add-x-rule it is
; not: tau rules are added by the install-event.

; It is of some concern that the nest of preparatory functions (like
; strip-force-and-case-split-in-hyps-of-pairs and
; split-on-conjoined-disjunctions-in-hyps-of-pairs) causes too much consing.
; So there are two questions: (a) Can we prepare the hyps for the tau
; constraint checks without repeatedly copying them?  (b) Do we prepare the
; hyps multiple times for the same rule?

; When a :tau-system rule is proposed, we prepare the hyps for each rule twice:
; once when we check that the rule is an acceptable tau-system rule and then
; again when we store it in install-event.  We cannot avoid this unless we save
; the prepared (hyps . concl) pairs from before the proof and feed them to
; install-event.  But this is quite a paradigm shift from the current and
; widely used interface with install-event so we chose not to do it.  On the
; other hand, when a :rewrite or other class of rule is proposed, we prepare
; the hyps only once: when we try to add it (optionally) as a tau rule.

; Since the vast majority of rules are presumably not :tau-system rules, we're
; willing to live with the current redundancy for :tau-system rules.  If we
; come to believe that the preparatory processing of rules for tau is costing
; too much, it is probably best to focus first on question (a) above: preparing
; more efficiently (or checking without preparing).

; A useful little test is to define foo, trace one of the preparatory functions,
; and then add a rule, either as a :tau-system rule or as a :rewrite rule.  Note
; how many times we prepare the rule for checking.
; (defun foo (x) (mv x x))
; (trace$ strip-force-and-case-split-in-hyps-of-pairs)
; (defthm sig (implies (force (natp x)) (natp (mv-nth 1 (foo x)))) :rule-classes :tau-system)
; (u)
; (defthm sig (implies (force (natp x)) (natp (mv-nth 1 (foo x)))))

(defun acceptable-tau-rulep (pair wrld)
  (let ((hyps (car pair))
        (concl (cdr pair)))
    (cond
     ((tau-boolean-formp hyps concl wrld) 'BOOLEAN)
     ((tau-eval-formp hyps concl wrld) 'EVAL)
     ((tau-simple-formp hyps concl wrld) 'SIMPLE)
     ((tau-conjunctive-formp hyps concl wrld) 'CONJUNCTIVE)
     (t (let ((n (tau-signature-formp hyps concl wrld)))
          (cond
           ((equal n 1) 'SIGNATURE-FORM-1)
           ((equal n 2) 'SIGNATURE-FORM-2)
           ((tau-big-switch-formp hyps concl wrld) 'BIG-SWITCH)
           ((tau-mv-nth-synonym-formp hyps concl) 'MV-NTH-SYNONYM)
           (t nil)))))))

(defun acceptable-tau-rulesp (flg pairs wrld)

; Pairs was computed by unprettyify and consists of pairs of the form (hyps
; . concl).  We check that every (flg = :all) or some (flg = :some) element of
; pairs may be coded as a tau rule of some kind.

  (cond ((endp pairs) (eq flg :all))
        ((acceptable-tau-rulep (car pairs) wrld)
         (if (eq flg :all)
             (acceptable-tau-rulesp flg (cdr pairs) wrld)
             t))
        ((eq flg :all) nil)
        (t (acceptable-tau-rulesp flg (cdr pairs) wrld))))

(defun acceptable-tau-rules (pairs wrld)

; Pairs was computed by unprettyify and consists of pairs of the form (hyps
; . concl).  We collect every acceptable tau rule pair.

  (cond ((endp pairs) nil)
        ((acceptable-tau-rulep (car pairs) wrld)
         (cons (car pairs) (acceptable-tau-rules (cdr pairs) wrld)))
        (t (acceptable-tau-rules (cdr pairs) wrld))))

(defun cross-prod1 (lst lst-lst acc)
  (cond ((endp lst-lst) acc)
        (t (cross-prod1 lst
                        (cdr lst-lst)
                        (cons (append lst (car lst-lst))
                              acc)))))

(defun cross-prod2 (lst1 lst2 acc)
  (cond ((endp lst1) (reverse acc))
        (t (cross-prod2 (cdr lst1)
                        lst2
                        (cross-prod1 (car lst1) lst2 acc)))))

(defun cross-prod (lst1 lst2)

; Lst1 and lst2 are both lists of lists.  Return:

;   (loop for a in lst1
;         append
;         (loop for b in lst2
;               collect
;               (append a b)))

; We compute this by accumulating all such (append a b) in reverse order, so
; that the functions are tail-recursive.

  (cross-prod2 lst1 lst2 nil))

(defun cnf-dnf (sign term cnfp)

; This function converts sign/term into either CNF or DNF form.  (Sign is t for
; positive, nil for negative.)  However, it only recognizes variables,
; constants, NOT, and IFs that represent ANDs or ORs.  It does not deal with
; IMPLIES or IFF (but it does recognize (IF x y T) as (OR (NOT x) y)).  We
; return a list of lists of terms.  If cnfp is t, the answer should be
; interpreted as a conjunction of disjunctions.  If cnfp is nil, the answer
; should be interpreted as a disjunction of conjunctions.  This function is not
; particularly efficient; it's only intended use at the time of its
; creation is to preprocess the hypotheses of rules so that from
; (AND p (OR q r) s) we could get (OR (AND p q r) (AND p r s)), as in
; the following use:
; ACL2 !>:trans (AND p (OR q r) s)
; (IF P (IF (IF Q Q R) S 'NIL) 'NIL)
; and
; (cnf-dnf t '(IF P (IF (IF Q Q R) S 'NIL) 'NIL) nil)
; = ((P Q S) (P R S))

  (cond
   ((variablep term)
    (list (list (if sign term (list 'NOT term)))))
   ((fquotep term)
    (let ((val (if (eq (cadr term) nil) (not sign) sign)))
; Val is propositionally equivalent to (if sign term (not term)).
      (if val
          (if cnfp
              nil               ; (AND) = T
              '(nil))           ; (OR (AND)) = T
          (if cnfp
              '(nil)            ; (AND (OR)) = NIL
              nil))))           ; (OR) = NIL
   ((eq (ffn-symb term) 'NOT)
    (cnf-dnf (not sign) (fargn term 1) (not cnfp)))
   ((eq (ffn-symb term) 'IF)
    (let ((x (fargn term 1))
          (y (fargn term 2))
          (z (fargn term 3)))

; Cases we consider:
; (if x y nil)  =   (AND x y)
; (if x nil z)  =   (AND (NOT x) z)
; (if x y t)    =   (OR (NOT x) y)
; (if x t z)   <--> (OR x z)        = (if x x z)

      (cond ((equal z *nil*) ; (AND x y)
             (if cnfp
                 (append (cnf-dnf sign x cnfp)
                         (cnf-dnf sign y cnfp))
                 (cross-prod (cnf-dnf sign x cnfp)
                             (cnf-dnf sign y cnfp))))
            ((equal y *nil*) ; (AND (NOT x) z)
             (if cnfp
                 (append (cnf-dnf (not sign) x cnfp)
                         (cnf-dnf sign z cnfp))
                 (cross-prod (cnf-dnf (not sign) x cnfp)
                             (cnf-dnf sign z cnfp))))
            ((equal z *t*) ; (OR (NOT x) y)
             (if cnfp
                 (cross-prod (cnf-dnf (not sign) x cnfp)
                             (cnf-dnf sign y cnfp))
                 (append (cnf-dnf (not sign) x cnfp)
                         (cnf-dnf sign y cnfp))))
            ((or (equal x y)    ; (OR x z)
                 (equal y *t*))
             (if cnfp
                 (cross-prod (cnf-dnf sign x cnfp)
                             (cnf-dnf sign z cnfp))
                 (append (cnf-dnf sign x cnfp)
                         (cnf-dnf sign z cnfp))))
            (t (list (list (if sign term (list 'NOT term))))))))
   (t (list (list (if sign term (list 'NOT term)))))))

(defun split-on-conjoined-disjunctions (lst)

; List is a list of terms that are implicitly conjoined, as found in the hyps
; returned in the pairs produced by unprettyify.  We split on the disjunctions
; among them, converting (the translated version of)
; (P (OR Q1 Q2) R (OR S1 S2)) to
; ((P Q1 R S1)
;  (P Q1 R S2)
;  (P Q2 R S1)
;  (P Q2 R S2))

  (cond ((endp lst) nil)
        ((endp (cdr lst)) (cnf-dnf t (car lst) nil))
        (t (cross-prod (cnf-dnf t (car lst) nil)
                       (split-on-conjoined-disjunctions (cdr lst))))))

(defun split-on-conjoined-disjunctions-in-hyps-of-pairs (pairs)

; Pairs is a list of (hyps . concl) pairs as produced by unprettyify.  We split
; out the disjunctions in the hyps, producing another list of pairs.  E.g.,
; from these two pairs (((p (or q1 q2)) . concl1) ((r (or s1 s2)) . concl2))
; we get these four:
; (((p q1) . concl1) ((p q2) .concl1) ((r s1) . concl2) ((r s2) . concl2)).

  (cond ((endp pairs) nil)
        (t (let ((hyps-lst (split-on-conjoined-disjunctions (car (car pairs)))))
             (cond ((endp hyps-lst)
                    (cons (car pairs)
                          (split-on-conjoined-disjunctions-in-hyps-of-pairs (cdr pairs))))
                   (t (append (pairlis-x2 hyps-lst
                                          (cdr (car pairs)))
                              (split-on-conjoined-disjunctions-in-hyps-of-pairs (cdr pairs)))))))))

(defun chk-acceptable-tau-rule (name term ctx wrld state)
  (let ((term1 (remove-guard-holders term wrld)))
    (mv-let
     (form j bc)
     (tau-bounder-formp term1 wrld)
     (declare (ignore j bc))
     (cond
      (form

; Term is a bounder correctness theorem of either form 1 or 2 (depending on
; form) and about slot j (if form 2), where bc is the bounder-correctness
; record representing it.  But all we care about here is to report that term is
; acceptable.
       (value nil))
      (t
       (let ((pairs
              (split-on-conjoined-disjunctions-in-hyps-of-pairs
               (strip-force-and-case-split-in-hyps-of-pairs
                (unprettyify term1)))))
         (cond
          ((acceptable-tau-rulesp :all pairs wrld)
           (value nil))
          ((null (cdr pairs))
           (er soft ctx
               "The formula of the theorem ~x0 fails to fit any of the forms ~
               for acceptable :TAU-SYSTEM rules.  See :DOC tau-system for the ~
               details of the acceptable forms."
               name))
          (t (er soft ctx
                 "The formula of the theorem ~x0 gives rise to ~n1 normalized ~
                 formulas (e.g., after stripping out conjuncts in the ~
                 conclusion, etc.).  In order to be a :TAU-SYSTEM rule, each ~
                 of these formulas must be acceptable as a tau rule and at ~
                 least one of them fails to be.  See :DOC tau for details of ~
                 the acceptable forms."
                 name (length pairs))))))))))

; On the Tau Msgp Protocol

; Several of the functions that add tau rules obey the Tau Msgp Protocol.  In
; that protocol, we return (mv msgp wrld), where msgp is either nil or an error
; message to be handled (signaled) by some caller of the function in question.
; When msgp is nil, wrld is the properly extended wrld.  When msgp is non-nil,
; wrld is the original wrld passed into the function, not some partially
; updated extension.  That is, functions obeying the msgp protocol are No
; Change Losers on wrld.  Most functions following the protocol take an
; additional argument, wrld0, as the ``good'' wrld to preserve.

; The reason we have the protocol is that we cannot always make tau rules out
; of previously approved :tau-system formulas because the ens has changed and
; some previously identified tau recognizers are no longer identified as tau
; recognizers.  This may or may not be an error, depending on lost-rune-action.
; When not an error, we just accumulate those lost runes on the global value of
; 'tau-lost-runes.  The possibility that we should actually signal an error
; arises when we are processing the original introduction of the :tau-system
; rule, where the explanation of the inadequacy of the syntactic check is due
; to it having been done in the first pass of an encapsulate that failed to
; export the Boolean property to the second pass where the error is to be
; signaled.

(defun add-tau-rule1 (lost-rune-action rune pairs ens wrld wrld0)

; We try to convert each (hyps . concl) pair in pairs to a tau rule and extend
; wrld accordingly.  We obey the Tau Msgp Protocol and return (mv msgp wrld').
; Wrld0 is the original world we started with and will be returned in the error
; case, as per the protocol.  Pairs was derived by unprettyify from some
; :corollary for a rule named rune.

; Lost-rune-action determines what we do if we encounter a term that cannot be
; coded as a tau rule.  If lost-rune-action is IGNORE, we quietly ignore such
; terms.  If lost-rune-action is REPORT, we return a non-nil error message.
; This can happen if we're in the second pass of an encapsulate and discover
; that a function that was Boolean during the first pass is no longer known to
; be Boolean.  If lost-rune-action is ACCUMULATE then we add the rune of the
; lost rule to the 'tau-lost-runes list in wrld.

  (cond
   ((endp pairs) (mv nil wrld))
   (t (mv-let
       (msgp wrld)
       (let* ((hyps (car (car pairs)))
              (concl (cdr (car pairs)))
              (kind (acceptable-tau-rulep (cons hyps concl) wrld)))
         (case kind
           (BOOLEAN
            (mv nil (add-tau-boolean-rule rune hyps concl wrld)))
           (EVAL
            (mv nil (add-tau-eval-rule rune hyps concl wrld)))
           (SIMPLE
            (mv nil (add-tau-simple-rule rune hyps concl ens wrld)))
           (CONJUNCTIVE
            (mv nil (add-tau-conjunctive-rule rune hyps concl ens wrld)))
           (SIGNATURE-FORM-1
            (mv nil (add-tau-signature-rule rune 1 hyps concl ens wrld)))
           (SIGNATURE-FORM-2
            (mv nil (add-tau-signature-rule rune 2 hyps concl ens wrld)))
           (BIG-SWITCH
            (mv nil (add-tau-big-switch-rule rune hyps concl wrld)))
           (MV-NTH-SYNONYM
            (mv nil (add-tau-mv-nth-synonym-rule rune hyps concl wrld)))
           (otherwise
            (cond
             ((eq lost-rune-action 'REPORT)
              (mv (msg
                   "Unable to generate a :TAU-SYSTEM rule for the rune ~x0 ~
                    with formula ~x1.  A possible explanation is that we are ~
                    in the second pass of an ENCAPSULATE (e.g., we've just ~
                    printed ``End of Encapsulated Events.''). If so, then ~
                    evidently the formula in question was accepted during the ~
                    first pass but is no longer acceptable.  This can happen ~
                    if the ENCAPSULATE established too few constraints.  For ~
                    example, the local witness to some monadic function might ~
                    have been Boolean but that fact was not exported as ~
                    :TAU-SYSTEM (or, in tau automatic mode, ~
                    :TYPE-PRESCRIPTION) rule.  See :DOC tau for the details ~
                    of the acceptable forms of :TAU-SYSTEM rules."
                   rune
                   (reprettyify hyps concl wrld))
; No Change Loser on wrld0 when msgp non-nil:
                  wrld0))
             ((eq lost-rune-action 'ACCUMULATE)
              (mv nil
                  (global-set 'tau-lost-runes
                              (cons rune (global-val 'tau-lost-runes
                                                     wrld))
                              wrld)))
             (t ; IGNORE lost runes
                (mv nil wrld))))))
       (cond
; No Change Loser on wrld0 when msgp non-nil:
        (msgp (mv msgp wrld0))
        (t (add-tau-rule1 lost-rune-action rune (cdr pairs) ens wrld wrld0)))))))

(defun add-tau-rule (first-visitp rune term ens wrld0)

; We convert term into tau rules, if possible.  We obey the Tau Msgp Protocol
; and return (mv msgp wrld'); No Change Loser on wrld0.

; First-visitp is t if this is the first time in this world that this rune has
; been visited.  What that really means is that tau is visiting the event that
; install-event is installing.  Otherwise, this is a re-visit of an event.
; Based on whether this is the first visit or not, we set lost-rune-action to
; REPORT, ACCUMULATE, or IGNORE to indicate what should be done if term cannot
; be represented as a tau rule.  REPORT means we'll report a non-nil msgp;
; ACCUMULATE means we just add rune to 'tau-lost-runes, and IGNORE means we
; just quietly ignore the situation.

  (let ((term1 (remove-guard-holders term wrld0)))
    (mv-let
     (form j bc)
     (tau-bounder-formp term1 wrld0)
     (cond
      (form

; Term is a bounder correctness theorem of form 1 or 2 (depending on form), j
; is the form 2 slot, and bc is the bounder-correctness record that represents
; term.  We add it to the list of of bounder-correctness records for the
; subject-fn.

       (mv nil (add-tau-bounder-rule rune form j bc wrld0)))
      (t
       (let* ((pairs
               (split-on-conjoined-disjunctions-in-hyps-of-pairs
                (strip-force-and-case-split-in-hyps-of-pairs
                 (unprettyify term1))))
              (lost-rune-action (if (eq (car rune) :tau-system)
                                    (if first-visitp
                                        'REPORT
                                        'ACCUMULATE)
                                    'IGNORE)))

         (add-tau-rule1 lost-rune-action rune pairs ens wrld0 wrld0)))))))

; We now turn to the topic of ``visiting'' events and building up the tau
; database.  Recall that we may be visiting an event for the first time (e.g.,
; in the install-event just after it has been executed) or as part of a
; chronological sweep of the world to regenerate the tau database under a
; different enabled structure.  But from tau's perspective, every visit to an
; event is (almost) like the first time.  This means that it must essentially
; erase any tau properties before starting to add the ``new'' ones.

; We have already defined tau-visit-function-introduction where we clear the
; tau properties of a function symbol.  This is not necessary on the first
; visit to a DEFUN because we know the symbol is new.  Furthermore, on an
; ENCAPSULATE event, it is too late to initialize the tau properties of the
; constrained functions when we see the encapsulate event!  So we visit
; function introductions when we see FORMALS properties stored on the world and
; we don't consider that part of the (re-)visits to events.

; What does tau learn by visiting a defined function?  (a) Whether the function
; is a tau recognizer.  (b) Whether the function's type-prescription(s) are tau
; signature rules.  (c) Whether the function's definitional equation is a
; big-switch rule.  (d) Whether the function's definitional equation is an
; mv-nth-synonym.  The last three possibilities are contingent upon tau being
; in automatic mode and upon certain runes being enabled.

(defun discover-tau-pred (fn ens wrld)

; If fn is a monadic Boolean under ens, we initialize the tau properties for a
; tau recognizer; else not.  We return the modified wrld.

; Note: This function (re-)initializes the tau properties of fn!  Normally,
; this is a straightforward initialization because discover-tau-pred (actually
; the -preds version below) is only called by tau-visit-defuns, which will have
; just introduced the new name fn.  However, it is possible that fn is being
; redefined.  In that case, either we Erased old properties or else we are
; Overwriting.  In the former case, the re-initialization here is still
; correct.  In the latter case, one might argue that we should not
; re-initialize because we're supposed to just add to existing properties.  But
; the tau implicants already stored under fn and derived from its now-obsolete
; definition may be quite extensive.  We think it is quite likely that adding
; new deductions to those implicants from this new definition will produce
; inconsistency.  Therefore, we make the arbitrary decision to Erase the tau
; properties even upon Overwriting redefinitions.

  (mv-let
   (monadic-booleanp ttree)
   (monadic-boolean-fnp fn ens wrld)
   (cond
    (monadic-booleanp
     (initialize-tau-pred fn
                          (set-tau-runes 'list
                                         (tagged-objects 'lemma ttree)
                                         wrld)))
    (t wrld))))

(defun discover-tau-preds (fns ens wrld)
  (cond ((endp fns) wrld)
        (t (discover-tau-preds (cdr fns) ens
                               (discover-tau-pred (car fns) ens wrld)))))

(defun tau-rules-from-type-prescriptions (tp-lst fn ens wrld wrld0)

; We map over tp-lst, which is a list of type-prescriptions on fn, and for
; every rule that is both enabled in ens and has fn as a base symbol, we store
; an appropriate tau rule (if possible) into wrld.  This function should only
; be called if tau is in automatic mode.  The reason we focus on those rules
; with base symbol fn is that when visiting a defun we act like the defun event
; was just executed.  We obey the Tau Msgp Protocol and return (mv msgp wrld');
; No Change Loser on wrld0.

; Programming Note: At first we thought we could achieve No Change Loser status
; without passing in wrld0.  The idea is that add-tau-rule1 is a No Change
; Loser and so if it signaled an error, we'd get back what we gave it.  But
; because this function is recursive and maps over tp-lst, it could be that
; what we gave add-tau-rule1 has already been extended.

; Note also that this function uses add-tau-rule1 rather than add-tau-rule.  In
; so doing, it precludes the possibility that the rule being added is a
; tau-bounder-formp, which is handled by add-tau-rule.  But no
; type-prescription can be a bounder correctness theorem.

  (cond
   ((endp tp-lst)
    (mv nil wrld))
   ((and (eq (cadr (access type-prescription (car tp-lst) :rune)) fn)
         (enabled-numep (access type-prescription (car tp-lst) :nume) ens))
    (mv-let
     (term ttree)
     (convert-type-prescription-to-term (car tp-lst) ens wrld)
     (let ((pairs
            (acceptable-tau-rules
             (split-on-conjoined-disjunctions-in-hyps-of-pairs
              (strip-force-and-case-split-in-hyps-of-pairs
               (unprettyify
                (remove-guard-holders term wrld0))))
             wrld)))
       (cond
        ((null pairs)
         (tau-rules-from-type-prescriptions (cdr tp-lst) fn ens
                                            wrld wrld0))
        (t (mv-let (msgp wrld)
                   (add-tau-rule1 'IGNORE ; this is a :TYPE-PRESCRIPTION rune
                                          ; so we can't count on it being of
                                          ; interest
                                  (access type-prescription
                                          (car tp-lst)
                                          :rune)
                                  pairs ens wrld wrld0)

; If msgp is non-nil, then x is nil and the attempt to add this rule caused an
; error as explained by msgp.  On the other hand, if msgp is nil, then x is the
; extended wrld.

                   (cond
                    (msgp

; We actually know here that wrld is wrld0 given that add-tau-rule1 is a No
; Change Loser, but just to be explicit:

                          (mv msgp wrld0))
                    (t (tau-rules-from-type-prescriptions
                        (cdr tp-lst) fn ens
                        (set-tau-runes 'list
                                       (tagged-objects 'lemma ttree)
                                       wrld)
                        wrld0)))))))))
   (t (tau-rules-from-type-prescriptions (cdr tp-lst) fn ens
                                         wrld wrld0))))

(defun original-def-body1 (fn def-bodies)
  (cond ((endp def-bodies) nil)
        ((eq (cadr (access def-body (car def-bodies) :rune)) fn)
         (car def-bodies))
        (t (original-def-body1 fn (cdr def-bodies)))))

(defun original-def-body (fn wrld)

; Return the def-body originally added for fn in wrld, identified as the body
; whose rune has base symbol fn.

  (original-def-body1 fn (getpropc fn 'def-bodies nil wrld)))

(defun tau-like-propositionp (var term wrld)

; Warning:  Keep this function in sync with expand-tau-like-proposition.

; We determine whether term is propositional expression built out of tau-like
; terms with subject var, which is a variable symbol.  We give special
; treatment only to the propositional-like functions typically expanded by
; expand-some-non-rec-fn (in *definition-minimal-theory*) that are likely to
; appear in defuns expressing propositional facts about boolean recognizers.
; So, for example, we handle IFF but not EQUAL and its synonyms even though
; when both arguments are Boolean they are the same.  See the comment in
; expand-tau-like-proposition below.

  (mv-let (sign recog e criteria)
          (tau-like-term term var wrld)
          (declare (ignore sign e criteria))
          (cond
           (recog t)
           ((variablep term) nil)
           ((fquotep term)
            (or (equal term *t*)
                (equal term *nil*)))
           ((eq (ffn-symb term) 'IF)
            (and (tau-like-propositionp var (fargn term 1) wrld)
                 (tau-like-propositionp var (fargn term 2) wrld)
                 (tau-like-propositionp var (fargn term 3) wrld)))
           ((eq (ffn-symb term) 'RETURN-LAST)
            (tau-like-propositionp var (fargn term 3) wrld))
           ((and (eq (ffn-symb term) 'NOT)
                 (eq (ffn-symb term) 'NULL))
            (tau-like-propositionp var (fargn term 1) wrld))
           ((or (eq (ffn-symb term) 'IMPLIES)
                (eq (ffn-symb term) 'IFF))
            (and (tau-like-propositionp var (fargn term 1) wrld)
                 (tau-like-propositionp var (fargn term 2) wrld)))
           (t nil))))

(defun expand-tau-like-proposition (term)

; Warning: Keep this function in sync with tau-like-propositionp for some
; unknown variable var.  That implies that var is the only variable in the
; term.  It should be the case that if term is a tau-like-propositionp, then
; the value of term is EQUAL to the value of (expand-tau-like-proposition
; term).  Key to the correctness of the definition below is that all the
; components of tau-like propositions are boolean.

; Warning: At one point we considered handling (EQUAL x y) as (IFF x y) since
; we ``knew'' that x and y are tau-like propositions.  However, we don't.  It
; could be that we are looking at (EQUAL var '123) in which case it is a
; tau-like proposition because it is a tau recognizer.  If we dive into it we
; get out of the boolean world.  So to treat EQUAL as IFF we have to make sure
; that both arguments are tau like.  Rather than consider that, we just punt
; and don't consider EQUAL, EQ, EQL, and = as propositional connectors.

  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((eq (ffn-symb term) 'IF)
    (fcons-term* 'IF
                 (expand-tau-like-proposition (fargn term 1))
                 (expand-tau-like-proposition (fargn term 2))
                 (expand-tau-like-proposition (fargn term 3))))
   ((eq (ffn-symb term) 'RETURN-LAST)
    (expand-tau-like-proposition (fargn term 3)))
   ((or (eq (ffn-symb term) 'NOT)
        (eq (ffn-symb term) 'NULL)) ; we map (NULL x) to (NOT x)
    (fcons-term* 'NOT (expand-tau-like-proposition (fargn term 1))))
   ((eq (ffn-symb term) 'IMPLIES)
    (fcons-term* 'IF
                 (expand-tau-like-proposition (fargn term 1))
                 (expand-tau-like-proposition (fargn term 2))
                 *t*))
   ((eq (ffn-symb term) 'IFF)

; Warning: We know that both arguments are Boolean.  Why?  Because this term is
; a tau-like-proposition and we don't treat (IFF x NIL), say, as a tau
; recognizer!  If we did change tau-like-term to look into (IFF NIL x) we would
; have to check here that x is Boolean to do the expansion we do below!
    (let ((arg2 (expand-tau-like-proposition (fargn term 2))))
      (fcons-term* 'IF
                   (expand-tau-like-proposition (fargn term 1))
                   arg2
                   (fcons-term* 'NOT arg2))))
   (t term)))

(defun add-only-simple-and-conjunctive-tau-rules (rune pairs ens wrld)

; We believe every clause in clauses corresponds to a Simple or Conjunctive
; rule.  But we confirm that, adding each Simple or Conjunctive rule and
; ignoring any clause that is not.

  (cond
   ((endp pairs) wrld)
   (t (add-only-simple-and-conjunctive-tau-rules
       rune
       (cdr pairs)
       ens
       (let ((hyps (car (car pairs)))
             (concl (cdr (car pairs))))
         (cond
          ((tau-conjunctive-formp hyps concl wrld)

; Simple if hyps is of length 1.
           (cond
            ((null (cdr hyps))
             (add-tau-simple-rule rune hyps concl ens wrld))
            (t (add-tau-conjunctive-rule rune hyps concl ens wrld))))
          (t wrld)))))))

(defun convert-normalized-term-to-pairs (rhyps term ans)

; Term is a term in IF-normal form.  We convert it to a list of (hyps . concl)
; pairs such that the conjunction of the (implies (and ,hyps) concl) terms is
; IFF-equivalent to term.

  (cond
   ((variablep term)
    (cons (cons (revappend rhyps nil) term) ans))
   ((fquotep term)
    (if (equal term *nil*)
        (cond ((consp rhyps)
               (cons (cons (revappend (cdr rhyps) nil) (dumb-negate-lit (car rhyps)))
                     ans))
              (t (cons (cons nil *nil*) ans)))
        ans))
   ((eq (ffn-symb term) 'IF)
    (cond
     ((equal (fargn term 3) *nil*)
      (convert-normalized-term-to-pairs
       rhyps (fargn term 2)
       (cons (cons (revappend rhyps nil)
                   (fargn term 1)) ans)))
     ((equal (fargn term 2) *nil*)
      (convert-normalized-term-to-pairs
       rhyps (fargn term 3)
       (cons (cons (revappend rhyps nil)
                   (dumb-negate-lit (fargn term 1))) ans)))
     (t (convert-normalized-term-to-pairs
         (cons (fargn term 1) rhyps)
         (fargn term 2)
         (convert-normalized-term-to-pairs
          (cons (dumb-negate-lit (fargn term 1)) rhyps)
          (fargn term 3)
          ans)))))
   (t (cons (cons (revappend rhyps nil) term) ans))))

; In convert-term-to-pairs, below, we convert a term (known to be a theorem)
; into a list of (hyps . concl) pairs.  We basically walk through its
; propositional structure collecting hyps and then the conclusion at each tip.
; We ought to just clausify the term instead, but we have not yet defined
; clausify.  The following code is a cheap and dirty approximation of clausify
; used just to process non-recursive propositional definition bodies containing
; only tau recognizers.

; To see the need for more than stripping, define a recognizer as a disjunction
; of other recognizers, e.g., (DEFUN FOO (X) (OR (A X) (B X) (C X) (D X))).  To
; make it easier to play, let's just think of proposition letters:

; FOO <--> (A v B v C v D).

; We want to store a tau rule of the form (A v B v C v D) --> foo.
; If we express that as an IF we get

; (IF (IF A 'T (IF B 'T (IF C 'T D))) FOO 'T)

; which normalizes to

; (IF A FOO (IF B FOO (IF C FOO (IF D FOO 'T))))

; and then a rudimentary strip branches produces the pairs:

; (((A) . FOO)
;  ((-A B) . FOO)
;  ((-A -B C) . FOO)
;  ((-A -B -C D) . FOO))

; Our job now is to clean this up by getting rid of unnecessary hyps to produce:

; (((A) . FOO)
;  ((B) . FOO)
;  ((C) . FOO)
;  ((D) . FOO))

; This is done quite nicely by the subsumption-replacement loop in clausify.
; But we don't have clausify.

(defun complementaryp (lit1 lit2)
  (declare (xargs :guard (and (pseudo-termp lit1)
                              (pseudo-termp lit2))))

; Suppose lit1 and lit2 are terms and neither is of the form (NOT (NOT &)).
; Then we determine whether one is the complement of the other, i.e., one
; is (NOT lit) where lit is the other.  Note that we do not use any
; commutativity knowledge.  Thus,

; WARNING:  (EQUAL A B) and (NOT (EQUAL B A)) are *not* complementaryp, by
; this definition!

  (or (and (ffn-symb-p lit1 'not)
           (equal (fargn lit1 1) lit2))
      (and (ffn-symb-p lit2 'not)
           (equal (fargn lit2 1) lit1))))

; Note on Terminology: Below we use the expression ``ancestor literal'' which
; was introduced by Bob Kowalski in the early 1970s to name a literal
; previously resolved upon in an SL-resolution proof.  Our ancestor literals
; are similar in spirit but we make no claim that they are the exactly the same
; as Kowalski's; they may be, but we haven't thought about it.  The word
; ``ancestor'' is just appropriate.  We define our use of the term below.

(defun subsumes-but-for-one-negation (hyps1 hyps2 ancestor-lits)

; First, think of hyps1 and hyps2 as merely sets of literals.  This function
; returns either nil or identifies a literal, lit, in hyps1, whose complement,
; lit', occurs in hyps2, and such that the result of removing lit from hyps1 is
; a subset of hyps2.  It ``identifies'' that literal by returning the non-nil
; list whose car is lit' (the element of hyps2) and whose cdr is ancestor-lits,
; i.e., (cons lit' ancestor-lits).  We call lit' an ``ancestor literal'' in
; this context.

; However, what we check is weaker than the spec above.  Our requirement on
; this function is that when it is non-nil. the result is as described above.
; However, if the function returns nil it does not mean there is no such lit!
; It only means we failed to find it.

; What we actually check is this: Let lit be the first literal of hyps1 that is
; not equal to its counterpart at the same position in hyps2.  Let tail1 be the
; remaining literals of hyps1.  Let tail2 be the tail of hyps2 starting with
; the counterpart of lit.  Then we insist that somewhere in tail2 the
; complement, lit', of lit appears, that every literal passed before the first
; occurrence of lit' is in ancestor-lits, and that tail1 is a subset of the
; rest of tail2 from the point at which lit' was found.  We return either nil
; or (cons lit' ancestor-lits) depending on whether these conditions hold.

; Thus, if this function returns non-nil, the lit' it identifies occurs in
; hyps2, occurs complemented in hyps1, and all the other literals of hyps1 are
; in hyps2.

; In this function, one may think of ancestor-lits merely as heuristic
; ``permissions'' to scan deeper into hyps2 to find the complement of lit.  But
; in subsequent functions it will play a crucial soundness role.

  (cond ((endp hyps1) nil)
        ((endp hyps2) nil)
        ((equal (car hyps1) (car hyps2))
         (subsumes-but-for-one-negation (cdr hyps1) (cdr hyps2) ancestor-lits))
        ((complementaryp (car hyps1) (car hyps2))
         (if (subsetp-equal (cdr hyps1) (cdr hyps2))
             (cons (car hyps2) ancestor-lits)
             nil))
        ((member-equal (car hyps2) ancestor-lits)
         (subsumes-but-for-one-negation hyps1 (cdr hyps2) ancestor-lits))
        (t nil)))

; On Removal of Ancestor Literals -- The Satriani Hack Prequel

; Pair1 is a (hyps . concl) pair, say (hyps1 . concl1) and pairs is a list of
; such pairs.  We ``clean up'' pairs with a very limited one-pass
; ``subsumption-replacement'' loop.  The idea is to use pair1 to clean up the
; first pair of pairs, pair2, producing new-pair2.  Then we use new-pair2 to
; clean up the next pair of pairs, etc.  The tricky bit is the use of
; ancestor-lits, which is accumulated from all the pairs we've cleaned up and
; the maintenance of which is crucial to soundness.  This entire body of code
; is reminiscent of the Satriani Hack, which is actually a little more
; elaborate (and slower) because it checks for subsumptions we don't here.

; We can ``use pair1 to clean pair2'' if the following three conditions hold:
; (a) they have the same concls, (b) there is a literal, lit, of the hyps of
; pair1 that appears complemented in the hyps of pair2, and (c) removing lit
; from the hyps of pair1 produces a subset of the hyps of pair2.  Note that
; conditions (b) and (c) are assured by subsumes-but-for-one-negation, which
; treats ancestor-lits merely as heuristic permissions to scan further.

; If we can use pair1 to clean up pair2, and the complement of the identified
; lit is lit', then we ``clean up pair2'' by removing from its hyps not just
; lit' but all the ancestor-lits!

; In the discussion below we call lit' the ``ancestor literal'' of the cleaned
; up pair2.  The ancestor literal of a newly derived pair is the literal
; removed from the parent pair.  Its complement occurs as a hyp in an earlier
; pair and that earlier pair's other hyps all occur in the newly derived pair.

; For example, if pair1 is ((A B C) . concl) and pair2 is ((A -B C D) . concl)
; then we can use pair1 to clean up pair2 and the process of checking that
; identifies -B as an ancestor literal.  Cleaning up pair2 produces pair2', ((A
; C D) . concl) and -B is the ancestor of literal of that pair in the context
; of this derivation.

; Why is it sound to clean up this way?  We start with two observations.

; Observation 1.  If we have two theorems of the form ((H1 & p) --> c) and ((H2
; & -p) --> c), where H1 is a subset of H2, then we can replace the second with
; (H2 --> c).  This is most easily seen by putting the first into
; contrapositive form, ((H1 & -c) --> -p), and observing that we can then
; rewrite the -p in the second theorem to T.

; Observation 2: We maintain the following invariant about ancestors-lits and the
; ``current'' pair (the car of pairs), which we call pair2 in the statement of
; the invariant:

;    for every element, lit' (with complement lit), of ancestor-lits there
;    exists a pair, say pair', among those we have already collected such that
;    the concl of pair' is the concl of the pair2, lit occurs in the hyps of
;    pair', and the remaining hyps of pair' form a subset of the hyps of pair2.

; If this invariant is true, then we can remove every ancestor-lit from pair2.
; The previous pair' can with Observation 1 to remove each ancestor.  Note that
; lit' may not appear in the hyps of pair2.

; One might wonder what gives us the right, subsequently, to remove the
; ancestor lit of pair2 from the next pair encountered, even though we just
; check that those hyps, which may be missing lit', are a subset of the next
; pair.  The invariant insures we can.  But if this conundrum bothers you,
; just add lit' as a hyp to pair2: it is never unsound to add a hypothesis to a
; theorem!  [The key part of the invariant is that, except for lit, the hyps of
; pair' are members of the hyps of pair2.]

; The invariant in Observation 2 is clearly true when ancestors-lit is nil, and
; inspection of the code below shows that we make it nil when the concls of two
; successive pairs are not equal and when the hyps of one are not in the
; appropriate subset relation with the next.  The only time we add a lit' to
; ancestors-lit we know that lit is a member of the hyps pair1 (which we
; collect) and that the rest of the hyps of pair1 are a subset of the hyps of
; pair2.  Since subset is transitive, we know that the pairs from which the
; ancestors lit descend (minus the lit in question) are all subsets of the hyps
; of the last pair collected.

; Here is an example of this process:

; Suppose we have:
; pairs                                 pairs'                      ancestor-lits
; [1] x y  A u --> concl                [1'] x y A u --> concl
; [2] x y -A  B u v --> concl           [2'] x y B u v --> concl           -A
; [3] x y -A -B  C u v w --> concl      [3'] x y C u v w --> concl      -B -A

; ----- let's consider the next step ---

; [4] x y -A -B -C  D u v w z --> concl [4'] x y D u v w z --> concl -C -B -A

; By the time we use [2] to clean up [3] to produce [3'], we're the state shown
; above the ``let's consider'' line.  We will next produce [4'] from [3'] and
; [4].  Using Observation 1, [3'] allows us to knock off the -C from [4]
; because the concls of [3'] and [4] are the same and the hyps of [3'] are a
; subset of those of [4] except for the literal C which appears negated in the
; hyps of [4].  -C is the ancestor literal of this step.

; We thus get to remove -C from [4] and add -C to the ancestor lits going
; forward.  But we also get to remove the other ancestor lits, -B and -A.  We
; show why below.

; Why can we remove -B? By the invariant, we know there exists a pair' among
; those we have already collected such that the concl of pair' is the concl of
; the [4], B occurs in the hyps of pair', and the remaining hyps of pair' form
; a subset of the hyps of [4].  The pair' in question is [2'] and it allows us
; to drop -B from [4].

; Why can we remove -A? By the invariant, we know there exists a pair' among
; those we have already collected such that the concl of pair' is the concl of
; [4], A occurs in the hyps of pair', and the remaining hyps of pair' form a
; subset of the hyps of [4].  The pair' in question is [1'] and it allows us to
; drop -A from [4].

; In this example, all the ancestor lits are in the current pair.  But that need
; not be true.  For example, imagine that [4] did not contain -A.

; [4] x y    -B -C  D u v w z --> concl [4'] x y D u v w z --> concl -C -B -A

; The presence of -A in ancestors still means there is a collected pair, pair',
; that would allow us to delete A because the other hyps of pair' are a subset
; of [4].  We know the subset relation holds because the hyps of [1'] (minus A)
; are a subset of [2'], the hyps of [2'] (minus B) are a subset of those of
; [3'], and the hyps of [3'] (minus C) are a subset of those of [4].  So we
; COULD delete -A even if it weren't there!

; The function remove-ancestor-literals-from-pairs below is the top-level
; entry to this process.  It takes a list of pairs, uses the first one as
; pair1 and the rest as pairs.  The initial ancestor-lits is nil.

; Here are some examples of the function in action.  These examples show how we
; are sensitive to the order of the literals.  This sensitivity is deemed
; unimportant because stripping the branches of normalized IFs produces the
; regular order that we exploit.

;   (remove-ancestor-literals-from-pairs
;    '(((x y  A        u) . concl)
;      ((x y (NOT A)  B        u v) . concl)
;      ((x y (NOT A) (NOT B)  C        u v w) . concl)
;      ((x y (NOT A) (NOT B) (NOT C) D u v w z) . concl)))
;   =
;   (((x y A u) . concl)
;    ((x y B u v) . concl)
;    ((x y C u v w) . concl)
;    ((x y D u v w z) . concl))

; However, if we permute the first pair we fail to get any of the -A, but we do
; knock off the -B, -C, and -D:

;   (remove-ancestor-literals-from-pairs
;    '(((x A  y        u) . concl)
;      ((x y (NOT A)  B        u v) . concl)
;      ((x y (NOT A) (NOT B)  C        u v w) . concl)
;      ((x y (NOT A) (NOT B) (NOT C) D u v w z) . concl)))
;   =
;   (((x A y u) . concl)
;    ((x y (not A) B u v) . concl)
;    ((x y (not A) C u v w) . concl)
;    ((x y (not A) D u v w z) . concl))

; Similarly, if the second pair fails the subset test, we start over.

;   (remove-ancestor-literals-from-pairs
;    '(((x y  A           u1) . concl)
;      ((x y (NOT A)  B        u1 v) . concl)
;      ((x y         (NOT B)  C        u2 v w) . concl)
;      ((x y (NOT A) (NOT B) (NOT C) D u2 v w z) . concl)))
;   =
;   (((x y A u1) . concl)
;    ((x y B u1 v) . concl)
;    ((x y (not B) C u2 v w) . concl)
;    ((x y (not A) (not B) (not C) D u2 v w z) . concl))

; Note that we do not get to knock off the -B in the third pair or the -A and
; -B in the fourth, because u1 is not u2.  We would actually be justified in
; knocking off the -C in the fourth, but we fail to find it because -A is
; blocking the subset check for going deep enough to find the -C.  We would get
; the improved result if we permuted the fourth input pair:

;   (remove-ancestor-literals-from-pairs
;    '(((x y  A           u1) . concl)
;      ((x y (NOT A)  B        u1 v) . concl)
;      ((x y         (NOT B)  C        u2 v w) . concl)
;   ; On the next line, moved the -A to end.
;      ((x y         (NOT B) (NOT C) D u2 v w z (NOT A)) . concl)))
;   =
;   (((x y A u1) . concl)
;    ((x y B u1 v) . concl)
;    ((x y (not B) C u2 v w) . concl)
;    ((x y (not B) D u2 v w z (not A)) . concl))

; Returning to the first, classic, example but changing the concl of the last
; two rules:

;   (remove-ancestor-literals-from-pairs
;    '(((x y  A        u) . concl1)
;      ((x y (NOT A)  B        u v) . concl1)
;      ((x y (NOT A) (NOT B)  C        u v w) . concl2)
;      ((x y (NOT A) (NOT B) (NOT C) D u v w z) . concl2)))
;   =
;   (((x y A u) . concl1)
;    ((x y B u v) . concl1)
;    ((x y (not A) (not B) C u v w) . concl2)
;    ((x y (not A) (not B) D u v w z) . concl2))

; we see we simplify the two concl1 pairs and the two concl2 pairs, but we
; don't carry over from concl1 to concl2.

(defun remove-ancestor-literals-from-pairs1 (pair1 pairs ancestor-lits)

; See the discussion above On Removal of Ancestor Literals -- The Satriani Hack
; Prequel

  (cond
   ((endp pairs) nil)
   (t (let ((pair2 (car pairs)))
        (cond
         ((equal (cdr pair1) (cdr pair2))
          (let ((new-ancestor-lits
                 (subsumes-but-for-one-negation (car pair1) (car pair2)
                                                ancestor-lits)))
            (cond
             (new-ancestor-lits
              (let ((new-pair2 (cons (set-difference-equal (car pair2)
                                                           new-ancestor-lits)
                                     (cdr pair2))))
                (cons new-pair2
                      (remove-ancestor-literals-from-pairs1
                       new-pair2 (cdr pairs) new-ancestor-lits))))
             (t (cons pair2
                      (remove-ancestor-literals-from-pairs1
                       pair2 (cdr pairs) nil))))))
         (t (cons pair2
                  (remove-ancestor-literals-from-pairs1
                   pair2 (cdr pairs) nil))))))))

(defun remove-ancestor-literals-from-pairs (pairs)

; See the discussion above On Removal of Ancestor Literals -- The Satriani Hack
; Prequel for a thorough treatment of this function.  Pairs is a list of (hyps
; . concl) pairs and we clean it up -- eliminating unnecessary hyps -- using a
; very limited form of subsumption-replacement akin to the Satriani Hack.

  (cond ((endp pairs) nil)
        ((endp (cdr pairs)) pairs)
        (t (cons (car pairs)
                 (remove-ancestor-literals-from-pairs1
                  (car pairs) (cdr pairs) nil)))))

(defun convert-term-to-pairs (term ens wrld)

; Term is assumed to be the result of expanding a tau-like-propositionp.  Thus,
; it is a term composed entirely of T, NIL, (recog var), and IF expressions
; composed of such terms.  We wish to convert term to a list of (hyps . concl) pairs.

  (mv-let (nterm ttree)
          (normalize term t nil ens wrld nil
                     (backchain-limit wrld :ts))
          (mv (remove-ancestor-literals-from-pairs
               (convert-normalized-term-to-pairs nil nterm nil))
              (all-runes-in-ttree ttree nil))))

; On the Motivation for Tau-Subrs

; Consider two tau recognizers, A and B, and their conjunction as another tau
; recognizer, AB.  Suppose we know the theorem (AB x) --> (AB (fn x)) as a tau
; signature rule.  Then does tau prove that same theorem?  No!

; The reason is that preprocess-clause, which tries tau-clausep, expands some
; functions.  It will expand the (AB x) in the hypothesis, because it is a
; conjunction, but it will not expand it in the conclusion.  The result is that
; tau-clausep is presented with: ((NOT (A x)) (NOT (B x)) (AB (fn x))) and
; without some more work, tau does not know know that A & B --> AB.  That is
; the role of tau-subrs below.  It essentially recognizes nonrecursive
; conjunctions of tau and adds the appropriate tau rules in both directions:
; (A & B) --> AB and AB --> A and AB --> B.

; Below is an example.  The first thm below failed until tau-subrs was implemented.

; (defun A (x) (integerp x))
; (defun B (x) (< 1000 x))

; (defun AB (x) (and (A x)(B x)))

; (defun fn (x) (+ x 1))
; (defthm fn-sig
;   (implies (AB x) (AB (fn x)))
;   :rule-classes :tau-system)

; We disable B to keep the example simple.  As an extra stressor on tau during
; this experiment, we leave A enabled so that its (trivial) conjunctive nature
; must be also exploited by tau.

; (in-theory (disable fn B))

; This should succeed whether AB is enabled or not.  The first thm failed
; before tau-subr was added.

; (thm (implies (AB x) (AB (fn x))) :hints (("Goal" :in-theory (enable AB))))
; (thm (implies (AB x) (AB (fn x))) :hints (("Goal" :in-theory (disable AB))))

; Now for the disjunctive analogue:

; (defun C (x) (stringp x))
; (defun AC (x) (or (A x) (C x)))
; (defun gn (x) (if (integerp x) (if (< 999 x) "NaN" (+ x 1)) "NaN"))
; (defthm gn-sig
;   (implies (AC x) (AC (gn x)))
;   :rule-classes :tau-system :hints (("Goal" :in-theory (enable A))))
; (thm (implies (AC x) (AC (gn x)))  :hints (("Goal" :in-theory (enable AC))))
; (thm (implies (AC x) (AC (gn x)))  :hints (("Goal" :in-theory (disable AC))))

(defun tau-subrs (rune fn formals rhs ens wrld)

; See the On the Motivation for Tau-Subrs for some background.

; We know fn is a non-rec monadic Boolean, formals has one element, v, rhs is
; the body of fn.  Thus, (fn v) --> rhs and rhs --> (fn v).  However, we only
; add the corresponding tau rules if rhs is a propositional combination of
; tau-like :same-var terms.  So, for example, rhs might be (and (A x) (B x))
; or (or (A x) (and (B x) (C x))) but may not contain interesting non-tau
; functions.  If rhs is a propositional combination of tau-like terms, we add
; the rules that link fn to the subroutines in rhs.

  (let ((var (car formals)))
    (cond
     ((tau-like-propositionp var rhs wrld)
      (let* ((lhs (fcons-term fn formals))
             (rhs1 (expand-tau-like-proposition rhs)))
        (mv-let
         (pairs1 runes1)
         (convert-term-to-pairs
          (fcons-term* 'IF lhs rhs1 *t*) ens wrld)
         (mv-let
          (pairs2 runes2)
          (convert-term-to-pairs
           (fcons-term* 'IF rhs1 lhs *t*) ens wrld)

; We only consider the possibilities of these clauses being Simple or
; Conjunctive rules.  We do not think they could be signature rules because of
; the tau-like-propositionp condition, but we take no chances.  We also
; store in tau-runes all the runes used in the normalization of the body.

          (let ((wrld
                 (add-only-simple-and-conjunctive-tau-rules
                  rune
                  pairs1
                  ens
                  (add-only-simple-and-conjunctive-tau-rules
                   rune
                   pairs2
                   ens wrld))))
            (set-tau-runes 'list (union-equal runes1 runes2) wrld))))))
     (t wrld))))

(defun tau-visit-defuns1 (fns ens wrld wrld0)

; This function is a subroutine of tau-visit-defuns and should only be called
; if tau is in automatic mode.  We collect the big-switch, mv-nth-synonym, and
; signature rules, if any for the given ens, for each fn in fns.  We obey the
; Tau Msgp Protocol and return (msgp wrld'); No Change Loser on wrld0.


  (cond
   ((endp fns) (mv nil wrld))
   (t
    (let* ((fn (car fns))
           (db (original-def-body fn wrld))
           (formals (access def-body db :formals))
           (rhs (access def-body db :concl))
           (def-eqn
             (cond
              ((null db) nil)
              ((or (access def-body db :hyp)
                   (not (eq (access def-body db :equiv)
                            'equal)))
               nil)
              (t
               (fcons-term* 'equal
                            (fcons-term fn formals)
                            rhs))))
           (def-nume (access def-body db :nume))
           (def-rune (access def-body db :rune)))

; First, we collect the big-switch and mv-nth-synonym rules (if any) from fn,
; provided the definitional equation is enabled in ens.  It is impossible for
; fn to be both a big switch and an mv-nth synonym.  Note also that the def-eqn
; is nil if it somehow has hypotheses.

      (let ((wrld
             (cond
              ((or (null def-eqn)
                   (not (enabled-numep def-nume ens)))
               wrld)
              ((tau-big-switch-equationp def-eqn wrld)
               (add-tau-big-switch-rule def-rune nil def-eqn wrld))
              ((tau-mv-nth-synonym-formp nil def-eqn)
               (add-tau-mv-nth-synonym-rule def-rune nil def-eqn wrld))
              (t (tau-subrs def-rune fn formals rhs ens wrld)))))
        (mv-let (msgp wrld)
                (tau-rules-from-type-prescriptions
                 (getpropc fn 'type-prescriptions nil wrld)
                 fn ens wrld wrld0)
                (cond
                 (msgp (mv msgp wrld0))
                 (t
                  (tau-visit-defuns1 (cdr fns) ens wrld wrld0)))))))))

(defun tau-visit-defuns (fns auto-modep ens wrld0)

; This is the function the tau system uses to update the tau database in
; response to a mutual-recursion event.  Every element of fns is a defined
; function in wrld0.  That means that each has all the properties one would
; expect of a defined function except the tau properties, which are determined
; below.  We assume that all tau properties of the fns in question are cleared
; (either because this is the first visit and the fns are all new or because we
; are in a tau regeneration and we have already visited the corresponding
; function introductions.

; We follow the Tau Msgp Protocol and return (mv msgp wrld').  No Change Loser
; on wrld0.

; We identify all the tau recognizers before we start to process any other kind
; of tau rules, so that if a mutually recursive nest introduces several
; recognizers, we treat them all appropriately when doing the syntactic checks
; for other rules.  We discover the tau recognizers among defun'd functions
; whether or not we are in automatic mode.

  (let* ((wrld (discover-tau-preds fns ens wrld0)))

; Then, if in auto mode, gather the big-switch, mv-nth-synonym, and signature
; rules for each member of fns.

    (if auto-modep
        (tau-visit-defuns1 fns ens wrld wrld0)
        (mv nil wrld))))

(defun tau-visit-defun (fn auto-modep ens wrld0)

; This function updates the tau database in response to a single defun.
; It is just a special case of mutual-recursion.  We obey the Tau
; Msgp Protocol and return (mv msgp wrld'); No Change Loser on wrld0.

  (tau-visit-defuns (list fn) auto-modep ens wrld0))

; Next we implement the tau visit to a defthm event.  In manual mode, all we do
; is add the ens-enabled explicit :tau-system rules originally introduced by
; this event.  In automatic mode, we mine each of the ens-enabled
; non-:tau-system rules.  But there are four nuances.

; First, what if an event has both :tau-system and non-:tau-system rules and we
; are in automatic mode?  Do we look for tau rules among the non-:tau-system
; rules?  Our answer to that is no: if the user mentions :tau-system rules in
; an event, we assume that those are the only tau rules wanted.  We think it
; would be too confusing if the user has to think about the impact of his
; non-:tau-system rules while being explicit with his :tau-system rules.  If
; there is no mention of :tau-system rules and we're in automatic mode, we look
; for implicit rules.

; Second, how does the ens affect this analysis?  What if an event has an
; explicit :tau-system rule and it is disabled in ens?  Do we act as though
; that rule class were not present and look for implicit rules?  Or does the
; presence of a :tau-system rule, even a disabled one, signal that the user did
; not intend for the other rules to be mined?  Our answer is that the presence
; of a :tau-system rule signals that nothing automatic should be done, even if
; the :tau-system rule is disabled.  Note that an event might have several
; :tau-system rules, under different runes, and some might be enabled and other
; disabled.  Still, our analysis is the same: Any :tau-system rule in the
; original event means we look only at :tau-system rules and add the ones that
; are enabled.

; Third, this whole discussion suggests that an event has "enabled rules" but
; the chain of possession is more involved.  An event name has (truncated)
; rule-classes and runic-mapping-pairs (which are in 1:1 correspondence),
; truncated rule-classes each have a :corollary keyword (or not, in which case
; the event's theorem is to be used), rules are derived from corollaries, rules
; have runes, and runes are enabled or disabled.  So we have to deal with this
; mapping.

; Fourth, what do we do if an explicit :tau-system rule cannot be stored as a
; tau rule?  This will not happen during the original execution of the
; introductory event: chk-acceptable-rules will detect the problem and signal a
; soft error.  But it is possible in subsequent visits to a :tau-system rule.
; For example, perhaps a monadic function symbol that was previously
; recognized as Boolean is no longer so recognized because of ens.  We believe
; that even a soft error in this situation is unduly harsh.  The user is
; unlikely to know ahead of time that the ens will have that effect.  Our
; design is to keep a list of ``lost'' runes to be printed at the end of the
; regeneration process.  However, this means we must know while processing
; corollaries whether we are to signal an error or add the rune to the lost
; runes.

(defun corollaries-and-runes-of-enabled-rules
  (tau-system-onlyp rule-classes runic-mapping-pairs ens theorem)

; We map over rule-classes and runic-mapping-pairs in parallel and collect the
; corollaries of those rules that are enabled in ens.  We return a list of
; pairs, (formula . rune), where formula is the corollary of a collected rule
; and rune is its rune.  If tau-system-onlyp is on, we only collect such
; :tau-system rules, otherwise we collect all types of rules.  The given
; rule-classes have been ``truncated,'' which means that the :corollary has
; been omitted if the formula was the same as the 'theorem property of the
; event.  So this function is also given the theorem property of the event.

  (cond
   ((endp rule-classes) nil)
   (t (let* ((class-name (car (car rule-classes)))
             (formula
              (or (cadr (assoc-keyword :corollary (cdr (car rule-classes))))
                  theorem))
             (nume (car (car runic-mapping-pairs)))
             (rune (cdr (car runic-mapping-pairs)))
             (rest (corollaries-and-runes-of-enabled-rules
                    tau-system-onlyp
                    (cdr rule-classes)
                    (cdr runic-mapping-pairs)
                    ens theorem)))
        (cond
         ((and (or (not tau-system-onlyp)
                   (eq class-name :tau-system))
               (enabled-numep nume ens))
          (cons (cons formula rune) rest))
         (t rest))))))

(defun tau-visit-defthm1 (first-visitp terms-and-runes ens wrld wrld0)

; Terms-and-runes is a list of pairs, each of the form (term . rune), where
; term is a translated term used to create a rule, rune is its rune, and it is
; known that rune is enabled in the ens in question (which is not provided
; here).  We extend wrld with the tau rules we can get from the terms and add
; each rune so used to tau-runes.  We obey the Tau Msgp Protocol and return (mv
; msgp wrld'); No Change Loser on wrld0.

  (cond
   ((endp terms-and-runes) (mv nil wrld))
   (t (let ((term (car (car terms-and-runes)))
            (rune (cdr (car terms-and-runes))))

; We know rune is enabled since terms-and-runes is constructed that way.

        (mv-let (msgp wrld)
                (add-tau-rule first-visitp rune term ens wrld)
                (cond
                 (msgp (mv msgp wrld0))
                 (t (tau-visit-defthm1 first-visitp
                                       (cdr terms-and-runes)
                                       ens wrld wrld0))))))))

(defun tau-visit-defthm (first-visitp name auto-modep ens wrld0)

; This is the function the tau system uses to update the tau database in
; response to a defthm event named name, which has been introduced into wrld0.
; We follow the Tau Msgp Protocol and return (mv msgp wrld').  No Change Loser
; on wrld0.

  (let* ((classes (getpropc name 'classes nil wrld0))
         (terms-and-runes
          (corollaries-and-runes-of-enabled-rules
           (or (not auto-modep)
               (assoc-eq :tau-system classes))
           classes
           (getpropc name 'runic-mapping-pairs nil wrld0)
           ens
           (getpropc name 'theorem nil wrld0))))
    (tau-visit-defthm1 first-visitp terms-and-runes ens wrld0 wrld0)))

(defun tau-visit-event (first-visitp ev-type namex auto-modep ens
                                     ctx wrld state)

; This is the function tau uses to visit an event that was carried out in wrld.
; It is assumed that all the function symbols encountered in this event are new
; to tau, because the function symbols were either all new or introductions
; were made chronologically earlier in world and visited by tau before getting
; here.

; First-timep is t if this function is being called from install-event and is
; nil if it is being called while regenerating the tau database.  The flag
; affects whether we signal an error or quietly accumulate lost :tau-system
; runes.  Ev-type is the name of the primitive event macro that created the
; event.  The only values of interest to tau are DEFUN, DEFUNS, ENCAPSULATE,
; DEFCHOOSE, DEFTHM, and DEFAXIOM.  Namex is either a list of names, a single
; name, or 0 indicating the names introduced by the event (0 means no names
; were introduced).

; DEFSTOBJ and DEFABSSTOBJ introduce function symbols, some of which are even
; monadic Booleans.  But we ignore DEFSTOBJ and DEFABSSTOBJ here.  Why?
; Because all of the functions that they introduce are introduced by embedded
; defun events and so we will find defun event-tuples for each.

; ENCAPSULATE introduces function symbols, some of which may be monadic
; Booleans or have other tau properties.  But all these properties are
; established by embedded defun/defthm events.

; DEFCHOOSE introduces a function symbol.  But at the time of this writing the
; constraint cannot possibly be of interest to tau.  For example, could a
; defchoose event make fn a monadic Boolean?  Not syntactically.  We come close
; with:

; (defchoose pick-a-bool (x) (y) (booleanp x))

; but that would give the constraint:

; (implies (booleanp x)
;          (booleanp (pick-a-bool y)))

; from which one could prove (booleanp (pick-a-bool y)).  So the axiom that
; exists after the defchoose is not syntactically acceptable for a tau Boolean
; rule and the revelation that pick-a-bool is in fact Boolean only comes via a
; subsequent defthm event which will be visited eventually.  By similar
; reasoning, we the defchoose axiom can never be a big-switch or an mv-nth
; synonym.

  (mv-let (msgp wrld1)
          (case ev-type
            (DEFUN (tau-visit-defun namex auto-modep ens wrld))
            (DEFUNS (tau-visit-defuns namex auto-modep ens wrld))
            ((DEFTHM DEFAXIOM)
             (tau-visit-defthm first-visitp namex auto-modep ens wrld))
            (otherwise (mv nil wrld)))
          (cond
           (msgp
            (er soft ctx "~@0" msgp))
           (t (value wrld1)))))

; -----------------------------------------------------------------
; Using Conjunctive and Signature Rules

(defun apply-conjunctive-tau-rule (tau1 tau2 ens wrld)

; This function checks the conditions for a conjunctive tau rule, tau1, to
; apply.  It is given tau2, the set of all known recognizers.  It returns (mv
; contradictionp sign recog), contradictionp is t if the known facts contradict
; the rule.  If contradictionp is nil, then recog determines if the conditions
; are met: recog = nil means the rule cannot be fired.  Otherwise, sign/recog
; should be added to set of known recognizers.  However, the caller is
; responsible for adding it.  Sign is irrelevant if recog = nil.

; Recall: The theorem (implies (and a (not b) c) d) produces the Conjunctive
; rule {a (not b) c (not d)}, represented as a tau.  Note that if
; the first three elements are in the set of known recognizers, then we can add
; the negation of the last to the set.  More generally, if all but one of the
; elements of the conjunctive rule are known, we can add the negation of the
; unknown one.  If every element of the conjunctive rule is known, we have a
; contradiction.

  (mv-let
   (contradictionp sign recog)
   (tau-near-subsetp tau1 tau2 ens wrld)
   (cond
    (contradictionp (mv t nil nil))

; Note:  If the rule didn't fire, the returned recog is nil, even though sign
; might be t.

    (t (mv nil (not sign) recog)))))

(defun apply-conjunctive-tau-rules2 (conjunctive-rules tau ens wrld changedp)

; We map over the list of conjunctive tau rules, trying each wrt the known
; recognizers in tau.  We extend tau as rules fire and set changedp if any rule
; fires.  We return (mv changedp tau'), where tau' may be *tau-contradiction*.
; We assume tau is not *tau-contradiction* to begin with!

  (cond
   ((endp conjunctive-rules) (mv changedp tau))
   (t (mv-let
       (contradictionp sign recog)
       (apply-conjunctive-tau-rule (car conjunctive-rules) tau ens wrld)
       (cond
        (contradictionp
         (mv t *tau-contradiction*))
        ((null recog)
         (apply-conjunctive-tau-rules2
          (cdr conjunctive-rules)
          tau ens wrld
          changedp))
        (t (let ((new-tau
                  (add-to-tau sign recog tau ens wrld)))
             (cond ((eq new-tau *tau-contradiction*)
                    (mv t *tau-contradiction*))
                   (t (apply-conjunctive-tau-rules2
                       (cdr conjunctive-rules)
                       new-tau
                       ens wrld
                       (or changedp
                           (not (equal tau new-tau)))))))))))))

(defun apply-conjunctive-tau-rules1 (conjunctive-rules tau ens wrld max-loop)

; This function repeatedly applies conjunctive rules until no changes occur.
; It returns just the extended tau, which might be *tau-contradiction*.  We
; assume tau is not *tau-contradiction* to begin with!

; Max-loop is nil or a natp and controls how many times we iterate.  Max-loop =
; nil means loop until tau stabilizes.

  (if (and max-loop
           (equal max-loop 0))
      tau
      (mv-let (changedp tau)
              (apply-conjunctive-tau-rules2 conjunctive-rules tau ens wrld nil)
              (cond
               ((eq tau *tau-contradiction*)
                *tau-contradiction*)
               (changedp
                (apply-conjunctive-tau-rules1 conjunctive-rules tau ens wrld
                                              (if max-loop
                                                  (- max-loop 1)
                                                  nil)))
               (t tau)))))

; On the Tau Completion Alist (calist)

; We call the process of extending a tau with conjunction rules ``completion.''
; Completion can be quite expensive.  We therefore remember all the tau we have
; completed in a given proof and look up the answers when we can.  We use a
; simple alist mapping input (partial) tau to output (completed) tau.  The
; alist, called calist, is accumulated throughout an entire proof and is stored
; in the pspv when we're not in tau.  This mechanism may become too expensive
; if there are a lot of different partial tau involved in a proof.  But out
; experience so far is that the number is reasonable.

; For example, consider the community book
; books/centaur/vl/transforms/xf-expr-simp.lisp and the event within it:
; (verify-guards vl-expr-simp).  If one modifies these sources so as to ignore
; the values found in the calist (just choose the second t clause below) then
; the verify-guards event named above takes about 42 seconds to process (on a
; 2.6 GHz Intel Core i7 with 16 GB 1600 MHz DDR3 Macbook Pro).  If one uses the
; values in calist, then it takes about 6 seconds.  In all, 50 different
; partial tau are mentioned in this proof.  Completion is called about 41,000
; times on these various tau -- some as many as 6,000 times each.  49 different
; complete tau are generated.  27 of the 50 partial tau are changed by
; completion and the other 23 are actually already complete.  (Note that since
; we know that the val we compute is complete, we could pair it with itself on
; the new calist.  However, this does not gain anything in this particular
; test.  Apparently we often compute tau and do not even try to subsequently
; complete them so remembering the already completed ones is not much help.)

(defun apply-conjunctive-tau-rules (tau ens wrld calist)
  (cond ((eq tau *tau-contradiction*)
         (mv *tau-contradiction* calist))
        (t
         (let ((temp (assoc-equal tau calist)))
           (cond
            (temp (mv (cdr temp) calist))
            (t (let ((val (apply-conjunctive-tau-rules1
                           (getpropc 'tau-conjunctive-rules
                                     'global-value
                                     nil
                                     wrld)
                           tau
                           ens
                           wrld
                           nil)))
                 (mv val (cons (cons tau val) calist)))))))))

(defun add-to-tau! (sign recog tau ens wrld calist)

; Recog is a tau-pair or singleton evg list or else the special symbol :SKIP.
; Tau is a tau object, not *tau-contradiction*.  We add sign/recog, its
; implicants, and all conjunctive rules to tau.  We return tau', where tau' may
; be *tau-contradiction*.  When recog is :SKIP it means ``don't really add
; anything to tau, just apply conjunctive rules!''

  (let ((new-tau (if (eq recog :SKIP)
                     tau
                     (add-to-tau sign recog tau ens wrld))))
    (cond ((and (not (eq recog :SKIP))
                (equal tau new-tau))
           (mv tau calist))
          (t (apply-conjunctive-tau-rules new-tau ens wrld calist)))))

; -----------------------------------------------------------------
; Dealing with Terms

; We now turn our attention to computing the recognizer sets of terms
; and maintaining a list of assumptions about terms.  We start by
; using signature rules.  Then we will define how to use an alist of
; tau assumptions to compute the tau of a term.  Then we will define
; how to build an alist of tau assumptions.

; A slightly confusing fact about signature rules is that both form 1 and form
; 2 rules are the same.  The first applies to expressions like (fn a b) and the
; second applies to expressions like (mv-nth 'i (fn a b)).  To fire a rule, we
; just need to know whether a and b have appropriate tau (and whether the
; dependent hyps are relieved).  If a rule fires, we just need to know the sign
; and recog for the value produced.  We don't actually need to know fn or i or
; even which form of rule we are applying.

(defun all-tau-emptyp (lst)
  (cond ((endp lst) t)
        (t (and (equal (car lst) *tau-empty*)
                (all-tau-emptyp (cdr lst))))))

(defun all-unrestricted-signature-rulesp (sigrules)

; In general, when we see (fn a1 ... an) we will obtain the taus of the actuals,
; and then apply the signature rules of fn to (tau1 ... taun).  However, if all
; the rules for fn have unrestricted inputs, e.g., rules like: (fn *tau-empty*
; ... *tau-empty*) ==> sign/recog as happens for cons (consp), reverse
; (true-listp), member (boolean), etc., there no point in even getting the tau
; of the actuals.  Of course, we must also make sure there are no dependent
; hyps.

  (cond ((endp sigrules) t)
        ((and (null (access signature-rule (car sigrules) :dependent-hyps))
              (all-tau-emptyp (access signature-rule (car sigrules) :input-tau-list)))
         (all-unrestricted-signature-rulesp (cdr sigrules)))
        (t nil)))

; -----------------------------------------------------------------

; On Disjoining Tau

; In trying to compute the tau of (IF a b c), we compute the tau of b and c and
; disjoin them.  Because taus are conjunctions of all the things we know,
; disjoining them is akin to intersecting their representations.  This reduces
; the number of recognizers in them and hence enlarges the set of objects in
; the tau.  For example, if b has a tau that includes P and Q and c has a tau
; that includes P and R, their disjunction includes P but not Q or R.

; We lose a lot of precision in disjoining tau.  Here are two examples.

; For example, b might include RATIONALP and hence also ACL2-NUMBERP; c might
; include INTEGERP and hence also ACL2-NUMBERP; But their disjunction just
; includes ACL2-NUMBERP.  We've lost that it is an integer or a rational.

; Intervals raise another problem.  To take an extreme case, suppose the tau of
; b and c are both equalities-to-constant, say =0 and =100.  Then their
; respective intervals are 0 <= ... <= 0 and 100 <= ... <= 100 and when we
; ``disjoin'' them the only interval we can create that captures both is 0 <=
; ... <= 100.

; Another problem has to do with the fact that some recognizers that ``ought''
; to be in a tau are removed when the tau becomes an equality-to-constant.  For
; example, we might have two taus both of which contain WEEKDAYP.  But then we
; might assert ='MONDAY into one and ='TUESDAY into the other.  These explicit
; constants subsume all the :pos-pairs that compute true on them, and we would
; then drop the WEEKDAYP recognizers from each tau.  But now if we disjoin the
; two tau, we get the empty tau, even though it would have been legitimate to
; produce {WEEKDAYP}

(defun disjoin-intervals (interval1 interval2)

; The two arguments are tau-intervals.  We form the interval that stretches
; from the lower lower bound of the two to the upper upper bound, and has as
; its domain the less restrictive of the two domains.

; Motivation: Suppose we are finding the tau of (IF a b c) and suppose we have
; computed the tau of b and c and that they have intervals interval1 and
; interval2.  Then a tau for (IF a b c) will have the interval we compute
; here.

; The domain of the new interval is the most less restrictive of the two.  For
; example, if one is INTEGERP and the other is RATIONALP, we choose RATIONALP,
; since the first interval is also an interval over the rationals.  Note that
; the only way we can produce an INTEGERP interval is if both are INTEGERP.
; One implication is that the chosen endpoints are known to satisfy the
; requirement on INTEGERP intervals of using the relation <= (nil) and integer
; extends, since both endpoints come from INTEGERP intervals.

; A more problematic issue is whether the new domain is derivable from the
; :pos-pairs of the tau into which we put this interval.  Our computation of
; the :pos-pairs of the new tau will insure that it is because we will
; explicitly include INTEGERP, RATIONALP, or ACL2-NUMBERP as needed.  But it
; was not recognized at first that this would be necessary.  In particular, it
; was thought naively that since the domain was derivable from the :pos-pairs
; of both ancestor taus, it would be derivable from their disjunction.  But
; that argument is naive because it forgets that the :pos-pairs of
; equality-to-constants is empty!  (Recall that when a tau becomes an
; equality-to-constant, we just save those recognizers that won't evaluate
; appropriately on that constant, thus representing all others implicitly.)

; While this handling of the domains of intervals is accurate as far as it
; goes, we really lose a lot of precision in disjoining taus.  See the
; discussion On Disjoining Tau.

  (let* ((dom1 (access tau-interval interval1 :domain))
         (dom2 (access tau-interval interval2 :domain))
         (dom (cond ((eq dom1 dom2) dom1)
                    ((eq dom1 'INTEGERP) dom2)
                    ((eq dom2 'INTEGERP) dom1)
                    ((eq dom1 'RATIONALP) dom2)
                    ((eq dom2 'RATIONALP) dom1)
                    ((eq dom1 'ACL2-NUMBERP) dom2)
                    (t dom1)))
         (lo-rel1 (access tau-interval interval1 :lo-rel))
         (lo-rel2 (access tau-interval interval2 :lo-rel))
         (lo1 (access tau-interval interval1 :lo))
         (lo2 (access tau-interval interval2 :lo))
         (hi-rel1 (access tau-interval interval1 :hi-rel))
         (hi-rel2 (access tau-interval interval2 :hi-rel))
         (hi1 (access tau-interval interval1 :hi))
         (hi2 (access tau-interval interval2 :hi)))
    (mv-let
     (lo-rel lo)
     (if (lower-bound-> lo-rel1 lo1 lo-rel2 lo2)
         (mv lo-rel2 lo2)
         (mv lo-rel1 lo1))
     (mv-let
      (hi-rel hi)
      (if (upper-bound-< hi-rel1 hi1 hi-rel2 hi2)
          (mv hi-rel2 hi2)
          (mv hi-rel1 hi1))
      (if (and (null dom) (null lo) (null hi))
          nil ; universal interval
          (make tau-interval
                :domain dom
                :lo-rel lo-rel
                :lo lo
                :hi-rel hi-rel
                :hi hi))))))

; The following theorem establishes the correctness of disjoin-intervals.  We
; prove below that if int1 and int2 are intervals containing x and y
; respectively, then their disjunction is an interval that contains x and y.
; Recall that intervalp actually requires that its argument be a cons structure
; whereas we sometimes use nil to represent the universal interval in which all
; fields are nil.  Thus, we actually prove that disjoin-intervals is either nil
; or an interval and we allow int1 and int2 the same freedom.

; (verify-termination lower-bound->)
; (verify-termination upper-bound-<)
; (verify-termination disjoin-intervals)

; (thm (implies (and (or (equal int1 nil) (tau-intervalp int1))
;                    (or (equal int2 nil) (tau-intervalp int2))
;                    (in-tau-intervalp x int1)
;                    (in-tau-intervalp y int2))
;               (and (or (equal (disjoin-intervals int1 int2) nil)
;                        (tau-intervalp (disjoin-intervals int1 int2)))
;                    (in-tau-intervalp x (disjoin-intervals int1 int2))
;                    (in-tau-intervalp y (disjoin-intervals int1 int2))
;                    )))

; 52,409 subgoals
; Time:  213.06 seconds (prove: 210.02, print: 3.04, other: 0.00)
; Prover steps counted:  37141155

; While we're at it we also define how to conjoin two intervals, which
; shrinks them:

(defun conjoin-intervals (interval1 interval2)

; The two arguments are tau-intervals.  We form the interval that stretches
; from the upper lower bound of the two to the lower upper bound, and has as
; its domain the more restrictive of the two domains.

; Motivation: Suppose we are finding the tau of a term and know the term lies in
; both interval1 and in interval2.  Then the conjunction of those two intervals
; is a more restrictive interval that contains the term.

; The domain of the new interval is the more restrictive of the two.  For
; example, if one is INTEGERP and the other is RATIONALP, we choose INTEGERP.

; A more problematic issue is whether the new domain is derivable from the
; :pos-pairs of the tau into which we put this interval.  Our computation of
; the :pos-pairs of the new tau will insure that it is because we will
; explicitly include INTEGERP, RATIONALP, or ACL2-NUMBERP as needed.

; If the intervals have an empty intersection, we return *tau-empty-interval*.
; As of this writing (January, 2013, version_6.0+) this is the only place that
; we return the empty interval.

  (let* ((dom1 (access tau-interval interval1 :domain))
         (dom2 (access tau-interval interval2 :domain))
         (dom (cond ((eq dom1 dom2) dom1)
                    ((eq dom1 'INTEGERP) dom1)
                    ((eq dom2 'INTEGERP) dom2)
                    ((eq dom1 'RATIONALP) dom1)
                    ((eq dom2 'RATIONALP) dom2)
                    ((eq dom1 'ACL2-NUMBERP) dom1)
                    (t dom2)))
         (lo-rel1 (access tau-interval interval1 :lo-rel))
         (lo-rel2 (access tau-interval interval2 :lo-rel))
         (lo1 (access tau-interval interval1 :lo))
         (lo2 (access tau-interval interval2 :lo))
         (hi-rel1 (access tau-interval interval1 :hi-rel))
         (hi-rel2 (access tau-interval interval2 :hi-rel))
         (hi1 (access tau-interval interval1 :hi))
         (hi2 (access tau-interval interval2 :hi)))

; If one interval is INTEGERP and the other is not, we first squeeze the
; non-INTEGERP interval down to its integers.

    (mv-let
     (lo-rel1 lo1 hi-rel1 hi1)
     (if (and (eq dom 'INTEGERP)
              (not (eq dom1 'INTEGERP)))
         (mv nil (squeeze-k nil lo-rel1 lo1)
             nil (squeeze-k t   hi-rel1 hi1))
         (mv lo-rel1 lo1 hi-rel1 hi1))
     (mv-let
      (lo-rel2 lo2 hi-rel2 hi2)
      (if (and (eq dom 'INTEGERP)
               (not (eq dom2 'INTEGERP)))
          (mv nil (squeeze-k nil lo-rel2 lo2)
              nil (squeeze-k t   hi-rel2 hi2))
          (mv lo-rel2 lo2 hi-rel2 hi2))

; At this point, if either interval is INTEGERP, both are.  This is necessary
; because the lower-bound-> and upper-bound-< functions require both intervals
; to have the same domains.

      (mv-let
       (lo-rel lo)
       (if (lower-bound-> lo-rel1 lo1 lo-rel2 lo2)
           (mv lo-rel1 lo1)
           (mv lo-rel2 lo2))
       (mv-let
        (hi-rel hi)
        (if (upper-bound-< hi-rel1 hi1 hi-rel2 hi2)
            (mv hi-rel1 hi1)
            (mv hi-rel2 hi2))
        (cond
         ((and (null dom) (null lo) (null hi))
; universal interval -- Don't confuse this with the empty interval!
          nil)
         ((and lo hi
               (if (or lo-rel hi-rel)
                   (>= lo hi)
                   (> lo hi)))
          *tau-empty-interval*)
         (t (make tau-interval
                  :domain dom
                  :lo-rel lo-rel
                  :lo lo
                  :hi-rel hi-rel
                  :hi hi)))))))))

; Here is the correctness of conjoin-intervals.  See the discussion of the correctness of
; disjoin-intervals above.

; (verify-termination lower-bound->)
; (verify-termination upper-bound-<)
; (verify-termination squeeze-k)
; (verify-termination conjoin-intervals)
; (include-book "arithmetic-5/top" :dir :system)

; (defthm lemma
;   (implies (and (rationalp lo)
;                 (not (integerp lo))
;                 (integerp x)
;                 (<= lo x))
;            (<= (+ 1 (floor lo 1)) x))
;   :rule-classes :linear)

; (thm (implies (and (or (equal int1 nil) (tau-intervalp int1))
;                    (or (equal int2 nil) (tau-intervalp int2))
;                    (in-tau-intervalp x int1)
;                    (in-tau-intervalp x int2))
;               (and (or (equal (conjoin-intervals int1 int2) nil)
;                        (tau-intervalp (conjoin-intervals int1 int2)))
;                    (in-tau-intervalp x (conjoin-intervals int1 int2))
;                    )))

; The following establishes that if the conjunction of two intervals is empty
; then the equality of the two objects is false.  We exploit this in
; tau-interval-equal-decider.
;
; (thm (implies (and (or (equal int1 nil) (tau-intervalp int1))
;                    (or (equal int2 nil) (tau-intervalp int2))
;                    (in-tau-intervalp x int1)
;                    (in-tau-intervalp y int2)
;                    (equal (conjoin-intervals int1 int2) *tau-empty-interval*))
;               (not (equal x y))))

(defun combine-pos/neg-pairs-from-tau1 (sign pos-evg1 pairs1 pos-evg2 pairs2 ens wrld)

; Pairs1 and pairs2 are lists of tau-pairs, ordered descending by index.
; We intersect them, returning a list of tau-pairs ordered descending.
; However, we implicitly augment each list with the pairs which have been
; dropped because they are true (or false) because of the corresponding
; :pos-evg.

; For example, suppose we are dealing with :pos-pairs (sign=t and both pair1
; and pair2 are :pos-pairs of their respective tau).  Suppose pos-evg1 contains
; the evg 7 and pos-evg2 is nil.  Then pairs1 will only contain recognizers
; that cannot be evaluated on 7.  Thus, for example, pairs1 will NOT include
; INTEGERP.  But pairs2 may contain INTEGERP.  Our answer will include INTEGERP
; because it is IMPLICITLY listed in pairs1.

; Referring back to the discussion On Disjoining Tau above, if either of the
; pairs includes WEEKDAYP, we would preserve WEEKDAYP by this hack.  But this
; hack will not ``preserve'' WEEKDAYP if it has been made implicit in both tau!

; If both pos-evg1 and pos-evg2 are nil, this function is equivalent to
; intersection-equal.  But it is probably faster because it exploits
; the fact that the lists are ordered.

  (cond
   ((endp pairs1)
    (cond
     ((endp pairs2)
      nil)
     ((and pos-evg1
           (eq (ev-fncall-w-tau-recog (cdr (car pairs2)) pos-evg1 ens wrld)
               sign))
      (cons (car pairs2)
            (combine-pos/neg-pairs-from-tau1 sign
                                             pos-evg1 nil
                                             pos-evg2 (cdr pairs2)
                                             ens wrld)))
     (t (combine-pos/neg-pairs-from-tau1 sign
                                         pos-evg1 nil
                                         pos-evg2 (cdr pairs2)
                                         ens wrld))))
   ((endp pairs2)
    (cond
     ((and pos-evg2
           (eq (ev-fncall-w-tau-recog (cdr (car pairs1)) pos-evg2 ens wrld)
               sign))
      (cons (car pairs1)
            (combine-pos/neg-pairs-from-tau1 sign
                                    pos-evg1 (cdr pairs1)
                                    pos-evg2 nil
                                    ens wrld)))
     (t (combine-pos/neg-pairs-from-tau1 sign
                                pos-evg1 (cdr pairs1)
                                pos-evg2 nil
                                ens wrld))))
   ((equal (car pairs1)  ; We could compare just the indices, but that might
           (car pairs2)) ; be slower since the pairs are probably EQ
    (cons (car pairs1)
          (combine-pos/neg-pairs-from-tau1 sign
                                  pos-evg1 (cdr pairs1)
                                  pos-evg2 (cdr pairs2)
                                  ens wrld)))
   ((and pos-evg1
         (eq (ev-fncall-w-tau-recog (cdr (car pairs2)) pos-evg1 ens wrld)
             sign))
    (cons (car pairs2)
          (combine-pos/neg-pairs-from-tau1 sign
                                  pos-evg1 pairs1
                                  pos-evg2 (cdr pairs2)
                                  ens wrld)))
   ((and pos-evg2
         (eq (ev-fncall-w-tau-recog (cdr (car pairs1)) pos-evg2 ens wrld)
             sign))
    (cons (car pairs1)
          (combine-pos/neg-pairs-from-tau1 sign
                                  pos-evg1 (cdr pairs1)
                                  pos-evg2 pairs2
                                  ens wrld)))
   ((> (car (car pairs1))
       (car (car pairs2)))
    (combine-pos/neg-pairs-from-tau1 sign
                            pos-evg1 (cdr pairs1)
                            pos-evg2 pairs2
                            ens wrld))
   (t
    (combine-pos/neg-pairs-from-tau1 sign
                            pos-evg1 pairs1
                            pos-evg2 (cdr pairs2)
                            ens wrld))))

(defun augment-pos/neg-pairs-with-implicit-numeric-recogs
  (pos-evg sign pairs wrld)

; Pairs is the :pos-pairs (or :neg-pairs, as per sign) of some tau whose
; :pos-evg is pos-evg.  If :pos-evg is non-nil, then the tau in question is an
; equality-with-constant.  If in fact the constant is numeric, we augment pairs
; with the positive (or negative) implicants of the most specific tau-interval
; domain (INTEGERP, RATIONALP, or ACL2-NUMBERP) containing that constant.

  (if pos-evg
      (let* ((pred
              (if (acl2-numberp (car pos-evg))
                  (cond ((integerp (car pos-evg)) 'INTEGERP)
                        ((rationalp (car pos-evg)) 'RATIONALP)
                        (t 'ACL2-NUMBERP))
                  nil))
             (implicit-pairs
              (if pred
                  (if sign
                      (access tau
                              (tau-simple-implicants t pred wrld)
                              :pos-pairs)
                      (access tau
                              (tau-simple-implicants t pred wrld)
                              :neg-pairs))
                  nil)))
        (merge-car-> pairs implicit-pairs))
      pairs))

(defun combine-pos/neg-pairs-from-tau (sign tau1 tau2 ens wrld)
  (let* ((pos-evg1 (access tau tau1 :pos-evg))
         (pos-evg2 (access tau tau2 :pos-evg))
         (pairs1 (augment-pos/neg-pairs-with-implicit-numeric-recogs
                  pos-evg1
                  sign
                  (if sign
                      (access tau tau1 :pos-pairs)
                      (access tau tau1 :neg-pairs))
                  wrld))
         (pairs2 (augment-pos/neg-pairs-with-implicit-numeric-recogs
                  pos-evg2
                  sign
                  (if sign
                      (access tau tau2 :pos-pairs)
                      (access tau tau2 :neg-pairs))
                  wrld)))
    (combine-pos/neg-pairs-from-tau1 sign
                                     pos-evg1
                                     pairs1
                                     pos-evg2
                                     pairs2
                                     ens wrld)))

(defun combine-tau (tau1 tau2 ens wrld)

; We form a tau, tau3, such that ((M[tau1] --> M[tau3]) & (M[tau2] -->
; M[tau3])).  For example, if tau1 includes the recognizers P and Q and tau2
; includes P and R, then all we can include is P.  Thus, tau3 is sort of the
; ``intersection'' of tau1 and tau2, which because of the conjunctive nature of
; taus, is really disjunction.  The way we disjoin intervals is to widen them.
; For example, we disjoin the interval 1 <= ... <= 5 with the interval 100 <=
; ... <= 200 to get the interval 1 <= ... <= 200..

; If neither tau1 nor tau2 is *tau-contradiction*, we don't have to worry about
; consistency because everything in the resulting tau is in both tau1 and tau2,
; which are known to be consistent.  But it is possible that one or both of
; tau1 and tau2 is contradictory.  Think of *tau-contradiction* as denoting the
; (infinite) set of recognizers of both signs.  Then the intersection is the
; other set.

; Note that intersection-equal preserves the order of its first argument; so if
; two lists are ordered according to some criteria, so is their intersection.

  (cond
   ((eq tau1 *tau-contradiction*) tau2)
   ((eq tau2 *tau-contradiction*) tau1)
   (t

; We avoid consing up *tau-empty* by testing for it first.  The computation of
; :pos-evg below is a little strange.  We ought to ask whether both are
; non-empty and then compare their contents.  But if one is empty and the other
; isn't, then their ``contents'' won't be equal and nil is the correct answer.

    (let ((pos-evg (if (equal (access tau tau1 :pos-evg)
                              (access tau tau2 :pos-evg))
                       (access tau tau1 :pos-evg)
                       nil))
          (neg-evgs (intersection-equal
                     (access tau tau1 :neg-evgs)
                     (access tau tau2 :neg-evgs)))

; As noted above, disjoining loses a lot of precision.  Indeed, before we added
; the augmentation of :pos-pairs by implicit numeric recognizers (as done in
; combine-pos/neg-pairs-from-tau), we could produce tau that violated our
; convention that the domain of every interval is derivable from the
; :pos-pairs.  Just consider two tau, =1 and =2, and disjoin them.  Their
; empty :pos-pairs produce an empty :pos-pairs EVEN THOUGH the interval
; provided has domain INTEGERP.

          (pos-pairs (combine-pos/neg-pairs-from-tau t tau1 tau2 ens wrld))
          (neg-pairs (combine-pos/neg-pairs-from-tau nil tau1 tau2 ens wrld))
          (interval (disjoin-intervals
                     (access tau tau1 :interval)
                     (access tau tau2 :interval))))
      (let ((dom (access tau-interval interval :domain))
            (lo-rel (access tau-interval interval :lo-rel))
            (lo (access tau-interval interval :lo))
            (hi-rel (access tau-interval interval :hi-rel))
            (hi (access tau-interval interval :hi)))
        (cond
         ((and (not (singleton-tau-intervalp lo-rel lo hi-rel hi))
               dom
               (not (tau-pair-member
                     (case dom
                       (INTEGERP *tau-integerp-pair*)
                       (RATIONALP *tau-rationalp-pair*)
                       (otherwise *tau-acl2-numberp-pair*))
                     pos-pairs)))
          (er hard 'combine-tau
              "We have just constructed an interval, ~x0, whose domain is not ~
               in the :pos-pairs of the tau we planned to put it into!  The ~
               offending interval was constructed by disjoin-intervals from ~
               the intervals in these two tau ~x1 and ~x2."
              interval
              tau1
              tau2))
         ((or pos-evg neg-evgs pos-pairs neg-pairs interval)
          (make tau
                :pos-evg pos-evg
                :neg-evgs neg-evgs
                :pos-pairs pos-pairs
                :neg-pairs neg-pairs
                :interval interval))
         (t *tau-empty*)))))))

; -----------------------------------------------------------------
; Tau-Term and Tau-Assume

; Tau-term is the function that takes a term and an alist of tau assumptions,
; tau-alist, and computes the tau of the term under the assumptions in
; tau-alist.  Tau-assume takes a term and tau-alist and augments the tau-alist
; with the assumption that the term is true (or false as specified by a flag).

; These two functions are mutually recursive.  However, before we get to their
; definitions we must deal with various auxiliary issues and helper functions.

; On the Role of Rewriting in Tau

; We have gone back and forth on the question of whether tau-term and
; tau-assume should do any rewriting.  The existence of mutually recursive
; recognizers is the motivation of our decision to do some rewriting.  If
; recognizers are mutually recursive then the system will involve ``big
; switch'' recognizers that turn into standard recognizer nests depending on
; the value of some flag.  (Think of the flagged version of a mutually
; recursive clique of recognizers, except replace the singly recursive calls
; with their mutually recursive but now disabled counterparts.)  We must expand
; these big switches when their controlling flags are known.  It also pays to
; do this expansion in the context of some tau assumptions, since that permits
; simplification.  If we do not do this rewriting in the tau system we spill
; over into the simplifier where much more heavy-duty machinery is invoked.

; But how should rewriting in tau interact with signature rules?  Our current
; policy is that rewriting will not expand a function that possesses a tau
; signature rule.  The idea is that if the user has provided a signature rule,
; that is what we use.  If no signature rule is provided and the function is a
; big switch, we consider expanding it.

; Given this simple heuristic, how do we handle (mv-nth 3 (fn a b))?  Clearly
; if there is a form 2 signature rule for this we apply it.  But if not, we
; expand (fn a b) and look for a signature rule about the result.  In the happy
; event that (fn a b) is a big-switch-like function and expands to (gn b),
; we're in good shape.  But if it expands into an IF, we push the mv-nth
; down to the tips of the IF before recurring.

(defun push-mv-nth-down (i term)

; We put (MV-NTH i *) around each output of the IF-tree term.

  (cond ((variablep term) (fcons-term* 'MV-NTH i term))
        ((fquotep term)

; We only call this function when i is a quoted natp.  Thus,
; we can simply compute the answer here.

         (kwote (mv-nth (cadr i) (cadr term))))
        ((eq (ffn-symb term) 'IF)
         (fcons-term* 'IF
                      (fargn term 1)
                      (push-mv-nth-down i (fargn term 2))
                      (push-mv-nth-down i (fargn term 3))))
        (t (fcons-term* 'MV-NTH i term))))

; If term defines a big switch function, then we can partially evaluate a call
; of that function efficiently under a tau-alist.  Here is how.

(defun tau-expand-big-switch (body switch-var switch-tau var-alist ens wrld)

; Body is the body of a big switch function being applied to some actuals.
; Switch-var is the switch var of that switch, switch-val is the corresponding
; actual expression, and switch-tau is the tau of that actual.  It is assumed
; that switch-tau is not *tau-contradiction*.  Var-alist is the variable
; substitution mapping formals to actuals.  We partially evaluate body under
; the assumptions in tau-alist.  We return (mv hitp term') where hitp is T or
; NIL.  If hitp is T, term' is provably equal to body/var-alist under
; tau-alist.  If hitp is NIL, term' is NIL and irrelevant.  The heuristic we
; use to determine whether we hit or not is whether tau-alist allows us to
; navigate past all the switch tests.  We have arrived at a leaf if the body no
; longer mentions switch-var.  This way we don't have to build the
; instantiation of any part of body except that leaf.

  (cond
   ((not (ffn-symb-p body 'IF))

; If we are at a leaf of the big switch, we instantiate the body and we
; report hitp = t.  Otherwise, we report hitp = nil.  We are at a leaf
; if the switch-var no longer occurs in the body.

    (cond ((occur switch-var body)
           (mv nil nil))
          (t (mv t (sublis-var var-alist body)))))
   (t
    (mv-let
     (sign recog e criterion)
     (tau-like-term (fargn body 1) :various-any wrld)
     (declare (ignore criterion))
     (cond ((and recog
                 (eq e switch-var))

; Body is of the form (IF (sign/recog switch-var) ...)
            (let ((temp (reduce-sign/recog switch-tau sign recog ens wrld)))
              (cond
               ((eq temp t)
                (tau-expand-big-switch (fargn body 2)
                                       switch-var switch-tau var-alist
                                       ens wrld))
               ((eq temp nil)
                (tau-expand-big-switch (fargn body 3)
                                       switch-var switch-tau var-alist
                                       ens wrld))
               (t (mv nil nil)))))
           (t (mv nil nil)))))))

; -----------------------------------------------------------------
; Closing in On Tau-Term and Tau-Assume

; Because conjunction is treated as a special case in tau-assume, we must be
; able to deconstruct IFs that are really conjunctions.

(defun deconstruct-conjunction (sign a b c)

; Consider sign/(IF a b c).  There are four cases in which this is a
; conjunction.

; sign=t     c=nil             (and a b)
; sign=t     b=nil             (and (not a) c)
; sign=nil   b=a or b=T        (and (not a) (not c))
; sign=nil   c=t               (and a (not b))

; We return (mv conjunctionp sign1 conjunct1 sign2 conjunct2), where either
; conjunctionp is nil (meaning sign/(IF a b c) is not a conjunction), or else
; conjunctionp is t and sign/(IF a b c) <--> (AND sign1/conjunct1
; sign2/conjunct2)

  (if sign
      (if (equal c *nil*)
          (mv t t a t b)
          (if (equal b *nil*)
              (mv t nil a t c)
              (mv nil nil nil nil nil)))
      (if (or (equal a b)
              (equal b *t*))
          (mv t nil a nil c)
          (if (equal c *t*)
              (mv t t a nil b)
              (mv nil nil nil nil nil)))))

; Finally:  the definitions of tau-term and tau-assume!

(defun ok-to-fire-signature-rulep1 (formal-tau-lst actual-tau-lst ens wrld)

; Note: The claim below that formal-tau-lst and actual-tau-lst are equal-length
; is not quite true!  See note below or Abuse of Tau Representation.

; This function takes two equal-length lists of tau and compares corresponding
; ones.  For each pair, formal-tau and actual-tau, we check that every
; recognizer in formal-tau is included in actual-tau.  In general, each
; actual-tau is much bigger than its corresponding formal-tau because the
; formal-tau only includes the specific recognizer(s) mentioned in a signature
; theorem while the actual-tau includes all the implicants.  So, for example,
; formal-tau might be {integerp} but actual-tau might be {natp integerp
; rationalp}.  What we are really checking is that any object satisfying all
; the actual-tau recognizers will satisfy all the formal-tau recognizers, i.e.,
; (implies M[actual-tau] M[formal-tau]). We return t or nil.

; Note: We sometimes call this function with tau-lst2 = nil, knowing that every
; element will be nil and that when nil is treated like a tau it behaves like
; *tau-empty*!  Note that the only corresponding formal-tau that would be
; acceptable is the empty one.

  (cond ((endp formal-tau-lst) t)
        ((tau-implies (car actual-tau-lst) (car formal-tau-lst) ens wrld)
         (ok-to-fire-signature-rulep1 (cdr formal-tau-lst)
                                      (cdr actual-tau-lst)
                                      ens wrld))
        (t nil)))

(defun smart-member-equal-+- (lit clause)

; We return '+ if lit is a member of clause.  We return '- if the complement of
; lit is a member of clause.  Otherwise we return nil.  If both conditions are
; met, we return either '+ or '- depending on which occurs first.  For example,
; let clause be '(A (NOT B)).  Then if lit is A we return '+.  If lit is (NOT
; A) we return '-.  We also return '- when lit is B.  If lit is C we return
; nil.

  (cond ((null clause) nil)
        ((equal lit (car clause)) '+)
        ((let ((lit1 lit)
               (lit2 (car clause)))
           (or (and (ffn-symb-p lit1 'not)
                    (equal (fargn lit1 1) lit2))
               (and (ffn-symb-p lit2 'not)
                    (equal (fargn lit2 1) lit1))))
           '-)
        (t (smart-member-equal-+- lit (cdr clause)))))

; Here are useful trace$ commands for tau-term and tau-assume:

;   (trace$ (tau-term :entry
;                     (list 'tau-term (car arglist)
;                           (decode-tau-alist (cadr arglist) nil) (caddr arglist))
;                     :exit
;                     (list 'tau-term (if (eq value *tau-contradiction*) value
;                                         (decode-tau value (car arglist))))))
;
;   (trace$ (tau-assume :entry (list 'tau-assume
;                                    (if (car arglist) 'positive 'negative)
;                                    (cadr arglist)
;                                    (decode-tau-alist (caddr arglist) nil)
;                                    (cadddr arglist))
;                       :exit (list 'tau-assume
;                                   (if (nth 0 values) 'contradiction! nil)
;                                   (if (nth 1 values) 'must-be-true! nil)
;                                   (if (nth 2 values) 'must-be-false! nil)
;                                   (decode-tau-alist (nth 3 values) nil))))

(defmacro recursivep (fn def-body-p wrld)

; Fn should be a :logic-mode function symbol of wrld.

; Experiments showed (when def-body-p was implicitly always t) a slight speedup
; in Allegro CL (perhaps a half percent on a very small run) by making this a
; macro.

  (declare (xargs :guard (booleanp def-body-p)))
  (cond (def-body-p `(access def-body
                             (def-body ,fn ,wrld)
                             :recursivep))
        (t `(getpropc ,fn 'recursivep nil ,wrld))))

(defun find-first-acceptable-domain (actual-dom acceptable-domains)

; Actual-dom is an interval domain, i.e., INTEGERP, RATIONALP, ACL2-NUMBERP, or
; NIL, of an interval known to contain the value of some actual parameter to a
; call of some (unspecified) function fn.  Acceptable-domains is a list of the
; interval domains acceptable for a bounder of fn for that same argument of fn.
; We determine whether actual-dom is one the acceptable ones.  In the most
; trivial situation, we might expect the actual domain to be something like
; INTEGERP and the acceptable domains to be (INTEGERP RATIONALP).  But we
; consider INTEGERP to be ok for the acceptable domains (RATIONALP
; ACL2-NUMBERP) too, because if the actual is an integer then it is also a
; rational.  Therefore we actually return two results, (mv flg dom).  Flg is t
; or nil indicating whether actual-dom is acceptable, and dom is the first
; listed acceptable domain that includes the actual one.  For example, given
; actual-dom = 'INTEGERP and acceptable-domains = '(RATIONALP ACL2-NUMBERP), we
; return (mv t 'RATIONALP).  Note that if the acceptable domains are presented
; in the reversed order we'd get (mv t 'ACL2-NUMBERP).  It would be best to
; keep the acceptable domains ordered from most to least restrictive.

  (cond ((endp acceptable-domains) (mv nil nil))
        ((eq actual-dom (car acceptable-domains))
         (mv t actual-dom))
        (t (let* ((more-specific-acceptable-domains
                   (cdr (assoc-eq (car acceptable-domains)
                                  '((rationalp integerp)
                                    (acl2-numberp rationalp integerp)
                                    (nil acl2-numberp rationalp integerp)))))
                  (winner (member-eq actual-dom more-specific-acceptable-domains)))
             (cond
              (winner (mv t (car acceptable-domains)))
              (t (find-first-acceptable-domain actual-dom (cdr acceptable-domains))))))))

(defun tau-lst-with-acceptable-domainsp (actual-tau-lst doms-lst)

; Actual-tau-lst is a list of the tau of successive arguments to some call of
; some function fn.  Doms-lst is the :acceptable-domains field of a
; bounder-correctness rule for fn.  We check that the actual tau satisfy
; the acceptable domain criteria of the rule.

; An actual in domain INTEGERP satisfies a bounder with an acceptable domains
; (RATIONALP ACL2-NUMBERP).  Note that it would be a mistake to pass such an
; interval to the corresponding bounder!  The bounder was proved correct under
; the assumption that the domain was either RATIONALP or ACL2-NUMBERP.  Thus,
; the bounder could actually look at the domain of its argument and do
; something completely wrong for INTEGERP and still be proved correct.
; However, an INTEGERP interval is contained within the corresponding RATIONALP
; interval, so we can modify the actual interval by enlarging the domain to
; RATIONALP and get a correct answer from the bounder.

; But note that this is a two-step process.  First we check that all the
; actuals have acceptable domains.  Then we enlarge the actual intervals as
; required and apply the bounder.  This function just checks acceptability.

  (cond ((endp doms-lst) t)
        ((eq (car doms-lst) t)
         (tau-lst-with-acceptable-domainsp (cdr actual-tau-lst) (cdr doms-lst)))
        (t (mv-let (flg dom)
                   (find-first-acceptable-domain
                    (access tau-interval
                            (access tau (car actual-tau-lst) :interval)
                            :domain)
                    (car doms-lst))
                   (declare (ignore dom))
                   (and flg
                        (tau-lst-with-acceptable-domainsp
                         (cdr actual-tau-lst)
                         (cdr doms-lst)))))))

(defun collect-bounder-args (actual-tau-lst doms-lst bounder-args)

; Actual-tau-lst is a list of tau corresponding to the arguments of some
; (unspecified) function, fn.  Doms-lst is the corresponding list of acceptable
; domains for some bounder function.  Bounder-args is a list of naturals
; specifying the positions of the relevant arguments for the bounder function.
; For example, actual-tau-lst might be (t0 t1 t2 t3) and the bounder function
; requires in its first argument the interval from t3 and in its second
; argument the interval from t1.  Then bounder-args would be (3 1).

; We collect the intervals of those tau (whose positions are) listed in
; bounder-args and we change the domain of each collected interval to be the
; domain that admitted the actual one.  So for example, if we collect the
; interval from t3 and its domain is INTEGERP but the acceptable domains there
; are (RATIONALP ACL2-NUMBERP), the we change the interval's domain to
; RATIONALP before collecting it.

  (cond ((endp bounder-args) nil)
        (t (let ((actual-int (access tau
                                     (nth (car bounder-args) actual-tau-lst)
                                     :interval))
                 (acceptable-doms (nth (car bounder-args) doms-lst)))
             (mv-let (flg dom)
                     (find-first-acceptable-domain
                      (access tau-interval actual-int :domain)
                      acceptable-doms)
                     (declare (ignore flg))
                     (cons (change tau-interval actual-int :domain dom)
                           (collect-bounder-args actual-tau-lst
                                                 doms-lst
                                                 (cdr bounder-args))))))))

(defun bounding-interval (bc actual-tau-lst wrld)

; Bc is a bounder-correctness record for some fn and actual-tau-lst is the list
; of tau of the actuals of a call of fn.  If those actuals satisfy the domains
; proved acceptable for the bounder, we apply the bounder appropriately and
; return the resulting interval.  Otherwise, we return nil -- which is the
; universal interval.

  (let ((doms-lst (access bounder-correctness bc :acceptable-domains)))
    (cond
     ((tau-lst-with-acceptable-domainsp actual-tau-lst doms-lst)
      (let ((bounder-fn (access bounder-correctness bc :bounder-fn))
            (bounder-args
             (collect-bounder-args
              actual-tau-lst
              doms-lst
              (access bounder-correctness bc :bounder-args))))
        (mv-let (erp val)
                (ev-fncall-w bounder-fn
                             bounder-args
                             wrld nil nil t t nil)
                (cond
                 (erp nil)
                 (t val)))))
     (t nil))))

(defun conjoin-bounding-intervals (bounders actual-tau-lst wrld)

; Given a list of bounder-correctness records for some function and the actual
; tau for a call of that function, we conjoin together all the intervals the
; bounders compute for the call.  This interval will contain the value of the
; call.

  (cond
   ((endp bounders) nil)
   (t (conjoin-intervals
       (bounding-interval (car bounders) actual-tau-lst wrld)
       (conjoin-bounding-intervals (cdr bounders) actual-tau-lst wrld)))))

(defun apply-tau-bounders (bounders actual-tau-lst ens wrld calist)

; Given the bounders for a function and the tau of its actuals, we compute the
; tau of the call -- as computed just by the bounders of the function.  This
; function does not take account of the signature rules for the function.  We
; return (mv tau' calist').

  (let ((int (conjoin-bounding-intervals bounders actual-tau-lst wrld)))
    (cond
     ((null int)
      (mv *tau-empty* calist))
     ((tau-empty-intervalp int)
      (mv *tau-contradiction* calist))
     (t (let ((dom    (access tau-interval int :domain))
              (lo-rel (access tau-interval int :lo-rel))
              (lo     (access tau-interval int :lo))
              (hi-rel (access tau-interval int :hi-rel))
              (hi     (access tau-interval int :hi)))
          (cond
           ((and (null dom) (null lo) (null hi))
            (mv *tau-empty* calist))
           (t
            (let* ((dom-pair
                    (case dom
                      (integerp *tau-integerp-pair*)
                      (rationalp *tau-rationalp-pair*)
                      (acl2-numberp *tau-acl2-numberp-pair*)
                      (otherwise nil)))
                   (tau1
                    (if (null dom-pair)
                        *tau-empty*
                        (add-to-tau t dom-pair *tau-empty* ens wrld))))
              (mv-let
               (sign k token)
               (tau-interval-endpoint-to-sign-k-token nil lo-rel lo)
               (let ((tau2
                      (if (null k)
                          tau1
                          (add-to-tau sign (cons k token) tau1 ens wrld))))
                 (mv-let
                  (sign k token)
                  (tau-interval-endpoint-to-sign-k-token t hi-rel hi)
                  (add-to-tau! sign
                               (if (null k) :SKIP (cons k token))
                               tau2 ens wrld calist))))))))))))

; The following two functions are used in tau-term to use intervals to
; determine whether (EQUAL x y) and (< x y) are T or NIL (or unknown).

(defun tau-interval-equal-decider (int1 int2)

; If x is in interval int1 and y is in interval int2, what can we say about
; (equal x y)?  The possible answers are T, NIL, or ?.  The only way we can
; answer T is if both intervals are identities with the same constant.  We can
; answer NIL if the intervals do not intersect.  Otherwise, we return ?.  We
; determine whether the intervals intersect by conjoining them and looking for
; the empty interval.  A theorem in a comment after conjoin-interval
; establishes the soundness of this use of conjoin-intervals.

  (cond ((and (identity-intervalp int1)
              (identity-intervalp int2)
              (equal (access tau-interval int1 :lo)
                     (access tau-interval int2 :lo)))
         t)
        ((equal (conjoin-intervals int1 int2) *tau-empty-interval*)
         nil)
        (t '?)))

; (verify-termination lower-bound->)
; (verify-termination upper-bound-<)
; (verify-termination squeeze-k)
; (verify-termination conjoin-intervals)
; (include-book "arithmetic-5/top" :dir :system)
; (verify-termination identity-intervalp)
; (verify-termination tau-interval-equal-decider)

; (defthm lemma
;   (implies (and (rationalp lo)
;                 (not (integerp lo))
;                 (integerp x)
;                 (<= lo x))
;            (<= (+ 1 (floor lo 1)) x))
;   :rule-classes :linear)

; Below we prove that the EQUAL decider is correct when it returns
; t or nil and we make no claims about it when it returns ?.

; (thm (implies (and (or (null int1) (tau-intervalp int1))
;                    (or (null int2) (tau-intervalp int2))
;                    (in-tau-intervalp x int1)
;                    (in-tau-intervalp y int2)
;                    (eq (tau-interval-equal-decider int1 int2) t))
;               (equal x y)))

; (thm (implies (and (or (null int1) (tau-intervalp int1))
;                    (or (null int2) (tau-intervalp int2))
;                    (in-tau-intervalp x int1)
;                    (in-tau-intervalp y int2)
;                    (eq (tau-interval-equal-decider int1 int2) nil))
;               (not (equal x y))))

(defun tau-interval-<-decider (int1 int2)

; If x is in interval int1 and y is in interval int2, then what can we say
; about (< x y)?  Basically, we return t if int1 is entirely below int2, nil if
; int1 is above int2, and ? otherwise.

  (let ((lo-rel1 (access tau-interval int1 :lo-rel))
        (lo1 (access tau-interval int1 :lo))
        (hi-rel1 (access tau-interval int1 :hi-rel))
        (hi1 (access tau-interval int1 :hi))
        (lo-rel2 (access tau-interval int2 :lo-rel))
        (lo2 (access tau-interval int2 :lo))
        (hi-rel2 (access tau-interval int2 :hi-rel))
        (hi2 (access tau-interval int2 :hi)))
    (cond ((and hi1 lo2
                (<? (not (or hi-rel1 lo-rel2)) hi1 lo2))
           t)
          ((and hi2 lo1
                (<? (not (or hi-rel2 lo-rel1)) hi2 lo1))
           nil)
          (t '?))))

; (verify-termination tau-interval-<-decider)

; (thm (implies (and (or (null int1) (tau-intervalp int1))
;                    (or (null int2) (tau-intervalp int2))
;                    (in-tau-intervalp x int1)
;                    (in-tau-intervalp y int2)
;                    (eq (tau-interval-<-decider int1 int2) t))
;               (< x y))
;      :hints (("Goal" :use completion-of-<)))

; (thm (implies (and (or (null int1) (tau-intervalp int1))
;                    (or (null int2) (tau-intervalp int2))
;                    (in-tau-intervalp x int1)
;                    (in-tau-intervalp y int2)
;                    (eq (tau-interval-<-decider int1 int2) nil))
;               (not (< x y)))
;      :hints (("Goal" :use completion-of-<)))

(mutual-recursion

(defun tau-term (term tau-alist type-alist pot-lst ens wrld calist)

; Basic Design of tau-term:

; Given a term, a tau-alist, a type-alist and a pot-lst compute the tau of the
; term.  We return either a tau or *tau-contradiction*.

; If a term is bound on tau-alist, we just look up its tau.  We do not
; implement the ``double-whammy'' idea of type-set.

; Tau-term gives special handling to certain function calls:

; - lambda applications: expand and recur.  This is as opposed to an Abstract
;   Interpretation approach where we might compute the tau of a lambda
;   application by computing the tau of the body under the alist pairing the
;   formals to the tau of the actuals.  We tried it both ways and expansion
;   actually seems to result in very slightly fewer calls of tau-term.

; - (NOT x):  compute the tau of x, taux, and return the tau for T or NIL
;   if taux is the tau of NIL or T, respectively; else return the tau for
;   Boolean

; - IF: If the test must be true (or must be false) under tau-alist, compute the
;   tau of the appropriate branch; otherwise, compute the tau of each branch
;   under the appropriately augmented tau assumptions and then intersect the two
;   recognizer sets.

; - (UNSIGNED-BYTE-P 'n x) where (natp n):  expand definition to conjunction

; - (MV-NTH 'i (fn ...)) where fn has form 2 signature rules: apply the ith set
;   of signature rules for fn.  We also handle mv-nth synonyms here.  Thus, for
;   synonyms we do not look for signatures or big-switch expansions.

; - (MV-NTH 'i (fn ...)) where fn is a big switch: expand the fn call (if
;   heuristically allowed), distribute the (MV-NTH 'i ...) down to the tips of
;   any IF thus produced, and recur.  We also handle mv-nth synonyms here and
;   do not consider signatures or big-switch expansions for them.

; - (MV-NTH x y) for any other combinations of x and y: *tau-empty*.  We also
;   handle mv-nth synonyms here and do not consider signatures or big-switch
;   expansions for them.

; - sign/(recog e): compute the tau of e and return the tau for T, NIL, or
;   Boolean appropriately

; - (EQUAL x y): if the intervals of the taus of x and y allow the equal
;   to be decided, return the appropriate tau; else apply signature rules
;   for EQUAL (which probably is just Boolean)

; - (< x y):  analogous to EQUAL above

; - (fn ...) where fn has bounder rules and/or form 1 signature rules: compute
;   the tau of each actual, then apply the bounder rules to compute a tau
;   containing (fn ...), and then further refine it with the applicable
;   signature rules.  The existence of a bounder or signature rule us from
;   opening the function or considering it as a big switch.

; - (fn ...) where fn is a big switch: Expand (if heuristically allowed) and
;   recur

; - otherwise, *tau-empty*

  (let ((temp (assoc-equal term tau-alist)))
    (cond
     (temp (mv (cdr temp) calist))
     (t (cond
         ((variablep term) (mv *tau-empty* calist))
         ((fquotep term)

; We avoid consing up two common cases.

          (cond ((equal term *t*)
                 (mv *tau-t* calist))
                ((equal term *nil*)
                 (mv *tau-nil* calist))
                (t

; Note that (cdr term) is a singleton evg list and thus a suitable pos-evg.

                 (mv (make tau
                           :pos-evg (cdr term)
                           :neg-evgs nil
                           :pos-pairs nil
                           :neg-pairs nil
                           :interval
                           (make-identity-interval nil
                                                   (car (cdr term))))
                     calist))))
         ((flambdap (ffn-symb term))

; We just expand lambdas.  This is in the spirit of our decision to expand
; nonrec fns when they don't have signature rules.  This is as opposed to an
; Abstract Interpretation approach where we would compute the tau of a lambda
; application by computing the tau of the body under the alist pairing the
; formals to the tau of the actuals.  We tried it both ways and expansion
; actually seems to result in very slightly fewer calls of tau-term.

          (tau-term (subcor-var (lambda-formals (ffn-symb term))
                                (fargs term)
                                (lambda-body (ffn-symb term)))
                    tau-alist type-alist pot-lst ens wrld calist))
         ((eq (ffn-symb term) 'NOT)
          (mv-let (tau1 calist)
                  (tau-term (fargn term 1) tau-alist type-alist pot-lst
                            ens wrld calist)
                  (cond
                   ((eq tau1 *tau-contradiction*)
                    (mv *tau-contradiction* calist))
                   ((equal tau1 *tau-nil*)
                    (mv *tau-t* calist))
                   ((or (equal tau1 *tau-t*)
                        (and (access tau tau1 :pos-evg)
                             (not (eq (car (access tau tau1 :pos-evg)) nil)))
                        (member-nil-neg-evgs (access tau tau1 :neg-evgs)))

; Each of the following tau are non-nil:  T or any evg other than nil or any tau
; containing NIL in its :neg-evgs.  There are other obviously true tau, e.g., one
; containing the positive recognizer NATP.  But that would make the subject, e, be
; a numeric expression and would mean we are here dealing with (NOT e), which is
; strange.  In the interests of simplicity, we just handle ``Boolean-like'' trues.

                    (mv *tau-nil* calist))
                   (t

; We'd like to return just the Boolean tau, but it changes as new recognizers
; are added so we complete it each time we need it.

                    (add-to-tau! t *tau-booleanp-pair* *tau-empty*
                                 ens wrld calist)))))
         ((eq (ffn-symb term) 'IF)
          (mv-let
           (contradictionp1 mbt1 mbf1 tau-alist1 calist)
           (tau-assume t (fargn term 1)
                       tau-alist type-alist pot-lst
                       ens wrld calist)
           (mv-let
            (contradictionp2 mbt2 mbf2 tau-alist2 calist)
            (tau-assume nil (fargn term 1)
                        tau-alist type-alist pot-lst
                        ens wrld calist)

; Once upon a time, we assumed the term T first and didn't ``bother'' to assume
; the term NIL unless the first assumption gave us no information.  But then we
; realized (via a bug reported by Dmitry Nadezhin) that it's possible for the
; NIL assumption to tell us that the T assumption should have produced mbt1=T:
; Suppose (P x) is defined to recognize just 0 or 1.  Now suppose we know (via
; tau-alist) that (P x) is true.  Assume (INTEGERP X) true.  We get nothing but
; a new tau-alist because we don't deduce right then that (P X) --> (INTEGERP
; X).  But when we assume (INTEGERP X) false we get a contradictionp2 because
; we can carry that assumption into (P X).  So we learn mbt1 should have been T
; from a contradictionp2!  So now we go both ways on the assumptions and figure
; out what we know.  We could try to short-circuit the computation above by not
; doing the assume false if the assume true told us the answer.  But it is
; possible the assume false will tell us a different answer, in which case we
; have detected a contradiction in the world or tau-alist.  By doing both we
; treat assume true and assume false symmetrically; the short-circuit destroys
; that symmetry.

; So now we ``figure out what we know.''  This is realized by setting the
; variables contradictionp, mbt, mbf, true-tau-alist, and false-tau-alist
; according to all we've learned from the two assumptions (T and NIL) above
; which generated six variables, contradictionp1, mbt1, mbf1 (generated by
; assuming term true) and contradictionp2, mbt2, mbf2 (generated by assuming
; the negation of term true).  We assume that whenever an mbti or mbfi flag is
; set the corresponding tau-alisti is the appropriate extension of tau-alist.

; Below is a table showing all possible combinations of the six flags we now
; hold, where ctr1 and ctr2 are abbreviations for contradictionp1 and
; contradictionp2.  (BTW: This table was generated by forming all combinations
; of the six boolean flags and then filtering out the impossible combinations,
; namely, those in which the contradictionp is T while either mbt or mbf is T,
; and those in which mbt and mbf are T.)  Depending on the combination of
; flags, we set contradictionp, mbt, mbf, true-tau-alist and false-tau-alist;
; we obey the following constraints:

; (a) at most one of contradictionp, mbt, and mbf can be T

; (b) if either mbt or mbf is t, the true- and false-tau-alists are the
;     original tau-alist

; (c) if both mbt and mbf are nil, the true- and false-tau-alists are
;     appropriate extensions of the original tau-alist.

; Note that the only time we extend the tau-alist to get true-tau-alist and
; false-tau-alist is when we learn nothing by assuming the term true and
; nothing by assuming the negation of the term true.  In all other cases,
; the true- and false-tau-alists are just the original tau-alist.

; Below we show a case split on the combinations.  We state in English what
; each combination means and what we deduce from it, because we found it easy
; to make coding mistakes.  The ``short answers'' are ``try both!'' (we learned
; nothing and have the appropriate extensions), ``mbt!'' (term must be true),
; ``mbf!'' (term must be false), and ``contradiction!'' (term is true and
; false, meaning we've found a contradiction in the hypotheses or world).

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    NIL    NIL    NIL    NIL    NIL)       try both!

;  We can establish neither parity of the term, nor do we see a contradiction
;  in the world; we assume tau-alist1 correctly extends tau-alist for the case
;  that the term is true, and we assume that tau-alist2 correctly extends
;  tau-alist for the case that term is false.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (T      NIL    NIL    NIL    NIL    NIL)       mbf!

; A contradiction was discovered when assuming term true, so it must be false.
; This could be rephrased: it's impossible for term to be true so it must be false.
; One might have hoped that the assumption of the negation of term would confirm
; that the negation is true (mbt2) but tau was too weak to deduce this.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    T      NIL    NIL    NIL    NIL)       mbt!

; Term must be true; one might have hoped that the assumption of its negation
; would produce a contradiction but it did not, because of a weakness in tau.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    NIL    T      NIL    NIL    NIL)       mbf!

; Term must be false; one might have hoped that the assumption of its negation
; would reinforce our discovery by saying the negation must be true (mbt2=T),
; but it did not because of a weakness in tau.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    NIL    NIL    T      NIL    NIL)       mbt!

; A contradiction was discovered when assuming the negation of term true, so
; term must be true; one might have hoped that the assumption of term would
; have produced mbt1 directly, but it did not because of a weakness in tau.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (T      NIL    NIL    T      NIL    NIL)       contradiction!

; Contradictions were discovered when assuming term true and when assuming its
; negation.  This means there must be a contradiction in the tau-alist (or
; world).  We call this a ``global contradiction.''

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    T      NIL    T      NIL    NIL)       mbt!

; Term must be true; furthermore, assuming its negation true produced a
; contradiction, confirming the earlier deduction.  This is a case of wasted
; work.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    NIL    T      T      NIL    NIL)       contradiction!

; Assuming term true established that it must be false.  But assuming its
; negation produced a contradiction, meaning that term must be true.  So we've
; reached a global contradiction.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    NIL    NIL    NIL    T      NIL)       mbf!

; Term must be false because its negation must be true; one might have hoped
; that assuming term true directly would discover that it must be false, but it
; didn't because of a weakness in tau.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (T      NIL    NIL    NIL    T      NIL)       mbf!

; A contradiction was discovered when assuming term true, so it must be false.
; This is confirmed by assuming the negation of term true and learning that the
; negation must be true.  This is a case of wasted work.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    T      NIL    NIL    T      NIL)       contradiction!

; Term must be true and its negation must be true, a global contradiction.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    NIL    T      NIL    T      NIL)       mbf!

; Term must be false and this is confirmed by assuming the negation of term and
; seeing that the negation must be true.  Wasted work.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    NIL    NIL    NIL    NIL    T  )       mbt!

; The negation of term must be false, so term must be true; one might have
; hoped that we'd have learned this directly by assuming term true, but we
; didn't because of a weakness in tau.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (T      NIL    NIL    NIL    NIL    T  )       contradiction!

; Assuming term true produces a contradiction, so it must be false.  But
; the negation of term must be false, which means term must be true.  A
; global contradiction has be discovered.

; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    T      NIL    NIL    NIL    T  )       mbt!

; Term must be true and that is confirmed by learning that the negation of term
; must be false.  Wasted work.


; ctr1   mbt1   mbf1   ctr2   mbt2   mbf2        short answer
; (NIL    NIL    T      NIL    NIL    T  )       contradiction!

; Term must be false, but the negation of term must be false also.  This is a
; global contradiction.

; We could test this by doing IF-splits on the six variables, but that gets
; tedious.  We could also do a CASE split on the vector of six booleans but
; that would require consing.  Instead, we convert the vectors to natural
; numbers and do a CASE split on that natural.  We reorder the case by
; the natural to (perhaps) help the compiler:

;  32     16     8      4      2      1
; (NIL    NIL    NIL    NIL    NIL    NIL) =  0  ==> both!
; (NIL    NIL    NIL    NIL    NIL    T  ) =  1  ==> mbt!
; (NIL    NIL    NIL    NIL    T      NIL) =  2  ==> mbf!
; (NIL    NIL    NIL    T      NIL    NIL) =  4  ==> mbt!
; (NIL    NIL    T      NIL    NIL    NIL) =  8  ==> mbf!
; (NIL    NIL    T      NIL    NIL    T  ) =  9  ==> contradiction!
; (NIL    NIL    T      NIL    T      NIL) = 10  ==> mbf!
; (NIL    NIL    T      T      NIL    NIL) = 12  ==> contradiction!
; (NIL    T      NIL    NIL    NIL    NIL) = 16  ==> mbt!
; (NIL    T      NIL    NIL    NIL    T  ) = 17  ==> mbt!
; (NIL    T      NIL    NIL    T      NIL) = 18  ==> contradiction!
; (NIL    T      NIL    T      NIL    NIL) = 20  ==> mbt!
; (T      NIL    NIL    NIL    NIL    NIL) = 32  ==> mbf!
; (T      NIL    NIL    NIL    NIL    T  ) = 33  ==> contradiction!
; (T      NIL    NIL    NIL    T      NIL) = 34  ==> mbf!
; (T      NIL    NIL    T      NIL    NIL) = 36  ==> contradiction!

            (let ((n (+ (if contradictionp1 32 0)
                        (if mbt1 16 0)
                        (if mbf1  8 0)
                        (if contradictionp2  4 0)
                        (if mbt2  2 0)
                        (if mbf2  1 0))))
              (mv-let
               (contradictionp mbt mbf true-tau-alist false-tau-alist)
               (case n
                 ( 0  (mv nil nil nil tau-alist1 tau-alist2)) ; both!
                 ( 1  (mv nil t   nil tau-alist  tau-alist))  ; mbt!
                 ( 2  (mv nil nil t   tau-alist  tau-alist )) ; mbf!
                 ( 4  (mv nil t   nil tau-alist  tau-alist))  ; mbt!
                 ( 8  (mv nil nil t   tau-alist  tau-alist )) ; mbf!
                 ( 9  (mv t   nil nil tau-alist  tau-alist))  ; contradiction!
                 (10  (mv nil nil t   tau-alist  tau-alist )) ; mbf!
                 (12  (mv t   nil nil tau-alist  tau-alist))  ; contradiction!
                 (16  (mv nil t   nil tau-alist  tau-alist))  ; mbt!
                 (17  (mv nil t   nil tau-alist  tau-alist))  ; mbt!
                 (18  (mv t   nil nil tau-alist  tau-alist))  ; contradiction!
                 (20  (mv nil t   nil tau-alist  tau-alist))  ; mbt!
                 (32  (mv nil nil t   tau-alist  tau-alist )) ; mbf!
                 (33  (mv t   nil nil tau-alist  tau-alist))  ; contradiction!
                 (34  (mv nil nil t   tau-alist  tau-alist )) ; mbf!
                 (36  (mv t   nil nil tau-alist  tau-alist))  ; contradiction!
                 (otherwise
                  (mv (er hard 'tau-term
                          "Unexpected combination of Booleans resulting from ~
                           assuming the term ~x0 both true and false.  Those ~
                           with index 1 are from assuming the term true. ~
                           Those with index 2 are from assuming the term ~
                           false, i.e., assuming the negation of the term ~
                           true. According to a long comment in tau-term we ~
                           considered every possible case but we have ~
                           encountered the following case which was not ~
                           anticipated:  ~x1."
                          (fargn term 1)
                          (list (list 'contradictionp1 contradictionp1)
                                (list 'mbt1  mbt1)
                                (list 'mbf1 mbf1)
                                (list 'contradictionp2 contradictionp2)
                                (list 'mbt2 mbt2)
                                (list 'mbf2 mbf2)))
                      nil nil nil nil)))
               (cond
                (contradictionp (mv *tau-contradiction* calist))
                (mbt
                 (tau-term (fargn term 2)
                           tau-alist type-alist pot-lst
                           ens wrld calist))
                (mbf
                 (tau-term (fargn term 3)
                           tau-alist type-alist pot-lst
                           ens wrld calist))
                (t (mv-let
                    (tau2 calist)
                    (tau-term (fargn term 2)
                              true-tau-alist type-alist pot-lst
                              ens wrld calist)
                    (mv-let
                     (tau3 calist)
                     (tau-term (fargn term 3)
                               false-tau-alist type-alist pot-lst
                               ens wrld calist)
                     (mv (combine-tau tau2 tau3 ens wrld)
                         calist))))))))))
         ((and (eq (ffn-symb term) 'UNSIGNED-BYTE-P)
               (quotep (fargn term 1))
               (integerp (cadr (fargn term 1)))
               (<= 0 (cadr (fargn term 1))))

; (UNSIGNED-BYTE-P bits x) = (AND (INTEGERP x) (<= 0 x) (< x (expt 2 bits))), provided
; bits is natp.  We just open UNSIGNED-BYTE-P under that condition.

          (tau-term `(if (integerp ,(fargn term 2))
                         (if (< ,(fargn term 2) '0)
                             'nil
                             (< ,(fargn term 2) (quote ,(expt 2 (cadr (fargn term 1))))))
                         nil)
                    tau-alist type-alist pot-lst ens wrld calist))
         ((or (eq (ffn-symb term) 'MV-NTH)
              (member-eq (ffn-symb term)
                         (global-val 'tau-mv-nth-synonyms wrld)))
          (cond ((or (not (quotep (fargn term 1)))
                     (not (natp (cadr (fargn term 1)))))

; We are dealing with (MV-NTH x y), or a synonym of MV-NTH, where x is not a
; quoted natural.  We can't do anything with this.

                 (mv *tau-empty* calist))
                ((and (nvariablep (fargn term 2))
                      (not (fquotep (fargn term 2)))
                      (not (flambdap (ffn-symb (fargn term 2))))
                      (or (nth (cadr (fargn term 1))
                               (getpropc (ffn-symb (fargn term 2))
                                         'signature-rules-form-2 nil wrld))
                          (nth (cadr (fargn term 1))
                               (getpropc (ffn-symb (fargn term 2))
                                         'tau-bounders-form-2 nil wrld))))

; We are dealing with (MV-NTH 'i (fn a1 ... ak)), or a synonym of MV-NTH, where
; the ith slot of fn has some signature rules.  We confine our attention to
; those rules and do not consider expanding fn via the big-switch property.
; Put another way, if signature and/or bounder rules are available then they are
; all that tau uses.

                 (let* ((fn (ffn-symb (fargn term 2)))
                        (sigrules (nth (cadr (fargn term 1))
                                       (getpropc fn
                                                 'signature-rules-form-2
                                                 nil
                                                 wrld)))
                        (bounders (nth (cadr (fargn term 1))
                                       (getpropc fn
                                                 'tau-bounders-form-2
                                                 nil
                                                 wrld))))
                   (mv-let
                    (actual-tau-lst calist)
                    (tau-term-lst nil
                                  (fargs (fargn term 2))
                                  tau-alist type-alist pot-lst
                                  ens wrld calist)
                    (mv-let
                     (tau1 calist)
                     (apply-tau-bounders bounders actual-tau-lst
                                         ens wrld calist)
                     (apply-signature-tau-rules
                      sigrules
                      (fargs term)
                      (if (all-unrestricted-signature-rulesp sigrules)
                          nil ; Abuse of Tau Representation
                          actual-tau-lst)
                      tau1
                      tau-alist type-alist pot-lst
                      ens wrld calist)))))
                (t

; Otherwise, we are dealing with (MV-NTH 'i y), or a synonym of MV-NTH.  We
; first expand y, if possible.  If y is hit, then we push the MV-NTH down
; through any IFs thus revealed, and recur.  Note if we're actually dealing
; with a synonym of MV-NTH we still push MV-NTH, not the synonym, down.  This
; is ok because (a) we prefer MV-NTH and (b) we don't consider signature or
; other rules for synonyms.  So it doesn't really matter what mv-nth-synonym we
; push down.

                 (mv-let (contradictionp hitp term1 calist)
                         (tau-rewrite (fargn term 2)
                                      tau-alist type-alist pot-lst
                                      ens wrld calist)
                         (cond
                          (contradictionp (mv *tau-contradiction* calist))
                          (hitp (tau-term
                                 (push-mv-nth-down (fargn term 1)
                                                   term1)
                                 tau-alist type-alist pot-lst
                                 ens wrld calist))
                          (t (mv *tau-empty* calist)))))))
         (t
          (mv-let
           (sign recog e criterion)
           (tau-like-term term :various-any wrld)
           (declare (ignore criterion))
           (cond
            (recog

; We are dealing with sign/(recog e).

             (mv-let
              (tau calist)
              (tau-term e tau-alist type-alist pot-lst
                        ens wrld calist)
              (cond
               ((eq tau *tau-contradiction*) (mv *tau-contradiction* calist))
               (t
                (let ((temp (reduce-sign/recog tau sign recog ens wrld)))
                  (cond
                   ((eq temp t)
                    (mv *tau-t* calist))
                   ((eq temp nil)
                    (mv *tau-nil* calist))
                   (t (mv (getpropc 'booleanp 'pos-implicants nil wrld)
                          calist))))))))
            (t (let* ((fn (ffn-symb term))
                      (sigrules (getpropc fn 'signature-rules-form-1 nil wrld))

                      (bounders (getpropc fn 'tau-bounders-form-1 nil wrld)))
                 (cond
                  ((and (null sigrules)
                        (null bounders)
                        (not (eq fn 'EQUAL))
                        (not (eq fn '<)))

; We are dealing with (fn a1 ... ak) and have no bounder or signature rules.
; We expand, if possible, and recur.

                   (mv-let (contradictionp hitp term1 calist)
                           (tau-rewrite term
                                        tau-alist type-alist pot-lst
                                        ens wrld calist)
                           (cond
                            (contradictionp (mv *tau-contradiction* calist))
                            (hitp (tau-term term1
                                            tau-alist
                                            type-alist pot-lst
                                            ens wrld calist))
                            (t (mv *tau-empty* calist)))))
                  (t

; For all other functions we compute the tau of the actuals, then apply bounder rules,
; and then apply signature rules.

                   (mv-let
                    (actual-tau-lst calist)
                    (tau-term-lst nil
                                  (fargs term)
                                  tau-alist type-alist pot-lst
                                  ens wrld calist)
                    (cond
                     ((eq actual-tau-lst *tau-contradiction*)
                      (mv *tau-contradiction* calist))
                     ((eq fn 'EQUAL)
                      (let ((ans
                             (tau-interval-equal-decider
                              (access tau (car actual-tau-lst) :interval)
                              (access tau (cadr actual-tau-lst) :interval))))
                        (cond
                         ((eq ans t) (mv *tau-t* calist))
                         ((eq ans nil) (mv *tau-nil* calist))
                         (t (apply-signature-tau-rules
                             sigrules
                             (fargs term)
                             (if (all-unrestricted-signature-rulesp sigrules)
                                 nil ; Abuse of Tau Representation
                                 actual-tau-lst)
                             *tau-empty*
                             tau-alist type-alist pot-lst
                             ens wrld calist)))))
                     ((eq fn '<)
                      (let ((ans
                             (tau-interval-<-decider
                              (access tau (car actual-tau-lst) :interval)
                              (access tau (cadr actual-tau-lst) :interval))))
                        (cond
                         ((eq ans t) (mv *tau-t* calist))
                         ((eq ans nil) (mv *tau-nil* calist))
                         (t (apply-signature-tau-rules
                             sigrules
                             (fargs term)
                             (if (all-unrestricted-signature-rulesp sigrules)
                                 nil ; Abuse of Tau Representation
                                 actual-tau-lst)
                             *tau-empty*
                             tau-alist type-alist pot-lst
                             ens wrld calist)))))
                     (t
                      (mv-let
                       (tau1 calist)
                       (apply-tau-bounders bounders actual-tau-lst
                                           ens wrld calist)
                       (apply-signature-tau-rules
                        sigrules
                        (fargs term)
                        (if (all-unrestricted-signature-rulesp sigrules)
                            nil ; Abuse of Tau Representation
                            actual-tau-lst)
                        tau1
                        tau-alist type-alist pot-lst
                        ens wrld calist)))))))))))))))))

(defun tau-term-lst (vars terms tau-alist type-alist pot-lst ens wrld calist)

; When non-nil, vars is assumed to be of the same length as terms.  This
; function computes the tau of each term in terms, wrt to the tau tau-alist
; supplied.  If any of those terms have contradictory tau, we return
; *tau-contradiction* instead of a normal answer.  Otherwise, if each tau is a
; standard recognizer set, we return the ``list of tau'' in one of two forms
; depending on vars.  If vars is nil, we return literally the list of tau
; computed.  If vars is not nil, we return a tau-alist pairing successive
; elements of vars with the tau of corresponding terms.  Note that when vars is
; initially a non-empty list of vars it is the same length as terms, so that if
; terms has not yet been exhausted, vars is still non-nil.

  (cond
   ((endp terms) (mv nil calist))
   (t (mv-let
       (tau calist)
       (tau-term (car terms) tau-alist type-alist pot-lst
                 ens wrld calist)
       (cond
        ((eq tau *tau-contradiction*) (mv *tau-contradiction* calist))
        (t (mv-let
            (taut calist)
            (tau-term-lst (cdr vars) (cdr terms)
                          tau-alist type-alist pot-lst
                          ens wrld calist)
            (cond
             ((eq taut *tau-contradiction*)
              (mv *tau-contradiction* calist))
             (t
              (mv (cons (if vars (cons (car vars) tau) tau)
                        taut)
                  calist))))))))))

(defun tau-rewrite (term tau-alist type-alist pot-lst ens wrld calist)

; We return (mv contradictionp hitp term').  If contradictionp is t, we found a
; contradiction.  If contradictionp is nil then if hitp is t, term' is a
; rewritten version of term that is provably equal to term under the
; assumptions in tau-alist.  If hitp is nil, we haven't changed term and term'
; is term.  This is a No Change Loser on term.

; This function isn't really recursive, it just calls tau-term and could have
; been expanded in place where it is used in tau-term and tau-assume.  But we
; define it for code-sharing reasons.

; See below for a discussion of how we might extend this function to do
; more rewriting.

  (cond
   ((and (nvariablep term)
         (not (fquotep term))
         (not (flambdap (ffn-symb term))))
    (let* ((bs (getpropc (ffn-symb term) 'big-switch nil wrld)))
      (cond
       (bs
        (let ((switch-val (nth (access big-switch-rule bs :switch-var-pos)
                               (fargs term))))
          (mv-let
           (switch-tau calist)
           (tau-term switch-val tau-alist type-alist pot-lst
                     ens wrld calist)
           (cond
            ((eq switch-tau *tau-contradiction*)

; If any term, whether one we're looking at or one that someone dreams up, has
; a contradictory tau, then there is a contradiction in the system and/or
; tau-alist.  Thus, the term we are looking at is contradictory too.

             (mv t nil term calist))
            ((equal switch-tau *tau-empty*)

; If we know nothing about the switch, then the attempt to expand it will
; fail.  Why bother?

             (mv nil nil term calist))
            (t (mv-let (hitp term1)
                       (tau-expand-big-switch
                        (access big-switch-rule bs :body)
                        (access big-switch-rule bs :switch-var)
                        switch-tau
                        (pairlis$ (access big-switch-rule bs :formals)
                                  (fargs term))
                        ens wrld)
                       (cond
                        (hitp (mv nil t term1 calist))
                        (t (mv nil nil term calist)))))))))
       (t (mv nil nil term calist)))))
   (t (mv nil nil term calist))))

(defun relieve-dependent-hyps (hyps formals actuals
                                    tau-alist type-alist pot-lst
                                    ens wrld calist)
  (declare (ignore tau-alist))

; At the moment, we relieve dependent hyps solely by type-set reasoning (which
; may involve a little linear reasoning).  But we do not use tau reasoning
; because of the issue reported in On Loops in Relieving Dependent Hyps in Tau
; Signature Rules.  However, in case we find a better heuristic, we continue to
; pass both tau-alist and  into this function.  Note that this also means
; that the incoming calist is always equal to the outgoing calist for this
; function, but we don't code for that.  We return the calist to our callers,
; so that we could change the heuristic later without damage to the rest of
; this nest.

  (cond
   ((endp hyps) (mv t calist))
   (t (let* ((inst-hyp (subcor-var formals actuals (car hyps))))
        (mv-let (ts ttree)
                (type-set inst-hyp nil nil type-alist
                          ens wrld nil pot-lst nil)
                (cond
                 ((or (tagged-objectsp 'assumption ttree)
                      (tagged-objectsp 'fc-derivation ttree))
                  (mv (er hard 'relieve-dependent-hyps
                          "Type-set returned a ttree containing one or more ~
                           'ASSUMPTION or 'FC-DERIVATION entries.  This was ~
                           thought to be impossible given the way type-alist ~
                           and pot-lst are configured by ~
                           CHEAP-TYPE-ALIST-AND-POT-LST.  The term on which ~
                           type-set was called is ~X01."
                          inst-hyp nil)
                      calist))
                 ((not (ts-intersectp ts *ts-nil*))
                  (relieve-dependent-hyps (cdr hyps)
                                          formals actuals
                                          nil ; = tau-alist
                                          type-alist pot-lst
                                          ens wrld calist))
                 (t (mv nil calist))))))))

(defun ok-to-fire-signature-rulep (sigrule actuals actual-tau-lst
                                           tau-alist type-alist pot-lst
                                           ens wrld calist)

  (if (ok-to-fire-signature-rulep1
       (access signature-rule sigrule :input-tau-list)
       actual-tau-lst ens wrld)
      (let ((hyps (access signature-rule sigrule :dependent-hyps)))
        (if (null hyps)
            (mv t calist)
            (relieve-dependent-hyps hyps
                                    (access signature-rule sigrule :vars)
                                    actuals
                                    tau-alist type-alist pot-lst
                                    ens wrld calist)))
      (mv nil calist)))

(defun apply-signature-tau-rule (sigrule actuals actual-tau-lst
                                         tau-alist type-alist pot-lst
                                         ens wrld calist)

; We decide whether sigrule applies to the (fn . actuals) in the current
; context.  Sigrule is a signature-rule about function symbol fn.  Actuals is a
; list of terms to which fn is being applied.  Actual-tau-lst is a list of the
; tau for the actuals.  We return (mv sign recog) or (mv nil nil), indicating
; whether sigrule applies to (fn . actuals).

  (mv-let (okp calist)
          (ok-to-fire-signature-rulep sigrule actuals
                                      actual-tau-lst
                                      tau-alist type-alist pot-lst
                                      ens wrld calist)
          (cond (okp
                 (mv (access signature-rule sigrule :output-sign)
                     (access signature-rule sigrule :output-recog)
                     calist))
                (t (mv nil nil calist)))))

(defun apply-signature-tau-rules1 (sigrules actuals actual-tau-lst tau
                                            tau-alist type-alist pot-lst
                                            ens wrld calist)

; Sigrules is the list of signature-rules for some expression involving some
; actual expressions.  Actual-tau-lst is a list of n recognizer sets
; characterizing those actuals.  Several of the rules in sigrules may apply and
; we apply all that do and accumulate the resulting tau about the call of
; whatever function these rules are stored under.  We return tau', where tau'
; may be *tau-contradiction*.

  (cond
   ((eq tau *tau-contradiction*) (mv *tau-contradiction* calist))
   ((endp sigrules) (mv tau calist))
   (t (mv-let
       (sign recog calist)
       (apply-signature-tau-rule (car sigrules) actuals actual-tau-lst
                                 tau-alist type-alist pot-lst
                                 ens wrld calist)
       (cond
        ((null recog)
         (apply-signature-tau-rules1 (cdr sigrules) actuals actual-tau-lst
                                     tau
                                     tau-alist type-alist pot-lst
                                     ens wrld calist))
        (t (mv-let
            (tau calist)
            (add-to-tau! sign recog tau ens wrld calist)
            (cond
             ((eq tau *tau-contradiction*) (mv *tau-contradiction* calist))
             (t (apply-signature-tau-rules1 (cdr sigrules) actuals
                                            actual-tau-lst tau
                                            tau-alist type-alist pot-lst
                                            ens wrld calist))))))))))

(defun apply-signature-tau-rules (sigrules actuals actual-tau-lst tau
                                           tau-alist type-alist pot-lst
                                           ens wrld calist)

; Sigrules is the list of signature-rules for some function application
; involving some actual expressions.  Actual-tau-lst is either
; *tau-contradiction* or a list of n recognizer sets characterizing those
; actuals.  If actual-tau-lst is *tau-contradiction* it means one of the
; actuals has a contradictory tau and we return the contradictory tau.
; Otherwise, we use the rules in sigrules to compute the tau of function
; application.  Several of the rules in sigrules may apply and we apply all
; that do and accumulate the resulting tau about the call of the function in
; question.  We return tau', where tau' may be *tau-contradiction*.

  (cond ((or (eq actual-tau-lst *tau-contradiction*)
             (eq tau *tau-contradiction*))
         (mv *tau-contradiction* calist))
        (t (apply-signature-tau-rules1 sigrules actuals actual-tau-lst tau
                                       tau-alist type-alist pot-lst
                                       ens wrld calist))))

(defun tau-assume-basic (sign term tau-alist type-alist pot-lst ens wrld calist)

; Here is the generic way to assume an arbitrary term true in the tau system.
; Of course, recognizer terms get special treatment, as do conjunctions, lambda
; applications, and big switches.  But this generic processing is done in
; several places in tau-assume and it is helpful to package it up in a single
; function.

; We return (mv contradictionp mbt mbf tau-alist') and this is a No Change
; Loser on tau-alist.  If contradictionp is t, a contradiction in the system
; (tau-alist and wrld) has been detected.

; Note on sign: It may be easier to think of sign as controlling whether we
; want to assume term true (sign = t) or false (sign = nil) than it is to think
; of sign as modifying the term we're assuming true.  Furthermore, note that if
; the tau of term is tau1 and you want to assume term true (sign = t), you add
; NIL to the :NEG-EVGS of tau1; if you want to assume term false (sign = nil),
; you add NIL to the :POS-EVG.  So you add NIL to the ``evg'' component of the
; opposite sign.

  (mv-let
   (tau calist)
   (tau-term term tau-alist type-alist pot-lst
             ens wrld calist)
   (cond
    ((eq tau *tau-contradiction*)
     (mv t nil nil tau-alist calist))
    (t (mv-let
        (tau1 calist)
        (add-to-tau! (not sign) *nil-singleton-evg-list* tau ens wrld calist)

; Tau1 is the tau of sign/term with the ``additional'' fact that sign/term is
; non-NIL.  If we get a contradiction from that addition, then we already know
; that term is nil, so we signal mbf.  If we don't change anything, we already
; know term must be non-nil, so we signal mbt.  Otherwise, we return the new
; alist.

        (cond
         ((eq tau1 *tau-contradiction*)
          (mv nil nil t tau-alist calist))
         ((equal tau1 tau)
          (mv nil t nil tau-alist calist))
         (t (mv nil nil nil (cons (cons term tau1) tau-alist) calist))))))))

(defun tau-assume (sign term tau-alist type-alist pot-lst ens wrld calist)

; We assume sign/term true and augment tau-alist appropriately.  We return (mv
; contradictionp mbt mbf tau-alist').  Recall that sign is T (positive) or NIL
; (negative).  Thus, if sign is T we assume term true and if sign is NIL we
; assume term false.  If contradictionp is t, we found a contradiction in the
; original alist; mbt and mbf are mutually exclusive flags indicating that
; sign/term must be true (mbt) or must be false (mbf), and tau-alist' is the
; extended tau-alist with sign/term in it.  No Change Loser on tau-alist.

; Basic Design of tau-assume:

; The special cases are:

; - lambda application: expand and recur. Note that abstract interpretation is
;   not a likely option in tau-assume.  We really need to express the new
;   assumptions in terms of the actuals, not the tau of the actions.  E.g.,
;   ((lambda (x) (NATP x)) A) should produce the assumption ``A is a NATP,''
;   not ``x is a NATP, where x is the tau of A'' (whatever that means).  Also,
;   see the mention of the abstract interpretation method tau-term above.

; - (IF a b NIL) and other forms of conjunction:  assume both conjuncts

; - (UNSIGNED-BYTE-P 'n x) where (natp n):  expand definition to conjunction

; - (recog a): add recog (and its implicants) to the tau of a as computed under
;   tau-alist

; - (fn ...) where fn is a big switch:  expand the big switch if heuristically
;   allowed and recur

; - otherwise, just use the basic technique of adding nil or non-nil to the
;   tau of the term

  (mv-let
   (notp term)
   (strip-not term)
   (let ((sign (if notp (not sign) sign)))
     (cond
      ((or (variablep term)
           (fquotep term))
       (tau-assume-basic sign term tau-alist type-alist pot-lst
                         ens wrld calist))
      ((flambdap (ffn-symb term))
       (tau-assume sign
                   (subcor-var (lambda-formals (ffn-symb term))
                               (fargs term)
                               (lambda-body (ffn-symb term)))
                   tau-alist type-alist pot-lst
                   ens wrld calist))
      ((eq (ffn-symb term) 'IF)
       (mv-let
        (conjunctionp sign1 conjunct1 sign2 conjunct2)
        (deconstruct-conjunction sign
                                 (fargn term 1)
                                 (fargn term 2)
                                 (fargn term 3))
        (cond
         (conjunctionp
          (mv-let
           (contradictionp mbt1 mbf1 tau-alist1 calist)
           (tau-assume sign1 conjunct1 tau-alist type-alist pot-lst
                       ens wrld calist)
           (cond
            (contradictionp (mv t nil nil tau-alist calist))
            (mbf1 (mv nil nil t tau-alist calist))
            (t
             (mv-let
              (contradictionp mbt2 mbf2 tau-alist2 calist)
              (tau-assume sign2 conjunct2
                          tau-alist1 type-alist pot-lst
                          ens wrld calist)
              (cond
               (contradictionp (mv t nil nil tau-alist calist))
               ((and mbt1 mbt2) (mv nil t nil tau-alist calist))
               (mbf2 (mv nil nil t tau-alist calist))
               (t (mv nil nil nil tau-alist2 calist))))))))
         (t (mv-let
             (tau-test calist)
             (tau-term (fargn term 1)
                       tau-alist type-alist pot-lst
                       ens wrld calist)
             (cond
              ((eq tau-test *tau-contradiction*)
               (mv t nil nil tau-alist calist))
              (t (let ((pos-evg (access tau tau-test :pos-evg)))
                   (cond
                    (pos-evg
                     (tau-assume sign
                                 (if (equal *nil-singleton-evg-list* pos-evg)
                                     (fargn term 3)
                                     (fargn term 2))
                                 tau-alist type-alist pot-lst
                                 ens wrld calist))
                    ((member-nil-neg-evgs (access tau tau-test :neg-evgs))
                     (tau-assume sign (fargn term 2)
                                 tau-alist type-alist pot-lst
                                 ens wrld calist))

; Note: It is still possible that the tau system could be used to determine
; that tau-test excludes nil!  How can this happen if nil is not among the
; neg-evgs?  It could be that there is a pos-pair for, say, INTEGERP, that
; rules nil out by evaluation.  Because we delete any neg-evg that is
; implicitly determined by the pos-pairs, we won't find an explicit nil in
; neg-evgs.  This ought to be fixed.  But at the moment we'll just let tau be
; this weak.

                    (t (tau-assume-basic sign term
                                         tau-alist type-alist pot-lst
                                         ens wrld calist)))))))))))
      ((and (eq (ffn-symb term) 'UNSIGNED-BYTE-P)
            (quotep (fargn term 1))
            (integerp (cadr (fargn term 1)))
            (<= 0 (cadr (fargn term 1))))

; (UNSIGNED-BYTE-P bits x) = (AND (INTEGERP x) (<= 0 x) (< x (expt 2 bits))), provided
; bits is natp.  We just open UNSIGNED-BYTE-P under that condition.

       (tau-assume sign
                   `(if (integerp ,(fargn term 2))
                        (if (< ,(fargn term 2) '0)
                            'nil
                            (< ,(fargn term 2) (quote ,(expt 2 (cadr (fargn term 1))))))
                        nil)
                   tau-alist type-alist pot-lst ens wrld calist))
      (t
       (mv-let
        (rsign recog e criterion)
        (tau-like-term term :various-any wrld)
        (declare (ignore criterion))
        (cond
         (recog
          (mv-let
           (tau calist)
           (tau-term e tau-alist type-alist pot-lst
                     ens wrld calist)
           (cond
             ((eq tau *tau-contradiction*)
              (mv t nil nil tau-alist calist))
             (t
              (let* ((qsign (if sign rsign (not rsign)))

; Note: sign/term = sign/(rsign/(recog e)) = (sign/rsign)/(recog e) =
; qsign/(recog e).

                     (temp (reduce-sign/recog tau qsign recog ens wrld)))
                (cond
                 ((eq temp t)
                  (mv nil t nil tau-alist calist))
                 ((eq temp nil)
                  (mv nil nil t tau-alist calist))
                 (t (mv-let
                     (tau1 calist)
                     (add-to-tau! qsign recog tau ens wrld calist)
                     (cond ((eq tau1 *tau-contradiction*)
                            (mv t nil nil tau-alist calist))
                           (t (mv nil nil nil
                                  (cons (cons e tau1) tau-alist)
                                  calist)))))))))))
         (t (mv-let (contradictionp hitp term1 calist)
                    (tau-rewrite term tau-alist type-alist pot-lst
                                 ens wrld calist)
                    (cond
                     (contradictionp (mv t nil nil tau-alist calist))
                     (hitp (tau-assume sign term1
                                       tau-alist type-alist pot-lst
                                       ens wrld calist))
                     (t (tau-assume-basic sign term
                                          tau-alist type-alist pot-lst
                                          ens wrld calist))))))))))))
)

; Note on a Possible Extension of Tau-Rewrite: We have considered adding other
; kinds of expansions, e.g., with ABBREVIATION rewrite rules or with
; unconditional ``nonrec'' DEFINITION rules.  We quote nonrec because sometimes
; alternative definitions have non-trivial recursivep fields, indicating that
; they are mutually recursive with other functions.  But sometimes these other
; functions are full fledged tau recognizers (now effectively disabled) and the
; ``recursive'' definition in question is just an abbreviation for some nest of
; those.  To handle this the tau database would need to have a set of
; unconditional rewrite rules for which rewrite termination was guaranteed.
; Such a set might be formed by looking at all alternative definitions and
; layering them.  Let's say a function is ``tau primitive'' if it is an ACL2
; primitive (e.g., IF) or a tau recognizer.  Let's say function gn is
; ``earlier'' than fn if the absolute-event-number of gn is less than that of
; fn.  Then layer 0 functions are the tau primitives.  Layer 1 functions are
; those defined in terms of earlier functions and/or layer 0 functions.  Layer
; 2 functions are those defined in terms of earlier functions and/or layer 0 or
; 1 functions.  Etc.  Any function not so classified is a member of a mutually
; recursive clique and its definition involves another such function.
; Equations for such functions would be ignored, i.e., when setting up the tau
; database we create a set of unconditional rewrite rules only for those
; functions assigned some layer.  But until we see the need for this we will
; not add other forms of rewrite rules.

; On Tau-Clause -- Using Tau to Prove or Mangle Clauses

; Now we develop the code for tau-clause, which processes a clause with tau
; information.  In the first cut at this design, tau-clause transformed a
; clause into a provably equivalent clause.  In particular, it could delete a
; literal known to be false given the other literals.  We call this the
; ``deleted literal'' problem below.  It causes real problems in the
; regression.  If a literal, say lit, is dropped from a clause because of tau
; reasoning then that literal had better be derivable by non-tau reasoning just
; as if it were in the clause (e.g., by type-set) if it is involved in the
; eventual proof of the clause by type-set, rewrite, etc.

; The regression exposed two kinds of commonly occurring problems related to
; literal deletion.  One was where the user had introduced (perhaps by a hint)
; hypothesis like (rel-prime-moduli '(11 13 17)) and did not want it to
; disappear and so disabled the executable-counterpart of the function
; involved.  Sometimes this happened accidently: users would be operating in a
; minimal theory in which almost everything was disabled and then after the
; hint they would employ rules that had been designed (only) to operate with
; these literals explicitly around.  Such scripts could be reworked to enable
; the hyp to evaporate, but we just turned the tau system off and reverted to
; the old proof.

; The second common instance of the literal deletion problem is when a
; signature rule, perhaps proved as a rewrite rule rather than as
; type-prescription, allowed tau to delete a key literal.  We saw many examples
; of literals like this evaporating: (integerp (mv-nth 1 (foo x y))).

; The deletion of literals is a problem because the tau system has no way to
; tell type-set what is knows.  So allowing tau to drop a literal turns out to
; have caused a large number of changes in the regression suite (relative to
; that for Version_4.3).  In general, tau can damage a proof script in two
; ways: the literal deletion problem and the subgoal renaming problem.  The
; latter happens when tau proves one of the several clauses that used to be
; generated by simplification, causing subsequent clauses to have new clause
; ids -- which becomes a problem if a hint is stored under the old clause id.

; As of August, 2011, with the first tau implementation on top of Version_4.3,
; the following community books were changed to support a regression with Tau
; System enabled.  The "i + j" notes in the left margins mean that i disablings
; of tau-system were inserted into the book to deal with literal deletion
; problems and j disablings were inserted to deal with subgoal renumbering
; problems or other more basic problems (e.g., coi/util/extra-info-test.lisp
; uses a must-fail event to show that a certain theorem is not provable while
; some things are disabled and tau must be among them!).

;  2 + 0 books/proofstyles/invclock/c2i/c2i-partial.lisp
;  4 + 0 books/proofstyles/invclock/c2i/c2i-total.lisp
;  1 + 0 books/proofstyles/invclock/i2c/inv-to-clock.lisp
;  1 + 0 books/proofstyles/invclock/compose/compose-c-c-partial.lisp
;  1 + 0 books/proofstyles/invclock/compose/compose-c-c-total.lisp
;  5 + 0 books/data-structures/memories/memory-impl.lisp
;  2 + 0 books/rtl/rel8/support/lib2.delta1/mult-new-proofs.lisp
;  3 + 0 books/coi/records/mem-domain.lisp
;  1 + 0 books/workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly/fucongruencias-producto.lisp
;  1 + 0 books/str/natstr.lisp
;  2 + 0 books/coi/osets/listsets.lisp
;  6 + 0 books/workshops/2006/schmaltz-borrione/GeNoC-support/GeNoC.lisp
;  1 + 0 books/coi/gacc/abstract-gacc.lisp
;  1 + 0 books/coi/gacc/fr-path-connection.lisp
; 11 + 0 books/workshops/2007/schmaltz/genoc-v1.0/generic-modules/GeNoC.lisp
;  3 + 0 books/workshops/1999/embedded/Proof-Of-Contribution/Proof-Of-Equiv-From-M-Corr.lisp
;  1 + 0 books/workshops/1999/embedded/Proof-Of-Contribution/Proof-Of-Correctness-OneCycle.lisp
;  3 + 0 books/workshops/2004/sawada/support/bv.lisp

;  1 + 1 books/workshops/2006/cowles-gamboa-euclid/Euclid/ed3.lisp
;  0 + 1 books/coi/util/extra-info-test.lisp  [tau-system completely disabled at top of book]
;  0 + 2 books/workshops/2002/cowles-flat/support/flat-ackermann.lisp
;  0 + 3 books/workshops/2002/cowles-flat/support/flat-reverse.lisp
;  0 + 1 books/workshops/2007/schmaltz/genoc-v1.0/instantiations/routing/xy-routing/xy-routing.lisp
;  0 + 2 books/workshops/2007/schmaltz/genoc-v1.0/instantiations/routing/doubleY-routing/doubleY-routing.lisp
;  0 + 1 books/workshops/2009/verbeek-schmaltz/verbeek/instantiations/scheduling/circuit-switching-global/circuit.lisp
;  0 + 4 books/workshops/2009/verbeek-schmaltz/verbeek/instantiations/genoc/simple-ct-global/simple.lisp

; In order to deal with the literal deletion problem, we changed the design so
; that tau no longer deletes literals known (by it) to be false!  By making tau
; no longer delete literals we reduced the number of modified books to just
; those last eight above.  To find the required modifications, search the
; relevant books for tau-system.

; Returning to the design of tau-clause, there is the standard problem of
; tail-biting.  Because of performance considerations, we have adopted a cheap
; approach: reorder the clause in a heuristic way and then process each literal
; in turn, tau-assuming only the literals to its left in the (re-)ordering.

; To support literal deletion (perhaps someday, when tau can communicate to
; type-set) we must be able to return a simplified clause to its original
; order.  To facilitate this we annotate the clause, converting it to a list of
; triples, where one component of the triple controls the ordering for purposes
; of tau-assume and the other component controls the ordering for re-assembling
; the final answer.  (The third component is, of course, the literal itself.)
; Given that we don't support literal deletion, one of these components is
; simply ignored right now.

; But this still leaves the tau-assume order to be determined.

; The original heuristic was to identify each literal with a key term, which
; was the recognizer subject of the literal.  Thus, (integerp v) and (not
; (equal v 'evg)) both had the key term v, and non-recognizer literals were
; their own key terms.  Then we sorted by term-order on the key terms.  But
; this failed to get a typical kind of clause arising in Dave Greve's work.
; Consider a clause containing among its literals both (not (big-switch flg
; x)), where conditions on flg allow big-switch to dive to something useful
; like (integerp x), and the literal (integerp (fn x)).  Suppose there is a
; signature rule on fn that tells us it returns an integer if given one.  Such
; a clause would be recognized as true if the big-switch is processed first.
; But it is not recognized as true if the big-switch is processed second.  The
; problem, of course, is that (big-switch flg x) could be of either ``kind'' --
; a helpful ``context setter'' or an appeal to a signature rule.  We can't know
; until we dive into it.  Worse, we can't know until we dive into it WITH THE
; RIGHT context!  That is, (big-switch flg x) might expand to (integerp x) if
; we have assumed (integerp (fn x)) true and might not otherwise.  So we might
; be in the impossible situation of having to try every ordering or even to
; iterate, e.g., assume (integerp (fn x)), then process (big-switch flg x) and
; other literals in some order, learn that (integerp x), and then look at
; (integerp (fn x)) again -- all while not biting our own tail.

; So we punted and decided to ``trust the user'' to present these problematic
; literals in the order required!  Least problematic are recognizer literals
; about variables, so we'll do them first.  In fact, we'll put the negative
; variable equality literals first (they are hypotheses of the form (EQUAL var
; 'evg)) and all the other ``variable recognizer'' literals in order (though
; their order doesn't matter).  And otherwise, we will leave the literals in
; the order given.  The rationale of this ``trust the user'' idea is: guard
; verification requires that tests govern usage.

; We want to assign numbers to literals so that when the literals are ordered
; ascending according to the assigned numbers, the negative variable equalities
; are first, then the remaining variable recognizers, and finally the remaining
; literals -- with all literals within a block ordered as given.  We could do
; this with lexicographic ordering but arithmetic is simpler since there are a
; finite number of indices for any given clause.  Let max be the number of
; literals in the clause.  We assume max > 0.  Let i be the position of a given
; literal.  Then we will assign that literal i if it is a negative variable
; equality, i+max, if it a positive variable equality or other variable
; recognizer, and i+2max otherwise.  We call this number the key number of the
; literal.

(defun annotate-clause-with-key-numbers (clause max i wrld)

; We replace each lit of clause with (k i lit), where k is its key number and i
; is its position in the original clause.  To sort the resulting list for
; purposes of tau-assume, use merge-sort-car-<.  To restore that sorted list to
; its original order use merge-sort-cadr-<

  (cond
   ((endp clause) nil)
   (t (let ((lit (car clause)))
        (mv-let
         (rsign recog e criterion)
         (tau-like-term lit :various-any wrld)
         (declare (ignore rsign criterion))
         (cons (list
                (if (and recog (variablep e))
                    (if (cdr recog) ; i.e., recog = (i . fn), not (evg).
                        (+ i (* 2 max))
                        i)
                    (+ i (* 3 max)))
                i lit)
               (annotate-clause-with-key-numbers
                (cdr clause) max (+ 1 i) wrld)))))))

(defun tau-clause1p (triples tau-alist type-alist pot-lst ens wrld calist)

; Warning: type-alist and pot-lst are always nil!  See the Note at the top of
; mutual-recursion clique defining tau-term and tau-assume.

; Triples is some tail of an annotated clause (that has been reordered by its
; key numbers).  Tau-alist assumes the falsity of every literal of the original
; reordered annotation PRECEDING the first literal in triples.  Similarly,
; type-alist and pot-list record the falsity of every literal and are used to
; relieve dependent hyps.  See On Loops in Relieving Dependent Hyps in Tau
; Signature Rules for a note about our weakness at relieving these hyps.

; We successively assume the falsity of every literal in triples.  We return
; either T or NIL, where T means the annotated clause is true by tau reasoning
; and NIL means we could not prove it by tau reasoning.

  (cond
   ((endp triples) (mv nil calist))
   (t (mv-let
       (contradictionp mbt mbf tau-alist calist)
       (tau-assume nil (caddr (car triples))
                   tau-alist type-alist pot-lst
                   ens wrld calist)

       (declare (ignore mbt))

; Note that we assume the truth of (NOT lit).  If (NOT lit) must be false, then
; lit must be true and the clause is true.  If (NOT lit) must be true, lit must
; be false and we can drop it from the clause.  If we get a contradiction then
; we can prove the clause is true.

       (cond
        (contradictionp (mv t calist))
        (mbf (mv t calist))
        (t (tau-clause1p (cdr triples)
                         tau-alist type-alist pot-lst ens wrld calist)))))))

; We are now almost ready to define tau-clausep, the function that recognizes
; true clauses based on tau reasoning... except we can't because we might need
; to construct a type-alist and pot-lst for use in relieving dependent hyps and
; need that machinery.  So we delay the definition of tau-clausep until
; prove.lisp.


; -----------------------------------------------------------------
; Gathering Data about the TAU World

; At the bottom of this section you'll find two forms that print stats.

(defun tau-get-all-preds (wrld ans)
  (cond ((endp wrld) ans)
        ((eq (cadr (car wrld)) 'tau-pair)
         (tau-get-all-preds (cdr wrld) (add-to-set-eq (car (car wrld)) ans)))
        (t (tau-get-all-preds (cdr wrld) ans))))

(defun tau-get-stats-new-max-block (pred prop val-len block)

; Block is a data structure that maintains information about the two longest
; implicant lists seen so far.  We accumulate into it the current implicant
; list.

  (case-match block
    (((':MAX max-pred max-prop max-len)
      (':NEXT & & next-len))
     (cond ((> val-len max-len)
            `((:MAX ,pred ,prop ,val-len)
              (:NEXT ,max-pred ,max-prop ,max-len)))
           ((> val-len next-len)
            `((:MAX ,max-pred ,max-prop ,max-len)
              (:NEXT ,pred ,prop ,val-len)))
           (t block)))
    (& block)))


(defun tau-size (tau)
  (+ (if (access tau tau :pos-evg) 1 0)
     (length (access tau tau :neg-evgs))
     (length (access tau tau :pos-pairs))
     (length (access tau tau :neg-pairs))))

(defun tau-get-stats-on-implicant-sizes (preds wrld ans max-block)
; Max2 is (pred prop . value) for the longest implicant list.
; Max1 is the second longest.  The -lens are the corresponding lengths.

  (cond
   ((endp preds) (list (merge-sort-lexorder ans) max-block))
   (t (let ((pos-size (tau-size (getpropc (car preds) 'pos-implicants nil
                                          wrld)))
            (neg-size (tau-size (getpropc (car preds) 'neg-implicants nil
                                          wrld))))
        (tau-get-stats-on-implicant-sizes
         (cdr preds)
         wrld
         (cons pos-size (cons neg-size ans))
         (tau-get-stats-new-max-block
          (car preds)
          'neg-implicants
          neg-size
          (tau-get-stats-new-max-block (car preds)
                                       'pos-implicants
                                       pos-size
                                       max-block)))))))

(defun decode-recog (sign recog e)
  (let* ((discriminator (cdr recog))
         (atm
          (cond ((null discriminator)
                 `(equal ,e (quote ,@recog)))
                ((eq discriminator :lessp-k-x)
                 `(< ',(car discriminator) ,e))
                ((eq discriminator :lessp-x-k)
                 `(< ,e ',(car discriminator)))
                (t `(,discriminator ,e)))))
    (if sign
        atm
        `(not ,atm))))

(defun decode-recog-lst (sign lst e)
  (cond ((endp lst) nil)
        (t (cons (decode-recog sign (car lst) e)
                 (decode-recog-lst sign (cdr lst) e)))))

(defun decode-tau1 (tau e)
  (append (decode-recog-lst t
                            (if (access tau tau :pos-evg)
                                (list (access tau tau :pos-evg))
                                nil)
                            e)
          (decode-recog-lst t
                            (revappend (access tau tau :pos-pairs) nil)
                            e)
          (decode-tau-interval (access tau tau :interval) e t)
          (decode-recog-lst nil
                            (access tau tau :neg-evgs)
                            e)
          (decode-recog-lst nil
                            (revappend (access tau tau :neg-pairs) nil)
                            e)))

(defun decode-tau (tau e)
  (cond
   ((eq tau *tau-contradiction*) nil)
   (t (let ((terms (decode-tau1 tau e)))
        (cond ((endp terms) t)
              ((endp (cdr terms)) (car terms))
              (t `(and ,@terms)))))))

; On Tau Debugging Features

; These functions and macros are for debugging only.  They're not used by
; our code.

;   (program)
;
;   (mutual-recursion
;    (defun ptrans (term)
;   ; Like translate, but very limited: quote unquoted constants and expand
;   ; >, <=, and >=.
;      (cond ((atom term)
;             (cond
;              ((or (eq term nil)
;                   (eq term t))
;               (list 'quote term))
;              ((symbolp term) term)
;              ((or (acl2-numberp term)
;                   (stringp term)
;                   (characterp term))
;               (list 'quote term))
;              (t term)))
;            ((eq (car term) 'quote)
;             term)
;            ((member (car term) '(> <= >=))
;             (let ((a1 (ptrans (nth 1 term)))
;                   (a2 (ptrans (nth 2 term))))
;               (case (car term)
;                 (> `(< ,a2 ,a1))
;                 (<= `(not (< ,a2 ,a1)))
;                 (otherwise `(not (< ,a1 ,a2))))))
;            (t (cons (car term)
;                     (ptrans-lst (cdr term))))))
;    (defun ptrans-lst (terms)
;      (cond ((endp terms) nil)
;            (t (cons (ptrans (car terms))
;                     (ptrans-lst (cdr terms)))))))
;
;   ; (mktau nil (natp e) (<= e 100)) produces a tau representing just those two
;   ; recognizers.  Replacing the nil by t produces a ``complete'' tau with the
;   ; implicants.  Mktau! makes such a tau and then decodes it back to a pseudo-term.
;
;   (defmacro mktau (complete-flg &rest terms)
;     `(convert-tau-like-terms-to-tau ,complete-flg ',(ptrans-lst terms)
;                                     (ens state) (w state)))
;
;   (defmacro mktau! (complete-flg &rest terms)
;     `(decode-tau
;       (convert-tau-like-terms-to-tau ,complete-flg
;                                      ',(ptrans-lst terms)
;                                      (ens state)
;                                      (w state))
;       'e))
;
;   (logic)

(defun decode-tau-conjunctive-rule (tau)
  (cond
   ((eq tau *tau-contradiction*) nil)
   (t (let* ((terms (decode-tau1 tau 'v)))

; Terms ought to contain at least three literals if it is really a conjunctive
; rule.  It cannot be nil because of the test above.  If it contains just 1
; literal it could be thought of as the pathological conjunctive rule (t & t)
; --> p, where tau is -p.  Similarly for two literals.

        (cond
         ((null (cdr terms)) (dumb-negate-lit (car terms)))
         (t (let ((concl (dumb-negate-lit (car (last terms))))
                  (hyps (all-but-last terms)))
              (cond
               ((null hyps) (dumb-negate-lit concl))
               ((null (cdr hyps)) `(implies ,(car hyps) ,concl))
               (t  `(implies (and ,@hyps) ,concl))))))))))

(defun decode-tau-conjunctive-rules (lst)
  (cond ((endp lst) nil)
        (t (cons (decode-tau-conjunctive-rule (car lst))
                 (decode-tau-conjunctive-rules (cdr lst))))))

(defun decode-tau-lst (lst e-lst)
  (cond ((endp lst) nil)
        (t (let ((hyp (decode-tau (car lst) (car e-lst))))
             (cond ((eq hyp t)
                    (decode-tau-lst (cdr lst) (cdr e-lst)))
                   (t (cons hyp (decode-tau-lst (cdr lst) (cdr e-lst)))))))))

(defun decode-tau-alist (alist seen)
  (cond ((endp alist) nil)
        ((member-equal (car (car alist)) seen)
         (decode-tau-alist (cdr alist) seen))
        (t (cons (decode-tau (cdr (car alist)) (car (car alist)))
                 (decode-tau-alist (cdr alist)
                                   (cons (car (car alist)) seen))))))

(defun decode-tau-signature-rule (flg fn sr wrld)

; If flg is nil, we decode sr as a form 1 rule about (fn v1 ... vk).  If flg is
; non-nil, it is some natural i and we decode sr as a form 2 rule about (mv-nth
; i (fn v1 ... vk)).

  (cond
   ((and (symbolp fn)
         (arity fn wrld))
    (let* ((vars (access signature-rule sr :vars))
           (input-tau-list (access signature-rule sr :input-tau-list))
           (dependent-hyps (access signature-rule sr :dependent-hyps))
           (output-recog (access signature-rule sr :output-recog))
           (output-sign (access signature-rule sr :output-sign))
           (discriminator (cdr output-recog))
           (eterm (if (null flg)
                      `(,fn ,@vars)
                      `(mv-nth ,flg (,fn ,@vars))))
           (hyps (append (decode-tau-lst input-tau-list vars)
                         dependent-hyps))
           (concl-atm
            (cond ((null discriminator)
                   `(equal ,eterm
                           ,(kwote
                             (car (access signature-rule sr
                                          :output-recog)))))
                  ((eq discriminator :lessp-k-x)
                   `(< ,(kwote (car output-recog)) ,eterm))
                  ((eq discriminator :lessp-x-k)
                   `(< ,eterm ,(kwote (car output-recog))))
                  (t
                   `(,discriminator ,eterm))))
           (concl (if output-sign
                      concl-atm
                      (fcons-term* 'not concl-atm))))
      (reprettyify hyps concl wrld)))
   (t nil)))

(defun decode-tau-signature-rules1 (flg fn sr-lst wrld)
  (cond ((endp sr-lst) nil)
        (t (cons (decode-tau-signature-rule flg fn (car sr-lst) wrld)
                 (decode-tau-signature-rules1 flg fn (cdr sr-lst) wrld)))))

(defun decode-tau-signature-rules2 (i fn mv-lst wrld)
  (cond ((endp mv-lst) nil)
        (t (append (decode-tau-signature-rules1 i fn (car mv-lst) wrld)
                   (decode-tau-signature-rules2 (+ 1 i) fn
                                                (cdr mv-lst)
                                                wrld)))))

(defun decode-tau-signature-rules (flg fn sr-lst wrld)
  (let ((temp (cond ((null flg)
                     (decode-tau-signature-rules1 nil fn sr-lst wrld))
                    (t (decode-tau-signature-rules2 0 fn sr-lst wrld)))))
    (cond ((null temp) t)
          ((null (cdr temp)) (car temp))
          (t `(and ,@temp)))))

; We compute various counts relating to signature rules:
; - fn-cnt-1: how many functions have form 1 signatures ONLY
; - fn-cnt-2: how many functions have form 2 signatures ONLY
; - fn-cnt-1-and-2: how many functions have BOTH form 1 and 2 signatures
; - multi-sig-cnt-1: how many functions have more than 1 form 1 signature
; - multi-sig-cnt-2: how many functions have more than 1 form 2 signature
;    for some slot
; - multi-sig-cnt-alist: for each fn with with more than one signature
;    (of either form)

(defun tau-get-all-sig-fns (wrld fns-seen)
  (cond ((endp wrld) fns-seen)
        ((and (or (eq (cadr (car wrld)) 'signature-rules-form-1)
                  (eq (cadr (car wrld)) 'signature-rules-form-2))
              (not (member-eq (car (car wrld)) fns-seen)))
         (tau-get-all-sig-fns (cdr wrld) (cons (car (car wrld)) fns-seen)))
        (t (tau-get-all-sig-fns (cdr wrld) fns-seen))))

(defun some-slot-has-multiple-tau-sigs (slots)
  (cond ((endp slots) nil)
        ((> (length (car slots)) 1) t)
        (t (some-slot-has-multiple-tau-sigs (cdr slots)))))

(defun count-tau-sigs-by-slot (slots)
  (cond ((endp slots) nil)
        (t (cons (length (car slots))
                 (count-tau-sigs-by-slot (cdr slots))))))

(defun collect-rules-with-dependent-hyps (fn i rules wrld ans)
  (cond ((endp rules) ans)
        (t (collect-rules-with-dependent-hyps
            fn i (cdr rules) wrld
            (if (access signature-rule (car rules) :dependent-hyps)
                (cons (decode-tau-signature-rule i fn (car rules) wrld)
                      ans)
                ans)))))

(defun collect-rules-with-dependent-hyps-across-mv (fn i mv-lst wrld ans)
  (cond ((endp mv-lst) ans)
        (t (collect-rules-with-dependent-hyps-across-mv
            fn (+ i 1) (cdr mv-lst) wrld
            (collect-rules-with-dependent-hyps fn i (car mv-lst) wrld ans)))))

(defun tau-get-stats-on-signatures1 (fn wrld
                                        fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
                                        multi-sig-cnt-1 multi-sig-cnt-2
                                        multi-sig-cnt-alist
                                        rules-with-dependent-hyps)
  (let ((sigs1 (getpropc fn 'signature-rules-form-1 nil wrld))
        (sigs2 (getpropc fn 'signature-rules-form-2 nil wrld)))
    (mv-let
     (fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2)
     (cond
      ((and sigs1 sigs2)
       (mv fn-cnt-1 fn-cnt-2 (+ 1 fn-cnt-1-and-2)))
      (sigs1
       (mv (+ 1 fn-cnt-1) fn-cnt-2 fn-cnt-1-and-2))
      (t
       (mv fn-cnt-1 (+ 1 fn-cnt-2) fn-cnt-1-and-2)))
     (let* ((multi-sig-cnt-1
             (if (> (length sigs1) 1)
                 (+ 1 multi-sig-cnt-1)
                 multi-sig-cnt-1))
            (multi-sig-cnt-2
             (if (some-slot-has-multiple-tau-sigs sigs2)
                 (+ 1 multi-sig-cnt-2)
                 multi-sig-cnt-2))
            (multi-sig-cnt-alist
             (cond
              ((or (> (length sigs1) 1)
                   (some-slot-has-multiple-tau-sigs sigs2))
               (cons `(,fn ,(length sigs1)
                           (mv ,@(count-tau-sigs-by-slot sigs2)))
                     multi-sig-cnt-alist))
              (t multi-sig-cnt-alist)))
            (rules-with-dependent-hyps
             (collect-rules-with-dependent-hyps-across-mv
              fn 0 sigs2 wrld
              (collect-rules-with-dependent-hyps
               fn nil sigs1 wrld rules-with-dependent-hyps))))
       (mv fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
           multi-sig-cnt-1 multi-sig-cnt-2 multi-sig-cnt-alist
           rules-with-dependent-hyps)))))

(defun tau-get-stats-on-signatures (fns wrld
                                        fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
                                        multi-sig-cnt-1 multi-sig-cnt-2
                                        multi-sig-cnt-alist
                                        rules-with-dependent-hyps)
  (cond ((endp fns)
         `((:fns-with-signatures (:form-1-only ,fn-cnt-1)
                                 (:form-2-only ,fn-cnt-2)
                                 (:both-forms  ,fn-cnt-1-and-2))
           (:fns-with-multiple-sigs (:form-1 ,multi-sig-cnt-1)
                                    (:form-2 ,multi-sig-cnt-2))
           (:fn-with-multiple-sigs-details
            (fn form-1-cnt (mv slot-1-cnt dot-dot-dot slot-k-cnt))
            ,@multi-sig-cnt-alist)
           (:rules-with-dependent-hyps ,(length rules-with-dependent-hyps)
                                       ,(revappend rules-with-dependent-hyps nil))))
        (t (mv-let
            (fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
                      multi-sig-cnt-1 multi-sig-cnt-2 multi-sig-cnt-alist
                      rules-with-dependent-hyps)
            (tau-get-stats-on-signatures1 (car fns) wrld
                                          fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
                                          multi-sig-cnt-1 multi-sig-cnt-2
                                          multi-sig-cnt-alist
                                          rules-with-dependent-hyps)
            (tau-get-stats-on-signatures (cdr fns) wrld
                                         fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
                                         multi-sig-cnt-1 multi-sig-cnt-2
                                         multi-sig-cnt-alist
                                         rules-with-dependent-hyps)))))

(defun collect-tau-big-switches (wrld ans)
  (cond ((endp wrld) ans)
        ((eq (cadr (car wrld)) 'big-switch)
         (collect-tau-big-switches (cdr wrld)
                                   (add-to-set-eq (car (car wrld)) ans)))
        (t (collect-tau-big-switches (cdr wrld) ans))))

(defun tau-sum-lst (x)
; This function should be called sum-lst, but we put a ``tau'' in it
; just to allow a function named ``sum-lst'' to be defined by the user.
  (cond ((endp x) 0)
        (t (+ (car x) (tau-sum-lst (cdr x))))))

(defun tau-get-stats (wrld)
  (let* ((preds (tau-get-all-preds wrld nil))
         (fns (tau-get-all-sig-fns wrld nil))
         (implicant-sizes
          (tau-get-stats-on-implicant-sizes preds wrld nil
                                            `((:MAX nil nil 0)
                                              (:NEXT nil nil 0))))
         (implicants (car implicant-sizes)) ; really this is list of sizes
         (sum-size (tau-sum-lst implicants)))
    `((:preds ,(length preds))
      (:implicant-sizes ,implicant-sizes)
      (:average-implicant-size
       ,(floor sum-size (length implicants)) --
       ,(ceiling sum-size (length implicants)))
      (:median-implicant-size
       ,(if (evenp (length implicants))
            `(,(nth (- (floor (length implicants) 2) 1) implicants)
              --
              ,(nth (floor (length implicants) 2) implicants))
            (nth (floor (length implicants) 2) implicants)))
      (:conjunctive-rules
       ,(length (getpropc 'tau-conjunctive-rules 'global-value
                         nil wrld)))
      ,@(tau-get-stats-on-signatures fns wrld 0 0 0 0 0 nil nil)
      (:big-switches ,(collect-tau-big-switches wrld nil))
      (:mv-nth-synonyms ,(global-val 'tau-mv-nth-synonyms wrld))
      (:tau-runes ,(len (get-tau-runes wrld)))
      (:tau-lost-runes ,(len (global-val 'tau-lost-runes wrld))))))




; If you execute this form you get a self-explanatory printout.

; (tau-get-stats (w state))

; If you define the fns and macros in the comment containing defmacro mktau, you
; can also write:

; (mktau t (not (equal x 23)) (natp x) (integerp x) (not (symbolp x)))

; to get a complete tau, or use a nil in place of the t to get one that just
; codes those recognizers.  Be careful of the need for translation -- ptrans
; defined above is used which is a poor-man's translate.

; If you have a tau, you can print it as an untranslated term with (decode-tau
; tau 'v).  A variety of decoders are provided above, including for a list of
; tau, a tau-alist, a tau signature of either form, a list of signatures of
; either form, and (below) all the information tau knows about a function
; symbol.  See tau-data.

(defmacro tau-status (&key (system 'nil system-p) (auto-mode 'nil auto-mode-p))
  (cond
   (system-p
    (cond
     (auto-mode-p
      `(progn (in-theory (,(if system 'enable 'disable)
                          (:executable-counterpart tau-system)))
              (set-tau-auto-mode ,auto-mode)))
     (t `(in-theory (,(if system 'enable 'disable)
                     (:executable-counterpart tau-system))))))
   (auto-mode-p
    `(set-tau-auto-mode ,auto-mode))
   (t '(er-let* ((amp (table acl2-defaults-table :tau-auto-modep)))
         (value (list
                 (list :system
                       (if (enabled-numep *tau-system-xnume* (ens state))
                           t
                           nil))
                 (list :auto-mode amp)))))))

(defun tau-data-fn (fn wrld)
  (let ((fn (deref-macro-name fn (macro-aliases wrld))))
    (cond
     ((and (symbolp fn)
           (arity fn wrld))
      (let ((tau-pair (getpropc fn 'tau-pair nil wrld))
            (sigs1 (getpropc fn 'signature-rules-form-1 nil wrld))
            (sigs2 (getpropc fn 'signature-rules-form-2 nil wrld))
            (big-switch (getpropc fn 'big-switch nil wrld))
            (mv-nth-synonym (member-eq fn (global-val 'tau-mv-nth-synonyms
                                                      wrld))))
        (cond
         ((or tau-pair sigs1 sigs2 big-switch mv-nth-synonym)
          `(,fn
            (recognizer-index
             ,(car tau-pair))
            (pos-implicants
             ,(decode-tau
               (getpropc fn 'pos-implicants *tau-empty* wrld)
               'v))
            (neg-implicants
             ,(decode-tau
               (getpropc fn 'neg-implicants *tau-empty* wrld)
               'v))
            (signatures
             ,(let ((sigs1 (decode-tau-signature-rules nil fn sigs1 wrld))
                    (sigs2 (decode-tau-signature-rules t fn sigs2 wrld)))
                (if (eq sigs1 t)
                    (if (eq sigs2 t)
                        t
                      sigs2)
                  (if (eq sigs2 t)
                      sigs1
                    `(and ,sigs1 ,sigs2)))))
            (big-switch? ,(if big-switch :yes :no))
            (mv-nth-synonym? ,(if mv-nth-synonym :yes :no))))
         (t nil))))
     (t nil))))

(defmacro tau-data (fn)
  `(tau-data-fn ',fn (w state)))

(defun all-fnnames-world1 (trips logicp wrld ans)

; Logicp should be t if you want to collect :logic mode function symbols,
; nil if you want to collect :program mode functions, and :either if you
; want to collect both.

  (cond ((endp trips) ans)
        ((and (eq (cadr (car trips)) 'formals)
              (if (eq logicp t)
                  (not (eq (symbol-class (car (car trips)) wrld) :program))
                  (if logicp t
                      (eq (symbol-class (car (car trips)) wrld) :program)))
              (not (member-eq (car (car trips)) ans)))
         (all-fnnames-world1 (cdr trips) logicp wrld
                             (cons (car (car trips)) ans)))
        (t (all-fnnames-world1 (cdr trips) logicp wrld ans))))

(defun all-fnnames-world (mode wrld)

; Collect all function symbols of the given mode in world.  Mode may be :logic,
; :program, or :either.

  (all-fnnames-world1 wrld
                      (if (eq mode :logic)
                          t
                          (if (eq mode :program) nil :either))
                      wrld nil))

(defun tau-data-fns (fns wrld ans)
  (cond ((endp fns) ans)
        (t (tau-data-fns (cdr fns)
                         wrld
                         (let ((temp (tau-data-fn (car fns) wrld)))
                           (if temp
                               (cons temp ans)
                               ans))))))

(defun tau-database (wrld)
  (tau-data-fns
   (merge-sort-lexorder (all-fnnames-world :logic wrld))
   wrld
   `((tau-next-index ,(global-val 'tau-next-index wrld))
     (tau-conjunctive-rules
      ,(decode-tau-conjunctive-rules
        (merge-sort-lexorder (global-val 'tau-conjunctive-rules wrld))))
     (tau-mv-nth-synonyms ,(merge-sort-lexorder
                            (global-val 'tau-mv-nth-synonyms wrld)))
     (tau-runes ,(get-tau-runes wrld))
     (tau-lost-runes ,(merge-sort-lexorder
                       (global-val 'tau-lost-runes wrld))))))

; -----------------------------------------------------------------
; Regenerating the Tau Database

; Because tau does not track which runes it is using, disabling a rune has no
; effect on the inferences tau makes.  However, we do provide the ability to
; recompute the tau database with respect to a given enabled structure.  This
; is an event command and we cannot actually define the entire event command
; until we have more infrastructure in place.  (The regenerate-tau-database
; event is defined in other-events.lisp.)  But we can do the hard work, which
; is mapping over the world and re-visiting every event for its tau rules.

; The regeneration facility first clears the tau global variables.  Then it
; revisits every tuple in the world, in chronological order, and calls the
; appropriate tau-visit function on each relevant tuple.  The only relevant
; tuples are those that declare new function symbols and those that mark event
; boundaries, i.e., triples of the forms (fn FORMALS . (v1 ... vn)) and
; (EVENT-LANDMARK GLOBAL-VALUE . ev-tuple) We look out for the
; exit-boot-strap-mode event-landmark because there we switch the boot-strap
; setting of auto-modep to the user-specified setting.  Visiting the tuples in
; chronological order is hard to do efficiently because of the length of the
; world (about 87,000 at the moment), so we just reverse the world, collecting
; only the tuples of interest.

(defun initialize-tau-globals (wrld)

; Keep this in sync with the initial tau global values in
; primordial-world-globals, which at the moment consists of

; (tau-runes nil)
; (tau-next-index 0)            ; <--- We do not re-initialize this one!
; (tau-conjunctive-rules nil)
; (tau-mv-nth-synonyms nil)
; (tau-lost-runes nil)

  (putprop-if-different
   'tau-runes 'global-value nil
;  (putprop-if-different
;   'tau-next-index 'global-value 0
    (putprop-if-different
     'tau-conjunctive-rules 'global-value nil
     (putprop-if-different
      'tau-mv-nth-synonyms 'global-value nil
      (putprop-if-different
       'tau-lost-runes 'global-value nil
       wrld)))
;             )
    ))

; Tau Todo:  Investigate how redefinition screws up this collection...

(defun collect-tau-relevant-triples (wrld ans)
  (cond ((endp wrld) ans)
        ((or (and (eq (cadr (car wrld)) 'FORMALS)
                  (not (eq (cddr (car wrld)) *acl2-property-unbound*)))
             (and (eq (car (car wrld)) 'EVENT-LANDMARK)
                  (eq (cadr (car wrld)) 'GLOBAL-VALUE)))
         (collect-tau-relevant-triples (cdr wrld)
                                      (cons (car wrld) ans)))
        (t (collect-tau-relevant-triples (cdr wrld) ans))))

; To define the regeneration event we must have some additional event-level
; infrastructure (e.g., how to interpret the event tuples stored as
; EVENT-LANDMARKs, not to mention ctx computation, install-event, etc.  So we
; delay the rest of the regeneration event until other-events.lisp.
