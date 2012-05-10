; ACL2 Version 4.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

(in-package "ACL2")

; In this file we define the Tau system, a collection of data strutures and
; algorithms for reasoning quickly about monadic predicates.  However, we need
; certain basic facilities from the rest of ACL2's sources and we have put them
; all in the following ``prelude.''  See the Essay on the Tau System below for
; a discussion of the tau design.

; Prelude:  General-Purpose Functions Having Nothing Specific to do with Tau

(defun lexorder-member (x lst)

; Lst is lexordered ascending.  We determine whether x is a member of lst.

  (cond ((endp lst) nil)
        ((lexorder (car lst) x)
         (or (equal x (car lst))
             (lexorder-member x (cdr lst))))
        (t nil)))

(defun lexorder-subsetp (lst1 lst2)

; Provided both arguments are duplicate-free lexorded ascending we determine
; whether (subsetp-equal lst1 lst2).

  (cond ((endp lst1) t)
        ((endp lst2) nil)
        ((lexorder (car lst1) (car lst2))
         (or (equal (car lst1) (car lst2))
             (lexorder-subsetp (cdr lst1) (cdr lst2))))
        (t (lexorder-subsetp lst1 (cdr lst2)))))

; We need to be able to build neg-evgs and pos- and neg-pairs satisfying the
; basic constraints of being duplicate-free and appropriately ordered.

(defun insert-lexorder (x lst)

; Lst is lexordered, ascending.  We insert x into lst or else return t if it is
; already there.

  (cond ((endp lst) (cons x nil))
        ((lexorder (car lst) x)
         (if (equal (car lst) x)
             t
             (let ((rest (insert-lexorder x (cdr lst))))
               (if (eq rest t)
                   t
                   (cons (car lst) rest)))))
        (t (cons x lst))))

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
  (cond ((null x) nil)
        (t (cons (caddar x) (strip-caddrs (cdr x))))))

; In forming rules from terms we often strip out individual branches of the term, e.g.,
; (implies (and h1 h2) (and c1 (implies h3 c2))) is treated as though it were
; (and (implies (and h1 h2) c1) (implies (and h1 h2 h3) c2)), except after distributing
; the IMPLIES over the concluding ANDs, we do not form a term but just
; traffic in list of pairs (((h1 h2) . c1) ((h1 h2 h3) . c2)).  This is called
; ``unprettyifying.''

(defun unprettyify/add-hyps-to-pairs (hyps lst)

; Each element of lst is a pair of the form (hypsi . concli), where hypsi
; is a list of terms.  We append hyps to hypsi in each pair.

  (cond ((null lst) nil)
        (t (cons (cons (append hyps (caar lst)) (cdar lst))
                 (unprettyify/add-hyps-to-pairs hyps (cdr lst))))))

(defun flatten-ands-in-lit (term)
  (case-match term
              (('if t1 t2 t3)
               (cond ((equal t2 *nil*)
                      (append (flatten-ands-in-lit (dumb-negate-lit t1))
                              (flatten-ands-in-lit t3)))
                     ((equal t3 *nil*)
                      (append (flatten-ands-in-lit t1)
                              (flatten-ands-in-lit t2)))
                     (t (list term))))
              (& (cond ((equal term *t*) nil)
                       (t (list term))))))

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

; Rockwell Addition:  A major change is the removal of THEs from
; many terms.

; Essay on the Removal of Guard Holders

; We now develop the code to remove THEs from a term.  Suppose the
; user types (THE type expr), type is translated (using
; translate-declaration-to-guard) into a predicate in one variable.
; The variable is always VAR.  Denote this predicate as (guard VAR).
; Then the entire (THE type expr) is translated into ((LAMBDA (VAR)
; (IF (guard VAR) VAR (THE-ERROR 'type VAR))) expr).  The-error is
; defined to have a guard of nil and so when we generate guards for
; the translation above we generate the obligation to prove (guard
; expr).  Futhermore, the definition of the-error is such that
; executing it in the *1* function tests (guard expr) at runtime and
; signals an error.

; But logically speaking, the definition of (THE-ERROR x y) is (CDR
; (CONS x y)).  The silly expression is just to keep x from being
; irrelevant.  Thus, (THE-ERROR x y) is identically y.  Hence,
;   (THE type expr)
; = ((LAMBDA (VAR) (IF (guard VAR) VAR (THE-ERROR 'type VAR))) expr)
; = ((LAMBDA (VAR) (IF (guard VAR) VAR VAR)) expr)
; = ((LAMBDA (VAR) VAR) expr)
; = expr.
; Observe that this is essentially just the expansion of certain
; non-rec functions (namely, THE-ERROR, if one thinks of it as defined
; to be y rather than (cdr (cons x y)), and the lambda application)
; and IF-normalization.

; We belabor this obvious point because until Version_2.5, we kept the
; THEs in bodies, which injected them into the theorem proving
; process.  We now remove them from the stored BODY property.  It is
; not obvious that this is a benign change; it might have had
; unintended side-affects on other processing, e.g., guard generation.
; But the BODY property has long been normalized with certain non-rec
; fns expanded, and so we argue that the removal of THE could have
; been accomplished by the processing we were already doing.

; But there is another place we wish to remove such ``guard holders.''
; We want the guard clauses we generate not to have these tests in
; them.  The terms we explore to generate the guards WILL have these
; tests in them.  But the output we produce will not, courtesy of the
; following code which is used to strip the guard holders out of a
; term.

; Starting with Version_2.8 the ``guard holders'' code appears elsewhere,
; because remove-guard-holders needs to be defined before it is called by
; constraint-info.

(mutual-recursion

(defun remove-guard-holders1 (term)

; WARNING.  Remove-guard-holders is used in constraint-info,
; induction-machine-for-fn1, and termination-machine, so (remove-guard-holders1
; term) needs to be provably equal to term, for every term, in the ground-zero
; theory.  In fact, because of the use in constraint-info, it needs to be the
; case that for any axiomatic event e, (remove-guard-holders e) can be
; substituted for e without changing the logical power of the set of axioms.
; Actually, we want to view the logical axiom added by e as though
; remove-guard-holders had been applied to it, and hence RETURN-LAST and
; MV-LIST appear in *non-instantiable-primitives*.

  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((or (eq (ffn-symb term) 'RETURN-LAST)
        (eq (ffn-symb term) 'MV-LIST))

; Recall that PROG2$ (hence, RETURN-LAST) is used to attach the dcl-guardian of
; a LET to the body of the LET for guard generation purposes.  A typical call
; of PROG2$ is (PROG2$ dcl-guardian body), where dcl-guardian has a lot of IFs
; in it.  Rather than distribute them over PROG2$ and then when we finally get
; to the bottom with things like (prog2$ (illegal ...) body) and (prog2$ T
; body), we just open up the prog2$ early, throwing away the dcl-guardian.

    (remove-guard-holders1 (car (last (fargs term)))))
   ((flambdap (ffn-symb term))
    (case-match
     term
     ((('LAMBDA ('VAR) ('IF & 'VAR ('THE-ERROR & 'VAR)))
       val)
      (remove-guard-holders1 val))
     ((('LAMBDA formals ('RETURN-LAST ''MBE1-RAW & logic))
       . args) ; pattern for equality variants
      (subcor-var formals
                  (remove-guard-holders1-lst args)
                  (remove-guard-holders1 logic)))
     (&
      (mcons-term (make-lambda (lambda-formals (ffn-symb term))
                               (remove-guard-holders1
                                (lambda-body (ffn-symb term))))
                  (remove-guard-holders1-lst (fargs term))))))
   (t (mcons-term (ffn-symb term)
                  (remove-guard-holders1-lst (fargs term))))))

(defun remove-guard-holders1-lst (lst)
  (cond ((null lst) nil)
        (t (cons (remove-guard-holders1 (car lst))
                 (remove-guard-holders1-lst (cdr lst)))))))

; We wish to avoid copying the body to remove stuff that we won't find.
; So we have a predicate that mirrors the function above.

(mutual-recursion

(defun contains-guard-holdersp (term)
  (cond
   ((variablep term) nil)
   ((fquotep term) nil)
   ((or (eq (ffn-symb term) 'RETURN-LAST)
        (eq (ffn-symb term) 'MV-LIST))
    t)
   ((flambdap (ffn-symb term))
    (case-match term
                ((('LAMBDA ('VAR) ('IF & 'VAR ('THE-ERROR & 'VAR)))
                  &)
                 t)
                ((('LAMBDA & ('RETURN-LAST ''MBE1-RAW & &))
                  . &) ; pattern for equality variants
                 t)
                (&
                 (or (contains-guard-holdersp
                      (lambda-body (ffn-symb term)))
                     (contains-guard-holdersp-lst (fargs term))))))
   (t (contains-guard-holdersp-lst (fargs term)))))

(defun contains-guard-holdersp-lst (lst)
  (cond ((null lst) nil)
        (t (or (contains-guard-holdersp (car lst))
               (contains-guard-holdersp-lst (cdr lst)))))))
                 
(defun remove-guard-holders (term)

; Return a term equal to term, but slightly simplified.  See also the warning
; in remove-guard-holders1.

  (cond ((contains-guard-holdersp term)
         (remove-guard-holders1 term))
        (t term)))

(defun remove-guard-holders-lst (lst)

; Return a list of terms element-wise equal to lst, but slightly simplified.

  (cond ((contains-guard-holdersp-lst lst)
         (remove-guard-holders1-lst lst))
        (t lst)))

(defun contains-guard-holdersp-lst-lst (lst)
  (cond ((null lst) nil)
        (t (or (contains-guard-holdersp-lst (car lst))
               (contains-guard-holdersp-lst-lst (cdr lst))))))

(defun remove-guard-holders1-lst-lst (lst)
  (cond ((null lst) nil)
        (t (cons (remove-guard-holders1-lst (car lst))
                 (remove-guard-holders1-lst-lst (cdr lst))))))

(defun remove-guard-holders-lst-lst (x)

; Return a list of clauses element-wise equal to lst, but slightly simplified.

  (cond ((contains-guard-holdersp-lst-lst x)
         (remove-guard-holders1-lst-lst x))
        (t x)))

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

;; RAG - I added a rule for realp, non-zero real, non-negative real,
;; non-positive real, positive real, negative real, irrational,
;; negative irrational, positive irrational, and complex.

(defconst *initial-type-set-inverter-rules*
  (list (make type-set-inverter-rule                 ;;; 11 (14) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-complement *ts-cons*)
              :terms '((atom x)))
        (make type-set-inverter-rule                 ;;; 6 (9) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-acl2-number*
              :terms '((acl2-numberp x)))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (7) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-real*
              :terms '((realp x)))
        (make type-set-inverter-rule                 ;;; 5 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-rational*
              :terms '((rationalp x)))
        (make type-set-inverter-rule                 ;;; 5 (8) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-intersection *ts-acl2-number* (ts-complement *ts-zero*))
              :terms '((acl2-numberp x) (not (equal x '0))))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (6) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-intersection *ts-real* (ts-complement *ts-zero*))
              :terms '((realp x) (not (equal x '0))))
        (make type-set-inverter-rule                 ;;; 4 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-intersection *ts-rational* (ts-complement *ts-zero*))
              :terms '((rationalp x) (not (equal x '0))))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (4) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-union *ts-positive-real* *ts-zero*)
              :terms '((realp x) (not (< x '0))))
        (make type-set-inverter-rule                 ;;; 3 bits
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
        (make type-set-inverter-rule                 ;;; 3 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-integer*
              :terms'((integerp x)))                
        (make type-set-inverter-rule                 ;;; 2 bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts (ts-intersection *ts-integer* (ts-complement *ts-zero*))
              :terms '((integerp x) (not (equal x '0))))
        #+:non-standard-analysis
        (make type-set-inverter-rule                 ;;; _ (3) bits
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*
              :ts *ts-positive-real*
              :terms'((realp x) (< '0 x)))
        (make type-set-inverter-rule                 ;;; 2 bits
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
        (make type-set-inverter-rule                 ;;; 2 bits
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
        (make type-set-inverter-rule                 ;;; 1 bit
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

; Here is one of the most basic functions in the theorem prover.  It is
; surprising we got so far into the sources without defining it!  

; (Students of our code should study this elementary function just to see how
; we recur through terms.  The function instantiates a variable, i.e.,
; (subst-var new old form w) substitutes the term new for the variable old in
; the term form.  W is the property list world and is used merely to keep
; certain terms (constants) in a canonical form.  For example, (subst-var '(car
; a) 'x '(foo x y)) = '(foo (car a) y).)

(mutual-recursion

(defun subst-var (new old form)
  (declare (xargs :guard (and (pseudo-termp new)
                              (variablep old)
                              (pseudo-termp form))))
  (cond ((variablep form)
         (cond ((eq form old) new)
               (t form)))
        ((fquotep form) form)
        (t (cons-term (ffn-symb form)
                      (subst-var-lst new old (fargs form))))))

(defun subst-var-lst (new old l)
  (declare (xargs :guard (and (pseudo-termp new)
                              (variablep old)
                              (pseudo-term-listp l))))
  (cond ((endp l) nil)
        (t (cons (subst-var new old (car l))
                 (subst-var-lst new old (cdr l))))))

)

(defun convert-type-set-to-term (x ts ens w ttree)

; Given a term x and a type set ts we generate a term that expresses the
; assertion that "x has type set ts".  E.g., if x is the term (FN X Y) and ts
; is *ts-rational* then our output will be (RATIONALP (FN X Y)).  We return (mv
; term ttree), where term is the term and ttree contains the 'lemmas used.  We
; do not use disabled type-set-inverters.

; Note:  It would be a major change to make this function force assumptions.
; If the returned ttree contains 'assumption tags then the primary use of
; this function, namely the expression of type-alists in clausal form so that
; assumptions can be attacked as clauses, becomes problematic.  Don't glibbly
; generalize type-set-inverter rules to force assumptions.

  (cond ((ts= ts *ts-unknown*) (mv *t* ttree))

; The following case is probably fine, but we commented it out for Version_3.5
; because of a soundness issue that no longer exists (because we don't create
; type-prescription rules for subversive functions; see
; putprop-type-prescription-lst).  We will leave it commented out (we are soon
; releasing Version_4.0 as of this writing), because it seems to be an
; unimportant case that hasn't been missed.

;       ((and (ts= ts *ts-t*)
;             (ts-booleanp x ens w))
;        (mv x ttree))
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

(defun all-runes-in-lmi (lmi wrld ans)

; When we collect all the runes "in" lmi we actually expand symbolic lmis,
; e.g., ASSOC-OF-APP, to the list of all runes based on that symbol.

  (cond ((symbolp lmi)
         (union-equal (strip-cdrs (getprop lmi 'runic-mapping-pairs nil
                                           'current-acl2-world wrld))
                      ans))
        ((or (eq (car lmi) :instance)
             (eq (car lmi) :functional-instance))
         (all-runes-in-lmi (cadr lmi) wrld ans))
        ((eq (car lmi) :theorem) ans)
        (t (add-to-set-equal lmi ans))))

(defun all-runes-in-lmi-lst (lmi-lst wrld ans)
  (cond ((null lmi-lst) ans)
        (t (all-runes-in-lmi-lst (cdr lmi-lst) wrld
                                 (all-runes-in-lmi (car lmi-lst) wrld ans)))))

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

(defun all-runes-in-ttree (ttree ans)

; Ttree is any ttree produced by this system.  We sweep it collecting into ans
; every rune in it.  

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
; Shape: term
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
; Shape: (clause-processor-hint . clauses)
            ans)
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
; system.  Subsequent essays and comments go into much more detail.

; The Tau system is a collection of data structures and algorithms for
; reasoning quickly about the things we know to be true about a term.  It was
; motivated by our frustration over the time it took ACL2 to do elementary
; guard-like proofs -- ``proofs'' that could be almost instantaneous in a
; strongly typed language.  The ``tau'' of a term x, as used here, is a
; representation of a set of monadic predicates known to hold about x.  For
; example, we might say ``suppose the tau of x is {NATP, INTEGERP,
; RATIONALP}.''  Properly speaking, we should say ``a tau of x'' since we have
; no way of guaranteeing that there is only one uniquely identified or
; preferred set of predicates.  But generally speaking we try to deal with the
; largest tau we know and when we say ``the tau of x'' we really just mean the
; set that we know about x.

; ``Tau'' might stand for ``Types Are Unnecessary'' and if it did the name
; would be ironic because this whole idea is a tribute to type checking.  The
; truth is that ``tau'' doesn't stand for anything!  When we designed this
; system we needed a name for the meta objects denoting the set of monadic
; predicates (``recognizers'') that we know to hold about a term in a given
; context.

; We were tempted to call such a set a ``type'' of the term but felt that was
; inappropriate because the literature on types is so extensive and we have no
; interest in defending the proposition that our objects are ``types''.  We
; really don't think of them as anythin more than sets of recognizers known
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

; Basic Idea: We convert certain theorems (and defuns) into a data base
; designed explicitly to allow us to reason about monadic Boolean functions
; (predicates) and function signatures expressed in terms of them.  Several
; forms of theorems are of interest.

; Boolean:
; (booleanp (f v))

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

; where the predicate symbols above may be optionally negated and may be
; equalities (or any of the standard variants of EQUAL) against constants,
; e.g., (p v) might be (NOT (SYMBOLP v)), (EQUAL v 'LOAD), or (NOT (= v
; 123)).

; The shape of the data base is discussed in Essay on the Tau Data Base.

; It is possible to turn the tau reasoning engine on or off, by toggling the
; enabled status of the rune for TAU-SYSTEM.

; Our design allows for theorems to enter the tau data base in either of two
; ways, explicitly (because they have rule-classe :tau-system) or implicitly
; (because they are of the right syntactic shape).  Non-:tau-system theorems
; are swept up into the data base implicitly only when the tau system is in
; ``automatic mode.''

; The two modes just mentioned -- whether tau reasoning is used in proofs
; and whether the tau data base is extended implicitly -- are independent.

; The tau system does not track the rules it uses.  This design decision was
; motivated by the desire to make tau reasoning fast.  The tau data base does
; not record which tau facts come from which theorems or runes.  It is
; impossible to prevent tau from using a fact in the data base unless you
; disable TAU-SYSTEM altogether.  However, there is a facility for regenerating
; the tau data base with respect to a given enabled structure.

; Thus, the tau data base may be built incrementally as each event is processed
; or may be built in one fell swoop.  In the early implementations of the tau
; system the various modes and features were scattered all over our source
; code.  For example, we found ourselves possibly extending the tau data base:
; (a) when :tau-system rules are added by add-x-rule
; (b) when any non-:tau-system rule is added (e.g., by add-rewrite-rule)
; (c) when a defun or constraint added a Boolean type-prescription rule to
;     a monadic function
; (d) when an explicit regenerate event is triggered.

; This became too complicated.  We have therefore moved all the tau data base
; extension code into this file and invoke it only two places: in install-event
; and in the regeneration event (which mimics the sequential invocation on
; successive events in the world).

; One odd aspect of this implementation is that add-x-rule, which ``ought'' to
; know how to add every kind of rule class, does NOT add :tau-system rules.
; Instead, it is just a quiet no-op on :tau-system rules and those rules are
; handled by the centralized tau facility developed here.  To do otherwise
; would mean that :tau-system rules must be added both by add-x-rule and by
; regeneration of the tau data base.

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
; regenerating the tau data base under an ens in which the Boolean nature of p
; is disabled.  Then p-implies-q is no longer a legal :tau-system rule even
; though it was legal when checked.  Had p-implies-q just been a :rewrite rule,
; say, and swept into the tau data base by auto mode, it would make sense to
; quietly ignore this situation (and not add a tau rule).  But if p-implies-q
; is an explicit :tau-system rule it seems glib to ignore it in the
; reconstruction of the data base but harsh to cause a hard error because of
; the disabled status of a :type-prescription rule.  So instead, we collect a
; list of all the explicit :tau-system rules excluded by the user's chosen ens
; and report it at the end of the regeneration process.  We call these ``lost
; tau rules.''

; The tau system keeps track of all the monadic Boolean functions known to be
; true of certain terms.

; Underlying Premise: No function symbol is defined or constrained to be
; constantly T or constantly NIL, and no function symbol is defined or
; constrained to be equivalent to (EQUAL v 'evg) or (NOT (EQUAL v 'evg)).
; Thus, we don't expect to handle functions like:

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

; One implication of the Underlying Premise is that we will never see (or in
; any case, take no note of) theorems of the form (fn x) --> (equal x 'evg),
; because such a theorem implies that fn violates the premise.

; (encapsulate ((fn (x) t))
;              (local (defun fn (x) (equal x '23)))
;              (defthm fn-constraint (and (booleanp (fn x))
;                                        (implies (fn x) (equal x '23)))
;                :rule-classes nil))
; (thm (or (equal (fn x) nil)
;          (equal (fn x) (equal x '23)))
;      :hints (("Goal" :use fn-constraint)))

; Here we use the name ``recognizer'' loosely to refer to virtually any monadic
; Boolean function in ACL2.

; We will assign each monadic Boolean predicate a unique natural number called
; its tau index.  The index of each predicate will be stored on its property
; list under the property tau-pair, in a pair containing the index and
; predicate.  Thus, one might find under 'symbolp 'tau-pair the pair (7
; . SYMBOLP).

; We frequently use a sign and a tau-pair to denote a tau predicate.  Our
; convention is that a positive sign is concretely represented by T and a
; negative sign by NIL.  So for example, the sign T and the pair (7 . SYMBOLP)
; are together a concrete representation of the predicate (lambda (x) (SYMBOLP
; x)) and if the sign NIL is used instead we represent (lambda (x) (NOT
; (SYMBOLP x))).  If sign and r are two variable symbols in our code and we
; write, in a comment, sign/r, we mean the predicate indicated.

; So how do we concretely represent the predicate (lambda (x) (NOT (EQUAL x
; 'LOAD)))?  Clearly the sign component is NIL.  The ``pair'' component is
; (LOAD), i.e., the evg in question, enclosed in a singleton list.  If r is
; known to be either a tau-pair or a singleton list containing an evg, then it
; is possible to determine which it is by looking at its cdr.  If (cdr r)
; is nil, it is a singleton evg list; otherwise it is tau-pair, because
; tau-pairs always have a non-NIL function symbol as their cdrs.

; One reason it is convenient to represent ``equality-with-constant'' as a
; singleton evg is that we frequently have to apply predicates to constants
; with ev-fncall-w, which requires that we pass in the list of unquoted
; actuals.  Since our predicates are monadic, we must pass in a singleton list
; containing the evg in question.  Furthermore, since our
; equality-with-constant predicates always descend from translated terms, the
; term representation of the constant is (QUOTE evg) and we just cdr that to
; obtain the singleton evg list to use both as ``tau pair'' and as the actuals
; list.

; The main question is how do we represent sets of predicates?  That is, how do
; we represent a tau?

(defrec tau
  ((pos-evg . neg-evgs) . (pos-pairs . neg-pairs))
  t)

; where
; pos-evg:   nil or a singleton list containing an evg
; neg-evgs:  list of singleton lists of evgs, duplicate-free ordered ascending
; pos-pairs: list of tau-pairs, duplicate-free, ordered descending
; neg-pairs: list of tau-pairs, duplicate-free ordered descending

; Note: The ordering on neg-evgs is descending lexorder.  The ordering on the
; pairs is ascending by tau index of the pairs.  There is no reason for the
; opposite orders except for the pre-existence of certain sort functions.
; There are additional restrictions on these fields.  See below.

; Note: It might be wise to add a 5th slot to tau: :neg-nil.  This would be
; equivalent to having (nil) in :neg-evgs except we'd never delete it as
; subsumed and we wouldn't have to search or eval for it to test whether a tau
; is non-nil.  But unless the tau system is too slow, we won't add this
; optimization.

; It should be obvious what set of recognizers is denoted by a given tau. Each
; singleton evg and tau-pair can be understood as a predicate.  Think of each
; of the 4 components of a tau as a set of predicates (where the set for
; pos-evg is either empty or predicate denoted by the positively signed
; singleton evg).  Each component has a sign, either positive or negative.
; Distribute that sign across the elements of the corresponding sets and union
; the four sets together.

; For example,
 ; (make tau
;        :neg-evgs '((1)(2))
;        :pos-pairs '((55 . rationalp) (44 . integerp) (33 . natp))
;        :neg-pairs '((50 . symbolp) (40 . consp) (30 . booleanp)))

; represents the set:

; {(lambda (x) (not (equal x '1)))
;  (lambda (x) (not (equal x '2)))
;  (lambda (x) (rationalp x))
;  (lambda (x) (integerp x))
;  (lambda (x) (natp x))
;  (lambda (x) (not (symbolp x)))
;  (lambda (x) (not (consp x)))
;  (lambda (x) (not (booleanp x)))}

; That is, if we say x has that tau, then we know x is not 1 or 2 but is a
; rational, an integer, and a natural, and is not a symbol, a consp, or a
; booleanp.

; Note that the meaning of a tau is the CONJUNCTION of its elements.  We
; sometimes write M[tau] to mean the meaning of tau.  You can think of M[tau]
; for the tau above to be:

; (lambda (x)
;   (and (not (equal x '1))
;        (not (equal x '2))
;        (rationalp x)
;        (integerp x)
;        (natp x)
;        (not (symbolp x))
;        (not (consp x))
;        (not (booleanp x))))

; We sometimes informally exhibit a tau as a set in notation like this:

; {/=1, /=2, rationalp, integerp, natp, -symbolp, -consp, -booleanp}

; or

; {nil/1, nil/2, t/rationalp, t/integerp, t/natp, nil/symbolp, nil/consp, nil/booleanp}

; etc.

; Note: This interpretation of sets of recognizers is exactly the opposite of
; type-set!  For example, if we say x has type-set {p q} we mean x either
; satisfies p or satisfies q.  But if that same set is interpreted as a tau, we
; are saying that x satisfies both p and q.  Of course, some tau are
; inconsistent which is why we place additional restrictions (see below) on
; tau.

; Below is a well-formed but empty tau.  It says we don't know anything about
; the term to which it is associated.

(defconst *tau-empty*
  (make tau
        :pos-evg nil
        :neg-evgs nil
        :pos-pairs nil
        :neg-pairs nil))

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
                        :neg-pairs nil))

(defconst *tau-nil* (make tau
                          :pos-evg *nil-singleton-evg-list*
                          :neg-evgs nil
                          :pos-pairs nil
                          :neg-pairs nil))

; Additional Restrictions on Tau Fields:

; Restriction 0: No tau should be ``obviously contradictory''.  Thus,

;  Restriction 0.1:  The intersection of pos-pairs and neg-pairs is empty.

;  Restriction 0.2: When pos-evg is non-nil, no pos-pair evaluates to false on
;  it and no neg-pair evaluates to true on it.

; Restriction 1: If pos-evg is non-nil, neg-evgs must be nil.

; Restriction 2: If pos-evg is non-nil, pos-pairs (and neg-pairs) should be as
; short as possible, i.e., not contain predicates that evaluate to true (false)
; on that evg.  That means when pos-evg is non-nil the only elements in
; pos-pairs and neg-pairs are predicates that cannot be evaluated.

; Restriction 3: Neg-evgs is duplicate-free and ordered ascending by lexorder.
; Pos-pairs and neg-pairs are duplicate-free and ordered by their indices.

; Restriction 4: Neg-evgs should be as short as possible given pos-pairs and
; neg-pairs.  It is illegal to have an evg in :neg-evgs such that some p in
; :pos-pairs evaluates to false on evg or some p in :neg-pairs evaluates to
; true on evg.  For example, if :pos-pairs includes NATP, it is illegal to
; include (the singleton list containing) LOAD in :neg-evgs.  That inequality
; is implied by :pos-evgs.

; It is sometimes convenient to think in terms of the set comprehending the
; meaning of a tau.  S[tau] = {x | (M[tau] x)}.  Thus, S[{NATP}] = the set of
; all naturals.  If tau has :neg-evgs '((-23)(-24)), :pos-pairs '((1
; . integerp)) and :neg-pairs '((0 . NATP)), then S[tau] is the set of all
; non-natural integers other than -23 and -24.

; A tau is ``obviously contradictory'' if (a) there is a non-nil
; intersection between the pos-pairs and neg-pairs, or if (b) pos-evg is a
; singleton evg and either (b1) the predicate of some pos-pair evaluates to nil
; on that evg, or (b2) the predicate of some neg-pair evaluates to t on that
; evg.  If tau is obviously contradictory it is clear that M[tau] is nil.
; However, the converse is not necessarily true.  For example, one might define
; two predicates

; (defun IS-TEMP (x) (equal x 'TEMP))
; (defun IS-NOT-TEMP (x) (not (equal x 'TEMP)))

; and then the meaning of the recogizer set containing IS-TEMP in pos-pairs and
; IS-NOT-TEMP in neg-pairs is nil but the tau is not obviously contradictory.
; Similarly, the meaning of the recognizer set with TEMP in the neg-evgs and
; IS-TEMP in the pos-pairs is nil but is not obviously contradictory.
; Pragmatically, the user should not define predicates as the negations of
; other predicates nor should equality-with-constants be ``hidden'' as
; predicates.  But we do not enforce this and draw no logical conclusions from
; the fact that a tau is NOT obviously contradictory.

; We often return the keyword :contradiction instead of a tau when we have
; detected that tau is obviously contradictory.  That is, if a variable in our
; code is said to be a tau it may be an instance of the tau record class above
; or it may be the symbol :contradiction.  Generally speaking we try to avoid
; even constructing obviously contradictory recognizer sets.

; In order to highlight when :contradiction is being used as a tau, we define
; the following constant.  However, our code assumes the value of this constant
; is a symbol (e.g., we use EQ to test against it).  It is sometimes convenient
; to think of *tau-contradiction* as a recognizer set that contains every
; predicate in both its positive and negative fields.  That's a little
; misleading because the representation of tau do not allow more than one
; :pos-evg, but if it did (e.g., if we had :pos-evgs instead of :pos-evg), the
; canonical *tau-contradiction* contains all the evgs in :pos-evgs and in
; :neg-evgs and has all the recognizers in :pos-pairs and in :neg-pairs.

(defconst *tau-contradiction* :contradiction)

; Note on contradictionp versus :contradiction: When a tau is being returned we
; signal contradictions by using the bogus ``tau'' *tau-contradiction*.  But
; when we're trafficking in other objects, e.g., the property list world, we
; signal contradictions with the familiar (mv contradictionp ...) convention.
; We do not ever put *tau-contradiction* into objects containing tau data
; structures.

; We will be more precise about the data base later, but Simple rules are used
; to populate the data base, storing all the implications of a given
; recognizer's truth or falsity.  These implications are just tau representing
; the set of all truths that follow.  For example, under NATP we will store the
; tau of all known recognizers implied by t/NATP, as well as all known
; recognizers implied by nil/NATP.  The data base is used to collect known
; truths about a term, by unioning together the sets implied by everything we
; know about the term and then augmenting that set with Conjunctive rules that
; may tell us other things given the particular combination of things we know.

; Conjunctive rules are formulas that tell us that certain combinations of
; recognizers imply other recognizers.  For example, if a Conjunctive rule says
; that p and q imply r, and we have deduced a tau that contains p and contains
; q, then we add r to tau.  It happens that Conjunctive rules are represented
; as sets of recognizers, so we use the same tau datastructure to represent
; them but we do not interpret them with M.  The rule (p & q) --> r is
; represented by the set C = {-p -q -r}.  To use C as a conjunctive rule we ask
; whether some tau, just derived, contains all but one of the elements of C and
; if so we can add the negation of the omitted element of C.

; This brings us to Signature rules of both forms.  Signature rules tells us
; facts about the value of a function given facts about its inputs.  Signature
; rules play the primary role in determining the tau of a term (or of its
; MV-NTH components) given tau assumptions about subterms.

(defrec signature-rule (input-tau-list output-sign output-recog) t)

; :inputs-tau-list  - a list of tau in 1:1 correspondence with formals
; :output-sign     - T (positive) or NIL (negative)
; :output-recog    - (i . pred) | (evg) ; i.e., tau-pair or singleton evg list

; Foreshadowing: We use this same record for both forms of signature rules.
; Under the SIGNATURE-RULES-FORM-1 property of a function symbol fn we will
; find a list of these records, interpreted in the obvious way about calls of
; fn: if the actuals satisfy their respective tau in :inputs-tau-lst, the
; output of fn satisfies the output-sign and output-recog.  Under the
; SIGNATURE-RULES-FORM-2 property of fn we may find a list of length n, each
; element being a list of these records.  The interpretation of the records in
; slot i is that the ith value returned by fn has the indicated tau.  We will
; allow both properties to exist for a function symbol.  That is, one might
; prove that (fn x y) is a true-list of length 3 and might also characterize
; the tau of (mv-nth '0 (fn x y)), (mv-nth '1 (fn x y)), and (mv-nth '2 (fn x
; y)).  When trying to determine the tau of an (mv-nth 'i (fn a b)) expression
; we use only the rules in the ith slot of the form 2 rules for f.  When trying
; to determine the tau of (fn a b) we use only the form 1 rules for fn.

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
  (getprop pred (if sign 'pos-implicants 'neg-implicants)
           nil 'current-acl2-world wrld))

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

; Essay on the Use of ENS by Function Evaluation in the Tau System

; The following function is used throughout the tau system to determine whether
; a recognizer will accept (recognize) a given constant or not.  Note that the
; function is not sensitive to the enabled status of the recognizer fn.  This
; apparently trivial choice has sweeping consequences.  One argument for making
; the tau system respect the current enabled structure is that some authors
; disable :executable-counterparts in their proofs and if tau does not respect
; the disabling, it is behaving contrary to the author's wishes.  This happens
; in /u/moore/work/v4-3a/acl2-sources/books/workshops/1999/embedded/
; Proof-Of-Contribution/Proof-Of-Equiv-From-M-Corr.lisp by P.G. Bertoli and
; P. Traverso (which is a chapter in the ACL2 Case Studies book), where the
; authors execute (in-theory (current-theory 'ground-zero)) near the top of the
; book, thus disabling almost everything.  The hypothesis (rel-prime-moduli
; '(11 13 15 17 19)) is used frequently and proofs break if it is evaluated.
; This particular book is not a very good argument for respecting ens, since
; the script could probably have been developed without this draconian
; disabling.  A better reason to make tau respect ens is that some executable
; counterparts could be so inefficient to compute that the user would prefer
; that they never be run.  But tau would run them and lose.

; On the other side, however, is the issue that carries the day, at least for
; now.  The tau system adopts the convention that if a recognizer in the
; pos-pairs of a tau accepts a given evg, then that evg is not included in the
; neg-evgs.  For example, suppose we want to construct the tau that denotes
; (lambda (v) (and (not (equal v 23)) (foop v))).  But suppose that (foop 23)
; is false.  Then there is no point in including the ``(not (equal v 23))''
; since is implied by the (foop v).  Indeed, we'd represent this tau as the set
; {foop}.  Suppose that tau were stored as the positive implicants of some
; recognizer in the data base.  Now imagine the user disables the
; executable-counterpart of foop.  Are we to recompute the normal form of all
; the stored taus?  We just can't bear the thought!

; So what does the user do if he has a function that just should not be
; evaluated on some constant?  The only choice at the moment is to
; disable the whole tau-system.

(defun ev-fncall-w-tau-recog (fn evg-lst wrld)

; Fn is a monadic Boolean function symbol and evg-lst is a singleton list
; containing an evg.  We apply fn to evg-lst.  If fn is unevaluable, we look
; for a stored value in wrld (from proved theorems about fn).  We return T,
; NIL, or :UNEVALUABLE.  Since fn is Boolean, this is unambiguous.

; Note:  If you think about adding ens to this function, read the essay above
; on the Use of ENS by Function Evaluation in the Tau System.

  (mv-let (erp val)
          (ev-fncall-w fn evg-lst wrld nil nil t t nil)

; The arguments to ev-fncall-w above, after wrld, are safe-mode (= nil), gc-off
; (= t), hard-error-returns-nilp (= t), and aok (= nil).  These are the same
; arguments used in the call of ev-fncall-w in sublis-var!.

          (cond
           (erp

; Recog is unevaluable on evg.  See if its value is known through proof.

            (let ((temp (assoc-equal (car evg-lst)
                                     (getprop fn 'unevalable-but-known nil
                                              'current-acl2-world wrld))))
              (cond
               (temp (cdr temp))
               (t :UNEVALABLE))))
           (val t)
           (t nil))))

(defun bad-val-or-unknowns (bad-val pairs evg-lst wrld)

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
    (let ((val (ev-fncall-w-tau-recog (cdr (car pairs)) evg-lst wrld)))
      (cond
       ((eq val :UNEVALABLE)
        (let ((rest (bad-val-or-unknowns bad-val (cdr pairs) evg-lst wrld)))
          (cond ((eq rest t) t)
                (t (cons (car pairs) rest)))))
       (bad-val
        (if val
            t
            (bad-val-or-unknowns bad-val (cdr pairs) evg-lst wrld)))
       (t (if val
              (bad-val-or-unknowns bad-val (cdr pairs) evg-lst wrld)
              t)))))))

(defun exists-bad-valp (bad-val pairs evg-lst wrld)

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
    (let ((val (ev-fncall-w-tau-recog (cdr (car pairs)) evg-lst wrld)))
      (cond
       ((eq val :UNEVALABLE)
        (exists-bad-valp bad-val (cdr pairs) evg-lst wrld))
       (bad-val
        (if val
            t
            (exists-bad-valp bad-val (cdr pairs) evg-lst wrld)))
       (t (if val
              (exists-bad-valp bad-val (cdr pairs) evg-lst wrld)
              t)))))))


(defun all-eval-valp (good-val pairs evg-lst wrld)

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
    (let ((val (ev-fncall-w-tau-recog (cdr (car pairs)) evg-lst wrld)))
      (cond
       ((eq val :UNEVALABLE) nil)
       (good-val
        (if val
            (all-eval-valp val (cdr pairs) evg-lst wrld)
            nil))
       (t (if val
              nil
              (all-eval-valp val (cdr pairs) evg-lst wrld))))))))

(defun delete-bad-vals (neg-evgs pos-pairs neg-pairs wrld)

; We copy neg-evgs deleting those that falsify some element of pos-pairs or
; satisfy some element of neg-pairs.  We return (mv changedp result).  Changedp
; is t if the result is different from neg-evgs; else changedp is nil.

  (cond
   ((endp neg-evgs) (mv nil nil))
   (t (mv-let
       (changedp result)
       (delete-bad-vals (cdr neg-evgs) pos-pairs neg-pairs wrld)
       (cond
        ((exists-bad-valp nil pos-pairs (car neg-evgs) wrld)
         (mv t result))
        ((exists-bad-valp t neg-pairs (car neg-evgs) wrld)
         (mv t result))
        ((null changedp)
         (mv nil neg-evgs))
        (t (mv t (cons (car neg-evgs) result))))))))

(defun delete-bad-vals1 (neg-evgs sign tau-pair wrld)

; Despite the name, this function is not a subroutine of delete-bad-vals.
; Instead, it is a minor extension of it, equivalent to

; (delete-bad-vals neg-evgs
;                  (if sign (list tau-pair) nil)
;                  (if sign nil (list tau-pair))
;                  wrld)

; but avoids the consing of (list tau-pair).

; We sweep neg-evgs (a list of singleton lists containing evgs) and delete
; those that are bad in the sense of being redundanct wrt to a particular
; signed recognizer.  We return (mv changedp result).

  (cond ((endp neg-evgs) (mv nil nil))
        (t (let ((val (ev-fncall-w-tau-recog (cdr tau-pair) (car neg-evgs) wrld)))
             (mv-let
              (changedp result)
              (delete-bad-vals1 (cdr neg-evgs) sign tau-pair wrld)
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
; determine whether there is exactly one elemnt of pairs1 not in pairs2.  We
; return t if pairs1 is a subset of pairs2, nil if more than one element of
; pairs1 fails to be pairs2, and the missing tau-pair otherwise.

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
         (if (equal (car (car pairs)) (car pair))
             t
             (let ((rest (insert-tau-pair pair (cdr pairs))))
               (if (eq rest t)
                   t
                   (cons (car pairs) rest)))))
        (t (cons pair pairs))))


(defun reduce-sign/recog (tau sign recog wrld)

; Tau is a tau.  Sign is t or nil indicating positive or negative.
; Recog is either a tau-pair denoting the corresponding predicate or else is a
; singleton list containing an evg.  Note that (cdr recog) is always defined
; and is either a pred (in the case of tau-pairs) or nil (in the case of a
; singleton evg list).  

; We are asking what M[tau] implies about M[sign/recog].  We return T if we
; determine that M[sign/recog] is true under M[tau].  We return NIL if we
; determine that M[sign/recog] is false under M[tau].  Otherwise we return ?.

; For example, tau might be {NATP, EVENP} and sign/recog might be NATP.  If x
; satisfies tau, it satisfies sign/recog.  So we would return T.

; Note in general that if (p x) --> (q x), then {x|(p x)} \subset {x|(q x)}.
; Thus, if this function returns T, then S[tau] \subset S[sign/recog].  If this
; function returns NIL, then that subset relation does not hold.  Otherwise, we
; don't know.

  (cond
   ((eq tau *tau-contradiction*) t)
   ((cdr recog) ; recog is a tau-pair
    (cond
     ((access tau tau :pos-evg) ; tau is X='evg
      (let ((val (ev-fncall-w-tau-recog (cdr recog) (access tau tau :pos-evg)
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
     (t '?)))
   (sign ; sign/recog is a positive equality on the evg in recog.
    (cond
     ((access tau tau :pos-evg)
      (equal recog (access tau tau :pos-evg)))
     ((lexorder-member recog (access tau tau :neg-evgs))
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

     ((exists-bad-valp nil (access tau tau :pos-pairs) recog wrld)
      nil)
     ((exists-bad-valp t (access tau tau :neg-pairs) recog wrld)
      nil)
     (t '?)))
   (t ; sign/recog is a negative equality on the evg in recog
    (cond ((access tau tau :pos-evg)
           (not (equal recog (access tau tau :pos-evg))))
          ((lexorder-member recog (access tau tau :neg-evgs))
           t)
          ((exists-bad-valp nil (access tau tau :pos-pairs) recog wrld)
           t)
          ((exists-bad-valp t (access tau tau :neg-pairs) recog wrld)
           t)
          (t '?)))))

; Consider a term like (fn a).  Suppose tau1 is the recognizer set for a.
; Suppose the signature for fn is fn: tau2 --> tau3.  To fire this rule we will
; need to determine whether S[tau1] \subset S[tau2].

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

; Because of the concrete structure of tau we need only compare
; them component-wise.  For example, if q is among the :neg-pairs of one we
; need to search for it only among the :neg-pairs of the other.  This holds for
; all four components.

(defun every-neg-evg-in-tau-p1 (neg-evgs1 neg-evgs2 pos-pairs2 neg-pairs2 wrld)

; This function is just an efficient way of checking that every element of
; neg-evgs1 is either (a) in neg-evgs2, or (b) subsumed by an element of
; pos-pairs2, or (c) is subsumed by an element of neg-pairs2.  We could do this
; by mapping over neg-evgs1 and just check lexorder-member and the two
; exists-bad-valp on each element.  But that method is quadratic in the lengths
; of the two neg-evgs, since lexorder-member would repeatedly search neg-evgs2.
; Instead, we exploit the fact that both neg-evgs are lexordered ascending.

  (cond ((endp neg-evgs1) t)
        ((endp neg-evgs2)
         (and (or (exists-bad-valp nil pos-pairs2 (car neg-evgs1) wrld)
                  (exists-bad-valp t   neg-pairs2 (car neg-evgs1) wrld))
              (every-neg-evg-in-tau-p1 (cdr neg-evgs1)
                                       nil
                                       pos-pairs2 neg-pairs2 wrld)))
        ((lexorder (car neg-evgs1) (car neg-evgs2))
         (cond ((equal (car neg-evgs1) (car neg-evgs2))
                (every-neg-evg-in-tau-p1 (cdr neg-evgs1)
                                         (cdr neg-evgs2)
                                         pos-pairs2 neg-pairs2 wrld))
               (t (and (or (exists-bad-valp nil pos-pairs2 (car neg-evgs1) wrld)
                           (exists-bad-valp t   neg-pairs2 (car neg-evgs1) wrld))
                       (every-neg-evg-in-tau-p1 (cdr neg-evgs1)
                                                neg-evgs2
                                                pos-pairs2 neg-pairs2 wrld)))))
        (t (every-neg-evg-in-tau-p1 neg-evgs1
                                    (cdr neg-evgs2)
                                    pos-pairs2 neg-pairs2 wrld))))

(defun every-neg-evg-in-tau-p (neg-evgs tau wrld)

; Think of M[neg-evgs] as a conjunction of negative equalities with constants.
; We wish to know whether M[tau] --> M[neg-evgs].  We answer t if so, and nil if
; we do not know.

  (cond
   ((access tau tau :pos-evg)
    (not (lexorder-member (access tau tau :pos-evg) neg-evgs)))
   (t (every-neg-evg-in-tau-p1 neg-evgs
                               (access tau tau :neg-evgs)
                               (access tau tau :pos-pairs)
                               (access tau tau :neg-pairs)
                               wrld))))
        
(defun tau-subsetp (tau1 tau2 wrld)

; We check that every recog in tau1 is in tau2.  If we return T, it means
; that M[tau2] --> M[tau1].  Note the reversal of position. For example
; since
; {integerp} \subset {natp integerp rationalp}
; we know
; M[{natp, integerp, rationalp}} --> M[{integerp}]
; <==>
; (and (natp x) (integerp x) (rationalp x)) --> (integerp x).

; Furthermore, note that {integerp} \subset {'1} because the latter is really
; {'1 natp integerp rationalp ...}.  In particular, if tau2 is a :POS-EVG
; satisfying a given element of tau1, then that element of tau1 is implicitly
; in tau2.

; If we return nil, we simply don't know whether this subset (or implication)
; holds.

; Note that M[*tau-contradiction*] is NIL and M[*tau-empty*] is T.  Hence, we
; know that every tau1 is a subset of *tau-contradiction* and we know that
; *tau-empty* is a subset of every tau2.

  (cond
   ((eq tau2 *tau-contradiction*) t)
   ((eq tau1 *tau-contradiction*) nil)
   ((access tau tau1 :pos-evg)
    (if (access tau tau2 :pos-evg)
        (equal (access tau tau1 :pos-evg)
               (access tau tau2 :pos-evg))
        nil))
   ((access tau tau2 :pos-evg)

; In this case we know that tau1 contains some :neg-evgs, :pos-pairs, and some :neg-pairs,
; while tau2 consists entirely of a :pos-evg.  We need to check that that evg satisfies
; every recognizer in tau2.  To satisfy each element of :neg-evgs of tau2, the evg
; must simply be different from the element.  To satisfy each :pos-pair, the
; evg must satisfy the recognizer in it.  To satisfy each :neg-pair, the evg
; must not satisfy the recognizer ini t.

    (and (not (member-equal (access tau tau2 :pos-evg)
                            (access tau tau1 :neg-evgs)))
         (all-eval-valp t (access tau tau1 :pos-pairs)
                        (access tau tau2 :pos-evg)
                        wrld)
         (all-eval-valp nil (access tau tau1 :neg-pairs)
                        (access tau tau2 :pos-evg)
                        wrld)))
   (t (and (every-neg-evg-in-tau-p (access tau tau1 :neg-evgs)
                                   tau2 wrld)
           (tau-pairs-subsetp (access tau tau1 :pos-pairs)
                              (access tau tau2 :pos-pairs))
           (tau-pairs-subsetp (access tau tau1 :neg-pairs)
                              (access tau tau2 :neg-pairs))))))

(defun ok-to-fire-signature-rulep (formal-tau-lst actual-tau-lst wrld)

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
        ((tau-subsetp (car formal-tau-lst) (car actual-tau-lst) wrld)
         (ok-to-fire-signature-rulep (cdr formal-tau-lst) (cdr actual-tau-lst) wrld))
        (t nil)))

; We define add-to-tau1 which adds sign/recog to tau, and add-recogs-to-tau1
; which adds sign/recog for every recog in a list.  But these functions should
; be called only with due consideration because they don't add the implicants
; of the sign/recog.  For that, see add-to-tau.  Note on usage: We "add" recogs
; to tau and rules to the data base.  We "put" when we update the data base.

(defun add-to-tau1 (sign recog tau wrld)

; Recog is a tau-pair or singleton evg list.  Tau is a tau object or
; *tau-contradiction*.  Furthermore, tau is not obviously contradictory unless
; it is *tau-contradiction*.  We conjoin in sign/recog.  We return (mv changedp
; tau').  We clean up tau as much as possible, e.g., delete pos- or neg-pairs
; evaluable under pos-evg changes and delete negative evgs made redundant by
; pos- or neg-pairs, etc.  The motivation of this cleaning up is to keep tau
; small.

  (cond
   ((eq tau *tau-contradiction*) (mv nil *tau-contradiction*))
   ((cdr recog) ; recog is (i . fn)
    (cond
     ((access tau tau :pos-evg)
    
; tau is a :pos-evg.  Then if sign/fn is true on the evg, we don't change
; anything; if sign/fn is false on the evg, we return *tau-contradiction*; else
; sign/fn is unevaluable and we add fn to :pos-pairs or :neg-pairs.

      (let ((val (ev-fncall-w-tau-recog (cdr recog)
                                        (access tau tau :pos-evg)
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
                (mv nil tau))
               ((tau-pair-member recog
                                 (access tau tau :neg-pairs))
                (mv t *tau-contradiction*))
               (t
                (mv t (change tau tau :pos-pairs new-pos-pairs))))))
           (t
            (let ((new-neg-pairs
                   (insert-tau-pair recog
                                    (access tau tau :neg-pairs))))
              (cond
               ((eq new-neg-pairs t)
                (mv nil tau))
               ((tau-pair-member recog
                                 (access tau tau :pos-pairs))
                (mv t *tau-contradiction*))
               (t
                (mv t (change tau tau :neg-pairs new-neg-pairs))))))))
         ((if val sign (not sign)) ; (iff val sign); same as (eq val sign)?
; recog evals as expected; don't bother to store
          (mv nil tau))
         (t
; recog evals to false; signal contradiction
          (mv t *tau-contradiction*)))))
     ((tau-pair-member recog
                       (if sign
                           (access tau tau :pos-pairs)
                           (access tau tau :neg-pairs)))

; If recog is already in the appropriate pairs list, there is nothing to

      (mv nil tau))
     ((tau-pair-member recog
                       (if sign
                           (access tau tau :neg-pairs)
                           (access tau tau :pos-pairs)))

; If recog is in the other pairs list, we have a contradiction.

      (mv t *tau-contradiction*))
     (t

; Otherwise, it is ok to add recog to the appropriate pairs list.  But it may
; make it possible to delete some of the :neg-evgs in tau.  Suppose one of those
; :neg-evgs asserts that X is not 'ABC.  Suppose that recog asserts that X is
; INTEGERP.  Then we don't need that particular element of :neg-evgs any more.
; Note that we might worry that the assertion of sign/recog makes one of our
; :neg-evgs false, but that would violate the Underlying Premise.  Note that
; every exit below changes the tau, but by testing changedp after deleting bad
; vals we can avoid sometimes needlessly resetting the :neg-evgs field.

      (mv-let
       (changedp new-neg-evgs)
       (delete-bad-vals1 (access tau tau :neg-evgs)
                         sign
                         recog
                         wrld)
       (if sign
           (if changedp
               (mv t
                   (change tau tau
                           :neg-evgs new-neg-evgs
                           :pos-pairs (insert-tau-pair
                                       recog
                                       (access tau tau :pos-pairs))))
               (mv t
                   (change tau tau
                           :pos-pairs (insert-tau-pair
                                       recog
                                       (access tau tau :pos-pairs)))))
           (if changedp
               (mv t
                   (change tau tau
                           :neg-evgs new-neg-evgs
                           :neg-pairs (insert-tau-pair
                                       recog
                                       (access tau tau :neg-pairs))))
               (mv t
                   (change tau tau
                           :neg-pairs (insert-tau-pair
                                       recog
                                       (access tau tau :neg-pairs))))))))))
   (sign

; We are adding a positive evg equality to tau.

    (cond
     ((access tau tau :pos-evg)
      (if (equal recog (access tau tau :pos-evg))
          (mv nil tau)
          (mv t *tau-contradiction*)))
     ((lexorder-member recog (access tau tau :neg-evgs))
      (mv t *tau-contradiction*))
     (t (let ((new-pos-pairs
               (bad-val-or-unknowns nil
                                    (access tau tau :pos-pairs)
                                    recog wrld)))
          (cond
           ((eq new-pos-pairs t)

; There is a pos-pair that evals to nil on this new evg.
            (mv t *tau-contradiction*))
           (t
            (let ((new-neg-pairs
                   (bad-val-or-unknowns t
                                        (access tau tau :neg-pairs)
                                        recog wrld)))
              (cond
               ((eq new-neg-pairs t)
; There is a neg-pair that evals to t on this new evg.
                (mv t *tau-contradiction*))
               (t (mv t
                      (make tau
                            :pos-evg recog
                            :neg-evgs nil
                            :pos-pairs new-pos-pairs
                            :neg-pairs new-neg-pairs)))))))))))
   (t

; We are adding an evg to :neg-evgs.

    (cond
     ((access tau tau :pos-evg)
      (if (equal recog (access tau tau :pos-evg))
          (mv t *tau-contradiction*)
          (mv nil tau)))
     ((lexorder-member recog (access tau tau :neg-evgs))
      (mv nil tau))
     ((exists-bad-valp nil (access tau tau :pos-pairs) recog wrld)
      (mv nil tau))
     ((exists-bad-valp t (access tau tau :neg-pairs) recog wrld)
      (mv nil tau))
     (t (mv t
            (change tau tau
                    :neg-evgs
                    (insert-lexorder recog
                                     (access tau tau :neg-evgs)))))))))

(defun add-recogs-to-tau1 (sign recog-lst tau wrld changedp)

; Recog-lst is a list of recognizers, all of which have the same sign.  We add
; each to tau and return (mv changedp tau'), where tau' might be
; *tau-contradiction*.  Note: In fact, each recog in recog-lst is the same
; ``kind'', either each is a singleton evg list (because recog-lst was the
; :neg-evgs of some recognizer set) or is a tau-pair (from a :pos-pairs or
; :neg-pairs).  But we don't exploit this uniformity.

  (cond ((endp recog-lst) (mv changedp tau))
        (t (mv-let (changedp1 tau)
                   (add-to-tau1 sign (car recog-lst) tau wrld)
                   (cond ((eq tau *tau-contradiction*)
                          (mv (or changedp changedp1) *tau-contradiction*))
                         (t (add-recogs-to-tau1 sign (cdr recog-lst) tau wrld
                                                (or changedp changedp1))))))))

(defun tau-union (tau1 tau2 wrld)

; We add every sign/recog in tau1 to tau2.  We return (mv changedp tau2').
; tau2' may be *tau-contradiction*.  This function does not add implicants
; because we assume both tau1 and tau2 are already closed under simple
; implication.

  (mv-let
   (changedp tau2)
   (if (access tau tau1 :pos-evg)
       (add-to-tau1 t (access tau tau1 :pos-evg)
                    tau2 wrld)
       (mv nil tau2))
   (mv-let
    (changedp tau2)
    (if (eq tau2 *tau-contradiction*)
        (mv nil *tau-contradiction*)
        (add-recogs-to-tau1 nil (access tau tau1 :neg-evgs)
                            tau2 wrld changedp))
    (mv-let
     (changedp tau2)
     (if (eq tau2 *tau-contradiction*)
         (mv nil *tau-contradiction*)
         (add-recogs-to-tau1 t (access tau tau1 :pos-pairs)
                             tau2 wrld changedp))
     (mv-let
      (changedp tau2)
      (if (eq tau2 *tau-contradiction*)
          (mv nil *tau-contradiction*)
          (add-recogs-to-tau1 nil (access tau tau1 :neg-pairs)
                              tau2 wrld changedp))
      (mv changedp tau2))))))
         
(defun add-to-tau (sign recog tau wrld)

; Recog is a tau-pair or singleton evg list.  Tau is a tau object, not
; *tau-contradiction*.  We add sign/recog and its implicants to tau.  We return
; (mv changedp tau'), where tau' may be *tau-contradiction*.

  (cond
   ((cdr recog) ; new recog is tau-pair
    (tau-union (tau-simple-implicants sign (cdr recog) wrld)
               tau wrld))
   (t ; new recog is an evg
    (add-to-tau1 sign recog tau wrld))))

; Now we define the notion of one tau being a ``near subset'' of another.  We
; say a set is a near subset of another if there is exactly one element of the
; former that is not in the latter.  Our functions for checking this property
; (across various data structures like lexordered lists, tau-pairs,
; tau, etc) all follow the convention that they return t if every
; element of the former is in the latter (i.e., the subset relation holds), nil
; if more than one element fails to occur, and the unique missing element
; otherwise.  We are careful that the sets to which we apply this concept never
; contain nil as an element.

(defun pos-evg-near-subsetp (pos-evg1 pos-evg2)

; This is an odd little function that plays the role for the :pos-evg slot of
; tau that tau-pairs-near-subsetp plays for :pos-pairs and
; :neg-pairs.  By defining it explicitly we allow tau-near-subsetp to be defined
; as a composition across the four components.

; The :pos-evg slot of a tau is either nil or represents a singleton
; set containing the :pos-evg.  So think of s1 and s2 as the sets corresponding
; to the given pos-evg1 and pos-evg2.  Then we determine whether s1 is a
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

(defun neg-evgs-near-subsetp (neg-evgs1 neg-evgs2 e pos-pairs2 neg-pairs2 wrld)

; This is analogous to tau-pairs-near-subsetp, but for the neg-evgs components.

; We wish to check the near-subset relation between the neg-evgs of two
; tau tau1 and tau2.  (Recall that lst1 is a near-subset of lst2 if
; there is exactly one element of lst1 that is not in lst2.  Our convention is
; that ``near-subset'' functions return t to indicate that every element of the
; one is in the other, nil to indicate that more than one element is missing,
; and otherwise returns the missing element.)  However, suppose x /= 23 is in
; tau1 by being in its neg-evgs, while it is not in the neg-evgs of tau2 because
; it is ruled out by some pair.  For example, tau1 might be the integers except
; 23, while tau2 might be the even integers.  If the assumption that x = 23
; allows us to falsify some pos-pair in tau2, then x = 23 isn't really missing
; from tau2, it is swept up by the pos-pairs.  Neg-pairs are, of course,
; symmetric.  But this concept is just that codified in exists-bad-valp.

; If every element of neg-evgs1 is either in neg-evgs2 or else is subsumed by
; some pair in pos-pairs2 or neg-pairs2, we return t.  If more than one element
; of neg-evgs1 fails to have that property (i.e., is in neg-evgs2 or is
; subsumed by the pairs), we return nil.  Otherwise, we return the missing
; element.

  (cond
   ((endp neg-evgs1) (if e e t))
   ((endp neg-evgs2)

; If we have exhausted neg-evgs2, then we have lost unless every remaining
; element of neg-evgs1 is subsumed by the pairs.

    (cond 
     ((or (exists-bad-valp nil pos-pairs2 (car neg-evgs1) wrld)
          (exists-bad-valp t   neg-pairs2 (car neg-evgs1) wrld))
          
; So the ``missing'' element is actually subsumed by one of the pairs in tau2
; and we can treat it as found.

      (neg-evgs-near-subsetp (cdr neg-evgs1)
                             nil ; still exhausted!
                             e
                             pos-pairs2 neg-pairs2 wrld))

; Otherwise, we know (car neg-evgs1) really is missing and so we fail if we've
; already seen a missing element and we continue with (car neg-evgs1) as our
; candidate unique witness if we haven't.

     (t (if e
            nil
            (neg-evgs-near-subsetp (cdr neg-evgs1)
                                   nil ; still exhausted!
                                   (car neg-evgs1)
                                   pos-pairs2 neg-pairs2 wrld)))))
   ((lexorder (car neg-evgs1) (car neg-evgs2))
    (if (equal (car neg-evgs1) (car neg-evgs2))
        (neg-evgs-near-subsetp (cdr neg-evgs1)
                               (cdr neg-evgs2)
                               e
                               pos-pairs2 neg-pairs2 wrld)

; At this point, we've discovered that (car neg-evgs1) is missing from
; neg-evgs2.  But we can't treat it as missing until we make sure it
; isn't subsumed by one of the pairs.

        (cond
         ((or (exists-bad-valp nil pos-pairs2 (car neg-evgs1) wrld)
              (exists-bad-valp t   neg-pairs2 (car neg-evgs1) wrld))
          
; So the ``missing'' element is actually subsumed by one of the pairs in tau2
; and we can treat it as found.

          (neg-evgs-near-subsetp (cdr neg-evgs1)
                                 (cdr neg-evgs2)
                                 e
                                 pos-pairs2 neg-pairs2 wrld))
         (t

; Otherwise, it really is missing and we either fail or make this the candidate
; unique witness.

          (if e
              nil
              (neg-evgs-near-subsetp (cdr neg-evgs1)
                                     neg-evgs2
                                     (car neg-evgs1)
                                     pos-pairs2 neg-pairs2 wrld))))))
   (t (neg-evgs-near-subsetp neg-evgs1 (cdr neg-evgs2)
                             e
                             pos-pairs2 neg-pairs2 wrld))))


(defun tau-near-subsetp (tau1 tau2 wrld)

; Think of tau1 and tau2 simply as abstract recognizer sets.  If tau1 is a subset
; of tau2, we signal a contradiction.  If more than one element of tau1 is not in
; tau2, we return nil; otherwise, we return the sign and recog of the missing
; element.  We return (mv contradictionp sign recog), where the last two are
; nil when contradictionp is t.

; Some of the possibilities below don't really make sense -- we'd never be
; presented with a Conjunctive rule tau1 consisting of a :pos-evg.  But we
; behave as per the spec above just to keep the interface clean.  The main
; thing to remember is that we need only look for :neg-evgs, :pos-pairs, and
; neg-pairs of tau1 in the corresponding components of tau2.

; Imagine computing the four component-wise near-subsetp answers.  For each
; obtain a signed answer, sign1/temp1, sign2/temp2, etc, where if tempi = t,
; subset holds, if tempi=nil, two or more elements failed to be included, and
; otherwise tempi is the missing element.

; If any tempi is nil, we fail: (mv nil nil nil).  If all are t, we signal
; contradiction: (mv t nil nil).  If exactly one tempi is the missing element
; and other tempi are t, we won: (mv nil signi tempi) for the i that was
; witnessed.  Otherwise, we fail.

; Efficiency considerations: By cascading the (null tempi) checks we avoid even
; computing tempi for those i beyond the first failure.  Furthermore, if any
; tempi is nil, temp4 is nil.  And we don't actually have to remember signi
; because we know that for temp1 and temp3, the signs are positive (t), and for
; temp2 and temp4, the signs are negative (nil).

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
                          wrld))))
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

; Observe that if any tempi is nil, temp4 is nil.

    (cond
     ((null temp4) (mv nil nil nil))
     (t (if (eq temp1 t)
            (if (eq temp2 t)
                (if (eq temp3 t)
                    (if (eq temp4 t)
                        (mv t nil nil)
                        (mv nil nil temp4))
                    (if (eq temp4 t)
                        (mv nil t temp3)
                        (mv nil nil nil)))
                (if (and (eq temp3 t)
                         (eq temp4 t))
                    (mv nil nil temp2)
                    (mv nil nil nil)))
            (if (and (eq temp2 t)
                     (eq temp3 t)
                     (eq temp4 t))
                (mv nil t temp1)
                (mv nil nil nil)))))))

; Here is a test that yields a contradiction (all elements are found).  If you
; change the 25 to a 24, that becomes the missing element.  If you additionally
; change 23 to 22, it fails because there are two missing elements.

; (tau-near-subsetp
;  (fancy-tau (not (equal x '23)) (not (equal x '25)) (integerp x))
;  (fancy-tau (not (equal x '20)) (not (equal x '44)) (integerp x) (evenp x))
;  (@ wrld) (w state))

; -----------------------------------------------------------------
; Essay on the Tau Data Base

; We build a data base from certain kinds of theorems, as shown below.  In the
; forms shown, p, q, p1, p2, ..., are all understood to be recognizers (and
; thus may be (fn x), (NOT (fn x)), (EQUAL x 'evg), or (NOT (EQUAL x 'evg))).

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

; The data base will maintain the following properties on certain
; function symbols fn.

; property                   value

; tau-pair                   (i . fn), means fn is known to tau data base

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
;                            the MV returned by fn

; big-switch                 see defrec for big-switch-rule; indicates
;                            that fn is a big switch function

; global-value               we use the global-value property of the following
;                            symbol                GLOBAL-VALUE

;                            tau-next-index         n
;                            tau-conjunctive-rules  (conj-rule1 ... conj-rulek),
;                                                   where each conj-rulei is just
;                                                   a tau
;                            tau-runes              (rune1 rune2 ...)
;                            tau-mv-nth-synonyms    (fn1 ... fnk)
;                            tau-lost-runes         (rune1 rune2 ...)

; The first three proeprties are called ``tau predicate properties'' and the
; other fn specific properties are called ``tau function properties.''  A
; predicate symbol may have both kinds of properties, e.g., a predicate may
; also be unevalable-but-known and may be a big-switch.

; Closure of Simple Rules under Contraposition and Transitivity

; We now turn to implementing the closure operations.  We close the simple
; rules under contraposition and transitivity.  In particular, for the common
; case where p and q are calls of monadic Boolean functions, we store the
; simple rule (p x) --> (q x) by storing q in the pos-implicants of p and
; storing -p in the neg-implicants of q.  However, things are more complicated
; when p and/or q is an equality-on-constant, as explained below.  But, in the
; common case we add a recogizer to a tau in wrld with tau-put and add it
; transitively with the operation with tau-put*.

; Below we describe our handling of equality-with-constant in this context.
; Recall that the design of this system is based on the

; Underlying Premise: No function symbol is defined or constrained to be
; constantly T or constantly NIL, and no function symbol is defined or
; constrained to be equivalent to (EQUAL v 'evg) or (NOT (EQUAL v 'evg)).

; Consider illustrative examples of Simple rules involving
; equality-with-constant.

; [1] (equal x 'evg) --> (fn x)
; [2] (not (equal x 'evg)) --> (fn x)
; [3] (fn x) --> (equal x 'evg)
; [4] (fn x) --> (not (equal x 'evg))

; Cases where (fn x) is shown negated are handled symmetrically so we don't
; show them.  Furthermore, cases [3] and [4] below are really just the same as
; [2] and [1] (resp.)  with the negated fn.  So we only discuss [1] and [2].
; Furthermore, given the Underlying Premise, [2] never arises since it is
; equivalent to saying fn is either constant or a hidden equality.

; That leaves [1].  We can clearly store that x /= 'evg under the negative
; implicants of fn.  But we have no way to store fn under the positive
; implicants of (equal x 'evg).  Instead, we try to evaluate (fn 'evg) and if
; it computes (necessarily to T if [1] is a theorem) then we don't store the
; ``-->'' implication.  The idea is that if some term has tau {(lambda (x)
; (equal x 'evg))}, then we know the term is 'evg and we can determine if other
; recognizers hold by evaluating them.

; There is a fly in this ointment: it is possible that [1] can be proved but
; that (fn 'evg) cannot be evaluated because it is constrained.  In that case,
; we store (evg . T) on the unevalable-but-known alist of fn.

(defun tau-put (p-sign p-recog q-sign q-recog wrld)

; The two recogs are either tau-pairs or singleton lists of evgs.  They are
; signed as indicated by the two signs.  Think of these four arguments as
; describing signed recognizers p and q.  Roughly speaking, we simply store (p
; --> q) into the data base.  However, if that formula falls into case [1] above
; we either store nothing or add the evg to the UNEVALABLE-BUT-KNOWN alist for
; q.  If (p --> q) falls into case [2] above we ignore it (store nothing).  We
; return (mv contradictionp changedp wrld').  This is a No-Change Loser on
; wrld.

  (cond
   ((cdr p-recog)
    (cond
     ((cdr q-recog)
      (mv-let (changedp new-tau)
              (add-to-tau1 q-sign q-recog
                           (tau-simple-implicants p-sign (cdr p-recog) wrld)
                           wrld)

; Note: We use add-to-tau1 because we will propagate the implicants carefully as
; we update the data base.

              (cond
               ((null changedp)
                (mv nil nil wrld))
               ((eq new-tau *tau-contradiction*)
                (mv t nil wrld))
               (t (mv nil
                      t
                      (putprop (cdr p-recog)
                               (if p-sign 'pos-implicants 'neg-implicants)
                               new-tau
                               wrld))))))
     (q-sign

; The formula is of the form p --> x = 'evg.  This violates the Underlying
; Premise and so we just ignore it.

      (mv nil nil wrld))
     (t

; The formula is of the form p --> x /= 'evg, which means its contrapositive is
; ; x = 'evg --> -p.  This form of formula is handled when we see the contrapositive.

      (mv nil nil wrld))))
   (p-sign

; Below, we know that p-recog is a singleton list containing an evg.  We're
; handling the positive case, i.e., we know x is 'evg.

    (cond
     ((cdr q-recog)

; The formula is of the form x = 'evg --> q-sign/q-recog.  We store this by
; either successfully evaluating q-recog on evg or by adding evg to q's
; unevalable-but-known alist.  Note that the formula establishes that on 'evg,
; q-recog returns q-sign.

      (let ((val (ev-fncall-w-tau-recog (cdr q-recog) p-recog wrld)))
        (cond
         ((eq val :UNEVALABLE)

; At one point we mistakenly thought we should somehow update *tau-t* (or
; *tau-nil*) if the newly proved theorem established x = t --> q for some
; unevalable q.  But that is not necessary.  By adding (t . t) to the
; unevalable-but-known property of q we insure that in the future when a tau is
; created containing t we will know that q is true on it by the
; pseudo-evaluation that happens in ev-fncall-w-tau-recog.

          (mv nil t
              (putprop (cdr q-recog)
                       'unevalable-but-known
                       (cons (cons (car p-recog) q-sign) ; (evg . bool)
                             (getprop (cdr q-recog)
                                      'unevalable-but-known
                                      nil
                                      'current-acl2-world wrld))
                       wrld)))
         ((iff val q-sign)
          (mv nil nil wrld))
         (t (mv t nil wrld)))))
     (t

; The formula is either of the form (x = 'evg1 --> x = 'evg2) or
; of the form (x = 'evg1 --> x /= 'evg2).  It is either trivial or
; contradictory.

      (cond ((iff q-sign (equal (car p-recog) (car q-recog)))
             (mv nil nil wrld))
            (t (mv t nil wrld))))))
   (t

; The formula is of the form x /= 'evg --> q.

    (cond
     ((cdr q-recog)

; The formula is x /= 'evg --> q, which violates the Underlying Premise, so we
; do nothing.

      (mv nil nil wrld))
     (t

; The formula is of one of four possible forms depending on whether the two evgs
; are the same.  In the example forms below, we use 1 and 2 as two representative
; evgs; what is important is that either they're the same or they're different, 
; and that there always exists a third evg, say 3.

; x /= 1 --> x  = 2      contradiction, let x be 3
; x /= 1 --> x  = 1      contradiction, let x be 3
; x /= 1 --> x /= 2      contradiction, let x be 2
; x /= 1 --> x /= 1      trivial

      (cond ((and (not q-sign) (equal (car p-recog) (car q-recog)))
             (mv nil nil wrld))
            (t (mv t nil wrld))))))))

(mutual-recursion

(defun tau-put* (p-sign p-recog q-sign q-recog wrld)

; Let p be p-sign/p-recog and q be q-sign/q-recog.  We store q as an implicant
; of p, then store the contrapositive version, and then close both additions
; under transitivity.  More precisely, when we store q as an implicant of p, we
; store NOT/p as an implicant of NOT/q.  Then, for every element, r, of the
; implicants of q, we store r as an implicant of p.  Then, for every element,
; r, of the implicants of NOT/p, we store r as an implicant of NOT/q.  We
; return (mv contradictionp changedp wrld').  Wrld' is always either wrld
; unchanged (changedp=nil) or wrld extended appropriately.

; Note: It is possible for p-->q NOT to change the world but for -q --> -p to
; change the world.  For example, (x=2) --> (evenp x) does nothing, but -(evenp
; x) --> (x /= 2) adds the inequality to the implicants of not/evenp.
; (Remember, we are storing a user-supplied theorem to that effect.)

  (mv-let
   (contradictionp changedp1 wrld)
   (tau-put p-sign p-recog q-sign q-recog wrld)
   (cond
    (contradictionp (mv t nil wrld))
    (t
     (mv-let
      (contradictionp changedp2 wrld)
      (tau-put (not q-sign) q-recog (not p-sign) p-recog wrld)
      (cond
       (contradictionp (mv t (or changedp1 changedp2) wrld))
       ((and (not changedp1) (not changedp2))
        (mv nil nil wrld))

; At this point we know something changed, so we pursue the implicants.  But it
; could be that we can avoid one implicant chase or the other due to the
; no-change flags.  But every exit from this function below will indicate that
; wrld has changed because it changed above.

       (t
        (mv-let
         (contradictionp changedp wrld)
         (if (and changedp1
                  (cdr q-recog))

; We added q to the implicants of p.  So we have to add all the implicants of q
; to the implicants of p.  However, if adding q to the implicants of p didn't
; really change p (and provided the data base was already closed), then we don't
; have to do anything.  Also, if q-recog is not a tau-pair but is a singleton
; evg list, we don't chase it's implicants.

             (tau-put*-tau p-sign p-recog
                           (tau-simple-implicants q-sign (cdr q-recog) wrld)
                           wrld)
             (mv nil t wrld))
         (declare (ignore changedp)) ; always t!
         (cond
          (contradictionp (mv t t wrld))
          ((and changedp2
                (cdr p-recog))

; This is the symmetric case, which we do only if we really changed the
; implicants of q and p-recog is a tau-pair.

           (tau-put*-tau (not q-sign) q-recog
                         (tau-simple-implicants (not p-sign) (cdr p-recog) wrld)
                         wrld))
          (t (mv nil t wrld)))))))))))


(defun tau-put*-tau (p-sign p-recog tau wrld)

; We map over every r-sign/r-recog in tau and do 

; (tau-put* p-sign p-recog r-sign r-recog ...).

; Technically we return (mv contradictionp changedp wrld').  But actually the
; returned changedp flag is always t and we don't bother keeping track of that
; because we don't call this function except when the input wrld has changed.

; While abstractly tau is a set of recognizers that we might map over,
; concretely it is a tau with four quite different components:
; pos-evg, neg-evgs, pos-pairs, and neg-pairs.  It is clear how to map over the
; two -pairs.  But is there any point in mapping over the others?  Yes!  For
; example, consider pos-evg.  Adding that to p-sign/p-recog could have
; wonderful effects.  More likely, adding each of the neg-evgs could populate
; unevalable-but-known fields.  Thus, we really do map over every part of tau.

  (mv-let
   (contradictionp changedp wrld)
   (if (access tau tau :pos-evg)
       (tau-put* p-sign p-recog t (access tau tau :pos-evg)
                 wrld)
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
                       wrld)
      (declare (ignore changedp)) ; always t
      (cond
       (contradictionp (mv t t wrld))
       (t
        (mv-let
         (contradictionp changedp wrld)
         (tau-put*-recogs p-sign p-recog
                          t
                          (access tau tau :pos-pairs)
                          wrld)
         (declare (ignore changedp))
         (cond
          (contradictionp (mv t t wrld))
          (t
           (tau-put*-recogs p-sign p-recog
                            nil
                            (access tau tau :neg-pairs)
                            wrld)))))))))))

(defun tau-put*-recogs (p-sign p-recog r-sign r-recogs wrld)

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
       (tau-put* p-sign p-recog r-sign (car r-recogs) wrld)
       (declare (ignore changedp))
       (cond
        (contradictionp (mv t t wrld))
        (t (tau-put*-recogs p-sign p-recog r-sign (cdr r-recogs) wrld)))))))

)

; At one point we considered closing the data base under the conjunctive rules,
; in so far as we could.  We knew that we had to keep conjunctive rules around
; anyway and use them at query time because at query time we are given a list
; of knowns and must consider what the conjunctive rules tell us about that
; particular combination of recs.  But it seemed like possibly a good idea to
; also use the rules on the data base itself.  But that is very complicated.
; Suppose we have a db closed under everything (including conjunctive rules).
; Then we add p-->q.  This will touch the implicants of p (to add q and all the
; things q implies), -q (to add -p and all the things -p implies), and for
; every r in the implicants of q, -r (to add -p), and for every s in the
; implicants of -p, -s (to add q), and so on.  Every one of those implicant
; lists has to be closed again under conjunctive rules.  So we would need to
; track all the recs we change, not just whether we changed anything.

; Furthermore, if a conjunctive rule is added, we have to close every implicant
; list in the world again.

; Finally, how common will it be for the user to have told us that (a & b) -->
; c, and then told us that p --> a and p --> b?  Certainly it will happen,
; e.g., if p is added after the primitive types a, b, and c, have been defined.

; It turns out that this happens a lot.  For example, in the Rockwell benchmark
; used to test early versions of this (in which all :type-prescription and
; :forward-chaining rules were interpreted as :tau-system rules) we mapped over
; all the predicates and asked how often does a conjunctive rule file on the
; implicants (positive and negative).  The answer was that of 11,940 implicants
; stored in the data base, 4,640 of them could be extended with conjunctive
; rules.

; -----------------------------------------------------------------
; Converting the Theorems in a World to Tau Rules

; We populate the data base by processing certain theorems.  However, we do
; this both when an event is first processed (in install-event) and also when
; the tau data base is regenerated (regenerate-tau-data-base).  We call this
; ``visiting'' the event; sometimes that visit is the first time that event has
; ever been seen by tau and other times it is not.

; Recall also that theorems are added to the tau data base either because they
; are explicitly labeled :tau-system rules or because we are in automatic mode
; and the theorems are of the appropriate form.  This is also done when we visit
; an event, rather than in the core code for each event, to bring all the tau
; data base updates into one place.

; The following code deals with recognizing the shapes of theorems that can be
; represented as tau rules and adding those rules to the data base.  We
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

(defun monadic-boolean-fnp (fn ens wrld)

; Fn is known to be a function symbol.  We return (mv t ttree) if fn is a
; monadic Boolean function and (mv nil nil) otherwise.  Ttree is from the proof
; that fn is Boolean.

  (cond ((and
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

; Wrld must be the ACL2 logial world, not some user-defined world.  We store
; val as the property prop of sym unless it is already stored there.

  (if (equal (getprop sym prop *acl2-property-unbound*
                      'current-acl2-world wrld)
             val)
      wrld
      (putprop sym prop val wrld)))

(defun tau-visit-function-introduction (fn wrld)

; This function makes fn almost virgin wrt to the tau system.  Those functions
; in *primitive-monadic-booleans* as explained below.  For all other functions
; fn, the only tau property of fn that is preserved is its tau-pair-saved
; property (if any), which is the tau-pair fn will be assigned if it is ever
; again recognized as a tau predicate.

; This function is called when we are regenerating the tau data base by
; scanning the world and we encounter a function introduction, i.e., a FORMALs
; property.  But the monadic primitives, like CONSP and SYMBOLP, are known to
; be Boolean and are so initialized when we begin regenerating the world, in an
; immitation of what happens during boot-strap.  We do not want our encounter
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
; data bases under different enabled structures.

  (let ((old-pair (getprop fn 'tau-pair-saved nil 'current-acl2-world wrld)))
    (if old-pair
        (putprop fn 'tau-pair old-pair wrld)
        (let* ((nexti (global-val 'tau-next-index wrld))
               (new-pair (cons nexti fn)))
          (putprop fn 'tau-pair new-pair
                   (putprop fn 'tau-pair-saved new-pair
                            (global-set 'tau-next-index (+ 1 nexti) wrld)))))))

(defun initialize-tau-pred (fn wrld)

; Initialize the tau properties of fn as a monadic Boolean, i.e., give it a
; tau-pair and set up its pos- and neg-implicants.  It is assumed that all of
; fn's tau properties have previously been cleared.

  (let* ((wrld1 (putprop-tau-pair fn wrld))
         (tau-pair (getprop fn 'tau-pair nil 'current-acl2-world wrld1))
         (wrld2 (putprop fn 'pos-implicants
                         (make tau
                               :pos-evg nil
                               :neg-evgs nil
                               :pos-pairs (list tau-pair)
                               :neg-pairs nil)
                         wrld1))
         (wrld3 (putprop fn 'neg-implicants
                         (make tau
                               :pos-evg nil
                               :neg-evgs nil
                               :pos-pairs nil
                               :neg-pairs (list tau-pair))
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

(defun set-tau-runes (flg val wrld)

; This function updates the global-value of tau-runes, adding val to its
; current value.  Flg should be 'list or nil indicating whether val is a list
; of runes or a single rune.

; Note: The reason we need union-equal and add-to-set-equal, even though we
; never visit the same rule twice, is that some rules split into many (hyps
; . concl) pairs and each pair has the same rune.  For example, if a function
; foo has a :type-prescription rule that says the result is a symbol other than
; T or NIL, it turns into the conjunction of (symbolp v), (not (equal v 'T)),
; (not (equal v 'NIL)) and each is added with the same rune.

  (let ((runes0 (global-val 'tau-runes wrld)))
    (global-set 'tau-runes
                (cond ((eq flg 'list)
                       (union-equal val runes0))
                      (t (add-to-set-equal val runes0)))
                wrld)))

(defun add-tau-boolean-rule (rune hyps concl wrld)

; To add a tau Boolean rule, in which hyps is nil and concl is (BOOLEANP (f
; v)), we make f a tau predicate by giving it a (possibly new) tau pair and
; initializing its pos- and neg-implicants.  We also add rune to tau-runes.

  (declare (ignore hyps))
  (initialize-tau-pred (ffn-symb (fargn concl 1))
                       (set-tau-runes nil rune wrld)))

; We need to recognize terms that are suitable applications of tau predicates.
; We call these ``tau-like'' terms.  Technically, a term is ``tau-like'' if it
; is either (pred e) or (NOT (pred e)) where pred has a tau-pair, or else is
; (equal e 'evg) or (NOT (equal e 'evg)) and equal is any of the variants of
; EQUAL.  If a term is tau-like as above, then the ``subject'' of that tau-like
; term is e.

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
; nils.  If recog is non-nil, then it is a recognizer object.  Concretely, a
; non-nil recog is either a tau-pair, (index . fn), or else is a singleton
; list containing an evg, (evg).  To be ``tau-like'' term must be a possibly
; negated term of the form (fn e) or (equal e 'evg).  The returned sign is T if
; term is positive; sign is nil for negated terms.  The returned e is the
; subject of the term and meets the input criterion.  Criterion' is the NEXT
; criterion to use when mapping across a list of terms to determine if they are
; all tau-like in the given sense.

; Keep this function in sync with tau-big-switch-var.

  (mv-let
   (sign atm)
   (if (and (nvariablep term)
            (not (fquotep term))
            (eq (ffn-symb term) 'NOT))
       (mv nil (fargn term 1))
       (mv t term))
   (case-match atm
     ((fn e)
      (cond
       ((symbolp fn)
        (let ((tau-pair (getprop fn 'tau-pair nil 'current-acl2-world wrld)))
          (cond
           (tau-pair
            (let ((next-criterion (tau-like-subject-criterion criterion e)))
              (cond (next-criterion
                     (mv sign tau-pair e next-criterion))
                    (t (mv nil nil nil nil)))))
           (t (mv nil nil nil nil)))))
       (t (mv nil nil nil nil))))
     ((equiv e ('quote . singleton-evg))
      (cond ((member-eq equiv '(equal eq eql =))
             (let ((next-criterion (tau-like-subject-criterion criterion e)))
               (cond (next-criterion
                      (mv sign singleton-evg e next-criterion))
                     (t (mv nil nil nil nil)))))
            (t (mv nil nil nil nil))))
     ((equiv ('quote . singleton-evg) e)
      (cond ((member-eq equiv '(equal eq eql =))
             (let ((next-criterion (tau-like-subject-criterion criterion e)))
               (cond (next-criterion
                      (mv sign singleton-evg e next-criterion))
                     (t (mv nil nil nil nil)))))
            (t (mv nil nil nil nil))))
     (& (mv nil nil nil nil)))))

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
                         (t (tau-like-term-listp (cdr lst) next-criterion wrld)))))))


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
; where each tau-likei is a recognizer about a common variable
; symbol v.  This core function is used both to recognize the Conjunctive
; form and the Simple form, the latter being the special case when there is only
; one hypothesis.

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
; Subtype rule.  This means it has the form (implies (tau-like1 v) (tau-like2 v))
; for two tau predicates and a common variable symbol v.

  (and (tau-conjunctive-formp hyps concl wrld)
       (null (cdr hyps))))

(defun add-tau-simple-rule (rune hyps concl wrld)

; To add a simple subtype rule we extend the implicants in the data base,
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
                          (tau-put* p-sign p-recog q-sign q-recog wrld)
                          (declare (ignore changedp))
                          (cond
                           (contradictionp
                            (er hard 'add-tau-simple-rule
                                "It was thought impossible for the addition ~
                                 of a simple subtype tau rule (derived from a ~
                                 theorem) to yield a contradiction but it has ~
                                 happened with the rule named ~x0, derived ~
                                 from ~x1."
                                rune
                                (reprettyify hyps concl wrld)))
                           (t (set-tau-runes nil rune wrld)))))))

(defun convert-tau-like-terms-to-tau (terms wrld)

; We convert a list of tau-like terms, terms, to a tau.

  (cond
   ((endp terms) *tau-empty*)
   (t (mv-let
       (sign recog e criterion)
       (tau-like-term (car terms) :various-any wrld)
       (declare (ignore e criterion))
       (mv-let (changedp tau)
               (add-to-tau1 sign recog
                            (convert-tau-like-terms-to-tau (cdr terms) wrld)
                            wrld)

; Note: We use add-to-tau1 because we are not interested in the implicants of the
; terms, just the terms themselves.

               (declare (ignore changedp))
               (cond ((eq tau *tau-contradiction*)

; If we get a contradiction from assuming all the terms in terms it is because
; it is a propositional impossibility, e.g., (p & q & -p).  This happens if we
; try to produce a conjunctive rule from a tautology like (p & q) -> p.  We
; just ignore these.

                      *tau-empty*)
                     (t tau)))))))

(defun add-tau-conjunctive-rule (rune hyps concl wrld)

; A conjunctive rule (implies (and (p1 x) ... (pk x)) (q x)) is stored as {p1
; ... pk -q}.  The idea is that if we detect that we know all but one of the
; elements of such a set, we can assert the remaining element.  This is
; actually stored as a tau so that it is easier to search for each
; ``kind'' of recog in it.  But we are not interested in the semantics of such
; tau, i.e., M[tau] is irrelevant for conjunctive rules; we're just exploiting
; the data structure.

  (let ((tau (convert-tau-like-terms-to-tau
              (append hyps (list (case-match concl
                                   (('NOT p) p)
                                   (& `(NOT ,concl)))))

; Note that I move the negated conclusion into the hyps to produce the list
; that is converted to a tau.  I avoid dumb-negate-lit simply because it does
; more than just add or strip a NOT.

              wrld)))
    (if (equal tau *tau-empty*)
        wrld
        (set-tau-runes nil rune
                       (global-set 'tau-conjunctive-rules
                                   (cons tau
                                         (global-val 'tau-conjunctive-rules wrld))
                                   wrld)))))

(defun tau-signature-formp (hyps concl wrld)

; We return 1 or 2 or nil to indicate whether (implies (and . hyps) concl) is
; suitable as a tau signature rule of the indicated form.  To be of form 1, it
; must be of the

; Signature Form 1:
; (implies (and (tau-like1_1 x1) ... (tau-like1_k x1)
;               ...
;               (tau-liken_1 xn) ... (tau-liken_j xn))
;          (tau-like (fn x1 ... xn)))

; That is, we get to make an arbitrary number of tau-like hypotheses about
; distinct variables x1, ..., xn, and then assert a tau-like conclusion about
; (fn x1 ... xn).

; To be of form 2 it must be of the form:

; Signature Form 2
; (implies (and (tau-like1_1 x1) ... (tau-like1_k x1)
;               ...
;               (tau-liken_1 xn) ... (tau-liken_j xn))
;          (tau-like (mv-nth 'i (fn x1 ... xn)))

; Note that the hypotheses are of the same form as in form 1.  We used to
; require that the vars of the hyps be a subset of the vars of the concl, i.e.,
; that there be no free vars.  Now we allow but ignore any hyp with free vars.

  (cond ((tau-like-term-listp hyps :various-var wrld)

; All the hyps are tau literals applied to various variables.

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
; fn is a function symbol and the xi are distinct variables, and every hyp is
; about some xi.  The last condition means that when we collect the hyps about
; each xi no hyp will be omitted.  It is not necessarily the case that there is
; a hyp about each xi, e.g., (natp x) --> (natp (f x y)) is of signature form
; and the y slot of f is simply unrestricted.

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
                              (symbol-listp (fargs e))       ; faster than arglistp 
                              (no-duplicatesp-eq (fargs e))) ; for a list of terms.
                         2)
                        (t nil))))
                    (t nil)))
                  ((and (symbolp (ffn-symb e))
                        (nvariablep e)
                        (not (fquotep e))
                        (symbolp (ffn-symb e))
                        (symbol-listp (fargs e))       ; faster than arglistp
                        (no-duplicatesp-eq (fargs e))) ; for a list of terms.
                   1)
                  (t nil))))
        (t nil)))

(defun convert-tau-like-terms-to-subject-tau-alist (hyps alist hyps0 concl0 wrld)

; We assume hyps is tau-like :VARIOUS-VAR, e.g., every subject is a symbol!  We
; build an alist pairing each symbol v with the list of all recognizers about
; v.  Hyps0 and concl0 are the components of the unprettyified theorem from
; which this rule is being constructed and are used only for error reporting.

  (cond
   ((endp hyps) alist)
   (t (let* ((alist (convert-tau-like-terms-to-subject-tau-alist
                     (cdr hyps) alist hyps0 concl0 wrld)))
        (mv-let (sign recog v criterion)
                (tau-like-term (car hyps) :various-var wrld)
                (declare (ignore criterion))
                (let ((old-tau (or (cdr (assoc-eq v alist)) *tau-empty*)))
                  (mv-let
                   (changedp new-tau)
                   (add-to-tau1 sign recog old-tau wrld)
; Note: We use add-to-tau1 because we are not interested in the implicants.
                   (declare (ignore changedp))
                   (cond
                    ((eq new-tau *tau-contradiction*)
                     (er hard 'convert-tau-like-terms-to-subject-tau-alist
                         "It was thought impossible for a Signature rule to ~
                          yield a contradiction, but it happened when we ~
                          tried to compute the recognizer sets for the ~
                          arguments while turning ~x0 into a rule."
                         (reprettyify hyps0 concl0 wrld)))
                    (t (put-assoc-eq v new-tau alist))))))))))

(defun replace-vars-by-bindings (vars alist)

; Given a list of vars and an alist mapping vars to objects, we return the
; result replacing each var in the list by its image under the alist.

  (cond ((endp vars) nil)
        (t (cons (or (cdr (assoc-eq (car vars) alist))
                     *tau-empty*)
                 (replace-vars-by-bindings (cdr vars) alist)))))

(defun add-tau-signature-rule (rune form hyps concl wrld)

; Form is either 1 or 2 and indicates which form of signature rule we can
; construct from (implies (and . hyp) concl).  We update the data base
; appropriately.

; Signature Form 1:
; (implies (and (tau-like1_1 x1) ... (tau-like1_k x1)
;               ...
;               (tau-liken_1 xn) ... (tau-liken_j xn))
;          (tau-like (fn x1 ... xn)))

; Signature Form 2:
; (implies <same as above>
;          (tau-like (mv-nth 'i (fn x1 ... xn))))

  (mv-let
   (sign recog e criterion)
   (tau-like-term concl :various-any wrld)
   (declare (ignore criterion))
   (let* ((fn (if (eql form 1) (ffn-symb e) (ffn-symb (fargn e 2))))
          (i (if (eql form 1) nil (cadr (fargn e 1))))
          (vars (fargs (if (eql form 1) e (fargn e 2))))
          (alist (convert-tau-like-terms-to-subject-tau-alist
                  hyps nil hyps concl wrld))
          (rule (make signature-rule
                      :input-tau-list (replace-vars-by-bindings vars alist)
                      :output-sign sign
                      :output-recog recog)))

; It is easy to imagine that the same signature gets stored in two different
; theorems, as happens in the Rockwell work where types are mechanically
; generated and there is some redundancy.  So we check.

     (cond
      ((eql form 1)
       (let ((sigs (getprop fn 'signature-rules-form-1 nil
                            'current-acl2-world wrld)))
         (if (member-equal rule sigs)
             wrld
             (set-tau-runes nil rune
                            (putprop fn
                                     'signature-rules-form-1
                                     (cons rule sigs)
                                     wrld)))))
      (t (let ((sigs (getprop fn 'signature-rules-form-2 nil
                              'current-acl2-world wrld)))
           (if (member-equal rule (nth i sigs))
               wrld
               (set-tau-runes nil rune
                              (putprop fn
                                       'signature-rules-form-2
                                       (update-nth i
                                                   (cons rule (nth i sigs))
                                                   sigs)
                                       wrld)))))))))

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
; variable occuring freely in term is a switch for term.

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
       (and (symbolp fn)
            (not (equal fn 'quote))
            (not (getprop fn 'tau-pair nil 'current-acl2-world wrld))
            (not (getprop fn 'big-switch nil 'current-acl2-world wrld))
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
; by tau-like-term.  We see the subject of test.  That means we must determine
; what kind of tau-like term it is: (recog v), (EQUAL v 'evg), or some variant
; of EQUAL or a commuted version of such an equality, or the negation of one of
; these forms.

  (mv-let (sign test)
          (strip-not (fargn (fargn term 2) 1))
          (declare (ignore sign))

; Test is now (recog v) or (<equal-variant> a1 a2).

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
         (& nil))))

(defun add-tau-mv-nth-synonym-rule (rune hyps concl wrld)
  (declare (ignore hyps))
  (let* ((fn (ffn-symb (fargn concl 1)))
         (fns (global-val 'tau-mv-nth-synonyms wrld)))
    (cond ((member-eq fn fns)
           wrld)
          (t (set-tau-runes nil rune
                            (global-set 'tau-mv-nth-synonyms
                                        (cons fn fns)
                                        wrld))))))

; Now we define the functions for checking and adding tau rules

(defun acceptable-tau-rulep (pair wrld)
  (let ((hyps (car pair))
        (concl (cdr pair)))
    (cond
     ((tau-boolean-formp hyps concl wrld) 'BOOLEAN)
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

(defun chk-acceptable-tau-rule (name term ctx wrld state)
  (let ((pairs (unprettyify (remove-guard-holders term))))
    (cond
     ((acceptable-tau-rulesp :all pairs wrld)
      (value nil))
     ((null (cdr pairs))
      (er soft ctx
          "The formula of the theorem ~x0 fails to fit any of the forms for ~
           acceptable :TAU-SYSTEM rules.  See :DOC tau for the details of the ~
           acceptable forms."
          name))
     (t (er soft ctx
            "The formula of the theorem ~x0 gives rise to ~n1 normalized ~
             formulas (e.g., after stripping out conjuncts in the conclusion, ~
             etc.).  In order to be a :TAU-SYSTEM rule, each of these ~
             formulas must be acceptable as a tau rule and at least one of ~
             them fails to be.  See :DOC tau for details of the acceptable ~
             forms."
            name (length pairs))))))

; The Tau Msgp Protocol

; Several of the functions that add tau rules obey the Tau Msgp Protocol.  In
; that protocol, we return (mv msgp wrld), where msgp is either nil or an error
; message to be handled (signalled) by some caller of the function in question.
; When msgp is nil, wrld is the properly extended wrld.  When msgp is non-nil,
; wrld is the original wrld passed into the function, not some partially
; updated extension.  That is, functions obeying the msgp protocol are No
; Change Losers on wrld.  Most functions following the protocol take an
; additional argument, wrld0, as the ``good'' wrld to preserve.

; The reason we have the protocol is that we cannot always make tau rules out
; of previously approved :tau-system formulas because the ens has changed and
; some previously identified tau predicates are no longer identified as tau
; predicates.  This may or may not be an error, depending on lost-rune-action.
; When not an error, we just accumulate those lost runes on the global value of
; 'tau-lost-runes.  The possibility that we should actually signal an error
; arises when we are processing the original introduction of the :tau-system
; rule, where the explanation of the inadequacy of the syntactic check is due
; to it having been done in the first pass of an encapsulate that failed to
; export the Boolean property to the second pass where the error is to be
; signalled.  

(defun add-tau-rule1 (lost-rune-action rune pairs wrld wrld0)

; We try to convert each (hyps . concl) pair in pairs to a tau rule and extend
; wrld accordingly.  We obey the Tau Msgp Protocol and return (mv msgp wrld').
; Wrld0 is the original world we started with and will be returned in the error
; case, as per the protocol.  Pairs was derived by unprettyify from some
; :corollary for a rule named rune.

; Lost-rune-action determines what we do if we encounter a term that cannot be
; coded as a tau rule.  If lost-rune-action is IGNORE, we quietly ignore such
; terms.  If lost-rune-action is REPORT, we return a non-nil error message.
; This can happen if we're in the second pass of an encapsulate and discover
; that a predicate that was Boolean during the first pass is no longer known to
; be Boolean.  If lost-rune-action is ACCUMULATE then we add the rune of the lost
; rule to the 'tau-lost-runes list in wrld.

  (cond
   ((endp pairs) (mv nil wrld))
   (t (mv-let
       (msgp wrld)
       (let ((hyps (car (car pairs)))
             (concl (cdr (car pairs)))
             (kind (acceptable-tau-rulep (car pairs) wrld)))
         (case kind
           (BOOLEAN (mv nil (add-tau-boolean-rule rune hyps concl wrld)))
           (SIMPLE (mv nil (add-tau-simple-rule rune hyps concl wrld)))
           (CONJUNCTIVE (mv nil (add-tau-conjunctive-rule rune hyps concl wrld)))
           (SIGNATURE-FORM-1 (mv nil (add-tau-signature-rule rune 1 hyps concl wrld)))
           (SIGNATURE-FORM-2 (mv nil (add-tau-signature-rule rune 2 hyps concl wrld)))
           (BIG-SWITCH (mv nil (add-tau-big-switch-rule rune hyps concl wrld)))
           (MV-NTH-SYNONYM (mv nil (add-tau-mv-nth-synonym-rule rune hyps concl wrld)))
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
                    example, the local witness to some predicate might have ~
                    been Boolean but that fact was not exported as ~
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
        (t (add-tau-rule1 lost-rune-action rune (cdr pairs) wrld wrld0)))))))

; Tau todo:  Eliminate nume from this defun.  It is there only because
; of the call in add-x-rules, which should be eliminated too.

(defun add-tau-rule (first-visitp rune term wrld0)

; We convert term into tau rules, if possible.  We obey the Tau Msgp Protocol and
; return (mv msgp wrld'); No Change Loser on wrld0.

; First-visitp is t if this is the first time in this world that this rune has
; been visited.  What that really means is that tau is visiting the event that
; install-event is installing.  Otherwise, this is a re-visit of an event.
; Based on whether this is the first visit or not, we set lost-rune-action to
; REPORT, ACCUMULATE, or IGNORE to indicate what should be done if term cannot
; be represented as a tau rule.  REPORT means we'll report a non-nil msgp;
; ACCUMULATE means we just add rune to 'tau-lost-runes, and IGNORE means we
; just quietly ignore the situation.

  (let* ((pairs (unprettyify (remove-guard-holders term)))
         (lost-rune-action (if (eq (car rune) :tau-system) 
                               (if first-visitp
                                   'REPORT
                                   'ACCUMULATE)
                               'IGNORE)))
                                  
    (add-tau-rule1 lost-rune-action rune pairs wrld0 wrld0)))

; We now turn to the topic of ``visiting'' events and building up the tau data
; base.  Recall that we may be visiting an event for the first time (e.g., in
; the install-event just after it has been executed) or as part of a
; chronological sweep of the world to regenerate the tau data base under a
; different enabled structure.  But from tau's perspective, every visit to an
; event is (almost) like the first time.  This means that it must essentially
; erase any tau properties before starting to add the ``new'' ones.

; We have already defined tau-visit-function-introduction where we clear the
; tau properties of a function symbol.  This is not necessary on the first
; visit to a DEFUN because we know the symbol is new.  Furthermore, on an
; ENCAPSULATE event, it is too late to initialize the tau properties of the
; constrained functions when we see the encapuslate event!  So we visit
; function introductions when we see FORMALS properties stored on the world and
; we don't consider that part of the (re-)visits to events.

; What does tau learn by visiting a defined function?  (a) Whether the function
; is a tau predicate.  (b) Whether the function's type-prescription(s) are tau
; signature rules.  (c) Whether the function's definitional equation is a
; big-switch rule.  (d) Whether the function's definitional equation is an
; mv-nth-synonym.  The last three possibilities are contingent upon tau being
; in automatic mode and upon certain runes being enabled.

(defun discover-tau-pred (fn ens wrld)

; If fn is a monadic Boolean under ens, we initialize the tau properties for a
; tau predicate; else not.  We return the modified wrld.

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
; Loser and so if it signalled an error, we'd get back what we gave it.  But
; because this function is recursive and maps over tp-lst, it could be that
; what we gave add-tau-rule1 has already been extended.  

  (cond
   ((endp tp-lst)
    (mv nil wrld))
   ((and (eq (cadr (access type-prescription (car tp-lst) :rune)) fn)
         (enabled-numep (access type-prescription (car tp-lst) :nume) ens))
    (mv-let
     (term ttree)
     (convert-type-prescription-to-term (car tp-lst) ens wrld)
     (let ((pairs
            (acceptable-tau-rules (unprettyify (remove-guard-holders term))
                                  wrld)))
       (cond
        ((null pairs)
         (tau-rules-from-type-prescriptions (cdr tp-lst) fn ens
                                            wrld wrld0))
        (t (mv-let (msgp wrld)
                   (add-tau-rule1 'IGNORE ; this is a :TYPE-PRESCRIPTION rune so
                                          ; we can't count on it being of interest
                                  (access type-prescription
                                          (car tp-lst)
                                          :rune)
                                  pairs wrld wrld0)
           
; If msgp is non-nil, then x is nil and the attempt to add this rule caused an
; error as explained by msgp.  On the other hand, if msgp is nil, then x is the
; extended wrld.

                   (cond
                    (msgp 
                          
; We actually know here that wrld is wrld0 given that add-tau-rule1 is a No Change
; Loser, but just to be explicit:

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

  (original-def-body1 fn (getprop fn 'def-bodies nil 'current-acl2-world wrld)))

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
           (def-eqn
             (cond
              ((null db) nil)
              ((access def-body db :hyp) nil)
              (t
               (fcons-term* 'equal
                            (fcons-term fn (access def-body db :formals))
                            (access def-body db :concl)))))
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
              (t wrld))))
        (mv-let (msgp wrld)
                (tau-rules-from-type-prescriptions
                 (getprop fn 'type-prescriptions nil
                          'current-acl2-world wrld)
                 fn ens wrld wrld0)
                (cond
                 (msgp (mv msgp wrld0))
                 (t 
                  (tau-visit-defuns1 (cdr fns) ens wrld wrld0)))))))))

(defun tau-visit-defuns (fns auto-modep ens wrld0)

; This is the function the tau system uses to update the tau data base in
; response to a mutual-recursion event.  Every element of fns is a defined
; function in wrld0.  That means that each has all the properties one would
; expect of a defined function except the tau properties, which are determined
; below.  We assume that all tau properties of the fns in question are cleared
; (either because this is the first visit and the fns are all new or because we
; are in a tau regeneration and we have already visited the corresponding
; function introductions.

; We follow the Tau Msgp Protocol and return (mv msgp wrld').  No Change Loser
; on wrld0.
  
; We identify all the tau predicates before we start to process any other kind
; of tau rules, so that if a mutually recursive nest introduces several
; predicates, we treat them all appropriately when doing the syntactic checks
; for other rules.  We discover the tau predicates among defun'd functions
; whether or not we are in automatic mode.

  (let* ((wrld (discover-tau-preds fns ens wrld0)))

; Then, if in auto mode, gather the big-switch, mv-nth-synonym, and signature
; rules for each member of fns.

    (if auto-modep
        (tau-visit-defuns1 fns ens wrld wrld0)
        (mv nil wrld))))

(defun tau-visit-defun (fn auto-modep ens wrld0)

; This function updates the tau data base in response to a single defun.
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
; For example, perhaps a monadic predicate symbol that was previously
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
; been omited if the formula was the same as the 'theorem property of the
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

(defun tau-visit-defthm1 (first-visitp terms-and-runes wrld wrld0) 

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
                (add-tau-rule first-visitp rune term wrld)
                (cond
                 (msgp (mv msgp wrld0))
                 (t (tau-visit-defthm1 first-visitp
                                       (cdr terms-and-runes)
                                       wrld wrld0))))))))
                  
(defun tau-visit-defthm (first-visitp name auto-modep ens wrld0)

; This is the function the tau system uses to update the tau data base in
; response to a defthm event named name, which has been introduced into wrld0.
; We follow the Tau Msgp Protocol and return (mv msgp wrld').  No Change Loser
; on wrld0.

  (let* ((classes (getprop name 'classes nil 'current-acl2-world wrld0))
         (terms-and-runes
          (corollaries-and-runes-of-enabled-rules
           (or (not auto-modep)
               (assoc-eq :tau-system classes))
           classes
           (getprop name 'runic-mapping-pairs nil 'current-acl2-world wrld0)
           ens
           (getprop name 'theorem nil 'current-acl2-world wrld0))))
    (tau-visit-defthm1 first-visitp terms-and-runes wrld0 wrld0)))

(defun tau-visit-event (first-visitp ev-type namex auto-modep ens ctx wrld state)

; This is the function tau uses to visit an event that was carried out in wrld.
; It is assumed that all the function symbols encountered in this event are new
; to tau, because the function symbols were either all new or introductions
; were made chronologically earlier in world and visited by tau before getting
; here.

; First-timep is t if this function is being called from install-event and is
; nil if it is being called while regenerating the tau data base.  The flag
; affects whether we signal an error or quietly accumulate lost :tau-system
; runes.  Ev-type is the name of the primitive event macro that created the
; event.  The only values of interest to tau are DEFUN, DEFUNS, ENCAPSULATE,
; DEFCHOOSE, DEFTHM, and DEFAXIOM.  Namex is either a list of names, a single
; name, or 0 indicating the names introduced by the event (0 means no names
; were introduced).

; DEFSTOBJ introduces function symbols, some of which are even monadic
; Booleans.  But we ignore DFESTOBJ here.  Why?  Because all of the functions
; introduced by defstobj are introduced by embedded defun events and so we will
; find defun event-tuples for each.

; ENCAPSULATE introduces function symbols, some of which may be monadic
; Booleans or have other tau properties.  But all these properties are
; established by embedded defun/defthm events.

; DEFCHOOSE introduces a function symbol.  But at the time of this writing the
; constraint cannot possibly be of itnterest to tau.  For example, could a
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
        


    
    
;-----------------------------------------------------------------


; Now we mimic the code above to automatically detect and add
; tau rules.








; Now we consider how to recognize the theorems used to populate the data base
; and how to add each such theorem to the data base.


; -----------------------------------------------------------------
; Using Conjunctive and Signature Rules

(defun apply-conjunctive-tau-rule (tau1 tau2 wrld)

; This function checks the conditions for a conjunctive tau rule, tau1, to apply.
; It is given tau2, the set of all known recognizers.  It returns (mv
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
   (tau-near-subsetp tau1 tau2 wrld)
   (cond
    (contradictionp (mv t nil nil))

; Note:  If the rule didn't fire, the returned recog is nil, even though sign
; might be t.

    (t (mv nil (not sign) recog)))))
             
(defun apply-conjunctive-tau-rules2 (conjunctive-rules tau wrld changedp)

; We map over the list of conjunctive tau rules, trying each wrt the known
; recognizers in tau.  We extend tau as rules fire and set changedp if any rule
; fires.  We return (mv changedp tau'), where tau' may be *tau-contradiction*.
; We assume tau is not *tau-contradiction* to begin with!

  (cond
   ((endp conjunctive-rules) (mv changedp tau))
   (t (mv-let
       (contradictionp sign recog)
       (apply-conjunctive-tau-rule (car conjunctive-rules) tau wrld)
       (cond
        (contradictionp
         (mv t *tau-contradiction*))
        ((null recog)
         (apply-conjunctive-tau-rules2
          (cdr conjunctive-rules)
          tau wrld
          changedp))
        (t (mv-let
            (changedp1 tau)
            (add-to-tau sign recog tau wrld)
            (cond ((eq tau *tau-contradiction*)
                   (mv t *tau-contradiction*))
                  (t (apply-conjunctive-tau-rules2
                      (cdr conjunctive-rules)
                      tau
                      wrld
                      (or changedp changedp1)))))))))))

(defun apply-conjunctive-tau-rules1 (conjunctive-rules tau wrld)

; This function repeatedly applies conjunctive rules until no changes occur.
; It returns just the extended tau, which might be *tau-contradiction*.  We assume
; tau is not *tau-contradiction* to begin with!

  (mv-let (changedp tau)
          (apply-conjunctive-tau-rules2 conjunctive-rules tau wrld nil)
          (cond
           ((eq tau *tau-contradiction*)
            *tau-contradiction*)
           (changedp
            (apply-conjunctive-tau-rules1 conjunctive-rules tau wrld))
           (t tau))))

(defun apply-conjunctive-tau-rules (tau wrld)
  (cond ((eq tau *tau-contradiction*) *tau-contradiction*)
        (t
         (apply-conjunctive-tau-rules1
          (getprop 'tau-conjunctive-rules
                   'global-value
                   nil
                   'current-acl2-world wrld)
          tau
          wrld))))

(defun add-to-tau! (sign recog tau wrld)

; Recog is a tau-pair or singleton evg list.  Tau is a tau object,
; not *tau-contradiction*.  We add sign/recog, its implicants, and all conjunctive
; rules to tau.  We return tau', where tau' may be *tau-contradiction*.

  (mv-let (changedp tau)
          (add-to-tau sign recog tau wrld)
          (cond ((null changedp) tau)
                (t (apply-conjunctive-tau-rules tau wrld)))))
  
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
; just need to know whether a and b have appropriate tau.  If a rule fires, we
; just need to know the sign and recog for the value produced.  We don't
; actually need to know fn or i or even which form of rule we are applying.

(defun apply-signature-tau-rule (sigrule actual-tau-lst wrld)

; Sigrule is a signature-rule and so has a list of rec sets, called
; :input-tau-lst characterizing legal inputs and an output sign and recog,
; called :output-sign and :output-recog, characterizing the corresponding
; output of some expression involving those inputs.

; Actual-tau-lst is a list of n tau describing the actuals of a call
; of some fn where we found this rule.  We return (mv sign recog) or (mv nil
; nil), indicating whether sigrule applies to actual-tau-lst.

  (cond ((ok-to-fire-signature-rulep (access signature-rule sigrule :input-tau-list)
                                     actual-tau-lst
                                     wrld)
         (mv (access signature-rule sigrule :output-sign)
             (access signature-rule sigrule :output-recog)))
        (t (mv nil nil))))

(defun apply-signature-tau-rules1 (sigrules actual-tau-lst tau wrld)

; Sigrules is the list of signature-rules for some expression involving some
; actual expressions.  Actual-tau-lst is a list of n recognizer sets
; characterizing those actuals.  Several of the rules in sigrules may apply and
; we apply all that do and accumulate the resulting tau about the call of fn.
; We return tau', where tau' may be *tau-contradiction*.

  (cond
   ((eq tau *tau-contradiction*) *tau-contradiction*)
   ((endp sigrules) tau)
   (t (mv-let
       (sign recog)
       (apply-signature-tau-rule (car sigrules) actual-tau-lst wrld)
       (cond
        ((null recog)
         (apply-signature-tau-rules1 (cdr sigrules) actual-tau-lst tau wrld))
        (t (let ((tau (add-to-tau! sign recog tau wrld)))
             (cond
              ((eq tau *tau-contradiction*) *tau-contradiction*)
              (t (apply-signature-tau-rules1 (cdr sigrules)
                                             actual-tau-lst tau wrld))))))))))

(defun apply-signature-tau-rules (sigrules actual-tau-lst tau wrld)

; Sigrules is the list of signature-rules for some function application
; involving some actual expressions.  Actual-tau-lst is either
; *tau-contradiction* or a list of n recognizer sets characterizing those
; actuals.  If actual-tau-lst is *tau-contradiction* it means one of the actuals
; has a contradictory tau and we return the contradictory tau.  Otherwise, we use
; the rules in sigrules to compute the tau of function application.  Several of
; the rules in sigrules may apply and we apply all that do and accumulate the
; resulting tau about the call of fn.  We return tau', where tau' may be
; *tau-contradiction*.

  (cond ((eq actual-tau-lst *tau-contradiction*)
         *tau-contradiction*)
        (t (apply-signature-tau-rules1 sigrules actual-tau-lst tau wrld))))

(defun all-tau-emptyp (lst)
  (cond ((endp lst) t)
        (t (and (equal (car lst) *tau-empty*)
                (all-tau-emptyp (cdr lst))))))

(defun all-unrestricted-signature-rulesp (sigrules)

; In general, when we see (fn a1 ... an) we will obtain tau or the actuals,
; and then apply the signature rules of fn to (tau1 ... taun).  However, if all
; the rules for fn have unrestricted inputs, e.g., rules like: (fn *tau-empty*
; ... *tau-empty*) ==> sign/recog as happens for cons (consp), reverse
; (true-listp), member (boolean), etc., there no point in even getting the tau
; of the actuals.

  (cond ((endp sigrules) t)
        ((all-tau-emptyp (access signature-rule (car sigrules) :input-tau-list))
         (all-unrestricted-signature-rulesp (cdr sigrules)))
        (t nil)))


; -----------------------------------------------------------------

(defun tau-intersection (tau1 tau2)

; We intersect tau1 and tau2.  If neither is *tau-contradiction*, we don't have to
; worry about consistency because everything in the resulting tau is in both tau1
; and tau2, which are known to be consistent.  But it is possible that one or
; both of tau1 and tau2 is contradictory.  Think of *tau-contradiction* as denoting
; the (infinite) set of recognizers of both signs.  Then the intersection is
; the other set.

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
          (pos-pairs (intersection-equal
                      (access tau tau1 :pos-pairs)
                      (access tau tau2 :pos-pairs)))
          (neg-pairs (intersection-equal
                      (access tau tau1 :neg-pairs)
                      (access tau tau2 :neg-pairs))))
      (cond ((or pos-evg neg-evgs pos-pairs neg-pairs)
             (make tau
                   :pos-evg pos-evg
                   :neg-evgs neg-evgs
                   :pos-pairs pos-pairs
                   :neg-pairs neg-pairs))
            (t *tau-empty*))))))

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

(defun tau-expand-big-switch (body switch-var switch-tau var-alist wrld)

; Body is the body of a big switch function being applied to some actuals.
; Switch-var is the switch var of that switch, switch-val is the corresponding
; actual expression, and switch-tau is the tau of that actual.  It is assumed
; that switch-tau is not *tau-contradiction*.  Var-alist is the variable substitution
; mapping formals to actuals.  We partially evaluate body under the assumptions
; in tau-alist.  We return (mv hitp term') where hitp is T or NIL.  If hitp is
; T, term' is provably equal to body/var-alist under tau-alist.  If hitp is NIL,
; term' is NIL and irrelevant.  The heuristic we use to determine whether we
; hit or not is whether tau-alist allows us to navigate past all the switch
; tests.  We have arrived at a leaf if the body no longer mentions switch-var.
; This way we don't have to build the instantiation of any part of body except
; that leaf.

  (cond
   ((or (variablep body)
        (fquotep body)
        (not (eq (ffn-symb body) 'IF)))

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
            (let ((temp (reduce-sign/recog switch-tau sign recog wrld)))
              (cond
               ((eq temp t)
                (tau-expand-big-switch (fargn body 2)
                                       switch-var switch-tau var-alist wrld))
               ((eq temp nil)
                (tau-expand-big-switch (fargn body 3)
                                       switch-var switch-tau var-alist wrld))
               (t (mv nil nil)))))
           (t (mv nil nil)))))))

; -----------------------------------------------------------------
; Closing in On Tau-Term and Tau-Assume

; Because conjunction is treated as a special case in tau-assume, we must be
; able to deconstruct IFs that are really conjunctions.

(defun deconstruct-conjunction (sign a b c)

; Consider sign/(IF a b c).  There are four cases in which this is a conjunction.

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

(mutual-recursion

; Here are useful trace$ commands for tau-term and tau-assume:
#||
(trace$ (tau-term :entry
                  (list 'tau-term (car arglist) (decode-tau-alist (cadr arglist) nil))
                  :exit
                  (list 'tau-term (if (eq value *tau-contradiction*) value
                                      (decode-tau value (car arglist))))))

(trace$ (tau-assume :entry (list 'tau-assume
                                 (if (car arglist) 'positive 'negative)
                                 (cadr arglist)
                                 (decode-tau-alist (caddr arglist) nil))
                    :exit (list 'tau-assume
                                (if (nth 0 values) 'contradiction! nil)
                                (if (nth 1 values) 'must-be-true! nil)
                                (if (nth 2 values) 'must-be-false! nil)
                                (decode-tau-alist (nth 3 values) nil))))
||#

(defun tau-term (term tau-alist wrld)

; Basic Design of tau-term:

; Given a term and tau-alist we compute the tau of the term.  We return either
; a tau or *tau-contradiction* (meaning a contradiction has been detected in
; tau-alist and/or wrld).

; If a term is bound on tau-alist, we just look up its tau.  We do not implement
; the ``double-whammy'' idea of type-set.

; Tau-term gives special handling to certain function calls:

; - lambda applications: expand and recur.  This is as opposed to an Abstract
;   Interpretation approach where we might compute the tau of a lambda
;   application by computing the tau of the body under the alist pairing the
;   formals to the tau of the actuals.

; - IF: If the test must be true (or must be false) under tau-alist, compute the
;   tau of the appropriate branch; otherwise, compute the tau of each branch
;   under the appropriately augmented tau assumptions and then intersect the two
;   recognizer sets.

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

; - (fn ...) where fn has form 1 signature rules: compute the tau using all the
;   applicable signature rules under the current assumptions.  Thus, a
;   signature rule prevents us from considering the possibility that fn is a
;   big-switch.

; - (fn ...) where fn is a big switch: Expand (if heuristically allowed) and
;   recur

; - otherwise, *tau-empty*

  (let ((temp (assoc-equal term tau-alist)))
    (cond
     (temp (cdr temp))
     (t
      (cond
       ((variablep term) *tau-empty*)
       ((fquotep term)

; We avoid consing up two common cases.

        (cond ((equal term *t*)
               *tau-t*)
              ((equal term *nil*)
               *tau-nil*)
              (t

; Note that (cdr term) is a singleton evg list and thus a suitable pos-evg.

               (make tau
                     :pos-evg (cdr term)
                     :neg-evgs nil
                     :pos-pairs nil
                     :neg-pairs nil))))
       ((flambdap (ffn-symb term))

; We just expand lambdas.  This is in the spirit of our decision to expand
; nonrec fns when they don't have signature rules.

        (tau-term (subcor-var (lambda-formals (ffn-symb term))
                              (fargs term)
                              (lambda-body (ffn-symb term)))
                  tau-alist wrld))
       ((eq (ffn-symb term) 'IF)
        (mv-let
         (contradictionp mbt mbf tau-alist1)
         (tau-assume t (fargn term 1) tau-alist wrld)
         (cond
          (contradictionp *tau-contradiction*)
          (mbt
           (tau-term (fargn term 2) tau-alist wrld))
          (mbf
           (tau-term (fargn term 3) tau-alist wrld))
          (t (mv-let
              (contradictionp mbt mbf tau-alist2)
              (tau-assume nil (fargn term 1) tau-alist wrld)

; Can we get contradictionp, mbt, or mbf when we assume something false if we
; didn't get any of those when we assumed it true above?  Yes!  The reason is
; that T/(if a T b) is an OR but NIL/(if a T b) is an AND.  So when we assumed
; the term true, we did a completely different thing than when we assumed it
; false.

; If we get a contradiction, it is a contradiction in tau-alist or wrld and
; so we just pass that up.  If we get mbt from the assumption that the
; test is false, the test must be false, and vice versa for mbf.

              (cond
               (contradictionp *tau-contradiction*)
               (mbt ; note branch reversal below!
                (tau-term (fargn term 3) tau-alist wrld))
               (mbf ; note branch reversal below!
                (tau-term (fargn term 2) tau-alist wrld))
               (t (tau-intersection
                   (tau-term (fargn term 2) tau-alist1 wrld)
                   (tau-term (fargn term 3) tau-alist2 wrld)))))))))
       ((or (eq (ffn-symb term) 'MV-NTH)
            (member-eq (ffn-symb term)
                       (global-val 'tau-mv-nth-synonyms wrld)))
        (cond ((or (not (quotep (fargn term 1)))
                   (not (natp (cadr (fargn term 1)))))

; We are dealing with (MV-NTH x y), or a synonym of MV-NTH, where x is not a
; quoted natural.  We can't do anything with this.

               *tau-empty*)
              ((and (nvariablep (fargn term 2))
                    (not (fquotep (fargn term 2)))
                    (not (flambdap (ffn-symb (fargn term 2))))
                    (nth (cadr (fargn term 1))
                         (getprop (ffn-symb (fargn term 2))
                                  'signature-rules-form-2 nil
                                  'current-acl2-world wrld)))

; We are dealing with (MV-NTH 'i (fn a1 ... ak)), or a synonym of MV-NTH, where
; the ith slot of fn has some signature rules.  We confine our attention to
; those rules and do not consider expanding fn because no function with
; signature rules has a big-switch property.

               (let* ((fn (ffn-symb (fargn term 2)))
                      (sigrules (nth (cadr (fargn term 1))
                                     (getprop fn 'signature-rules-form-2 nil
                                              'current-acl2-world wrld))))
                 (apply-signature-tau-rules
                  sigrules
                  (if (all-unrestricted-signature-rulesp sigrules)
                      nil ; Abuse of Tau Representation
                      (tau-term-lst nil
                                    (fargs (fargn term 2))
                                    tau-alist wrld))
                  *tau-empty* wrld)))
              (t

; Otherwise, we are dealing with (MV-NTH 'i y), or a synonym of MV-NTH.  We
; first expand y, if possible.  If y is hit, then we push the MV-NTH down
; through any IFs thus revealed, and recur.  Note if we're actually dealing
; with a synonym of MV-NTH we still push MV-NTH, not the synonym, down.  This
; is ok because (a) we prefer MV-NTH and (b) we don't consider signature or
; other rules for synonyms.  So it doesn't really matter what mv-nth-synonym we
; push down.

               (mv-let (contradictionp hitp term1)
                       (tau-rewrite (fargn term 2) tau-alist wrld)
                       (cond
                        (contradictionp *tau-contradiction*)
                        (hitp (tau-term (push-mv-nth-down (fargn term 1) term1)
                                        tau-alist
                                        wrld))
                        (t *tau-empty*))))))
       (t
        (mv-let
         (sign recog e criterion)
         (tau-like-term term :various-any wrld)
         (declare (ignore criterion))
         (cond
          (recog

; We are dealing with sign/(recog e).

           (let ((tau (tau-term e tau-alist wrld)))
             (cond
              ((eq tau *tau-contradiction*) *tau-contradiction*)
              (t
               (let ((temp (reduce-sign/recog tau sign recog wrld)))
                 (cond
                  ((eq temp t)
                   *tau-t*)
                  ((eq temp nil)
                   *tau-nil*)
                  (t (getprop 'booleanp 'pos-implicants nil
                              'current-acl2-world wrld))))))))
          (t (let* ((fn (ffn-symb term))
                    (sigrules (getprop fn 'signature-rules-form-1 nil
                                       'current-acl2-world wrld)))
               (cond
                ((null sigrules)

; We are dealing with (fn a1 ... ak) and have no signature rules.  We expand,
; if possible, and recur.
              
                 (mv-let (contradictionp hitp term1)
                         (tau-rewrite term tau-alist wrld)
                         (cond
                          (contradictionp *tau-contradiction*)
                          (hitp (tau-term term1 tau-alist wrld))
                          (t *tau-empty*))))
                (t (apply-signature-tau-rules
                    sigrules
                    (if (all-unrestricted-signature-rulesp sigrules)
                        nil ; Abuse of Tau Representation
                        (tau-term-lst nil
                                      (fargs term)
                                      tau-alist wrld))
                    *tau-empty* wrld)))))))))))))

(defun tau-term-lst (vars terms tau-alist wrld)

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
   ((endp terms) nil)
   (t (let ((tau (tau-term (car terms) tau-alist wrld)))
        (cond
         ((eq tau *tau-contradiction*) *tau-contradiction*)
         (t (let ((taut (tau-term-lst (cdr vars) (cdr terms) tau-alist wrld)))
              (cond
               ((eq taut *tau-contradiction*) *tau-contradiction*)
               (t
                (cons (if vars (cons (car vars) tau) tau)
                      taut))))))))))

(defun tau-rewrite (term tau-alist wrld)

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
    (let* ((bs (getprop (ffn-symb term) 'big-switch nil 'current-acl2-world wrld)))
      (cond
       (bs
        (let* ((switch-val (nth (access big-switch-rule bs :switch-var-pos)
                                (fargs term)))
               (switch-tau (tau-term switch-val tau-alist wrld)))
          (cond
           ((eq switch-tau *tau-contradiction*)

; If any term, whether one we're looking at or one that someone dreams up, has a
; contradictory tau, then there is a contradiction in the system and/or tau-alist.
; Thus, the term we are looking at is contradictory too.

            (mv t nil term))
           ((equal switch-tau *tau-empty*)

; If we know nothing about the switch, then the attempt to expand it will
; fail.  Why bother?

            (mv nil nil term))
           (t (mv-let (hitp term1)
                      (tau-expand-big-switch
                       (access big-switch-rule bs :body)
                       (access big-switch-rule bs :switch-var)
                       switch-tau
                       (pairlis$ (access big-switch-rule bs :formals)
                                 (fargs term))
                       wrld)
                      (cond
                       (hitp (mv nil t term1))
                       (t (mv nil nil term))))))))
       (t (mv nil nil term)))))
   (t (mv nil nil term))))

(defun tau-assume-basic (sign term tau-alist wrld)

; Here is the generic way to assume an arbitrary term true in the tau system.
; Of course, recognizer terms get special treatment, as do conjunctions, lambda
; applications, and big switches.  But this generic processing is done in
; several places in tau-assume and it is helpful to package it up in a single
; function.

; We return (mv contradictionp mbt mbf tau-alist') and this is a No Change Loser
; on tau-alist.  If contradictionp is t, a contradiction in the system (tau-alist
; and wrld) has been detected.

; Note on sign: It may be easier to think of sign as controlling whether we
; want to assume term true (sign = t) or false (sign = nil) than it is to think
; of sign as modifying the term we're assuming true.  Furthermore, note that if
; the tau of term is tau1 and you want to assume term true (sign = t), you add
; NIL to the :NEG-EVGS of tau1; if you want to assume term false (sign = nil),
; you add NIL to the :POS-EVG.  So you add NIL to the ``evg'' component of the
; opposite sign.

  (let ((tau (tau-term term tau-alist wrld)))
    (cond
     ((eq tau *tau-contradiction*)
      (mv t nil nil tau-alist))
     (t (let ((tau1
               (add-to-tau! (not sign) *nil-singleton-evg-list* tau wrld)))

; Tau1 is the tau of sign/term with the ``additional'' fact that sign/term is
; non-NIL.  If we get a contradiction from that addition, then we already know
; that term is nil, so we signal mbf.  If we don't change anything, we already
; know term must be non-nil, so we signal mbt.  Otherwise, we return the new
; alist.

          (cond
           ((eq tau1 *tau-contradiction*)
            (mv nil nil t tau-alist))
           ((equal tau1 tau)
            (mv nil t nil tau-alist))
           (t (mv nil nil nil (cons (cons term tau1) tau-alist)))))))))

(defun tau-assume (sign term tau-alist wrld)

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
;   not ``x is a NATP, where x is the tau of A'' (whatever that means).

; - (IF a b NIL) and other forms of conjunction:  assume both conjuncts

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
       (tau-assume-basic sign term tau-alist wrld))
      ((flambdap (ffn-symb term))
       (tau-assume sign
                   (subcor-var (lambda-formals (ffn-symb term))
                               (fargs term)
                               (lambda-body (ffn-symb term)))
                   tau-alist wrld))
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
           (contradictionp mbt1 mbf1 tau-alist1)
           (tau-assume sign1 conjunct1 tau-alist wrld)
           (cond
            (contradictionp (mv t nil nil tau-alist))
            (mbf1 (mv nil nil t tau-alist))
            (t
             (mv-let
              (contradictionp mbt2 mbf2 tau-alist2)
              (tau-assume sign2 conjunct2 tau-alist1 wrld)
              (cond
               (contradictionp (mv t nil nil tau-alist))
               ((and mbt1 mbt2) (mv nil t nil tau-alist))
               (mbf2 (mv nil nil t tau-alist))
               (t (mv nil nil nil tau-alist2))))))))
         (t (let ((tau-test (tau-term (fargn term 1) tau-alist wrld)))
              (cond
               ((eq tau-test *tau-contradiction*)
                (mv t nil nil tau-alist))
               (t (let ((pos-evg (access tau tau-test :pos-evg)))
                    (cond
                     (pos-evg
                      (tau-assume sign
                                  (if (equal *nil-singleton-evg-list* pos-evg)
                                      (fargn term 3)
                                      (fargn term 2))
                                  tau-alist wrld))
                     ((lexorder-member *nil-singleton-evg-list*
                                       (access tau tau-test :neg-evgs))
                      (tau-assume sign (fargn term 2) tau-alist wrld))

; Note: It is still possible that the tau system could be used to determine
; that tau-test excludes nil!  How can this happen if nil is not among the
; neg-evgs?  It could be that there is a pos-pair for, say, INTEGERP, that
; rules nil out by evaluation.  Because we delete any neg-evg that is
; implicitly determined by the pos-pairs, we won't find an explicit nil in
; neg-evgs.  This ought to be fixed.  But at the moment we'll just let tau be
; this weak.
               
                     (t (tau-assume-basic sign term tau-alist wrld)))))))))))
      (t
       (mv-let
        (rsign recog e criterion)
        (tau-like-term term :various-any wrld)
        (declare (ignore criterion))
        (cond
         (recog
          (let* ((tau (tau-term e tau-alist wrld)))
            (cond
             ((eq tau *tau-contradiction*)
              (mv t nil nil tau-alist))
             (t
              (let* ((qsign (if sign rsign (not rsign)))

; Note:  sign/term = sign/(rsign/(recog e)) = (sign/rsign)/(recog e) = qsign/(recog e).

                     (temp (reduce-sign/recog tau qsign recog wrld)))
                (cond
                 ((eq temp t)
                  (mv nil t nil tau-alist))
                 ((eq temp nil)
                  (mv nil nil t tau-alist))
                 (t (let ((tau1 (add-to-tau! qsign recog tau wrld)))
                      (cond ((eq tau1 *tau-contradiction*)
                             (mv t nil nil tau-alist))
                            (t (mv nil nil nil
                                   (cons (cons e tau1) tau-alist))))))))))))
         (t (mv-let (contradictionp hitp term1)
                    (tau-rewrite term tau-alist wrld)
                    (cond
                     (contradictionp (mv t nil nil tau-alist))
                     (hitp (tau-assume sign term1 tau-alist wrld))
                     (t (tau-assume-basic sign term tau-alist wrld))))))))))))


)
           
; Note on a Possible Extension of Tau-Rewrite: We have considered adding other
; kinds of expansions, e.g., with ABBREVIATION rewrite rules or with
; unconditional ``nonrec'' DEFINITION rules.  We quote nonrec because sometimes
; alternative definitions have non-trivial recursivep fields, indicating that
; they are mutually recursive with other functions.  But sometimes these other
; functions are full fledged tau recognizers (now effectively disabled) and the
; ``recursive'' definition in question is just an abbreviation for some nest of
; those.  To handle this the tau data base would need to have a set of
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
; data base we create a set of unconditional rewrite rules only for those
; functions assigned some layer.  But until we see the need for this we will
; not add other forms of rewrite rules.

; Essay on Tau-Clause -- Using Tau to Prove or Mangle Clauses

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
; the following books were changed to support a regression with Tau System
; enabled.  The "i + j" notes in the left margins mean that i disablings of
; tau-system were inserted into the book to deal with literal deletion problems
; and j disablings were inserted to deal with subgoal renumbering problems or
; other more basic problems (e.g., coi/util/extra-info-test.lisp uses a
; must-fail event to show that a certain theorem is not provable while some
; things are disabled and tau must be among them!).

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
; type-set) we must be able to return to simplified clause to its original
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

(defun tau-clause1p (triples tau-alist wrld)

; Triples some tail of an annotated clause (that has been reordered by its key
; numbers).  Tau-alist assumes the falsity of every literal of the original
; reordered annotation preceding the first literal in triples.  We successively
; assume the falsity of every literal in triples.  We return either T or NIL,
; where T means the clause is true by tau reasoning and NIL means we could not
; prove it by tau reasoning.

  (cond
   ((endp triples) nil)
   (t (mv-let
       (contradictionp mbt mbf tau-alist)
       (tau-assume nil (caddr (car triples)) tau-alist wrld)

       (declare (ignore mbt))

; Note that we assume the truth of (NOT lit).  If (NOT lit) must be false, then
; lit must be true and the clause is true.  If (NOT lit) must be true, lit must
; be false and we can drop it from the clause.  If we get a contradiction then
; we can prove the clause is true.

       (cond
        (contradictionp t)
        (mbf t)
        (t (tau-clause1p (cdr triples) tau-alist wrld)))))))

; That tau system does not track lemmas.  However, when tau contributes to a
; proof we mark the ttree with the executable-counterpart of tau, which is also
; the rune that controls whether the tau system is enabled or disabled.  This
; constant ttree is used whenever tag contributes.  We exploit the fact that
; this constant is non-nil.

(defconst *tau-ttree*
  (add-to-tag-tree 'lemma '(:executable-counterpart tau-system) nil))

(defun tau-clause (clause ens wrld)

; This function returns (mv clause' ttree) where clause' is provably
; equivalent to clause by the tau rules.  If the executable-counterpart of tau
; is disabled, this function is a no-op.  The ttree returned is always either
; nil or contains the tag LEMMA containing just (:EXECUTABLE-COUNTERPART
; TAU-SYSTEM).  By testing the ttree result against nil you can determine
; whether clause changed.

  (cond
   ((enabled-numep *tau-system-xnume* ens)
    (let* ((triples (merge-sort-car-<
                     (annotate-clause-with-key-numbers clause (len clause) 0 wrld)))
           (ans (tau-clause1p triples nil wrld)))
      (cond
       ((eq ans t)
        (mv *true-clause* *tau-ttree*))
       (t (mv clause nil)))))
   (t (mv clause nil))))

(defun tau-clause-lst (clauses ens wrld ans ttree)

; We return (mv clauses' ttree) where clauses' are provably equivalent to
; clauses under the tau rules and ttree is either the tau ttree or nil
; depending on whether anything changed.  Note that this function knows that if
; tau-clause returns a non-nil ttree it is *tau-ttree*: we just OR the ttrees
; together, not CONS-TAG-TREES them!

  (cond
   ((endp clauses)
    (mv (revappend ans nil) ttree))
   (t (mv-let
       (clause1 ttree1)
       (tau-clause (car clauses) ens wrld)
       (tau-clause-lst (cdr clauses) ens wrld
                       (if (equal clause1 *true-clause*)
                           ans
                           (cons clause1 ans))
                       (or ttree1 ttree))))))

;---------------------------------------------------------------------------
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
   (t (let ((pos-size (tau-size (getprop (car preds) 'pos-implicants nil
                                         'current-acl2-world wrld)))
            (neg-size (tau-size (getprop (car preds) 'neg-implicants nil
                                         'current-acl2-world wrld))))
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

(defun tau-get-stats-on-signatures1 (fn wrld 
                                        fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
                                        multi-sig-cnt-1 multi-sig-cnt-2
                                        multi-sig-cnt-alist)
  (let ((sigs1 (getprop fn 'signature-rules-form-1 nil
                        'current-acl2-world wrld))
        (sigs2 (getprop fn 'signature-rules-form-2 nil
                        'current-acl2-world wrld)))
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
              (t multi-sig-cnt-alist))))
       (mv fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
           multi-sig-cnt-1 multi-sig-cnt-2 multi-sig-cnt-alist)))))

(defun tau-get-stats-on-signatures (fns wrld 
                                        fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
                                        multi-sig-cnt-1 multi-sig-cnt-2
                                        multi-sig-cnt-alist)
  (cond ((endp fns)
         `((:fns-with-signatures (:form-1-only ,fn-cnt-1)
                                 (:form-2-only ,fn-cnt-2)
                                 (:both-forms  ,fn-cnt-1-and-2))
           (:fns-with-multiple-sigs (:form-1 ,multi-sig-cnt-1)
                                    (:form-2 ,multi-sig-cnt-2))
           (:fn-with-multiple-sigs-details
            (fn form-1-cnt (mv slot-1-cnt dot-dot-dot slot-k-cnt))
            ,@multi-sig-cnt-alist)))
        (t (mv-let
            (fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
                      multi-sig-cnt-1 multi-sig-cnt-2 multi-sig-cnt-alist)
            (tau-get-stats-on-signatures1 (car fns) wrld
                                          fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
                                          multi-sig-cnt-1 multi-sig-cnt-2
                                          multi-sig-cnt-alist)
            (tau-get-stats-on-signatures (cdr fns) wrld 
                                         fn-cnt-1 fn-cnt-2 fn-cnt-1-and-2
                                         multi-sig-cnt-1 multi-sig-cnt-2
                                         multi-sig-cnt-alist)))))

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
       ,(length (getprop 'tau-conjunctive-rules 'global-value
                         nil 'current-acl2-world wrld)))
      ,@(tau-get-stats-on-signatures fns wrld 0 0 0 0 0 nil)
      (:big-switches ,(collect-tau-big-switches wrld nil))
      (:mv-nth-synonyms ,(global-val 'tau-mv-nth-synonyms wrld))
      (:tau-runes ,(len (global-val 'tau-runes wrld)))
      (:tau-lost-runes ,(len (global-val 'tau-lost-runes wrld))))))

(defmacro fancy-tau (&rest terms)
  `(convert-tau-like-terms-to-tau ',terms '(implies dots dots) (w state)))

(defun decode-recog (sign recog e)
  (cond ((cdr recog)
         (if sign
             `(,(cdr recog) ,e)
             `(not (,(cdr recog) ,e))))
        (sign
         `(equal ,e (quote ,@recog)))
        (t `(not (equal ,e (quote ,@recog))))))

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

(defun decode-tau-conjunctive-rule (tau)
  (cond
   ((eq tau *tau-contradiction*) nil)
   (t (let* ((terms (decode-tau1 tau 'v)))

; Terms ought to contain at least three literals if it is really a conjunctive rule.  
; It cannot be nil because of the test above.  If it contains just 1 literal
; it could be thought of as the pathological conjunctive rule (t & t) --> p,
; where tau is -p.  Similarly for two literals.

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
                 (decode-tau-alist (cdr alist) (cons (car (car alist)) seen))))))

(defun decode-tau-signature-rule (flg fn sr wrld)

; If flg is nil, we decode sr as a form 1 rule about (fn v1 ... vk).  If flg is
; non-nil, it is some natural i and we decode sr as a form 2 rule about (mv-nth
; i (fn v1 ... vk)).

  (cond
   ((and (symbolp fn)
         (arity fn wrld))
    (let* ((vars (formals fn wrld))
           (eterm (if (null flg)
                      `(,fn ,@vars)
                      `(mv-nth ,flg (,fn ,@vars))))
           (hyps (decode-tau-lst (access signature-rule sr :input-tau-list) vars))
           (concl-atm
            (cond ((cdr (access signature-rule sr :output-recog))
                   `(,(cdr (access signature-rule sr :output-recog)) ,eterm))
                  (t `(equal ,eterm
                             ,(kwote (car (access signature-rule sr :output-recog)))))))
           (concl (if (access signature-rule sr :output-sign)
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
                   (decode-tau-signature-rules2 (+ 1 i) fn (cdr mv-lst) wrld)))))

(defun decode-tau-signature-rules (flg fn sr-lst wrld)
  (let ((temp (cond ((null flg)
                     (decode-tau-signature-rules1 nil fn sr-lst wrld))
                    (t (decode-tau-signature-rules2 0 fn sr-lst wrld)))))
    (cond ((null temp) t)
          ((null (cdr temp)) (car temp))
          (t `(and ,@temp)))))

; If you execute this forms you get a self-explanatory printout.

; (tau-get-stats (w state))

; You can also write:

; (fancy-tau (not (equal x '23)) (natp x) (integerp x) (not (symbolp x)))

; to get a tau.  Be sure to quote the constants!  No translation is done for
; you.

; If you have a tau, you can print it as an untranslated term with (decode-tau
; tau 'v).  A variety of decoders are provided above, including for a list of
; tau, a tau-alist, a tau signature of either form, a list of signatures of
; either form, and (below) all the information tau knows about a function
; symbol.  See tau-data.

(defmacro tau-status (&key (system 'nil system-p) (auto-mode 'nil auto-mode-p))

  ":Doc-Section switches-parameters-and-modes

  query or set tau system status~/

  ~bv[]
  Examples:
  (tau-status)
  (tau-status :system t)
  (tau-status :auto-mode nil)
  (tau-status :system t :auto-mode nil)

  General Form:
  (tau-status :system a :auto-mode b)
  ~ev[]
  where ~c[a] and ~c[b] are Booleans.  Both keyword arguments are optional and
  they may be presented in either order.  Value ~c[a] controls whether the
  ~ilc[tau-system] is used during subsequent proofs.  Value ~c[b] controls
  whether the tau rules are automatically created as rules of other
  ~ilc[rule-classes] are added.~/

  There are two important flags associated with the ~ilc[tau-system]: (a)
  whether the tau system is used in proof attempts, and (b) whether the tau
  system is automatically extending its data base when other classes of rules
  are added.  These two flags are independent.  For example, the tau system may
  be disabled in proof attempts even though it is actively (and silently)
  extending its data base in as rules of other classes are added.

  This macro allows you to inspect or set the two flags.  Flag (a) is actually
  toggled by enabling or disabling the executable-counterpart of
  ~ilc[tau-system].  Flag (b) is toggled with the function
  ~ilc[set-tau-auto-mode], which manipulates the ~ilc[acl2-defaults-table].

  This macro expands into zero, one, or two ~il[events], as required by the
  supplied values of flags ~c[a] and ~c[b].

  If no arguments are supplied the form is not an event and simply returns (as
  an ``error triple'' ~c[(mv nil ans state)]) the current settings of the two
  flags.  For example:

  ~bv[]
  ACL2 !>(tau-system)
   ((:SYSTEM NIL) (:AUTO-MODE T))
  ~ev[]

  intended to be self-explanatory.~/"

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
  (cond
   ((and (symbolp fn)
         (arity fn wrld))
    (let ((tau-pair (getprop fn 'tau-pair nil 'current-acl2-world wrld))
          (sigs1 (getprop fn 'signature-rules-form-1 nil
                          'current-acl2-world wrld))
          (sigs2 (getprop fn 'signature-rules-form-2 nil
                          'current-acl2-world wrld))
          (big-switch (getprop fn 'big-switch nil 'current-acl2-world wrld))
          (mv-nth-synonym (member-eq fn (global-val 'tau-mv-nth-synonyms wrld))))
      (cond
       ((or tau-pair sigs1 sigs2 big-switch mv-nth-synonym)
        `(,fn
          (recognizer-index
           ,(car tau-pair))
          (pos-implicants
           ,(decode-tau
             (getprop fn 'pos-implicants *tau-empty* 'current-acl2-world wrld)
             'v))
          (neg-implicants
           ,(decode-tau
             (getprop fn 'neg-implicants *tau-empty* 'current-acl2-world wrld)
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
   (t nil)))

(defmacro tau-data (fn)

  ":Doc-Section History

  to see what tau knows about a function symbol~/

  ~bv[]
  Examples:
  (tau-data binary-+)

  General Form:
  (tau-data fn)
  ~ev[]

  This macro returns a list structure that indicates what facts about the
  function symbol ~c[fn] are known to the tau system.~/

  The list structure should be self-explanatory given the following brief
  comments.  The ``index'' of a function, when non-~c[nil], means the function
  is a monadic Boolean function treated by the tau system as a ``type.''

  The ``positive'' and ``negative implicants'' are conjunctions that indicate
  the ``types'' implied by the given one or its negation.

  The ``signatures'' entry is a formula indicating all the known signatures.
  If the signatures formula is ~c[T] it means there are no known signatures.
  (Signatures is the conjunction of all signature rules and the empty conjunction
  is ~c[T].)
  
  If you wish to see a long list of all the runes from which some tau 
  information has been gleaned, evaluate
  ~c[(global-val 'tau-runes (w state))]."

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
         (all-fnnames-world1 (cdr trips) logicp wrld (cons (car (car trips)) ans)))
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

(defun tau-data-base (wrld)
  
  ":Doc-Section History

  to see the tau data base as a (very large) object~/

  ~bv[]
  Example:
  (tau-data-base (w state))
  ~ev[]

  This function returns a large list object that shows in a human-readable way
  what the tau system knows about every function symbol.  It is supposed to
  be self-explanatory.~/

  If it is not, please contact the implementors and we will improve the output or
  the documentation."
  
  (tau-data-fns
   (merge-sort-lexorder (all-fnnames-world :logic wrld))
   wrld
   `((tau-next-index ,(global-val 'tau-next-index wrld))
     (tau-conjunctive-rules
      ,(decode-tau-conjunctive-rules
        (merge-sort-lexorder (global-val 'tau-conjunctive-rules wrld))))
     (tau-mv-nth-synonyms ,(merge-sort-lexorder (global-val 'tau-mv-nth-synonyms wrld)))
     (tau-runes ,(merge-sort-lexorder (global-val 'tau-runes wrld)))
     (tau-lost-runes ,(merge-sort-lexorder (global-val 'tau-lost-runes wrld))))))

; -----------------------------------------------------------------
; Regenerating the Tau Data Base

; Because tau does not track which runes it is using, disabling a rune has no
; effect on the inferences tau makes.  However, we do provide the ability to
; recompute the tau data base with respect to a given enabled structure.  This
; is an event command and we cannot actually define the entire event command
; until we have more infrastructure in place.  (The regenerate-tau-data-base
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
