; ACL2 Version 6.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2014, Regents of the University of Texas

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

; Arith-term-order

; As of Version_2.6, we now use a different term-order when ordering
; the alist of a poly.  Arith-term-order is almost the same as
; term-order (which was used previously) except that 'UNARY-/ is
; `invisible' when it is directly inside a 'BINARY-*.  The motivation
; for this change lies in an observation that, when reasoning about
; floor and mod, terms such as (< (/ x y) (floor x y)) are common.
; However, when represented within the linear-pot-lst, (BINARY-* X
; (UNARY-/ Y)) was a heavier term than (FLOOR X Y) and so the linear
; rule (<= (floor x y) (/ x y)) never got a chance to fire.  Now,
; (FLOOR X Y) is the heavier term.

; Note that this function is something of a hack in that it works
; because "F" is later in the alphabet than "B".  It might be better
; to allow the user to specify an order; but, if the linear rules
; present in the community books are representative this
; is sufficient.  Perhaps this should be reconsidered later.

;; RAG - I thought about adding lines here for real numbers, but since we
;; cannot construct actual real constants, I don't think this is
;; needed here.  Besides, I'm not sure what the right value would be
;; for a real number!

(defmacro fn-count-evg-max-val ()

; Warning: (* 2 (fn-count-evg-max-val)) must be a (signed-byte 30); see
; fn-count-evg-rec and max-form-count-lst.  Modulo that requirement, we just
; pick a large natural number rather arbitrarily.

  200000)

(defmacro fn-count-evg-max-val-neg ()
  (-f (fn-count-evg-max-val)))

(defmacro fn-count-evg-max-calls ()

; Warning: The following plus 2 must be a (signed-byte 30); see
; fn-count-evg-rec.

; Modulo that requirement, the choice of 1000 below is rather arbitrary.  We
; chose 1000 for *default-rewrite-stack-limit*, so for no great reason we
; repeat that choice here.

  1000)

#-acl2-loop-only
(declaim (inline min-fixnum))

(defun min-fixnum (x y)

; This is a fast version of min, for fixnums.  We avoid the name minf because
; it's already used in the regression suite.

  (declare (type (signed-byte 30) x y))
  (the (signed-byte 30) (if (< x y) x y)))

(defun fn-count-evg-rec (evg acc calls)

; See the comment in var-fn-count for an explanation of how this function
; counts the size of evgs.

  (declare (xargs :measure (acl2-count evg)
                  :ruler-extenders :all)
           (type (unsigned-byte 29) acc calls))
  (the
   (unsigned-byte 29)
   (cond
    ((or (>= calls (fn-count-evg-max-calls))
         (>= acc (fn-count-evg-max-val)))
     (fn-count-evg-max-val))
    ((atom evg)
     (cond ((rationalp evg)
            (cond ((integerp evg)
                   (cond ((< evg 0)
                          (cond ((<= evg (fn-count-evg-max-val-neg))
                                 (fn-count-evg-max-val))
                                (t (min-fixnum (fn-count-evg-max-val)
                                               (+f 2 acc (-f evg))))))
                         (t
                          (cond ((<= (fn-count-evg-max-val) evg)
                                 (fn-count-evg-max-val))
                                (t (min-fixnum (fn-count-evg-max-val)
                                               (+f 1 acc evg)))))))
                  (t
                   (fn-count-evg-rec (numerator evg)
                                     (fn-count-evg-rec (denominator evg)
                                                       (1+f acc)
                                                       (1+f calls))
                                     (+f 2 calls)))))
           #+:non-standard-analysis
           ((realp evg)
            (prog2$ (er hard? 'fn-count-evg
                        "Encountered an irrational in fn-count-evg!")
                    0))
           ((complex-rationalp evg)
            (fn-count-evg-rec (realpart evg)
                              (fn-count-evg-rec (imagpart evg)
                                                (1+f acc)
                                                (1+f calls))
                              (+f 2 calls)))
           #+:non-standard-analysis
           ((complexp evg)
            (prog2$ (er hard? 'fn-count-evg
                        "Encountered a complex irrational in ~ fn-count-evg!")
                    0))
           ((symbolp evg)
            (cond ((null evg) ; optimization: len below is 3
                   (min-fixnum (fn-count-evg-max-val)
                               (+f 8 acc)))
                  (t
                   (let ((len (length (symbol-name evg))))
                     (cond ((<= (fn-count-evg-max-val) len)
                            (fn-count-evg-max-val))
                           (t (min-fixnum (fn-count-evg-max-val)
                                          (+f 2 acc (*f 2 len)))))))))
           ((stringp evg)
            (let ((len (length evg)))
              (cond ((<= (fn-count-evg-max-val) len)
                     (fn-count-evg-max-val))
                    (t (min-fixnum (fn-count-evg-max-val)
                                   (+f 1 acc (*f 2 len)))))))
           (t ; (characterp evg)
            (1+f acc))))
    (t (fn-count-evg-rec (cdr evg)
                         (fn-count-evg-rec (car evg)
                                           (1+f acc)
                                           (1+f calls))
                         (+f 2 calls))))))

(defmacro fn-count-evg (evg)
  `(fn-count-evg-rec ,evg 0 0))

(defun var-fn-count-1 (flg x var-count-acc fn-count-acc p-fn-count-acc
                           invisible-fns invisible-fns-table)

; Warning: Keep this in sync with fn-count-1.

; We return a triple --- the variable count, the function count, and the
; pseudo-function count --- derived from term (and the three input
; accumulators).  "Invisible" functions not inside quoted objects are ignored,
; in the sense of the global invisible-fns-table.

; The fn count of a term is the number of function symbols in the unabbreviated
; term.  Thus, the fn count of (+ (f x) y) is 2.  The primitives of ACL2,
; however, do not give very natural expression of the constants of the logic in
; pure first order form, i.e., as a variable-free nest of function
; applications.  What, for example, is 2?  It can be written (+ 1 (+ 1 0)),
; where 1 and 0 are considered primitive constants, i.e., 1 is (one) and 0 is
; (zero).  That would make the fn count of 2 be 5.  However, one cannot even
; write a pure first order term for NIL or any other symbol or string unless
; one adopts NIL and 'STRING as primitives too.  It is probably fair to say
; that the primitives of CLTL were not designed for the inductive construction
; of the objects in an orderly way.  But we would like for our accounting for a
; constant to somehow reflect the structure of the constant rather than the
; structure of the rather arbitrary CLTL term for constructing it.  'A seems to
; have relatively little to do with (intern (coerce (cons #\A 'NIL) 'STRING))
; and it is odd that the fn count of 'A should be larger than that of 'STRING,
; and odder still that the fn count of "STRING" be larger than that of 'STRING
; since the latter is built from the former with intern.

; We therefore adopt a story for how the constants of ACL2 are actually
; constructed inductively and the pseudo-fn count is the number of symbols in
; that construction.  The story is as follows.  (z), zero, is the only
; primitive integer.  Positive integers are constructed from it by the
; successor function s.  Negative integers are constructed from positive
; integers by unary minus.  Ratios are constructed by the dyadic function quo
; on an integer and a natural.  For example, -2/3 is inductively built as (quo
; (- (s(s(z)))) (s(s(s(z))))).  Complex rationals are similarly constructed
; from pairs of rationals.  All characters are primitive and are constructed by
; the function of the same name.  Strings are built from the empty string, (o),
; by "string-cons", cs, which adds a character to a string.  Thus "AB" is
; formally (cs (#\A) (cs (#\B) (o))).  Symbols are constructed by "packing" a
; string with p.  Conses are conses, as usual.  Again, this story is nowhere
; else relevant to ACL2; it just provides a consistent model for answering the
; question "how big is a constant?"  (Note that we bound the pseudo-fn count;
; see fn-count-evg.)

; Previously we had made no distinction between the fn-count and the
; pseudo-fn-count, but Jun Sawada ran into difficulty because (term-order (f)
; '2).  Note also that before we had
; (term-order (a (b (c (d (e (f (g (h (i x))))))))) (foo y '2/3))
; but
; (term-order (foo y '1/2) (a (b (c (d (e (f (g (h (i x)))))))))).

  (declare (xargs :guard (and (if flg
                                  (pseudo-term-listp x)
                                (pseudo-termp x))
                              (integerp var-count-acc)
                              (integerp fn-count-acc)
                              (integerp p-fn-count-acc)
                              (symbol-listp invisible-fns)
                              (alistp invisible-fns-table)
                              (symbol-list-listp invisible-fns-table))
                  :verify-guards NIL))
  (cond
   (flg
    (cond
     ((atom x)
      (mv var-count-acc fn-count-acc p-fn-count-acc))
     (t
      (mv-let
       (var-cnt fn-cnt p-fn-cnt)
       (let* ((term (car x))
              (fn (and (nvariablep term)
                       (not (fquotep term))
                       (ffn-symb term)))
              (invp (and fn
                         (not (flambdap fn)) ; optimization
                         (member-eq fn invisible-fns))))
         (cond (invp (var-fn-count-1
                      t
                      (fargs term)
                      var-count-acc fn-count-acc p-fn-count-acc
                      (cdr (assoc-eq fn invisible-fns-table))
                      invisible-fns-table))
               (t (var-fn-count-1 nil term
                                  var-count-acc fn-count-acc p-fn-count-acc
                                  nil invisible-fns-table))))
       (var-fn-count-1 t (cdr x) var-cnt fn-cnt p-fn-cnt
                       invisible-fns invisible-fns-table)))))
   ((variablep x)
    (mv (1+ var-count-acc) fn-count-acc p-fn-count-acc))
   ((fquotep x)
    (mv var-count-acc
        fn-count-acc
        (+ p-fn-count-acc (fn-count-evg (cadr x)))))
   (t (var-fn-count-1 t (fargs x)
                      var-count-acc (1+ fn-count-acc) p-fn-count-acc
                      (and invisible-fns-table ; optimization
                           (let ((fn (ffn-symb x)))
                             (and (symbolp fn)
                                  (cdr (assoc-eq fn invisible-fns-table)))))
                      invisible-fns-table))))

(defmacro var-fn-count (term invisible-fns-table)

; See the comments in var-fn-count-1.

  `(var-fn-count-1 nil ,term 0 0 0 nil ,invisible-fns-table))

(defmacro var-or-fn-count-< (var-count1 var-count2 fn-count1 fn-count2
                                        p-fn-count1 p-fn-count2)

; We use this utility when deciding if an ancestors check should inhibit
; further backchaining.  It says that either the var-counts are in order, or
; else the fn-counts are in (lexicographic) order.

; We added the var-counts check after analyzing an example from Robert Krug, in
; which the ancestors check was refusing to allow relieve-hyp on a ground term.
; Originally we tried a lexicographic order based on the var-count first, then
; (as before) the fn-count and p-fn-count.  But this led to at least two
; regression failures that led us to reconsider.  The current solution meets
; the goal of weakening the ancestors check (for example, to allow backchaining
; on ground terms as in Robert's example).

  (declare (xargs :guard ; avoid capture
                  (and (symbolp var-count1)
                       (symbolp var-count2)
                       (symbolp fn-count1)
                       (symbolp fn-count2)
                       (symbolp p-fn-count1)
                       (symbolp p-fn-count2))))
  `(cond ((< ,var-count1 ,var-count2) t)
         ((< ,fn-count1 ,fn-count2) t)
         ((> ,fn-count1 ,fn-count2) nil)
         (t (< ,p-fn-count1 ,p-fn-count2))))

(defun term-order1 (term1 term2 invisible-fns-table)

; A simple -- or complete or total -- ordering is a relation satisfying:
; "antisymmetric" XrY & YrX -> X=Y, "transitive" XrY & Y&Z -> XrZ, and
; "trichotomy" XrY v YrX.  A partial order weakens trichotomy to "reflexive"
; XrX.

; Term-order1 is a simple ordering on terms.  (term-order1 term1 term2 nil) if
; and only if (a) the number of occurrences of variables in term1 is strictly
; less than the number in term2, or (b) the numbers of variable occurrences are
; equal and the fn-count of term1 is strictly less than that of term2, or (c)
; the numbers of variable occurrences are equal, the fn-counts are equal, and
; the pseudo-fn-count of term1 is strictly less than that of term2, or (d) the
; numbers of variable occurrences are equal, the fn-counts are equal, the
; pseudo-fn-counts are equal, and (lexorder term1 term2).  If the third
; argument is non-nil, then it has the form as returned by function
; invisible-fns-table, and in the same manner as the table of that name,
; specifies functions to ignore when doing the above counts.  However, for
; simplicity we use lexorder, independent of invisible-fns-table, if all the
; counts agree between the two terms.

; Moreover, we usually call term-order1 with a third argument of nil.  The third
; argument is new in Version_3.5, as a way of eliminating the
; arithmetic-specific counting functions that had been used in defining
; function arith-term-order.  It may be worth reconsidering our use of the
; wrapper term-order+ for term-order1 in loop-stopper-rec, now that a third
; argument of term-order1 makes it more flexible; but this seems unimportant.

; Fix a third argument, tbl, and let (STRICT-TERM-ORDER X Y) be the LISP
; function defined as (AND (TERM-ORDER1 X Y tbl) (NOT (EQUAL X Y))).  For a
; fixed, finite set of function symbols and variable symbols STRICT-TERM-ORDER
; is well founded, as can be proved with the following lemma.

; Lemma.  Suppose that M is a function whose range is well ordered by r and
; such that the inverse image of any member of the range is finite.  Suppose
; that L is a total order.  Define (LESSP x y) = (OR (r (M x) (M y)) (AND
; (EQUAL (M x) (M y)) (L x y) (NOT (EQUAL x y)))). < is a well-ordering.
; Proof.  Suppose ... < t3 < t2 < t1 is an infinite descending sequence. ...,
; (M t3), (M t2), (M t1) is weakly descending but not infinitely descending and
; so has a least element.  WLOG assume ... = (M t3) = (M t2) = (M t1).  By the
; finiteness of the inverse image of (M t1), { ..., t3, t2, t1} is a finite
; set, which has a least element under L, WLOG t27.  But t28 L t27 and t28 /=
; t27 by t28 < t27, contradicting the minimality of t27.  QED

; If (TERM-ORDER1 x y nil) and t2 results from replacing one occurrence of y
; with x in t1, then (TERM-ORDER1 t2 t1 nil).  Cases on why x is less than y.
; 1. If the number of occurrences of variables in x is strictly smaller than in
; y, then the number in t2 is strictly smaller than in t1.  2. If the number of
; occurrences of variables in x is equal to the number in y but the fn-count of
; x is smaller than the fn-count of y, then the number of variable occurrences
; in t1 is equal to the number in t2 but the fn-count of t1 is less than the
; fn-count of t2.  3. A similar argument to the above applies if the number of
; variable occurrences and fn-counts are the same but the pseudo-fn-count of x
; is smaller than that of y.  4. If the number of variable occurrences and
; parenthesis occurrences in x and y are the same, then (LEXORDER x y).
; (TERM-ORDER1 t2 t1 nil) reduces to (LEXORDER t2 t1) because the number of
; variable and parenthesis occurrences in t2 and t1 are the same.  The
; lexicographic scan of t1 and t2 will be all equals until x and y are hit.

  (mv-let (var-count1 fn-count1 p-fn-count1)
          (var-fn-count term1 invisible-fns-table)
          (mv-let (var-count2 fn-count2 p-fn-count2)
                  (var-fn-count term2 invisible-fns-table)
                  (cond ((< var-count1 var-count2) t)
                        ((> var-count1 var-count2) nil)
                        ((< fn-count1 fn-count2) t)
                        ((> fn-count1 fn-count2) nil)
                        ((< p-fn-count1 p-fn-count2) t)
                        ((> p-fn-count1 p-fn-count2) nil)
                        (t (lexorder term1 term2))))))

(defun arith-term-order (term1 term2)
  (term-order1 term1 term2 '((BINARY-* UNARY-/))))


(defun fn-count-1 (flg x fn-count-acc p-fn-count-acc)

; Warning: Keep this in sync with the var-fn-count-1.

; This definition is similar to var-fn-count-1, except that it counts only fns
; and pseudo-fns, not vars.  It was introduced when a check of fn-counts was
; added to ancestors-check1, in order to improve efficiency a bit.  (We now use
; var-fn-count for that purpose.)  A 2.6% decrease in user time (using Allegro
; 5.0.1) was observed when the fn-counts check was added, yet that test was
; found to be critical in certain cases (see the comment in ancestors-check1).

; We discovered that the Allegro compiler does not do as good a job at tail
; recursion elimination for mutual recursion nests as for single recursion.  So
; we code this as a singly recursive function with a flag, flg:  When flg is
; nil then x is a term, and otherwise x is a list of terms.  We have since also
; taken advantage of the use of this single "flag" function when verifying
; termination and guards.

  (declare (xargs :guard (and (if flg
                                  (pseudo-term-listp x)
                                (pseudo-termp x))
                              (integerp fn-count-acc)
                              (integerp p-fn-count-acc))
                  :verify-guards NIL))
  (cond (flg
         (cond ((atom x)
                (mv fn-count-acc p-fn-count-acc))
               (t
                (mv-let (fn-cnt p-fn-cnt)
                        (fn-count-1 nil (car x) fn-count-acc p-fn-count-acc)
                        (fn-count-1   t (cdr x) fn-cnt p-fn-cnt)))))
        ((variablep x)
         (mv fn-count-acc p-fn-count-acc))
        ((fquotep x)
         (mv fn-count-acc
             (+ p-fn-count-acc (fn-count-evg (cadr x)))))
        (t (fn-count-1 t (fargs x) (1+ fn-count-acc) p-fn-count-acc))))

(defmacro fn-count (term)
  `(fn-count-1 nil ,term 0 0))

(defun term-order (term1 term2)

; See term-order1 for comments.

  (term-order1 term1 term2 nil))

(defun remove-invisible-fncalls (term invisible-fns)

; Given a term and a list of unary function symbols considered invisible,
; strip off all the invisible outermost function symbols from the term.

  (cond
   ((or (variablep term)
        (fquotep term)
        (flambda-applicationp term))
    term)
   ((member-eq (ffn-symb term) invisible-fns)
    (remove-invisible-fncalls (fargn term 1) invisible-fns))
   (t term)))

(defun term-order+ (x1 x2 invisible-fns)

; See the doc string for loop-stopper to find an implicit description
; of this function.  See the comment below for a proof that this
; function is a total order, provided term-order is a total order.

  (let ((x1-guts (remove-invisible-fncalls x1 invisible-fns))
        (x2-guts (remove-invisible-fncalls x2 invisible-fns)))
    (cond
     ((equal x1-guts x2-guts)
      (term-order x1 x2))
     (t
      (term-order x1-guts x2-guts)))))

; We wish to prove that term-order+ is a total ordering on terms, which,
; recall, means that it is antisymmetric, transitive, and enjoys the trichotomy
; property.  However, because term-order+ and its main subroutine, term-order,
; are :program functions we cannot do this directly without reclassifying them.
; In addition, we would first need to prove the lemma that term-order is a
; total ordering.  Rather than undertake such a large proof effort, we attack a
; slightly different problem.  The basic idea is to constrain the new functions
; xtermp, xterm-order, and xremove-invisible-fncalls to have the properties we
; are willing to assume about the corresponding :program functions.  In
; particular, we assume that xterm-order is a total ordering on xtermps and
; that xremove-invisible-fncalls preserves xtermp.  Then we define xterm-order+
; analogously to the definition above of term-order+ and we prove that
; xterm-order+ is a total ordering on xterms.


; Introduce xtermp, xterm-order and xremove-invisible-fncalls by constraint.
; Observe that in the three properties characterizing xterm-order as a total
; ordering we restrict our claims to the cases where only xtermps are involved.
; We also require that xremove-invisible-fncalls preserve xtermp.

;   (encapsulate (((xtermp *) => *)
;                 ((xterm-order * *) => *)
;                 ((xremove-invisible-fncalls * *) => *))

; We witness xtermp with rationalp, xterm-order with <= on the rationals,
; and xremove-invisible-fncalls by the identify function.

;    (local (defun xtermp (x) (rationalp x)))
;    (local (defun xterm-order (x y)
;             (and (xtermp x) (xtermp y) (<= x y))))
;    (local (defun xremove-invisible-fncalls (x lst) (declare (ignore lst)) x))

; Here we establish that xremove-invisible-fncalls preserves xtermp.

;    (defthm xtermp-xremove-invisible-fncalls
;      (implies (xtermp x) (xtermp (xremove-invisible-fncalls x lst))))

; We now prove the three total ordering properties.  In each case we
; state the property elegantly and then store it as an effective
; rewrite rule.

;    (defthm antisymmetry-of-xterm-order
;      (implies (and (xtermp x)
;                    (xtermp y)
;                    (xterm-order x y)
;                    (xterm-order y x))
;               (equal x y))
;
;      :rule-classes
;      ((:rewrite :corollary
;                 (implies (and (xtermp x)
;                               (xtermp y)
;                               (xterm-order x y)
;                               (xterm-order y x))
;                          (equal (equal x y) t)))))
;
;    (defthm transitivity-of-xterm-order
;      (implies (and (xtermp x)
;                    (xtermp y)
;                    (xtermp z)
;                    (xterm-order x y)
;                    (xterm-order y z))
;               (xterm-order x z))
;
;      :rule-classes
;      ((:rewrite :corollary
;                 (implies (and (xtermp x)
;                               (xterm-order x y)
;                               (xtermp y)
;                               (xtermp z)
;                               (xterm-order y z))
;                          (xterm-order x z)))))
;
;    (defthm trichotomy-of-xterm-order
;      (implies (and (xtermp x)
;                    (xtermp y))
;               (or (xterm-order x y) (xterm-order y x)))
;
;      :rule-classes
;      ((:rewrite :corollary
;                 (implies (and (xtermp x)
;                               (xtermp y)
;                               (not (xterm-order x y)))
;                          (xterm-order y x))))))

; Introduce the derived order, xterm-order+, that transduces with
; xremove-invisible-fncalls.  This is exactly analogous to the definition
; of term-order+ above.

;    (defun xterm-order+ (x1 x2 invisible-fns)
;     (let ((x1-guts (xremove-invisible-fncalls x1 invisible-fns))
;           (x2-guts (xremove-invisible-fncalls x2 invisible-fns)))
;       (cond
;        ((equal x1-guts x2-guts)
;         (xterm-order x1 x2))
;        (t
;         (xterm-order x1-guts x2-guts)))))

; Prove the three properties of xterm-order+, restricted to the xtermp cases.

;    (defthm antisymmetry-of-xterm-order+
;     (implies (and (xtermp x)
;                   (xtermp y)
;                   (xterm-order+ x y invisible-fns)
;                   (xterm-order+ y x invisible-fns))
;              (equal x y))
;     :rule-classes nil)
;
;    (defthm transitivity-of-xterm-order+
;     (implies (and (xtermp x)
;                   (xtermp y)
;                   (xtermp z)
;                   (xterm-order+ x y invisible-fns)
;                   (xterm-order+ y z invisible-fns))
;              (xterm-order+ x z invisible-fns)))
;
;    (defthm trichotomy-of-xterm-order+
;     (implies (and (xtermp x)
;                   (xtermp y))
;              (or (xterm-order+ x y invisible-fns)
;                  (xterm-order+ y x invisible-fns)))
;     :rule-classes nil)



(defun merge-term-order (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((term-order (car l1) (car l2))
         (cons (car l1) (merge-term-order (cdr l1) l2)))
        (t (cons (car l2) (merge-term-order l1 (cdr l2))))))

(defun merge-sort-term-order (l)
  (cond ((null (cdr l)) l)
        (t (merge-term-order (merge-sort-term-order (evens l))
                             (merge-sort-term-order (odds l))))))



(defun merge-arith-term-order (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((arith-term-order (car l2) (car l1))
         (cons (car l2) (merge-arith-term-order l1 (cdr l2))))
        (t (cons (car l1) (merge-arith-term-order (cdr l1) l2)))))

(defun insert-arith-term-order (item list)
  (cond ((null list)
         (list item))
        ((arith-term-order item (car list))
         (cons item list))
        (t
         (cons (car list)
               (insert-arith-term-order item (cdr list))))))

(defun sort-arith-term-order (list)
  (cond ((null list)
         nil)
        (t
         (insert-arith-term-order (car list)
                                  (sort-arith-term-order (cdr list))))))

