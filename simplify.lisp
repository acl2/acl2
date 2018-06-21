; ACL2 Version 8.0 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2017, Regents of the University of Texas

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

; A quick sketch of the three main functions here

; We renamed these functions because their nqthm names were confusing to
; one of us.

; ACL2                   Nqthm
; simplify-clause        SIMPLIFY-CLAUSE
; simplify-clause1       SIMPLIFY-CLAUSE0
; rewrite-clause         SIMPLIFY-CLAUSE1

; Simplify-clause is the top-level clause simplifier but it does
; relatively little work.  It merely determines what to expand and
; what not to, taking into account induction as described in comments
; in simplify-clause.  The real workhorse of simplify-clause is its
; subroutine, simplify-clause1.

; Simplify-clause1 is non-recursive.  It does an enormous amount of
; clause level work: removing trivial equations, detecting
; propositional tautologies with type-set, setting up the
; simplify-clause-pot-lst for the later literal-by-literal-rewriting,
; detecting linear arithmetic tautologies, and retrieving useful
; equalities from the linear arithmetic pot-lst.  Once all that has
; happened, it calls rewrite-clause which begins the classic sweep of
; the clause rewriting each literal.

; Rewrite-clause is concerned only with rewriting the literals of a
; clause.  It does not do any clause level work aside from that
; necessary to avoid tail biting.  It rewrites each lit in turn,
; clausifies the result into a bunch of segments and splices them into
; the evolving set of answers.

; In this section we develop rewrite-clause.

; Note: The following two functions are no longer called.  The were
; called before we made type-set track dependencies.  However, after
; that change, we found the burden of passing up the ttrees generated
; below to be so off-putting that we eliminated their calls in favor
; of dumb-negate-lit and a no-op.  It is our belief that these changes
; do not seriously weaken the system.  Comments indicating the changes
; contain calls of the two functions so these decisions can be
; reconsidered.

(defun negate-lit (term type-alist ens force-flg wrld)

; This function returns a term equivalent to (not term) under the
; given type-alist and wrld.  It also returns a ttree justifying this
; result.

; Note Added After This Function Became Obsolete: Because
; known-whether-nil now may generate 'assumptions, negate-lit may
; generate 'assumptions.  Thus, use of this function is even more
; problematic since the ttrees not only must be tracked but the
; necessary case splits done.

  (mv-let (knownp nilp ttree)
          (known-whether-nil term type-alist ens force-flg
                             nil ; dwp
                             wrld nil)
          (cond (knownp
                 (cond (nilp (mv *t* ttree))
                       (t (mv *nil* ttree))))
                (t (mv (dumb-negate-lit term) nil)))))

(defun pegate-lit (term type-alist ens force-flg wrld)

; Like negate-lit but returns a term equivalent to term, and a ttree.

; Note Added After This Function Became Obsolete: Because
; known-whether-nil now may generate 'assumptions, negate-lit may
; generate 'assumptions.  Thus, use of this function is even more
; problematic since the ttrees not only must be tracked but the
; necessary case splits done.

  (mv-let (knownp nilp ttree)
          (known-whether-nil term type-alist ens force-flg
                             nil ; dwp
                             wrld nil)
          (cond (knownp
                 (cond (nilp (mv *nil* ttree))
                       (t (mv *t* ttree))))
                (t (mv term nil)))))

; Rockwell Addition:  Now we know hard-error returns nil too.

(defun add-literal (lit cl at-end-flg)

; We add lit to clause cl, optionally at the end as per the flag.
; We assume that lit has been subjected to rewriting modulo the geneqv
; iff.  Therefore, though we check lit against *t* and *nil* we do
; not do more powerful type-set reasoning.  In addition, we know that
; (hard-error ctx str alist) is logically nil.

  (cond ((quotep lit)
         (cond ((equal lit *nil*) cl)
               (t *true-clause*)))
        ((equal cl *true-clause*) *true-clause*)
        ((member-complement-term lit cl) *true-clause*)
        ((variablep lit)
         (cond ((member-term lit cl) cl)
               (at-end-flg (append cl (list lit)))
               (t (cons lit cl))))
; Now we can take the ffn-symb of lit.
        ((eq (ffn-symb lit) 'hard-error)

; (Hard-error ctx str alist) = nil.

         cl)
        ((and (eq (ffn-symb lit) 'rationalp)
              (member-complement-term1 (fcons-term 'integerp (fargs lit))
                                       cl))
         *true-clause*)
        ((and (eq (ffn-symb lit) 'not)
              (ffn-symb-p (fargn lit 1) 'integerp)
              (member-equal (fcons-term 'rationalp (fargs (fargn lit 1))) cl))
         *true-clause*)
        ((member-term lit cl) cl)
        (at-end-flg (append cl (list lit)))
        (t (cons lit cl))))

(defun add-each-literal (cl)
  (cond ((null cl) nil)
        (t (add-literal (car cl)
                        (add-each-literal (cdr cl))
                        nil))))

; By definition, clause cl1 subsumes clause cl2 provided some instance of cl1
; is a subset of cl2.  Operationally, we think of finding a suitable
; substitution, alist.  But this involves search since a given literal, lit1,
; of cl1 might be instantiated so that it becomes one of several literals in
; cl2, and which instantiation we choose depends on how we can similarly get
; the rest of cl1's literals ``absorbed.''

; We augment subsumption to handle the special case of clauses containing
; (EQUAL x 'const1) atoms.  First, note that cl1 subsumes cl2 below:

; cl1:  ((equal x 'const1) p...)
; cl2:  ((not (equal x 'const2)) p... q...)

; In particular, modulo the instantiation done for subsumption, subsumption
; just checks the truth of (IMPLIES (OR . cl1) (OR . cl2)).  But cl2 may be
; thought of as (IMPLIES (equal x 'const2) (OR p... q...)) and thus we are
; checking

; (IMPLIES (AND (equal x 'const2) (OR (equal x 'const1) p...))
;          (OR p... q...))

; which is the same as

; (IMPLIES (AND (equal x 'const2) (OR p...))
;          (OR p... q...))

; and hence true.

; To check this thinking for sanity, consider a specific application.  Suppose
; we have proved cl1: (or (equal x 'const1) (p x)), and we are later confronted
; by cl2: (or (not (equal A 'const2)) (p A) (q A)).  Are we justified in saying
; that the proved theorem establishes cl2?  Yes.  Think of cl1 as a rewrite
; rule: (implies (not (equal x 'const1)) (iff (p x) t)).  Now consider
; rewriting (p A) in cl2.  You may assume the falsity of the other literals of
; cl2.  So we have (equal A 'const2).  Backchain with cl1.  We must prove (not
; (equal A 'const1)), which is true because A is 'const2.

; So how extend subsumption to handle instantiation of an
; ``equality-with-a-constant''?  First recall the basic subsumption algorithm.
; We think of a literal lit2 from cl2 as ``absorbing'' a literal lit1 of cl1 if
; there is an extension of the current unify substitution alist such that
; lit1/alist is lit2.  Then we say that cl1 subsumes cl2 if for every literal
; lit1 of cl1 there is a literal lit2 of cl2 that absorbs it so that the rest
; of the literals of cl1 are subsumed.  To extend this basic idea to handle
; equality-with-constants we extend the notion of absorption.  We say (NOT
; (EQUAL a const2)) absorbs (EQUAL x const1) if const1 and const2 are distinct
; constants and x unifies with a.  This is implemented in the function
; subsumes!1-equality-with-const below.

; We code two versions of subsumption.  One, subsumes-rec fails after a certain
; specified number of unification calls.  The other, subsumes!-rec has no such
; limit.  They must be kept in sync.  Both handle the special case of
; equalities with constants and of the dummy EXTRA-INFO literal.

(mutual-recursion

(defun subsumes-rec (count cl1 cl2 alist)

; Keep this nest in sync with the subsumes!-rec nest, which is similar except
; that there is no restriction (count) on the number of one-way-unify1 calls.

; We return a positive or negative integer, according to whether or not
; (respectively) some instance of cl1 via an extension of alist is a subset of
; clause cl2.  In either case, the absolute value n of that integer is at most
; count, and (- count n) is the number of one-way-unify1 calls that were made.
; Otherwise we return 0, indicating that we could not determine subsumption
; using fewer than count such calls.

; Here is why subsumes-rec and subsumes1 take a "count" argument to limit the
; number of calls:

; Note that in the worst case, checking whether clause2 of length len2 is an
; instance of clause1 of length len1 is roughly on the order of len2^len1.  For
; suppose every term in each clause is (integerp x) for a distinct x, except
; that the last term in the first clause is not a match for any member of the
; second clause.  Then each (integerp x) in clause1 can be matched against any
; (integerp y) in clause2, so we have len2*len2*...*len2, len1-1 times.

  (declare (type (signed-byte 30) count))
  (the (signed-byte 30)
       (cond ((eql count 0) 0)
             ((null cl1) count)
             ((extra-info-lit-p (car cl1))
              (subsumes-rec count (cdr cl1) cl2 alist))
             ((ffn-symb-p (car cl1) 'EQUAL)
              (cond ((quotep (fargn (car cl1) 1))
                     (subsumes1-equality-with-const count
                                                    (car cl1)
                                                    (fargn (car cl1) 2)
                                                    (fargn (car cl1) 1)
                                                    (cdr cl1) cl2 cl2 alist))
                    ((quotep (fargn (car cl1) 2))
                     (subsumes1-equality-with-const count
                                                    (car cl1)
                                                    (fargn (car cl1) 1)
                                                    (fargn (car cl1) 2)
                                                    (cdr cl1) cl2 cl2 alist))
                    (t (subsumes1 count (car cl1) (cdr cl1) cl2 cl2 alist))))
             (t (subsumes1 count (car cl1) (cdr cl1) cl2 cl2 alist)))))

(defun subsumes1-equality-with-const (count lit x const1 tl1 tl2 cl2 alist)
  (the
   (signed-byte 30)
   (cond ((eql count 0) 0)
         ((null tl2) (-f count))
         ((extra-info-lit-p (car tl2))
          (subsumes1-equality-with-const count lit x const1 tl1 (cdr tl2) cl2 alist))
         ((and (ffn-symb-p (car tl2) 'NOT)
               (ffn-symb-p (fargn (car tl2) 1) 'EQUAL))
          (let ((arg1 (fargn (fargn (car tl2) 1) 1))
                (arg2 (fargn (fargn (car tl2) 1) 2)))
            (cond ((and (quotep arg1)
                        (not (equal arg1 const1)))
                   (mv-let
                     (wonp alist1)
                     (one-way-unify1 x arg2 alist)
                     (cond ((not wonp)
                            (subsumes1-equality-with-const (1-f count) lit x const1 tl1 (cdr tl2) cl2 alist))
                           (t (let ((new-count (subsumes-rec (1-f count) tl1 cl2 alist1)))
                                (cond ((<= 0 new-count) new-count)
                                      (t (subsumes1-equality-with-const (-f new-count)
                                                                        lit x const1 tl1 (cdr tl2)
                                                                        cl2 alist))))))))
                  ((and (quotep arg2)
                        (not (equal arg2 const1)))
                   (mv-let
                     (wonp alist1)
                     (one-way-unify1 x arg1 alist)
                     (cond ((not wonp)
                            (subsumes1-equality-with-const (1-f count)
                                                           lit x const1 tl1 (cdr tl2) cl2 alist))
                           (t (let ((new-count (subsumes-rec (1-f count) tl1 cl2 alist1)))
                                (cond ((<= 0 new-count) new-count)
                                      (t (subsumes1-equality-with-const (-f new-count)
                                                                        lit x const1 tl1 (cdr tl2)
                                                                        cl2 alist))))))))
                  (t (subsumes1-equality-with-const count lit x const1 tl1 (cdr tl2) cl2 alist)))))
         (t (mv-let
              (wonp alist1)
              (one-way-unify1 lit (car tl2) alist)
              (cond ((not wonp)
                     (subsumes1-equality-with-const (1-f count) lit x const1 tl1 (cdr tl2) cl2 alist))
                    (t (let ((new-count (subsumes-rec  (1-f count) tl1 cl2 alist1)))
                         (cond
                          ((<= 0 new-count) new-count)
                          (t (subsumes1-equality-with-const (-f new-count) lit x const1 tl1 (cdr tl2) cl2 alist)))))))))))

(defun subsumes1 (count lit tl1 tl2 cl2 alist)

; Keep this nest in sync with the subsumes!-rec nest, which is similar except
; that there is no restriction (count) on the number of one-way-unify1 calls.

; If we can extend alist to an alist1 so that lit/alist1 is a member of tl2 and
; tl1/alist1 is a subset of cl2, we return a positive integer obtained by
; decreasing count by the number of one-way-unify1 calls.  If we determine that
; there is no such alist, we return a negative integer whose absolute value is
; obtained by decreasing count as above.  But, if the number of one-way-unify1
; calls necessary is not less than count, we return 0.

  (declare (type (signed-byte 30) count))
  (the (signed-byte 30)
       (cond ((eql count 0) 0)
             ((null tl2) (-f count))
             ((extra-info-lit-p (car tl2))
              (subsumes1 count lit tl1 (cdr tl2) cl2 alist))
             (t (mv-let
                 (wonp alist1)
                 (one-way-unify1 lit (car tl2) alist)
                 (cond
                  ((not wonp)
                   (subsumes1 (1-f count) lit tl1 (cdr tl2) cl2 alist))
                  (t
                   (let ((new-count (subsumes-rec (1-f count) tl1 cl2 alist1)))
                     (declare (type (signed-byte 30) new-count))
                     (cond ((<= 0 new-count) new-count)
                           (t (subsumes1 (-f new-count) lit tl1 (cdr tl2) cl2
                                         alist)))))))))))

)

(mutual-recursion

(defun subsumes!-rec (cl1 cl2 alist)

; Keep this nest in sync with the subsumes1 nest, which is similar except that
; there is a restriction (count) on the number of one-way-unify1 calls.

; We return t if some instance of cl1 via an extension of alist is a subset of
; clause cl2, otherwise nil.

  (cond ((null cl1) t)
        ((extra-info-lit-p (car cl1))
         (subsumes!-rec (cdr cl1) cl2 alist))
        ((ffn-symb-p (car cl1) 'EQUAL)
         (cond ((quotep (fargn (car cl1) 1))
                (subsumes!1-equality-with-const (car cl1)
                                                (fargn (car cl1) 2)
                                                (fargn (car cl1) 1)
                                                (cdr cl1) cl2 cl2 alist))
               ((quotep (fargn (car cl1) 2))
                (subsumes!1-equality-with-const (car cl1)
                                                (fargn (car cl1) 1)
                                                (fargn (car cl1) 2)
                                                (cdr cl1) cl2 cl2 alist))
               (t (subsumes!1 (car cl1) (cdr cl1) cl2 cl2 alist))))
        (t (subsumes!1 (car cl1) (cdr cl1) cl2 cl2 alist))))

(defun subsumes!1-equality-with-const (lit x const1 tl1 tl2 cl2 alist)
  (cond ((null tl2) nil)
        ((extra-info-lit-p (car tl2))
         (subsumes!1-equality-with-const lit x const1 tl1 (cdr tl2) cl2 alist))
        ((and (ffn-symb-p (car tl2) 'NOT)
              (ffn-symb-p (fargn (car tl2) 1) 'EQUAL))
         (let ((arg1 (fargn (fargn (car tl2) 1) 1))
               (arg2 (fargn (fargn (car tl2) 1) 2)))
           (cond ((and (quotep arg1)
                       (not (equal arg1 const1)))
                  (mv-let
                   (wonp alist1)
                   (one-way-unify1 x arg2 alist)
                   (cond ((and wonp (subsumes!-rec tl1 cl2 alist1))
                          t)
                         (t (subsumes!1-equality-with-const lit x const1 tl1 (cdr tl2) cl2 alist)))))
                 ((and (quotep arg2)
                       (not (equal arg2 const1)))
                  (mv-let
                   (wonp alist1)
                   (one-way-unify1 x arg1 alist)
                   (cond ((and wonp (subsumes!-rec tl1 cl2 alist1))
                          t)
                         (t (subsumes!1-equality-with-const lit x const1 tl1 (cdr tl2) cl2 alist)))))
                 (t (subsumes!1-equality-with-const lit x const1 tl1 (cdr tl2) cl2 alist)))))
        (t (mv-let
            (wonp alist1)
            (one-way-unify1 lit (car tl2) alist)
            (cond ((and wonp (subsumes!-rec tl1 cl2 alist1))
                   t)
                  (t (subsumes!1-equality-with-const lit x const1 tl1 (cdr tl2) cl2 alist)))))))

(defun subsumes!1 (lit tl1 tl2 cl2 alist)

; Keep this nest in sync with the subsumes1 nest, which is similar except that
; there is a restriction (count) on the number of one-way-unify1 calls.

; If we can extend alist to an alist1 so that lit/alist1 is a member of tl2 and
; tl1/alist1 is a subset of cl2, we return t; otherwise, nil.

  (cond ((null tl2) nil)
        ((extra-info-lit-p (car tl2))
         (subsumes!1 lit tl1 (cdr tl2) cl2 alist))
        (t (mv-let
            (wonp alist1)
            (one-way-unify1 lit (car tl2) alist)
            (cond ((and wonp (subsumes!-rec tl1 cl2 alist1))
                   t)
                  (t (subsumes!1 lit tl1 (cdr tl2) cl2 alist)))))))

)

(defconst *init-subsumes-count*
  (the (signed-byte 30)

; The following value is rather arbitrary, determined by experimentation so
; that subsumes doesn't run for more than a small fraction of a second on a
; 2.6GH P4 (depending on the underlying Lisp).  The following takes about 0.04
; seconds to return '? (signaling that we have done 1,000,000 calls of
; one-way-unify1) on that machine using GCL 2.6.7 and about 0.17 seconds using
; Allegro CL 7.0.

; (subsumes 1000000
;           '((integerp x1) (integerp x2) (integerp x3) (integerp x4)
;             (integerp x5) (integerp x6) (integerp x7) (integerp x8)
;             (foo a))
;           '((integerp x1) (integerp x2) (integerp x3) (integerp x4)
;             (integerp x5) (integerp x6) (integerp x7) (integerp x8))
;           nil)

       1000000))

(defun subsumes (init-subsumes-count cl1 cl2 alist)

; If init-subsumes-count is not nil, then it is a nonnegative integer
; specifying a strict upper bound on the number of one-way-unify1 calls.  See
; the comment in subsumes-rec for an explanation of why we may want this bound.

; If the return value is t, then we can extend alist to a substitution s such
; that cl1/s is a subset of cl2.  If the return value is nil, then we cannot
; thus extend alist.  Otherwise (only possible if init-subsumes-count is not
; nil), the return value is '?, in which case we could not make such a
; determination with fewer than init-subsumes-count one-way-unify1 calls.

  (cond
   ((time-limit5-reached-p
     "Out of time in subsumption (subsumes).") ; nil, or throws
    nil)
   ((null init-subsumes-count)
    (subsumes!-rec cl1 cl2 alist))
   (t (let ((temp (subsumes-rec init-subsumes-count cl1 cl2 alist)))
        (cond ((eql temp 0)
               '?)
              (t (< 0 temp)))))))

(defun some-member-subsumes (init-subsumes-count cl-set cl acc)

; Returns t if some member of cl-set subsumes cl, acc if no member of cl-set
; subsumes cl, and '? (only possible if init-subsumes-count is non-nil) if we
; don't know.

  (cond ((null cl-set) acc)
        (t (let ((temp (subsumes init-subsumes-count (car cl-set) cl nil)))
             (cond
              ((eq temp t))
              (t (some-member-subsumes init-subsumes-count (cdr cl-set) cl
                                       (or temp acc))))))))

(defun equal-mod-commuting-lst (cl1 cl2)
  (cond ((endp cl1) (endp cl2))
        ((endp cl2) nil)
        (t (and (equal-mod-commuting (car cl1) (car cl2) nil)
                (equal-mod-commuting-lst (cdr cl1) (cdr cl2))))))

(defun member-equal-mod-commuting-lst (cl cl-set)

; Consider the following definition (which could be shortened, but equivalent,
; by calling mbt*).

;   (defun foo (x)
;     (declare (xargs :guard (and (integerp x)
;                                 (< 10 x))))
;     (mbe :logic t
;          :exec (mbe :logic (car (cons (< 5 x) t))
;                     :exec t)))

; The naively generated guard proof obligation is as follows.

;   (AND (IMPLIES (AND (< 10 X) (INTEGERP X))
;                 (EQUAL (CAR (CONS (< 5 X) T)) T))
;        (IMPLIES (AND (< 10 X) (INTEGERP X))
;                 (EQUAL T (CAR (CONS (< 5 X) T)))))

; We would like to avoid generating one of those two clauses, and we can do so
; by checking that the two clauses are equal except perhaps for commuted
; equalities and calls of iff.  (We could allow calls of equivalence relations
; too, but then we would need to pass in the world and, more significantly, we
; would feel obligated to track equivalence relations by passing back a tag
; ttree.)  The present function is essentially (member-equal cl cl-set), except
; that equality is tested using equal-mod-commuting-lst: thus, some member of
; cl-set is identical to cl except that literals can be commuted as explained
; above.

  (cond ((endp cl-set) nil)
        ((equal-mod-commuting-lst cl (car cl-set)) t)
        (t (member-equal-mod-commuting-lst cl (cdr cl-set)))))

(defun conjoin-clause-to-clause-set (cl cl-set)

; Once upon a time, in particular, in the two weeks before January 25,
; 1990, we did a subsumption check here.  The idea was that if cl was
; subsumed by some member of cl-set, don't add it and if it subsumes
; some member of cl-set, delete that member.  That caused unsoundness.
; The reason is that cl-set is not a set of clauses that is
; necessarily going to be proved.  For example, cl-set may contain a
; collection of clause segments to which we will eventually add some
; additional hypotheses.  If cl-set contains the clause segment ((P
; I)) and then we conjoin the clause segment ((P (F X))) to it, we
; don't want the first segment to subsume the second because we may
; eventually add the additional hypothesis (INTEGERP I) to all the
; segments.

  (cond ((member-equal *t* cl) cl-set)
        ((member-equal-mod-commuting-lst cl cl-set) cl-set)
        (t (cons cl cl-set))))

(defun add-each-literal-lst (cl-set)
  (cond ((null cl-set) nil)
        (t (conjoin-clause-to-clause-set
            (add-each-literal (car cl-set))
            (add-each-literal-lst (cdr cl-set))))))

(defun conjoin-clause-sets (cl-set1 cl-set2)
  (cond ((null cl-set1) cl-set2)
        (t (conjoin-clause-to-clause-set
            (car cl-set1)
            (conjoin-clause-sets (cdr cl-set1) cl-set2)))))

(defun some-element-member-complement-term (lst1 lst2)
  (cond ((null lst1) nil)
        ((member-complement-term (car lst1) lst2) t)
        (t (some-element-member-complement-term (cdr lst1) lst2))))

; Rockwell Addition: We used to just stick them together.  Now we add
; each literal to catch cases like hard-error.

(defun disjoin-clauses1 (cl1 cl2)

; This is equivalent to (append cl1 (set-difference-equal cl2 cl1))
; except that we add each literal with add-literal to check for
; complementary pairs, etc.

; Note: This function repeatedly adds literals from cl2 to cl1, at the
; end.  So it copies cl1's spine as many times as there are literals
; to add.  We used to use the append formulation above but found that
; complementary pairs were being missed once we extended the notion of
; complementary to include rational v integer.

  (cond ((endp cl2) cl1)
        (t (disjoin-clauses1 (add-literal (car cl2) cl1 t)
                             (cdr cl2)))))

(defun disjoin-clauses (cl1 cl2)
  (cond ((or (equal cl1 *true-clause*)
             (equal cl2 *true-clause*))
         *true-clause*)
        ((null cl1) cl2)
        ((null cl2) cl1)
        (t (disjoin-clauses1 cl1 cl2))))

; See comment in disjoin-clause-segment-to-clause-set.
; (defun disjoin-clause-segment-to-clause-set-rec (segment cl-set acc)
;   (cond ((null cl-set) acc)
;         (t (disjoin-clause-segment-to-clause-set-rec
;             segment
;             (cdr cl-set)
;             (conjoin-clause-to-clause-set
;              (disjoin-clauses segment (car cl-set))
;              acc)))))

(defun disjoin-clause-segment-to-clause-set (segment cl-set)

; This code is not tail-recursive, but it could be.  At one time it caused
; stack overflow problems in LispWorks 4.2.0.  Below is some alternate code,
; with a reverse call in order to provide unchanged functionality.  Would we
; gain efficiency by eliminating tail recursion at the cost of that reverse
; call?  Maybe.  A clearer win would be to avoid the reverse call, which should
; be logically OK but could change the prover's behavior, thus invalidating huge
; portions of the regression suite.

; The alternate code is simply the following line, in place of all that
; follows:
; (disjoin-clause-segment-to-clause-set-rec segment (reverse cl-set) nil)

  (cond ((null cl-set) nil)
        (t (conjoin-clause-to-clause-set
            (disjoin-clauses segment (car cl-set))
            (disjoin-clause-segment-to-clause-set segment (cdr cl-set))))))

(defun split-on-assumptions (assumptions cl ans)

; Cl is a clause and ans is a set of clauses that will be our answer.
; Assumptions is a list of literals.  For each lit in assumptions
; we add a new clause to ans, obtained by adding lit to cl.

  (cond ((null assumptions) ans)
        (t (split-on-assumptions
            (cdr assumptions)
            cl
            (conjoin-clause-to-clause-set
             (add-literal (car assumptions) cl nil)
             ans)))))

(defun rewrite-clause-action (lit branches)

; Lit is a term. Branches is the result of clausifying the result of
; rewriting lit.  We want to know if anything has happened.  The table
; below indicates our result:

; branches      result            meaning
;  {}          'shown-true      Lit was rewritten and clausified to
;                               the empty set, i.e., lit is T under our
;                               assumptions.
;  {NIL}       'shown-false     Lit was rewritten and clausified to
;                               the set containing the empty clause, i.e.,
;                               lit is NIL under our assumptions.
;  {{lit}}     'no-change       Neither rewrite nor clausify did anything.

;  otherwise   'change

  (cond ((consp branches)
         (cond ((null (cdr branches))
                (cond ((null (car branches))
                       'shown-false)
                      ((and (null (cdr (car branches)))
                            (equal lit (car (car branches))))
                       'no-change)
                      (t 'change)))
               (t 'change)))
        (t 'shown-true)))

; Forward Chaining

; ACL2 implements a rudimentary form of forward chaining -- though it is
; getting less rudimentary as time goes on!  Its primary use is at the
; top-level of clause simplification (simplify-clause1), where before we begin
; to rewrite the literals of the clause (and in the same place we set up the
; simplify-clause-pot-lst), we forward chain from the negations of the literals
; of the clause and construct a list of all the (heuristically approved)
; conclusions we can derive.  Each concl is paired with a tree that contains
; the 'lemma and 'pt dependencies.  That list of pairs is passed down to the
; rewrite-clause level, where it is used to augment the type-alist before
; rewriting any given literal.

; This is the fourth (or fifth, depending on how you count) version of forward
; chaining.  For an extensive comment on version II, see the historical plaque
; after the definition of rewrite-clause-type-alist.  (There are also
; historical plaques elsewhere in this code.)

; The top-level interface to forward chaining is the function named
; forward-chain.  However, forward-chain just calls forward-chain-top with one
; more argument, a token identifying the caller.  We tend to use
; forward-chain-top in our code so that a sensible caller is known.  But we
; provide forward-chain, with caller 'miscellaneous, mainly for builders of
; tools.

; Besides its use in simplify-clause1, forward-chain-top is called in several
; other places, including built-in-clausep (which is used in preprocess-clause
; and indirectly in defun's prove-termination), bdd-clause (which is used when
; we apply :bdd hints), get-induction-cands-from-cl-set1 (used in firing
; induction rules while computing induction schemes), and hyps-type-alist (used
; in show-rewrites).  All of these provide sensible caller tokens.  The caller
; is only relevant to the trace-like reporting facility.

; Basic Ideas and Terminology

; Forward chaining is implemented by the function forward-chain-top.  At the
; highest level, think of forward chaining as ``activating'' all the forward
; chaining rules triggered by the terms in the problem and then ``advancing''
; each activation in the context of a type-alist that tells us all the things
; we know.  An activation is actually an object with fields such as the
; instantiated hypothesis we're trying to relieve, the remaining hyps, the
; unify substitution, etc.  To advance an activation we check each
; (instantiated) hyp successively against the type-alist with type-set.  If we
; reach the end of the hyps, we know the conclusions of the rule are all true.
; We record each such deduced conclusion as an ``fc-derivation,'' aka an
; ``fcd,'' a kind of record.  (Note that just because we create an fcd does not
; mean we will incorporate it into our assumptions.  More on this below.)  If
; we reach a hyp whose truth is not known under the current type-alist, we
; ``suspend'' the activation.  Of course, if a hyp is found to be false, we
; simply drop the activation.  We must also handle the branching caused by free
; vars in a hyp -- which causes an activation to split into several different
; activations under each of the possible matches for the free vars plus to
; remain suspended in case additional matches arise later.

; When we have advanced all the activations we have a list of still-suspended
; activations and a list of forward-chaining derivations deduced so far.  We
; then heuristically decide which of the derivations to keep.  This is called
; ``approving'' the derivations and is imposed to prevent pumps like (implies
; (p x) (p (f x))) from causing infinite forward chaining.  Thus, one must be
; careful to distinguish ``fcds'' from ``approved fcds,'' a subset of the
; former though there is no indicator in the fc-derivation record to indicate
; that an fcd has been approved.  A key heuristic in approving an fcd is that
; the derived conclusion should not be worse than any conclusion used in its
; derivation.  This means we must be able to determine which conclusions were
; used in the derivation of another one.  We do that rather cheaply by
; embedding ttrees in fc-derivations.  These ttrees are tainted from the
; perspective of the rest of the code, because they have dependencies buried
; inside them.  We discuss this when we introduce them but it gives rise to
; such notions as an ``fcd-free'' ttree -- that is, a normal ttree as opposed
; to one with fc-derivations containing other ttrees in it -- and ``expunging''
; the fc-derivations from a non-fcd-free ttree to get an fcd-free ttree.  The
; forward chaining module traffics in non-fcd-free ttrees but ultimately
; returns fcd-free ttrees and type-alists that may be used in the rest of the
; prover.

; Once we have collected the approved derivations, we assume them all obtaining
; a new type-alist.  It is at that point that we process the disjunction
; triples, possibly shrinking some clauses or even deducing some new
; conclusions and getting a new type-alist.  During the processing we assume
; that if an fcd was approved then any disjunct in it is approved.  Thus, the
; fcds produced by eliminating all but one literal in a clause is added to the
; list of approved fcds.  Since the newly added conclusions may contain new
; terms, we add more activations to our list of suspended activations.  Then we
; start another ``round'' in which we try again to advance the suspended
; activations in the context of the new type-alist.

; The notion of a round is implemented by forward-chain1.  The top-level
; forward chain just sets up the initial type-alist and the initial activations
; and calls forward-chain1, and then expunges and elaborates the type-alist a
; little.  The notion of advancing an activation is implemented by a nest of
; three functions named advance-fc-activation1, 2, and 3, which roughly put,
; are designed to relieve a single hyp, relieve a list of hyps, and relieve
; hyps under a multiplicity of matches for free-vars.  Advancing an
; fc-activation introduces the notion of a ``virtual activation'' to avoid
; consing up activation objects as we move from hyp to hyp, for example.  A
; virtual activation, v, is an ordinary activation object, o, together with
; values held in certain local variables of the ``advance-fc-activation''
; functions; the actual activation represented by v could be obtained by
; writing those values to their respective fields in o.  But we don't do that
; until it is time to suspend the virtual activation because we get blocked.

; Finally, we also squirrel away certain data in a wormhole, named
; ``fc-wormhole'' to allow us to create a ``report'' on what happened in
; forward chaining.  Because forward chaining is called in several places and
; is an algorithm (like resolution) in which things are happening on many
; fronts (activations) at once, rather than a real-time trace-like facility we
; provide an after-the-fact reporting facility.

; We repeat some of this introductory material as we develop the code.  We also
; provide prettyify-fc-activation and prettyify-fc-derivation for debugging
; purposes even though they are not used in this code.  Prettyify-fc-derivation
; is particularly useful because it builds a decent representation of the
; derivation tree of conclusion produced by forward chaining and thus can help
; you understand fc-derivations and what has actually happened in a proof
; attempt.

; A forward chaining rule is (not defined in rewrite.lisp):

; (defrec forward-chaining-rule
;   ((rune . nume) trigger hyps concls . match-free) nil)

; One of the main inefficiencies in our earlier forward chaining schemes
; was that if a rule began to fire but misfired because some hyp could
; not be relieved, we would reconsider firing it later and redo the work
; associated with the misfire.  We avoid that by storing what we call a
; "forward chaining activation" record which permits us to suspend the
; attempt to fire a rule and resume it later.

(defrec fc-activation
  (inst-hyp (hyps . ttree)
            unify-subst inst-trigger . rule) t)

; Warning:  Despite the name, inst-hyp is not necessarily a term!
; See below.

; Warning: If you reorder the fields or add new ones, reconsider
; suspend-fc-activation, which is designed to save conses by exploiting
; the layout.  Suspend-fc-activation is correct independently of the
; order of the fields, but may not actually save conses if they're
; rearranged.

; An fc-activation represents an attempt to apply the given
; forward-chaining-rule.  Suppose a term of interest unifies with the
; trigger term of some rule.  Then we try to relieve the hypotheses of
; that rule, using the current set of assumptions coded in a type-alist.
; Imagine that we relieve all those up to but not including hypn,
; producing an extended unify substitution and a ttree recording the
; dependencies so far.  But then we learn that hypn is not yet
; definitely nil or definitely non-nil.  Since the list of assumptions
; is growing, we may be able eventually to establish hypn.  Therefore,
; instead of just quitting and starting over we suspend the attempted
; application of rule by producing an fc-activation record containing
; our current state.

; The current :unify-subst, :ttree and :rule are stored in the slots of
; those names.  The :inst-trigger is the term in the current problem
; that fired this rule.  What about :inst-hyps and :hyps?  What do they
; hold?  There are two cases of interest depending on whether the hyp we
; are stuck on (hypn above) contains free variables under unify-subst.

; :Inst-hyp is just hypn/unify-subst if hypn contains no free variables
; wrt unify-subst.  In that case, :hyps is the cdr of the rule's hyps
; starting immediately after hypn.  Furthermore, :inst-hyp is never an
; evaluable ground term (or else we would have evaluated it) or a FORCE
; or CASE-SPLIT (or else we would have forced or split on it).  That is,
; :inst-hyp is a term that must be true under type-alist to proceed, and
; :hyps contains the hyps we must relieve after relieving inst-hyp.  (We
; cannot get stuck on a hypothesis that is forced or split unless it
; contains free variables.  So we never build an activation stuck on
; such a hyp.)

; :Inst-hyp is a special marker, called the :FC-FREE-VARS marker, if
; hypn contains free variables wrt unify-subst.  In this case, :hyps is
; the cdr of the rule's hyps starting with the problematic hypn.  The
; :FC-FREE-VARS marker looks like this and so is not a term:

;   (:FC-FREE-VARS forcer-fn  . last-keys-seen)

; Forcer-fn is nil if the hyp is not to be forced, and is either FORCE
; or CASE-SPLIT otherwise.  (By providing for forcer-fn we can isolate
; the handling of free vars into one piece of code.  Observe how
; advance-fc-activation2 calls advance-fc-activation1 when the hyp in
; question has free vars.)   The FORCE or CASE-SPLIT annotation will have
; been stripped off of the car of :hyps, so that what is there is what
; must be found.   Last-keys-seen is a list of all the keys ever
; used to create matches up to now -- and thus those keys should be
; avoided in the future.

; Summary: :inst-hyp is either a term or a non-term starting with
; :FC-FREE-VARS.  If the former, it is the fully instantiated term that
; must be true under the current type-alist to proceed, it is not an
; evaluable ground term (except for possibly a constant like *t*) or a
; FORCE or CASE-SPLIT, and :hyps is the rest of the hyps.  If the
; latter, the marker tells us how to match it without reproducing
; matches already created and whether to force or split on it.  Note
; that we consider it very odd and rare to see a forced or split
; free-var hypothesis since it is either matched right away or
; introduces UNBOUND-FREE-vars into the proof.

; Historical Plaque: Forward chaining was first coded before type-set
; could force 'assumptions.  Thus, splitting on 'assumptions was
; uncommon, indeed, it was only done for the output of linear
; arithmetic, where we first used the idea in the late 70's.  Thus, the
; forward chaining mechanism was designed so as not to produce any
; 'assumptions, i.e., so as not to call rewrite.  When type-set was
; extended, assumption generation and handling became more wide-spread.
; In particular, this function can generate assumptions due to the call
; of type-set below and those assumptions are handled by the caller of
; the forward-chaining module.  So now, except for these historical
; comments, there is no rationale behind this function's abstinence from
; rewrite.  Mixing forward and backward chaining so intimately might be
; interesting.  It might also be a can of worms.  It might also be
; inevitable.  It just isn't the most important thing to do just yet.

; Historical Plaque: As of Version_4.1 we had a heuristic oversight in
; forward chaining that allowed the presence of one (irrelevant) forward
; chaining rule to thwart the application of a relevant forward chaining
; rule.  Here I describe how.  Suppose we have a relevant rule whose
; activation is blocked because it needs (FOOP x) where x is free.
; Suppose (FOOP (A)) is derived by some irrelevant rule.  Then the
; relevant activation advances, choosing (A) for x.  Eventually that
; activation terminates, e.g., because we can't prove the next hyp about
; x when x is (A).  In Version_4.1 and before, all traces of the
; relevant activation are lost when it is advanced over (FOOP x).  So if
; a subsequent rule derives (FOOP (B)) for us, we never make that choice
; for x.  In summary: the irrelevant rule derives a spurious guess for x
; and we never try the relevant rule with the right choice of x, even
; though the choice is suggested on the eventual type-alist.  This
; actually happened in an example distilled by Dave Greve.  The obvious
; problem with leaving the relevant activation around, still blocked on
; (FOOP x), is that we'll repeatedly re-discover the possibility that x
; is (A).  In discussing how to avoid such redundancy, Dave suggested
; searching only the ``new'' part of each type-alist (new since the last
; attempt to guess free vars).  However, that idea doesn't work because
; we cannot determine what part of the type-alist is ``new'' since we do
; not necessary just add pairs to a type-alist.  End of Plaque.

; When we advance an activation we keep the inst-hyp, hyp, unify-subst,
; and ttree fields in variables and only put them back into the activation
; record when we decide to suspend it.  They may or may not have changed.

(defun suspend-fc-activation (act inst-hyp hyps unify-subst ttree)

; This function is equivalent to

; (change fc-activation act
;         :inst-hyp inst-hyp
;         :hyps hyps
;         :unify-subst unify-subst
;         :ttree ttree)

; This would take 4 conses given the layout:

; (defrec fc-activation
;   (inst-hyp (hyps . ttree)
;             unify-subst inst-trigger . rule) t)

; But, for example, if only inst-hyp changes, then it could be done in 1 cons.
; So we optimize three cases: (a) where none of the fields change, (b) where
; :unify-subst didn't change, and (c) where only :inst-hyp changed.  These
; cases are chosen both for their estimated frequency and the fact that the
; data structure actually permits conses to be saved.  Case (a) is perhaps most
; common, when we make no progress relieving the hypothesis we're stuck on and
; free variables are not involved at all.  Case (b) is when we've made progress
; but not selected any new free variables.  Case (c) probably cannot occur --
; if inst-hyp changed then hyps changes too -- but we coded it because it was
; straightforward to do and because in past versions of this code it was
; possible for inst-hyp alone to change and thus it may become possible again.

; The only sense in which this function depends on the shape of
; fc-activation records is that if the shape were rearranged these
; optimizations might not save any conses.  The correctness of the
; function (given its arguments) is independent of the shape of the
; record.

  (cond ((equal unify-subst (access fc-activation act :unify-subst))

         (cond ((and (equal hyps (access fc-activation act :hyps))
                     (equal ttree (access fc-activation act :ttree)))
                (cond ((equal inst-hyp (access fc-activation act :inst-hyp))
; Case (a) -- 0 conses
                       act)
                      (t
; Case (c) -- 1 cons
                       (change fc-activation act
                               :inst-hyp inst-hyp))))
               (t
; Case (b) -- 3 conses
                (change fc-activation act
                        :inst-hyp inst-hyp
                        :hyps hyps
                        :ttree ttree))))
        (t
; Otherwise -- 4 conses
         (change fc-activation act
                 :inst-hyp inst-hyp
                 :hyps hyps
                 :unify-subst unify-subst
                 :ttree ttree))))



(defun prettyify-fc-activation (act level)

; This function converts an fc-activation act into a readable form and level is
; either 1 or 2 that specifies how much detail you want to see.  What you
; get is:
; level  result
; 1:     (name (trigger: inst-trigger)
;              (:blocked-hyp k)
;              (:reason inst-hyp) | (:reason :FREE inst-hyp' seen)
;              )
; 2:     (rune (trigger: inst-trigger)
;              (:blocked-hyp k)
;              (:reason inst-hyp) | (:reason :FREE inst-hyp' seen)
;              (:unify-subst unify-subst))

; where k is the number of the hyp that is currently blocking our
; progress and inst-hyp' is the hyp instantiated with the unbound-free
; extension of unify-subst and seen is the list of terms
; already used to bind the free vars in this hyp.  As with
; prettyify-fc-derivation, name is the basic symbol of rune or else a
; pair of that symbol and the nat that makes this rune unique.

; To see how to read a rule, look at the level 2 code.

  (let* ((rune (access forward-chaining-rule
                       (access fc-activation act :rule)
                       :rune))
         (name (if (null (cddr rune)) (cadr rune) (cdr rune)))
         (inst-trigger (access fc-activation act :inst-trigger))
         (inst-hyp (access fc-activation act :inst-hyp))
         (hyps (access fc-activation act :hyps))
         (unify-subst (access fc-activation act :unify-subst))
         (pretty-subst (pairlis$ (strip-cars unify-subst)
                                 (pairlis-x2 (strip-cdrs unify-subst) nil)))
         (k (+ 1 (- (len (access forward-chaining-rule
                                 (access fc-activation act :rule)
                                 :hyps))
                    (if (and (consp inst-hyp)
                             (eq (car inst-hyp) :FC-FREE-VARS))
                        (len hyps)
                        (+ 1 (len hyps)))))))
    (case level
      (1 `(,name (:TRIGGER ,inst-trigger)
                 (:BLOCKED-HYP ,k)
                 ,(if (and (consp inst-hyp)
                           (eq (car inst-hyp) :FC-FREE-VARS))
                      `(:REASON :FREE ,(sublis-var
                                        (bind-free-vars-to-unbound-free-vars
                                         (all-vars (car hyps))
                                         unify-subst)
                                        (car hyps))
                                ,(len (cddr inst-hyp)))
                      `(:REASON ,inst-hyp))))
      (otherwise
       `(
; This forward-chaining rule:
         ,rune
; was triggered by this term in the problem:
         (:TRIGGER ,inst-trigger)
; but is currently blocked waiting for hyp number k:
         (:BLOCKED-HYP ,k)
; which (either) contains a free var as shown or
; which is this when fully instantiated:
         ,(if (and (consp inst-hyp)
                   (eq (car inst-hyp) :FC-FREE-VARS))
              `(:REASON :FREE ,(sublis-var
                                (bind-free-vars-to-unbound-free-vars
                                 (all-vars (car hyps))
                                 unify-subst)
                                (car hyps))
                        ,(cddr inst-hyp))
              `(:REASON ,inst-hyp))
; with the current unify-substitution:
         (:UNIFY-SUBST ,pretty-subst))))))

(defun prettyify-fc-activations (acts level)
  (cond ((endp acts) nil)
        (t (cons (prettyify-fc-activation (car acts) level)
                 (prettyify-fc-activations (cdr acts) level)))))

(defun make-fc-activation (term rule ttree ens)

; If rule is enabled and the trigger of rule can be instantiated with
; some substitution unify-subst to be term, then we make an
; fc-activation for this pair, otherwise we return nil.  Activations
; have rather difficult-to-enforce rules on :inst-hyp and :hyps.  For
; example, if the hyp upon which we're stuck contains no free vars, then
; :inst-hyp is supposed to be the instance for which we're looking --
; but we want to make sure that :inst-hyp cannot be settled by
; evaluation and is not supposed to be forced or split upon.  Therefore,
; rather than try to enforce the invariants here we just start every
; activation with an :inst-hyp of *t*.  This way we can add new methods
; of establishing a hyp without having to reproduce the code here.

; The initial ttree of the activation is ttree.  When we are building an
; activation for a term in the initial clause, this ttree will be nil.
; When we are building an activation for a term derived by some earlier
; round, the ttree will contain its derivation, tagged 'fc-derivation as
; described below.  The presence of that derivation in this activation
; will mean that the conclusion we eventually derive must not be worse
; than the conclusion of the derivation from which this term sprang.
; Once upon a time this function did not take the ttree arg and just
; used nil.  But that gave rise to infinite loops that were not stopped
; by our worse-than hacks because the terms from which the bad terms
; were derived were not logically dependent on their parents.

  (cond ((not (enabled-numep (access forward-chaining-rule rule :nume)
                             ens))
         nil)
        (t
         (mv-let (unify-ans unify-subst)
                 (one-way-unify (access forward-chaining-rule rule :trigger)
                                term)

; Note:  We do not start accumulating the persistence of this rule until we
; advance the fc-activation we create below.

                 (cond ((null unify-ans) nil)
                       (t (let ((rule-hyps
                                 (access forward-chaining-rule rule :hyps)))
                            (make fc-activation
                                  :inst-hyp *t*
                                  :hyps rule-hyps
                                  :ttree ttree
                                  :unify-subst unify-subst
                                  :inst-trigger term
                                  :rule rule))))))))

(defun make-fc-activations (term rules ttree ens activations)
  (cond ((endp rules) activations)
        (t (let ((act (make-fc-activation term (car rules) ttree ens)))
             (make-fc-activations term (cdr rules) ttree ens
                                  (if act
                                      (cons act activations)
                                      activations))))))

(mutual-recursion

(defun collect-terms-and-activations (term ttree wrld ens trigger-terms activations)

; We sweep term and collect (a) every subterm starting with a function
; symbol having forward chaining rules -- whether or not the subterm
; triggers any activations, and (b) every activation of every forward
; chaining rule triggered.  We accumulate those two results onto our
; last two arguments and return (mv trigger-terms activations).  We do not
; collect activations for the same subterm twice.

  (cond ((variablep term) (mv trigger-terms activations))
        ((fquotep term) (mv trigger-terms activations))
        ((or (flambda-applicationp term)
             (eq (ffn-symb term) 'not))

; We do not sweep the bodies of lambda expressions nor do we allow NOT
; to trigger forward-chaining rules because printed clauses contain NOTs
; that aren't really there and it would confuse the user.

; Until Version_4.1 we swept the bodies of lambda expressions for
; triggering terms, but we see no point in doing that since the variable
; environment is different.  Anything we derived triggered by such a
; term is true (since we only use assumptions from the original clause
; and true derivations) but would very likely be irrelevant because the
; triggering term doesn't actually occur in the problem.

         (collect-terms-and-activations-lst (fargs term) ttree wrld ens
                                            trigger-terms activations))
        (t (let ((rules (getpropc (ffn-symb term)
                                  'forward-chaining-rules
                                  nil
                                  wrld)))

; If the term has rules, we collect it and add any activations it
; triggers (though there may be none).  But first we see whether we've
; already collected this term and don't do anything if we have.  If the
; term doesn't have rules, we don't collect it.  In any case, unless
; we've seen the term before, we sweep its args.

             (cond
              (rules
               (cond
                ((member-equal term trigger-terms)
                 (mv trigger-terms activations))
                (t
                 (collect-terms-and-activations-lst
                  (fargs term)
                  ttree wrld ens
                  (cons term trigger-terms)
                  (make-fc-activations term rules ttree ens activations)))))
              (t (collect-terms-and-activations-lst
                  (fargs term) ttree wrld ens trigger-terms activations)))))))

(defun collect-terms-and-activations-lst
  (terms ttree wrld ens trigger-terms activations)
  (cond
   ((endp terms) (mv trigger-terms activations))
   (t (mv-let (trigger-terms activations)
              (collect-terms-and-activations (car terms)
                                             ttree wrld ens
                                             trigger-terms activations)
              (collect-terms-and-activations-lst (cdr terms)
                                                 ttree wrld ens
                                                 trigger-terms activations)))))
)

(defun collect-terms-and-activations-from-fcd-lst (fcd-lst wrld ens
                                                           trigger-terms
                                                           activations)

; We map over a list of fc-derivations and treat each :concl as a source
; of trigger terms, each subterm being marked with the fc-derivation tag
; containing its derivation.  We accumulate all our changes onto the
; last two arguments and return the extended values of those two lists.

  (cond ((endp fcd-lst)
         (mv trigger-terms activations))
        (t (mv-let
            (trigger-terms activations)
            (collect-terms-and-activations
             (access fc-derivation (car fcd-lst) :concl)
             (add-to-tag-tree! 'fc-derivation (car fcd-lst) nil)
             wrld ens trigger-terms activations)
            (collect-terms-and-activations-from-fcd-lst
             (cdr fcd-lst)
             wrld ens trigger-terms activations)))))

; Now we develop the code to try to advance an activation.  We will
; advance each activation as far as possible and then suspend it.  Of
; course, many times re-suspending it is a no-op because we will have
; made no progress at all.

(mutual-recursion

; These two functions return non-nil when sublis-var (respectively,
; sublis-var-lst) can return a term (resp. list of terms) different from the
; input.

(defun sublis-varp (alist term)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (pseudo-termp term))))
  (cond ((variablep term)
         (assoc-eq term alist))
        ((fquotep term)
         nil)
        (t (sublis-var-lstp alist (fargs term)))))

(defun sublis-var-lstp (alist l)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (pseudo-term-listp l))))
  (if (null l)
      nil
    (or (sublis-varp alist (car l))
        (sublis-var-lstp alist (cdr l)))))
)

(defun mult-search-type-alist (rest-hyps concls term typ type-alist
                                         unify-subst ttree oncep keys-seen
                                         compound-rec-rune?)

; This function is a variant of search-type-alist that searches for
; all instances of term (other than those listed in keys-seen) bound to a
; subset of type-set typ.  It returns three lists in 1:1 correspondence:
; a list of substitutions (which produce those instances), a list of
; tag-trees each extending ttree, and a list of the instances themselves
; (actually EQ to the terms from the type-alist upon which
; one-way-unify1 was called).

; The argument compound-rec-rune? is either nil or else a rune of a
; compound-recognizer rule.  If the latter, then we include it in every
; tag-tree returned.

  (cond ((null type-alist)
         (mv nil nil nil))
        ((and (ts-subsetp (cadr (car type-alist)) typ)
              (not (member-equal (car (car type-alist)) keys-seen)))
         (mv-let (ans new-unify-subst)
                 (one-way-unify1 term (car (car type-alist)) unify-subst)
                 (cond
                  (ans (let ((diff-alist (alist-difference-eq new-unify-subst
                                                              unify-subst)))
                         (cond
                          ((or oncep
                               (not (or (sublis-var-lstp diff-alist rest-hyps)
                                        (sublis-var-lstp diff-alist concls))))

; We aren't going to look for additional bindings either because we're not
; supposed to (i.e. oncep is true) or there is no point.  In the latter
; case the newly-bound variables do not occur free in the remaining hyps or the
; conclusions of the forward-chaining rule under consideration.  So, there is
; no point to looking for additional bindings.

                           (mv (list new-unify-subst)
                               (list (cons-tag-trees (cddr (car type-alist))
                                                     (push-lemma?
                                                      compound-rec-rune?
                                                      ttree)))
                               (list (car (car type-alist)))))

; We found a new unify-subst but there may be additional interesting ones out
; there.

                          (t (mv-let (other-unifies other-ttrees other-instances)
                                     (mult-search-type-alist rest-hyps concls
                                                             term
                                                             typ
                                                             (cdr type-alist)
                                                             unify-subst
                                                             ttree
                                                             oncep
                                                             keys-seen
                                                             compound-rec-rune?)
                                     (mv (cons new-unify-subst other-unifies)
                                         (cons (cons-tag-trees
                                                (cddr (car type-alist))
                                                (push-lemma?
                                                 compound-rec-rune?
                                                 ttree))
                                               other-ttrees)
                                         (cons (car (car type-alist))
                                               other-instances)))))))

; We didn't find any new substitutions; try again.

                  (t (mult-search-type-alist rest-hyps concls term
                                             typ
                                             (cdr type-alist)
                                             new-unify-subst
                                             ttree
                                             oncep
                                             keys-seen
                                             compound-rec-rune?)))))
        (t (mult-search-type-alist rest-hyps concls term
                                   typ
                                   (cdr type-alist)
                                   unify-subst
                                   ttree
                                   oncep
                                   keys-seen
                                   compound-rec-rune?))))

(defun mult-lookup-hyp (hyp rest-hyps concls type-alist wrld unify-subst ttree
                            oncep last-keys-seen ens)

; This function basically takes a hyp and a type-alist.  It returns (mv
; new-unify-substs new-ttrees new-last-keys-seen), in which extensions of
; unify-subst that make hyp true under type-alist are listed in 1:1
; correspondence with extensions of ttree.  The function does not consider
; type-alist entries on the keys last-keys-seen and its third result is the
; keys it used this time.

; This function is basically a variant of lookup-hyp.

  (mv-let (term typ rune)
          (term-and-typ-to-lookup hyp wrld ens)
          (mult-search-type-alist rest-hyps concls term typ type-alist
                                  unify-subst ttree oncep last-keys-seen
                                  rune)))

(mutual-recursion

(defun ev-respecting-ens (form alist state latches ttree ens wrld)

; This is a variant of ev (see also ev-rec) that avoids calling functions whose
; executable-counterparts are disabled.  Thus, here we return (mv erp val
; latches ttree), where ev would return (mv erp val latches) and ttree extends
; the given ttree by adding executable-counterpart runes justifying the
; evaluation.  If erp is non-nil then val and ttree are to be taken as
; meaningless.

  (cond ((or (variablep form)
             (fquotep form))
         (mv-let (erp val latches)
           (ev form alist state latches t nil)
           (mv erp val latches ttree)))
        (t (let ((fn (ffn-symb form)))
             (cond
              ((or (flambdap fn)
                   (enabled-xfnp fn ens wrld))
               (cond ((eq fn 'if)
                      (mv-let
                        (test-er test latches ttree)
                        (ev-respecting-ens (fargn form 1) alist state
                                           latches ttree ens wrld)
                        (cond (test-er (mv t test latches ttree))
                              (test (ev-respecting-ens
                                     (fargn form 2)
                                     alist state latches
                                     (push-lemma '(:EXECUTABLE-COUNTERPART if)
                                                 ttree)
                                     ens wrld))
                              (t (ev-respecting-ens
                                  (fargn form 3)
                                  alist state latches
                                  (push-lemma '(:EXECUTABLE-COUNTERPART if)
                                                 ttree)
                                  ens wrld)))))
                     (t (mv-let
                          (args-er args latches ttree)
                          (ev-lst-respecting-ens (fargs form) alist state
                                                 latches ttree ens wrld)
                          (cond
                           (args-er (mv t args latches ttree))
                           (t (cond
                               ((flambdap fn)
                                (ev-respecting-ens
                                 (lambda-body (ffn-symb form))
                                 (pairlis$ (lambda-formals (ffn-symb form))
                                           args)
                                 state latches ttree ens wrld))
                               (t (mv-let (erp val latches)
                                    (ev-fncall fn args state latches t nil)
                                    (mv erp val latches
                                        (push-lemma
                                         `(:EXECUTABLE-COUNTERPART ,fn)
                                         ttree)))))))))))
              (t (mv t nil latches ttree)))))))

(defun ev-lst-respecting-ens (lst alist state latches ttree ens wrld)
  (cond ((endp lst)
         (mv nil nil latches ttree))
        (t (mv-let (erp val latches ttree)
             (ev-respecting-ens (car lst) alist state latches ttree ens wrld)
             (cond (erp (mv erp val latches ttree))
                   (t (mv-let (erp rst latches ttree)
                        (ev-lst-respecting-ens (cdr lst) alist state latches
                                               ttree ens wrld)
                        (cond (erp (mv erp rst latches ttree))
                              (t (mv nil (cons val rst) latches ttree))))))))))
)

; Forward Chaining Derivations - fc-derivations - fcds

; To implement forward chaining, especially to implement the heuristic controls
; on which derived conclusions to keep, we have to use ttrees in a rather
; subtle way that involves embedding a ttree in a tagged object in another
; ttree.  These tagged objects holding ttrees are called "fc-derivations" and a
; ttree that (may) contain fc-derivation tags is said to be ``not fcd-free''
; (i.e., not free of fc-derivation).  We speak of type-alists as being fcd-free
; in the obvious way.  We motivate and discuss fc-derivation here.  However, no
; fc-derivation gets out of the forward chaining module.  That is, once
; forward-chain-top has done its job, its returned ttrees are fcd-free.

; When we finally relieve all the hyps we will create the instantiated
; conclusion, concl.  After heuristic filtering, approved concls will find
; their way into the type-alist by being assumed true.  But within the forward
; chaining module we must be able to track dependencies for two reasons.  The
; first reason concerns the ultimate use of such derived conclusions: when we
; have finished all our forward chaining and go into the rewriting of literals
; we will need to choose from among the available forward chained concls those
; that don't depend upon the literal we are rewriting.  For this it is
; sufficient to have the ttree of the conclusion with its parent tree markers.
; But the second reason is entirely internal to forward chaining: we need loop
; stopping heuristics and the one we use is that no conclusion is worse than
; any of its immediate supporters (which, transitively means that no conclusion
; is worse than any of its supporters).

; So, associated with each derived conclusion is a derivation.  To keep things
; as efficient as possible we don't make these derivations as clean as we
; might!  Instead, we basically just store the ttree of each concl together
; with the concl and other information in a record.  All such records at the
; "top level" of a ttree are the immediate supporters and one must descend
; recursively into the ttrees of the derivations to get the whole tree.

; This is odd because it results in a ttree being a component of an object
; stored in a ttree.  Those interior ttrees are actually hidden from our ttree
; scanners.  Before we leave forward chaining we must lift out any important
; information.  But within forward chaining this structure is sufficient and
; reasonably efficient.

; An "fc-derivation" is a structure of the form:

; (defrec fc-derivation
;   (((concl . ttree) . (fn-cnt . p-fn-cnt))
;    .
;    ((inst-trigger . rune) . (fc-round . unify-subst)))
;   t)

; Note: This is just an 8-tipped perfectly symmetric tree.  We
; contemplated optimizing it for access time to the pieces.  Informally,
; we suspect concl, fn-cnt, p-fn-cnt, and ttree, are the most critical
; because of their use in fcd-worse-than-or-equal.  We also contemplated
; replacing ttree, inst-trigger, rune, and unify-subst by the
; fc-activation that gave rise to this conclusion, thereby saving the
; time of consing up so much in this record.  But (a) the activation is
; not already consed up at the time we build this fc-derivation ``from''
; it -- we are only holding its pieces in advance-fc-activation2.  (b)
; To do that would slow down access to those buried pieces.  (c) And
; risk having move the declaration of fc-activations into linear-a.lisp
; too.  So we just tear the activation apart and put the pieces into the
; derivation.

; Rune is the name of the rule applied, concl is the instantiated
; conclusion.  Fn-cnt is the function symbol count of concl (as computed
; by fn-count) and p-fn-cnt is the pseudo-function count (see
; term-order).  These are used in our heuristic for deciding whether to
; keep a concl, as are rune, concl, and inst-trigger.  Ttree is the
; ttree that derived concl from name.  Inst-trigger is the term in the
; current problem that fired this rule.  And fc-round is the number of
; the forward chaining round in which this concl was derived.

; If we decide to keep concl then we make a ttree that contains its
; fc-derivation as its only object, tagged 'fc-derivation.  That ttree is
; attached to the assumption of concl in the new type-alist and will
; attach itself to all uses of concl.  Given an fc-derivation we can
; reconstruct the derivation of its concl as follows: concl was derived
; by applying name to all of the derived concls in all of the
; 'fc-derivations in its ttree.

; When the forward chaining algorithm is complete we convert the
; recursively nested ttrees in 'fc-derivations to standard ttrees.  This
; destroys the information about exactly how concl was derived from its
; supporters but it lifts out and makes visible the 'lemmas and 'pt upon
; which the concl is based.

; Here ends the essay on fc-derivations.  Now we develop the code.

(defun add-fc-derivations (rune concls unify-subst inst-trigger
                                fc-round ens wrld state ttree
                                fcd-lst)

; Suppose concls is the instantiated concls of a successful forward
; chaining rule.  Here we convert each concl in it into an fc-derivation
; We add each fc-derivation to the list fcd-lst and return the final
; fcd-lst.

  (cond ((null concls) fcd-lst)
        (t (mv-let
            (flg concl new-ttree)
            (eval-ground-subexpressions (car concls) ens wrld state ttree)
            (declare (ignore flg))
            (mv-let
             (fn-cnt p-fn-cnt)
             (fn-count concl)
             (add-fc-derivations rune (cdr concls) unify-subst inst-trigger
                                 fc-round ens wrld state ttree
                                 (cons
                                  (make fc-derivation
                                        :fc-round fc-round
                                        :rune rune
                                        :concl concl
                                        :fn-cnt fn-cnt
                                        :p-fn-cnt p-fn-cnt
                                        :inst-trigger inst-trigger
                                        :unify-subst unify-subst
                                        :ttree new-ttree)
                                  fcd-lst)))))))

; The following function is not used in forward chaining except as a
; trace/debugging tool.  Given an fc-derivation, it produces a human
; readable (at least for some humans) form of the derivation.

(mutual-recursion

(defun prettyify-fc-derivation (fcd level)

; Level is a natural specifying how much detail we want.  ``Name'' below
; is just the event name of the rune if there is only one
; forward-chaining rune with that name, e.g., rune is (:FORWARD-CHAINING
; name), or the cdr of the rune otherwise, e.g., (:FORWARD-CHAINING
; name . 3).  The idea is to keep the prettyified version short and
; all the runes are :FORWARD-CHAINING ones, while being unambiguous.

; 1:  (fc-round concl name)
; 2:  (fc-round concl name (:literals ...) . level-0-supporters)
; 3:  (fc-round concl name (:literals ...) . level-3-supporters)
; 4:  (fc-round concl rune (:unify-subst ...)
;                         (:literals ...) . level-4-supporters)

; Look at the code for level 4 to see how you read these things.

  (let* ((fc-round (access fc-derivation fcd :fc-round))
         (concl (access fc-derivation fcd :concl))
         (rune (access fc-derivation fcd :rune))
         (name (if (null (cddr rune)) (cadr rune) (cdr rune)))
         (unify-subst (access fc-derivation fcd :unify-subst))
         (pretty-subst (pairlis$ (strip-cars unify-subst)
                                 (pairlis-x2 (strip-cdrs unify-subst) nil))))
    (case level
      (1 `(,fc-round ,concl ,name))
      (2 `(,fc-round ,concl ,name
                     (:LITERALS ,@(collect-parents
                                   (access fc-derivation fcd :ttree)))
                     ,@(prettyify-fc-derivations
                        (tagged-objects
                         'fc-derivation
                         (access fc-derivation fcd :ttree))
                        0)))
      (3 `(,fc-round ,concl ,name
                     (:LITERALS ,@(collect-parents
                                   (access fc-derivation fcd :ttree)))
                     ,@(prettyify-fc-derivations
                        (tagged-objects 'fc-derivation
                                        (access fc-derivation fcd :ttree))
                        3)))
      (otherwise
       `(
; Forward chaining round:
         ,fc-round
; produced the new fact:
         ,concl
; via the rule
         ,rune
; and unify-subst:
         (:UNIFY-SUBST ,@pretty-subst)
; relying on these literals from the original clause to relieve some of
; the hyps:
         (:LITERALS ,@(collect-parents
                       (access fc-derivation fcd :ttree)))
; and relying on these facts from earlier rounds for the other hyps:
         ,@(prettyify-fc-derivations
            (tagged-objects 'fc-derivation
                            (access fc-derivation fcd :ttree))
            4))))))

(defun prettyify-fc-derivations (fcd-lst level)
  (cond ((null fcd-lst) nil)
        (t (cons (prettyify-fc-derivation (car fcd-lst) level)
                 (prettyify-fc-derivations (cdr fcd-lst) level)))))
 )

(mutual-recursion

(defun expunge-fc-derivations (ttree)

; Ttree is a not fcd-free and we make it fcd-free.  In particular, we copy
; ttree, replacing each 'fc-derivation in it by a new node which tags the rule
; name with 'lemma and lifts out the interior ttrees and expunges them.  Thus,
; when we are done we have a ttree with no 'fc-derivation tags, but which has
; 'lemma tags on the set of names in the 'fc-derivations and which has all of
; the other tags, e.g., 'pt 'assumptions, etc, that were recursively embedded
; in 'fc-derivations.

; Note: This function must be able to find 'fc-derivations anywhere within the
; ttree.  Fc-derivations are for heuristic use only during forward chaining (to
; cheaply record the derivation of a fact, so that we can prevent
; forward-chaining ``pumps'').  We should be ruthless in finding and removing
; them.

; Once upon a time we detected an 'fc-derivation at the end of prove.  It
; slipped into the final proof tree as follows: Forward chaining made two
; rounds.  During the first, hyp1 was concluded.  During the second, hyp2 was
; concluded and forced an assumption.  That assumption contained the type-alist
; produced from the first round, which had the 'fc-derivation for hyp1.  Now if
; forward-chaining had proved the theorem, we would be in good shape.  But
; suppose it doesn't prove the theorem and we start rewriting.  Suppose the
; rewriter appeals to hyp2.  That causes it to raise the assumption.  We then
; try, at the end of rewrite-clause, to relieve the assumption by rewriting it
; under its type-alist.  Suppose that we use hyp1 during that successful
; relieving of the assumption: its 'fc-derivation then enters our final proof
; tree.  Here is a script that used to provoke this bug.  The fix, below, is to
; expunge fc-derivations from the :type-alists of assumptions.  We keep this
; script simply because it took a while to find the path down which the
; 'fc-derivation migrated out of forward-chaining.

;  (er-progn
;   (defstub hyp1 (x) t)
;   (defstub hyp2 (x) t)
;   (defstub trig (x) t)
;   (defstub assumptionp (x) t)
;   (defstub concl (x) t)
;
;   (defaxiom fc-to-hyp1
;     (hyp1 (trig x))
;     :rule-classes ((:forward-chaining :trigger-terms ((trig X)))))
;
;   (defaxiom then-fc-to-hyp2
;     (implies (and (hyp1 x) (force (assumptionp x)))
;              (hyp2 x))
;     :rule-classes :forward-chaining)
;
;   (defaxiom in-rewrite-use-hyp2-thus-raising-the-assumption
;     (implies (hyp2 x) (concl x)))
;
;   (defaxiom and-relieve-the-assumption-by-appeal-to-hyp1-sucking-in-the-fc-deriv
;     (implies (hyp1 x) (assumptionp x)))
;
;   (thm (concl (trig a))))

  (let ((objects (tagged-objects 'fc-derivation ttree)))
    (cond (objects
           (expunge-fc-derivations-assumptions
            (expunge-fc-derivations-lst
             objects
             (remove-tag-from-tag-tree! 'fc-derivation ttree))))
          (t (expunge-fc-derivations-assumptions ttree)))))

(defun expunge-fc-derivations-lst (fc-derivation-lst ttree)

; Each element of fc-derivations-lst is an fc-derivation.  Each such record has
; a :ttree and a :rune.  We accumulate into ttree the :rune of each
; fc-derivation as well as the :ttree of each fc-derivation after recursively
; expunging the fc-derivation tags from it.  Thus, for example, if the :ttree
; of an element of fc-derivations contains a PT or ASSUMPTIONS tag, it survives
; and is part of the final ttree returned.

  (cond ((endp fc-derivation-lst) ttree)
        (t (push-lemma
            (access fc-derivation (car fc-derivation-lst) :rune)
            (cons-tag-trees (expunge-fc-derivations
                             (access fc-derivation (car fc-derivation-lst)
                                     :ttree))
                            (expunge-fc-derivations-lst (cdr fc-derivation-lst)
                                                        ttree))))))

(defun expunge-fc-derivations-type-alist (type-alist)

; We expunge the fc-derivation tags from every ttree in type-alist.

  (cond
   ((endp type-alist)
    nil)
   (t (cons (cons (caar type-alist)
                  (cons (cadar type-alist)
                        (expunge-fc-derivations (cddar type-alist))))
            (expunge-fc-derivations-type-alist (cdr type-alist))))))

(defun expunge-fc-derivations-assumptions-lst (assumptions)

; For every assumption record in assumptions we replace the :type-alist
; field with the result of expunging fc-derivations from the type-alist.

  (cond
   ((endp assumptions) nil)
   (t (cons (change assumption (car assumptions)
                    :type-alist
                    (expunge-fc-derivations-type-alist
                     (access assumption (car assumptions) :type-alist)))
            (expunge-fc-derivations-assumptions-lst (cdr assumptions))))))

(defun expunge-fc-derivations-assumptions (ttree)

; If ttree contains an 'assumption tag, expunge fc-derivations from the ttrees
; in the type-alists of all the assumptions.

  (let ((objects (tagged-objects 'assumption ttree)))
    (cond
     (objects
      (extend-tag-tree 'assumption
                       (expunge-fc-derivations-assumptions-lst objects)
                       (remove-tag-from-tag-tree! 'assumption ttree)))
     (t ttree))))
)

; A Reporting Facility for Forward Chaining

; We now describe our design for a reporting facility for forward chaining.
; The facility is designed to help answer the question ``What happens with the
; attempt to use <some forward-chaining rules>?''  where the rules of interest
; are described with some ``criteria'' defined below.

; What should be displayed as the answer?

; (1) The clause being worked on (once we thought the clause-id was a good
;      idea, but not every clause given to forward-chain-top has a clause-id).

; (2) The final status of every rule activated that met the criteria.

; By ``final status'' we mean the rune, instantiated trigger, full
; unify-substitution, and disposition of every rule that meets the criteria.
; By ``disposition'' we mean one of these tuples:

; (a) SUCCESS ADDED <term> -- successfully fired and gave us <term>

; (b) SUCCESS REJECTED <term> -- successfully fired but conclusion <term> was
;                                disapproved

; (c) BLOCKED UNRELIEVED-HYPx <hyp> -- unable to relieve <hyp>;
;                               UNRELIEVED-HYPx is either UNRELIEVED-HYP or
;                               UNRELIEVED-HYP-FREE to indicate whether hyp has
;                               free vars.  But hyp is printed with the
;                               unify-subst applied and with UNBOUND-FREE-vars
;                               in place of the free vars.  We include the
;                               UNRELIEVED-HYP-FREE tag just to make it easier
;                               to mechanically recognize the presence of free
;                               vars.  (d) BLOCKED FALSE <hyp> -- hyp shown
;                               false <hyp>

; The ``criteria'' is a list of triples, sometimes called a ``criterion.''
; Each criterion consist of a rune, an inst-trigger, and a concl.  All three
; parts of a criterion are optional and we use t to indicate the absence of a
; part.  An activation satisfies the criteria if it satisfies one of the
; criterion.  An activation satisfies a criterion if it satisfies each of the
; provided (non-t) parts.  An activation satisfies the rune (or inst-trigger)
; part if the activation's rune (or inst-trigger) is the criterion's rune (or
; inst-trigger).  However, because of free variables we cannot always know if a
; still-active activation will produce the conclusion of the activation we
; seek.  If an activation has free variables in it, the best we can do is
; determine whether conclusion of the rule, under the unify-subst, can be made
; to match the concl we seek.  Therefore, an activation satisfies the concl
; part if the concl of its rule matches (with one-way-unify1 extending
; unify-subst) the concl we seek.  (To be precise, fc rules have :concls and we
; wish to know whether some member of the :concls of the rule matches the concl
; we seek.)  This is as good as an equality check if the unify-subst is
; complete on the variables in the concl.

; How can we collect and display this information?

; We will work inside a wormhole named the ``fc-wormhole''.

; The wormhole-data shall consist of an alist with the following keys:

; :CRITERIA - a list of triples

; :REPORT-ON-THE-FLYP - t if we are to print reports every time
; forward-chain-top is called, nil if we are to just save the data for browsing
; later.

; :FORWARD-CHAIN-CALLS - an alist pairing a ``call number'' n to an alist with
; the following keys.  The order of the keys in this alist is not necessarily
; that shown below.  We manipulate the alist only with assoc-eq and
; put-assoc-eq, but we initialize it with the keys in an ``optimized'' order.

;     :INPUT - all of the arguments of this call of forward-chain-top, except
;     for WRLD, ENS, STATE.  We omit the first two because they make it hard to
;     print the wormhole state.  We omit the last for obvious reasons.  The
;     omission of ens makes the stored data actually inadequate to reproduce
;     the call, since the ens used might be a locally installed :in-theory. The
;     arguments include caller, so these are really calls of forward-chain-top!

;     :ROUNDS - how many forward-chaining rounds were used

;     :OUTPUT - the output values returned by this call, as a triple: (flg
;     type-alist ttree-or-fc-pairs).  The semantics of this triple is that if
;     flg is t, then forward-chain-top found a contradiction, type-alist is nil
;     and ttree-or-fc-pairs is an fcd-free ttree explaining the contradiction;
;     on the other hand, if flg is nil, then forward-chain-top did not find a
;     contradiction, type-alist is an fcd-free type-alist extending the
;     original one with what we know and ttree-or-fc-pairs is a list of pairs
;     of the form (concl . ttree) where each concl is a derived conclusion and
;     its ttree is fcd-free.  See forward-chain-top.

;     If the :OUTPUT value is nil instead of a triple, it means the call was
;     interrupted before we stored the final values.

; (1) :BLOCKED-FALSE-SATISFYING-ACTIVATIONS - every time we abandon a
;      satisfying activation because its hyp is false, we add it to this list;
;      note that we will have to do some work to install inst-hyp, etc. into
;      the activation act0 just detected by advance-fc-activationi.

; (2) :ALL-SATISFYING-FC-DERIVATIONS - every time we make an fc derivation from a
;      satisfying activation, we save the fc-derivation here.

; (3) :APPROVED-SATISFYING-FC-DERIVATIONS - every time we approve a satisfying
;     fc-derivation we save the fc-derivation here.

; (4) :LEFTOVER-ACTIVATIONS - all activations still suspended at the
;      termination of of forward chaining

; (5) :REDUNDANT-APPROVED-FC-DERIVATIONS - every time we assume an approved
;     derived conclusion true, we check to see whether it changes the
;     type-alist.  If not, we put the fc-derivation on this list.

; For brevity we sometimes call the last five lists ``sites'' and number them
; as seen.  For example, we'll ask whether an fc-derivation ``is a member of
; site (3).''

; Note that there are three levels of alist here.  We call the top one ``the
; fc-wormhole data.''  We call the second level one, the ``calls alist'', and
; we call the third level one the ``call alist.''  That is, the fc-wormhole
; data is an alist with two keys, one of which is :FORWARD-CHAIN-CALLS.  The
; value of that particular key is the calls alist, which is an alist with n
; numeric keys.  There is a key for each time forward-chain-top has been
; called.  The calls alist is ordered with the largest key first.  Suppose k is
; the call number of the most recent call of forward chain.  Then the value of
; k in the calls alist is a call alist, which has :INPUT, :ROUNDS, :OUTPUT, and
; the four sites as its keys.

(defun current-fc-call-number (data)
; See paragraph above.
  (car (car (cdr (assoc-eq :FORWARD-CHAIN-CALLS data)))))

(defun current-fc-call-alist (data)
; See paragraph above.
  (cdr (car (cdr (assoc-eq :FORWARD-CHAIN-CALLS data)))))

(defun put-current-fc-call-alist (call-alist data)
; See paragraph above.
  (let* ((calls-alist (cdr (assoc-eq :FORWARD-CHAIN-CALLS data)))
         (temp (car calls-alist))
         (k (car temp))) ; current-fc-call-number
    (put-assoc-eq :FORWARD-CHAIN-CALLS
                  (cons (cons k call-alist) (cdr calls-alist))
                  data)))

; When prove is first called, we initialize the fc-wormhole data by clearing
; the calls-alist but leaving the :CRITERIA and :REPORT-ON-THE-FLYP settings as
; is.  The user is responsible for them.  All of our code is written to
; optimize the case where the :CRITERIA is nil.  In that case, we come as close
; as we can to doing nothing at all about tracking forward-chaining.

; To allow the user maintain the criteria and reporting flag, we provide these
; very basic primitives.

(defun initialize-fc-wormhole-sites ()
; This function initializes the fc-wormhole and is called in prove.
  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (let ((data (wormhole-data whs)))
        (set-wormhole-data
         whs
         `((:CRITERIA
            ,@(cdr (assoc-eq :criteria data)))
           (:REPORT-ON-THE-FLYP
            . ,(cdr (assoc-eq :REPORT-ON-THE-FLYP data)))
           (:FORWARD-CHAIN-CALLS . nil)))))
   nil))

(defun show-fc-criteria ()
  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (prog2$ (cw "Forward Chaining Tracking Criteria:~%~x0~%"
                  (cdr (assoc-eq :CRITERIA (wormhole-data whs))))
              whs))
   nil))

(defun reset-fc-reporting ()

; This user-level function resets the criteria but leaves the on-the-fly flg as
; last set.  All data is wiped out.

  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (set-wormhole-data
       whs
       '((:CRITERIA . nil)
         (:REPORT-ON-THE-FLYP . nil)
         (:FORWARD-CHAIN-CALLS . nil))))
   nil))

(defun translate-fc-criterion (x state)
  (cond
   ((and (true-listp x)
         (equal (length x) 3))
    (let ((rune (car x))
          (inst-trigger (cadr x))
          (concl (caddr x)))
      (cond
       ((not (or (eq rune t)
                 (and (runep rune (w state))
                      (eq (car rune) :forward-chaining))))
        (er soft 'set-fc-criteria
            "~x0 is not a :FORWARD-CHAINING rune."
            rune))
       (t (er-let*
            ((inst-trigger
              (cond ((eq inst-trigger t) (value t))
                    (t (translate inst-trigger
                                  t t t 'add-fc-criterion (w state) state))))
             (concl
              (cond ((eq concl t) (value t))
                    (t (translate concl
                                  t t t 'add-fc-criterion (w state) state)))))
            (value (list rune inst-trigger concl)))))))
   (t (er soft 'set-fc-criteria
          "Each element of a criteria must be a triple, (rune inst-trigger ~
           inst-concl), where rune is a :FORWARD-CHAINING rune or t, ~
           inst-trigger is a term or t, and inst-concl is a term or t.  ~
           But ~x0 is not of this form."
          x))))

(defun translate-fc-criteria (lst state)

; We either cause an error or return a properly translated forward chaining
; criteria.  Recall that a criteria is a true-list of triples, each of the form
; (rune inst-trigger inst-concl), where any of the three components may be nil
; but when a component is not nil, the rune must be a rune, and the other two
; must be terms.

  (cond ((atom lst)
         (cond ((equal lst nil) (value nil))
               (t (er soft 'set-fc-criteria
                      "The criteria must be a true-list."))))
        (t (er-let*
             ((triple (translate-fc-criterion (car lst) state))
              (rest (translate-fc-criteria (cdr lst) state)))
             (value (cons triple rest))))))

(defun set-fc-criteria-fn (x state)

; Warning: Keep this in sync with set-waterfall-parallelism-fn.

  (er-let* ((criteria
             (cond
              ((equal x '(nil)) (value nil))
              #+acl2-par ; the following test is always false when #-acl2-par
              ((f-get-global 'waterfall-parallelism state)
               (er soft 'set-fc-criteria
                   "It is illegal to track forward-chaining when ~
                    waterfall-parallelism is enabled. "))
              ((equal x '(t)) (value '((t t t))))
              (t (translate-fc-criteria x state)))))
    (prog2$
     (wormhole-eval
      'fc-wormhole
      '(lambda (whs)
         (set-wormhole-data
          whs
          (put-assoc-eq :CRITERIA criteria (wormhole-data whs))))
      nil)
     (value nil))))

(defmacro set-fc-criteria (&rest x)
  `(set-fc-criteria-fn ',x state))

(defun set-fc-report-on-the-fly (flg)

; This function allows the user to set the flag that determines whether we do
; on-the-fly reporting (flg = t) or not (flg = nil) during forward chaining.

  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (let ((data (wormhole-data whs)))
        (prog2$
         (cond
          (flg
           (cond
            ((cdr (assoc-eq :criteria data))
             (cw "On-the-fly reporting of forward-chaining activity is ~
                  enabled.  The criteria being tracked are: ~x0.~%"
                 (cdr (assoc-eq :criteria data))))
            (t
             (cw "On-the-fly reporting of forward-chaining activity is enabled ~
                  but no data will be collected because there are no criteria.~%"))))
          ((cdr (assoc-eq :criteria data))
           (cw "On-the-fly reporting of forward-chaining activity is disabled.  ~
                The criteria being tracked are: ~x0.~%"
               (cdr (assoc-eq :criteria data))))
          (t
           (cw "On-the-fly reporting of forward-chaining activity is disabled ~
                but no data will be collected because there are no criteria.~%")))
         (set-wormhole-data whs
                            (put-assoc-eq :REPORT-ON-THE-FLYP flg data)))))
   nil))

; When forward-chain-top is called, we add a new entry to the calls-alist:

(defun new-fc-call (caller cl pts force-flg do-not-reconsiderp wrld ens
                              oncep-override)

; Once upon a time we stored all the arguments (except state) in :INPUT.
; However, that makes it really hard to print whs because it contains many
; copies of world and ens.  So we just print those symbols, not their
; values.  This is inadequate to reproduce the call, since the ens
; might be local to the goal.

  (declare (ignore wrld ens))
  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (let* ((data (wormhole-data whs))
             (calls-alist (cdr (assoc-eq :FORWARD-CHAIN-CALLS data))))
        (cond
         ((cdr (assoc-eq :CRITERIA data))
          (set-wormhole-data
           whs
           (put-assoc-eq
            :FORWARD-CHAIN-CALLS
            (cons (cons (+ 1 (or (car (car calls-alist)) 0))  ; may be first time
                        `((:BLOCKED-FALSE-SATISFYING-ACTIVATIONS . nil)
                          (:ALL-SATISFYING-FC-DERIVATIONS . nil)
                          (:APPROVED-SATISFYING-FC-DERIVATIONS . nil)
                          (:LEFTOVER-ACTIVATIONS . nil)
                          (:INPUT
                           . ,(list caller cl pts force-flg do-not-reconsiderp
                                    'wrld 'ens oncep-override 'state))
                          (:ROUNDS . nil)
                          (:OUTPUT . nil)))
                  calls-alist)
            data)))
         (t whs))))
   :no-wormhole-lock))

; As forward-chain-top operates, it monitors the activations it creates and
; records certain information.  First, we must be able to determine whether an
; activation satisfies the criteria.  It is convenient to here develop several
; notions of satisfaction.  Bear with us.

; Here is the definition of when an fc-activation satisfies a criterion.  It
; uses the notion of whether some concl in the concls of a forward-chaining
; rule matches a given term, e.g., whether the term is a ``member (modulo
; unification)'' of the concls.

(defun member-one-way-unify1 (term pat-lst unify-subst)

; We return t or nil to indicate whether some member of pat-lst unifies with
; term, extending unify-subst.

  (cond
   ((endp pat-lst) nil)
   (t (mv-let (flg alist)
              (one-way-unify1 (car pat-lst) term unify-subst)
              (declare (ignore alist))
              (cond
               (flg t)
               (t (member-one-way-unify1 term (cdr pat-lst) unify-subst)))))))

(defun satisfying-fc-activation1p (criterion act)
  (let ((rune (car criterion))
        (trig (cadr criterion))
        (concl (caddr criterion))
        (rule (access fc-activation act :rule)))
    (and (or (eq rune t)
             (equal rune
                    (access forward-chaining-rule rule :rune)))
         (or (eq trig t)
             (equal trig
                    (access fc-activation act :inst-trigger)))
         (or (eq concl t)
             (member-one-way-unify1
              concl
              (access forward-chaining-rule rule :concls)
              (access fc-activation act :unify-subst))))))

; And then we can conjoin that across a criteria (list of ``criterions'').

(defun satisfying-fc-activationp (criteria act)
  (cond ((endp criteria) nil)
        (t (or (satisfying-fc-activation1p (car criteria) act)
               (satisfying-fc-activationp (cdr criteria) act)))))

(defun collect-satisfying-fc-activations (criteria acts ans)

; Accumulate all satisfying fc-activations in acts onto ans.

  (cond ((endp acts) ans)
        ((satisfying-fc-activationp criteria (car acts))
         (collect-satisfying-fc-activations criteria
                                            (cdr acts)
                                            (cons (car acts) ans)))
        (t (collect-satisfying-fc-activations criteria (cdr acts) ans))))

; The notion of a satisfying fc-activation applies naturally to the ``virtual
; activations'' manipulated in advance-fc-activation1, 2, and 3, where we have
; an activation represented by some initial version of it, act0, together with
; the current values of fields :inst-hyp, :hyps, :unify-subst, and :ttree --
; but without those values actually deposited in the activation.  The only one
; of the virtual fields that is relevant to satisfiability is the unify-subst.

(defun satisfying-virtual-fc-activation1p (criterion act0 unify-subst)

; Here we define the analog of satisfying-fc-activationp except that the
; activation we assess is a ``virtual'' one obtained by putting unify-subst
; into the act0.  The functions that advance fc-activations traffic in
; ``virtual'' activations represented by some initial act0 and the current
; values intended to occupy the inst-hyp, hyps, unify-subst, and ttree fields.
; But of those ``virtual'' fields, the only one that affects satisfiability is
; unify-subst.

  (let ((rune (car criterion))
        (trig (cadr criterion))
        (concl (caddr criterion))
        (rule (access fc-activation act0 :rule)))
    (and (or (eq rune t)
             (equal rune
                    (access forward-chaining-rule rule :rune)))
         (or (eq trig t)
             (equal trig
                    (access fc-activation act0 :inst-trigger)))
         (or (eq concl t)
             (member-one-way-unify1
              concl
              (access forward-chaining-rule rule :concls)
              unify-subst)))))

(defun satisfying-virtual-fc-activationp (criteria act0 unify-subst)
  (cond ((endp criteria) nil)
        (t (or (satisfying-virtual-fc-activation1p (car criteria)
                                                   act0 unify-subst)
               (satisfying-virtual-fc-activationp (cdr criteria)
                                                  act0 unify-subst)))))


; The notion of a satisfying fc-activation extends naturally to the notion of a
; satisfying fc-derivation.  However, by the time we get to fc-derivations we
; can check equality of the instantiated conclusion to the concl sought.

(defun satisfying-fc-derivation1p (criterion fcd)
  (let ((rune (car criterion))
        (trig (cadr criterion))
        (concl (caddr criterion)))
    (and (or (eq rune t)
             (equal rune
                    (access fc-derivation fcd :rune)))
         (or (eq trig t)
             (equal trig
                    (access fc-derivation fcd :inst-trigger)))
         (or (eq concl t)
             (equal concl
                    (access fc-derivation fcd :concl))))))

(defun satisfying-fc-derivationp (criteria fcd)
  (cond ((endp criteria) nil)
        (t (or (satisfying-fc-derivation1p (car criteria) fcd)
               (satisfying-fc-derivationp (cdr criteria) fcd)))))

(defun collect-satisfying-fc-derivations (criteria fcd-lst ans)

; Accumulate all satisfying fc-derivations in fcd-lst onto ans.

  (cond ((endp fcd-lst) ans)
        ((satisfying-fc-derivationp criteria (car fcd-lst))
         (collect-satisfying-fc-derivations criteria
                                            (cdr fcd-lst)
                                            (cons (car fcd-lst) ans)))
        (t (collect-satisfying-fc-derivations criteria (cdr fcd-lst) ans))))

; We now define the functions that move information into the five fc-wormhole
; sites.  We call this ``filtering'' because we only move the objects that
; satisfy the criteria.

(defun filter-satisfying-virtual-fc-activation (act0 inst-hyp hyps unify-subst ttree)

; This is the function that adds an activation to the
; :blocked-false-satisfying-activations, aka site (1), of the current
; forward-chain-top call, provided the activation satisfies the criteria.  This
; is called from both advance-fc-activation1 and advance-fc-activation2, which
; are the two functions that detect false hypotheses.  Those two functions will
; not actually have the realized activation available to them (without consing
; it up).  Instead, they have act0, inst-hyp, hyps, unify-subst, and ttree.
; The actual activation being considered is that obtained by putting those
; fields into act0, something that the advance-fc-activation functions don't do
; unnecessarily.  But we must create the actual from the virtual if we wish to
; save the actual activation.  This function avoids creating the activation if
; it is not satisfying.

; The prefix ``filter'' in this name is a little misleading.  We generally use
; that prefix to suggest mapping over a list and extracting the ones satisfying
; some criteria.  But here we have just one virtual activation and we either
; save it or not depending on whether it is satisfying.

  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (let ((criteria (cdr (assoc-eq :CRITERIA (wormhole-data whs)))))
        (cond
         ((null criteria) whs)
         ((satisfying-virtual-fc-activationp
           criteria
           act0 unify-subst)
; At this point we know we need the activation.  So we get comfortable.
          (let* ((data (wormhole-data whs))
                 (calls-alist (cdr (assoc-eq :FORWARD-CHAIN-CALLS data)))
                 (k (car (car calls-alist)))
                 (call-alist (cdr (car calls-alist)))
                 (act (suspend-fc-activation act0 inst-hyp hyps
                                             unify-subst ttree)))
            (set-wormhole-data
             whs
             (put-assoc-eq
              :FORWARD-CHAIN-CALLS
              (cons (cons k
                          (put-assoc-eq
                           :BLOCKED-FALSE-SATISFYING-ACTIVATIONS
                           (cons act
                                 (cdr (assoc-eq
                                       :BLOCKED-FALSE-SATISFYING-ACTIVATIONS
                                       call-alist)))
                           call-alist))
                    (cdr calls-alist))
              data))))
         (t whs))))
   :no-wormhole-lock))

(defun filter-all-satisfying-fc-derivations (fcd-lst)

; This function moves satisfying fcds from fcd-lst into site (2) of the current
; call of forward-chain-top.

; Two of our sites, (2) all-satisfying-fc-derivations and (3)
; approved-satisfying-fc-derivations, contain fc-derivations.  The process of
; collecting into these sites is the same: we map over some fcd-lst and cons
; every satisfying fcd onto the appropriate site.  One possibly confusing
; difference between the handling of these two sites is that to collect into
; site (2) we must call this function repeatedly during forward chaining, once
; per round, because it is only at the level of a round (forward-chain1) that
; we know all the fc-derivations made in a round.  But the top-level
; forward-chain-top process keeps track of all approved fc-derivations, so we
; call the guts of this function just once on the other site at the top-level
; (as we exit forward-chain-top) to filter site (3).

  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (let ((criteria (cdr (assoc-eq :CRITERIA (wormhole-data whs)))))
        (cond
         ((null criteria) whs)
         (t
          (let* ((data (wormhole-data whs))
                 (calls-alist (cdr (assoc-eq :FORWARD-CHAIN-CALLS data)))
                 (k (car (car calls-alist)))
                 (call-alist (cdr (car calls-alist))))
            (set-wormhole-data
             whs
             (put-assoc-eq
              :FORWARD-CHAIN-CALLS
              (cons (cons k
                          (put-assoc-eq
                           :ALL-SATISFYING-FC-DERIVATIONS
                           (collect-satisfying-fc-derivations
                            criteria
                            fcd-lst
                            (cdr (assoc-eq :ALL-SATISFYING-FC-DERIVATIONS
                                           call-alist)))
                           call-alist))
                    (cdr calls-alist))
              data)))))))
   :no-wormhole-lock))

(defun filter-satisfying-fc-activations (acts)

; Site (4) is leftover-activations.  At the termination of forward-chaining we
; are holding a list of all still-suspended fc-activations and this is the
; function that filters that list into site 4 of the current call of
; forward-chain-top.

  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (let ((criteria (cdr (assoc-eq :CRITERIA (wormhole-data whs)))))
        (cond
         ((null criteria) whs)
         (t (let* ((data (wormhole-data whs))
                   (calls-alist (cdr (assoc-eq :FORWARD-CHAIN-CALLS data)))
                   (k (car (car calls-alist)))
                   (call-alist (cdr (car calls-alist))))
              (set-wormhole-data
               whs
               (put-assoc-eq
                :FORWARD-CHAIN-CALLS
                (cons (cons k
                            (put-assoc-eq
                             :LEFTOVER-ACTIVATIONS
                             (collect-satisfying-fc-activations
                              criteria
                              acts
                              (cdr (assoc-eq :LEFTOVER-ACTIVATIONS
                                             call-alist)))
                             call-alist))
                      (cdr calls-alist))
                data)))))))
   :no-wormhole-lock))

(defun filter-redundant-approved-fc-derivation (fcd)

; We move fcd into site (5), :REDUNDANT-APPROVED-FC-DERIVATIONS, provided fcd
; meets the criteria.  By calling this function on fcd we are indicating that
; the conclusion of the fcd was already known true under the type-alist.

  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (let ((criteria (cdr (assoc-eq :CRITERIA (wormhole-data whs)))))
        (cond ((null criteria) whs)
              ((satisfying-fc-derivationp criteria fcd)
               (let* ((data (wormhole-data whs))
                      (calls-alist (cdr (assoc-eq :FORWARD-CHAIN-CALLS data)))
                      (k (car (car calls-alist)))
                      (call-alist (cdr (car calls-alist))))
                 (set-wormhole-data
                  whs
                  (put-assoc-eq
                   :FORWARD-CHAIN-CALLS
                   (cons (cons k
                               (put-assoc-eq
                                :REDUNDANT-APPROVED-FC-DERIVATIONS
                                (cons fcd
                                      (cdr (assoc-eq :REDUNDANT-APPROVED-FC-DERIVATIONS
                                                     call-alist)))
                                call-alist))
                         (cdr calls-alist))
                   data))))
              (t whs))))
   :no-wormhole-lock))

; So now we have got the machinery to populate sites (1)-(5) of the
; current call of forward-chain-top.

; When forward-chain-top is about to exit, we finish the task of recording the
; results of the current call.  fc-exit This consists of three main parts: we
; move some accumulated data into sites 3 and 4 (sites 1 and 2 will be
; accumulated as we go), we generate a report that is either long or short
; depending on the :REPORT-ON-THE-FLYP flag, and we store the returned values.

; We now develop the machinery to report.  Reports take two forms, a long and short
; form.  The short form is just:

; (Forward-chaining called by caller.  See (FC-Report k).)

; where caller is the token indicating the caller of forward-chain-top and k is
; the call-number of the current call of forward-chain-top.

; The long form will summarize all the activity.  We will arrange for the
; function fc-report to print the long form after the fact and we'll print the
; long form on the fly if the flag is set.

; A difficulty with reporting is that activations branch as free variables are
; instantiated.  Thus, a rule triggered by a given term may have many final
; unify-substs and dispositions.  The report therefore lists every rule and
; trigger term and then all the dispositions:

;  (<rune>
;   (:TRIGGER <inst-term>)
;   ((:UNIFY-SUBST <pretty-subst>)
;    (:DISPOSITION <outcome> <reason> <term>))
;   ...
;   ((:UNIFY-SUBST <subst>)
;    (:DISPOSITION <outcome> <reason> <term>)))

; We prepare this report in its raw form and will just print it.  The user may
; want to process it further with some attachment.

; When we begin to create the report we have:

; (1) blocked-false-satisfying-activations - every satisfying fc-activation
;     found to have a false hyp

; (2) all-satisfying-fc-derivations - every fc-derivation that satisfies the
;     criteria

; (3) approved-satisfying-fc-derivations - the fc-derivations that both satisfy
;     the criteria and were approved

; (4) leftover-activations - all activations still suspended at the termination
;     of forward chaining

; Recall that the status of an activation consists of its unify-subst (which
; completes the identification of the branch) and the disposition:

; (a) SUCCESS APPROVED <term> -- successfully fired and gave us <term>
; (b) SUCCESS REJECTED <term> -- successfully fired but conclusion <term> was disapproved
; (c) SUCCESS REDUNDANT <term> -- successfully fired and approved but already known
; (d) BLOCKED UNRELIEVED-HYPx <hyp> -- unable to relieve <hyp>
; (e) BLOCKED FALSE <hyp> --  hyp shown false <hyp>

; Our strategy will be first to collect all (rune . inst-trigger) pairs and
; then, for each such pair, map over each of the sites (1)-(5) to collect the
; status of that pair.

; To collect all (rune . inst-trigger) pairs we have to map over sites (1),
; (2), and (4), i.e., all blocked false activations, all fc-derivations, and
; all still-suspended activations.

(defun collect-rune-trigger-pairs-from-fc-activations (acts ans)
  (cond ((endp acts) ans)
        (t (collect-rune-trigger-pairs-from-fc-activations
            (cdr acts)
            (add-to-set-equal (cons (access forward-chaining-rule
                                            (access fc-activation (car acts) :rule)
                                            :rune)
                                    (access fc-activation (car acts) :inst-trigger))
                              ans)))))

(defun collect-rune-trigger-pairs-from-fc-derivations (fcds ans)
  (cond ((endp fcds) ans)
        (t (collect-rune-trigger-pairs-from-fc-derivations
            (cdr fcds)
            (add-to-set-equal (cons (access fc-derivation (car fcds) :rune)
                                    (access fc-derivation (car fcds) :inst-trigger))
                              ans)))))

; Once we've collected all the rune-trigger pairs, we can map over each site to
; collect the status information for each pair.

(defun prettyify-subst (alist)
; Turn a dotted-pair alist into a doublet alist, e.g.,
; ((X CAR A) (Y . B)) into ((X (CAR A)) (Y B)).
  (cond ((endp alist) nil)
        (t (cons (list (car (car alist)) (cdr (car alist)))
                 (prettyify-subst (cdr alist))))))

(defun collect-fc-status-site-1 (rune inst-trigger acts)

; Acts is site (1) blocked-false-satisfying-activations - every satisfying
; fc-activation found to have a false hyp.  Note that when we store a
; satisfying activation at this site we put the inst-hyp (which was either
; type-set to *ts-nil* or evaluated to *nil*) into the activation.  The hyp
; cannot possibly have free vars in it (because we never choose instantiations
; to falsify a hyp).  It may have a FORCE or CASE-SPLIT on it, but that's ok
; because type-set and eval handle those functions and accurately determined
; that the inst-hyp is false.

  (cond
   ((endp acts) nil)
   ((and (equal rune
                (access forward-chaining-rule
                        (access fc-activation (car acts) :rule)
                        :rune))
         (equal inst-trigger
                (access fc-activation (car acts) :inst-trigger)))
    (cons `((:UNIFY-SUBST
             ,(prettyify-subst (access fc-activation (car acts) :unify-subst)))
            (:DISPOSITION BLOCKED FALSE
                          ,(access fc-activation (car acts) :inst-hyp)))
          (collect-fc-status-site-1 rune inst-trigger (cdr acts))))
   (t (collect-fc-status-site-1 rune inst-trigger (cdr acts)))))

(defun collect-fc-status-sites-2-3-5 (rune inst-trigger all-fcds
                                           approved-fcds
                                           redundant-approved-fc-derivations)

; All-fcds is site (2) all-satisfying-fc-derivations - every fc-derivation that
; satisfies the criteria, approved-fcds is site (3)
; approved-satisfying-fc-derivations - the fc-derivations that both satisfy the
; criteria and were approved, and redundant-approved-fc-derivations is site
; (5).  We map down all-fcds and use the other two to determine if whether each
; was approved, redundant, or rejected.

  (cond
   ((endp all-fcds) nil)
   ((and (equal rune
                (access fc-derivation (car all-fcds) :rune))
         (equal inst-trigger
                (access fc-derivation (car all-fcds) :inst-trigger)))
    (cons `((:UNIFY-SUBST
             ,(prettyify-subst (access fc-derivation (car all-fcds) :unify-subst)))
            (:DISPOSITION
             SUCCESS
             ,(if (member-equal (car all-fcds) approved-fcds)
                  (if (member-equal (car all-fcds) redundant-approved-fc-derivations)
                      'REDUNDANT
                      'APPROVED)
                  'REJECTED)
             ,(access fc-derivation (car all-fcds) :concl)))
          (collect-fc-status-sites-2-3-5 rune inst-trigger (cdr all-fcds)
                                         approved-fcds
                                         redundant-approved-fc-derivations)))
   (t (collect-fc-status-sites-2-3-5 rune inst-trigger (cdr all-fcds)
                                     approved-fcds
                                     redundant-approved-fc-derivations))))

(defun prettyify-blocked-fc-inst-hyp (inst-hyp hyps unify-subst)

; The arguments are those respective fields in some fc-activation.  Hence,
; inst-hyp is either the :FC-FREE-VAR marker (which implicitly depends on the
; contents of the hyp and unify-subst fields) or an instantiated hyp.  We
; recover the actual (partially) instantiated hyp we're stuck on.

  (cond ((and (consp inst-hyp)
              (eq (car inst-hyp) :FC-FREE-VARS))
         (let ((hyp (sublis-var
                     (bind-free-vars-to-unbound-free-vars
                      (all-vars (car hyps))
                      unify-subst)
                     (car hyps))))
           (if (cadr inst-hyp) ; then FORCE or CASE-SPLIT should be added
               `(,(cadr inst-hyp) ,hyp)
               hyp)))
        (t inst-hyp)))

(defun collect-fc-status-site-4 (rune inst-trigger acts)

; Acts is site (4) leftover-activations - all activations still suspended at
; the termination of forward chaining.

  (cond
   ((endp acts) nil)
   ((and (equal rune
                (access forward-chaining-rule
                        (access fc-activation (car acts) :rule)
                        :rune))
         (equal inst-trigger
                (access fc-activation (car acts) :inst-trigger)))
    (let ((inst-hyp (access fc-activation (car acts) :inst-hyp)))
      (cons `((:UNIFY-SUBST
               ,(prettyify-subst (access fc-activation (car acts) :unify-subst)))
              (:DISPOSITION BLOCKED
                            ,(if (and (consp inst-hyp)
                                      (eq (car inst-hyp) :FC-FREE-VARS))
                                 'UNRELIEVED-HYP-FREE
                                 'UNRELIEVED-HYP)
                            ,(prettyify-blocked-fc-inst-hyp
                              inst-hyp
                              (access fc-activation (car acts) :hyps)
                              (access fc-activation (car acts) :unify-subst))))
            (collect-fc-status-site-4 rune inst-trigger (cdr acts)))))
   (t (collect-fc-status-site-4 rune inst-trigger (cdr acts)))))

(defun collect-fc-status (rune inst-trigger site1 site2 site3 site4 site5)

; Given a rune and instantiated trigger term we collect the final status of
; every activation of that pair recorded in the sites.  Every activation
; (derivation) in the sites is known to satisfy the criteria.

  `(,rune
    (:TRIGGER ,inst-trigger)
    ,@(collect-fc-status-site-1 rune inst-trigger site1)
    ,@(collect-fc-status-sites-2-3-5 rune inst-trigger site2 site3 site5)
    ,@(collect-fc-status-site-4 rune inst-trigger site4)))

(defun make-fc-activity-report1 (rune-trigger-pairs site1 site2 site3 site4 site5)

; Given a list of (rune . inst-trigger) pairs and the four sites, we
; collect the final status of each pair.

  (cond ((endp rune-trigger-pairs) nil)
        (t (cons (collect-fc-status (car (car rune-trigger-pairs))
                                    (cdr (car rune-trigger-pairs))
                                    site1 site2 site3 site4 site5)
                 (make-fc-activity-report1 (cdr rune-trigger-pairs)
                                         site1 site2 site3 site4 site5)))))

(defun make-fc-activity-report (call-alist)

; Given the data collected in the fc-wormhole by forward-chain-top, we prepare
; the final status reports of every activation satisfying the criteria.

  (let* ((site1
          (cdr (assoc-eq :blocked-false-satisfying-activations call-alist)))
         (site2
          (cdr (assoc-eq :all-satisfying-fc-derivations call-alist)))
         (site3
          (cdr (assoc-eq :approved-satisfying-fc-derivations call-alist)))
         (site4
          (cdr (assoc-eq :leftover-activations call-alist)))
         (site5
          (cdr (assoc-eq :redundant-approved-fc-derivations call-alist)))
         (rune-trigger-pairs
          (collect-rune-trigger-pairs-from-fc-activations
           site1
           (collect-rune-trigger-pairs-from-fc-derivations
            site2
            (collect-rune-trigger-pairs-from-fc-activations
             site4 nil)))))
    (merge-sort-lexorder
     (make-fc-activity-report1 rune-trigger-pairs
                               site1 site2 site3 site4 site5))))

(defun fc-report1 (whs k)

; We assume we are in the fc-wormhole when this function is called.  It takes
; the wormhole status and an alleged caller number, k, and prints the report
; for the kth call of forward-chain-top.  It returns nil.

  (let* ((data (wormhole-data whs))
         (calls-alist (cdr (assoc-eq :FORWARD-CHAIN-CALLS data)))
         (temp (assoc-equal k calls-alist)))
    (cond
     ((and temp
           (cdr (assoc-eq :OUTPUT (cdr temp))))
      (let* ((call-alist (cdr temp))
             (input (cdr (assoc-eq :INPUT call-alist)))
             (caller (car input))
             (clause (cadr input))
             (output (cdr (assoc-eq :OUTPUT call-alist)))
             (flg (car output))
             (rounds (cdr (assoc-eq :ROUNDS call-alist)))
             (activity (make-fc-activity-report call-alist)))
        (cw "~%~
       -----------------------------------------------------------------~%~
       Forward Chaining Report ~x0:~%~
       Caller: ~x1~%~
       Clause: ~x2~%~
       Number of Rounds: ~x3~%~
       Contradictionp: ~x4~%~
       Activations:~%~
       ~x5~%~
       -----------------------------------------------------------------~%"
            k
            caller
            clause
            rounds
            flg
            activity)))
     (t (cw "~%There is no Forward Chaining Report for ~x0.~%"
            k)))))

(defun fc-report (k)

; This function is intended to be called from outside the fc-wormhole,
; by the user.

  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (let ((criteria (cdr (assoc-eq :CRITERIA (wormhole-data whs)))))
        (cond
         ((null criteria) whs)
         (t (prog2$ (fc-report1 whs k) whs)))))
   nil))

; As noted above, when forward-chain-top is about to exit, we finish the task
; of recording the results of the current call.  We move some accumulated data
; into sites 3 and 4 (sites 1 and 2 will be accumulated as we go), we generate
; a report that is either long or short depending on the :REPORT-ON-THE-FLYP
; flag, and we store the returned values.

(defun fc-exit (flg type-alist ttree-or-fc-pairs
                    caller rounds all-approved-fcds all-leftover-activations)

; We exit forward-chain-top by calling this function.  Logically you can think
; of this function as just:

; (mv flg type-alist ttree-or-fc-pairs)

; The other arguments are used to report on forward-chaining.

; At the time this is called we will have already fully loaded sites (1) and
; (2), i.e., the satisfying activations with false hyps and the list of all
; satisfying fc-derivations.  We load sites (3) and (4) -- the approved
; satisfying fc-derivations and the (satisfying) leftover activations -- here,
; using the supplied all-approved-fcds and all-leftover-activations arguments.
; Then we generate a report -- long or short as appropriate -- and return.

  (prog2$
   (wormhole-eval
    'fc-wormhole
    '(lambda (whs)
       (let ((criteria (cdr (assoc-eq :CRITERIA (wormhole-data whs)))))
         (cond
          ((null criteria) whs)
         (t (let* ((data (wormhole-data whs))
                   (calls-alist (cdr (assoc-eq :FORWARD-CHAIN-CALLS data)))
                   (k (car (car calls-alist)))
                   (call-alist (cdr (car calls-alist)))
                   (new-data
                    (put-assoc-eq
                     :FORWARD-CHAIN-CALLS
                     (cons (cons k
                                 (put-assoc-eq
                                  :APPROVED-SATISFYING-FC-DERIVATIONS
                                  (collect-satisfying-fc-derivations
                                   criteria all-approved-fcds nil)
                                  (put-assoc-eq
                                   :LEFTOVER-ACTIVATIONS
                                   (collect-satisfying-fc-activations
                                    criteria all-leftover-activations nil)
                                   (put-assoc-eq
                                    :ROUNDS rounds
                                    (put-assoc-eq
                                     :OUTPUT
                                     (list flg type-alist ttree-or-fc-pairs)
                                    call-alist)))))
                           (cdr calls-alist))
                     data))
                   (new-whs (set-wormhole-data whs new-data)))
              (cond
               ((cdr (assoc-eq :REPORT-ON-THE-FLYP new-data))
                (prog2$ (fc-report1 new-whs k)
                        new-whs))
               (t (prog2$
                   (cw "~%(Forward Chaining on behalf of ~x0:  (FC-Report ~x1))~%"
                       caller k)
                   new-whs))))))))
    :no-wormhole-lock)
   (mv flg type-alist ttree-or-fc-pairs)))

; Explanation of the Kernel Code for FC Advancement

; The mutual-recursion nest below is the kernel code for advancing
; fc-activations.  There is a wrapper defined afterwards.  The kernel functions
; advance an activation along all possible threads and return a list of
; suspensions created only when they finally get stuck on some hypothesis.  But
; in the mutual recursion keep in mind act0, inst-hyps, hyps, unify-subst, and
; ttree.  Initially, act0 is the fc-activation with which we started.
; Initially, the other four were just the obvious fields extracted from this
; activation.  But as we recur we may change the other four.  When we finally
; get stuck, we suspend act0 by setting all four of the fields because we don't
; know which ones have changed.  The function suspend-fc-activation optimizes
; the construction for common cases of unchanged fields.

; The mutual recursion has 3 functions or phases and their names end in 1, 2,
; and 3.  Phase (1) works on the inst-hyp, which is either an :FC-FREE-VARS
; marker or the instantiated hyp upon which we were stuck the last time we saw
; this activation.  If the inst-hyp is just an instantiated hyp and we find it
; to be true now, we enter phase (2) below to work on the other hyps.  If the
; inst-hyp is a :FC-FREE-VARS marker and we find instances of it that are true,
; we enter phase (3) to pursue each possible unify-subst and ttree, but we also
; generally re-suspend in case further instances come along as the type-alist
; grows.  Phase (2) just loops down hyps calling itself recursively.  However,
; if it sees a hyp containing a free variable, it just manufactures an
; appropriate inst-hyp and calls phase (1) so we don't reproduce that code.
; Finally, Phase (3) just loops through the unify-substs and ttrees generated
; by finding suitable instances and calls phase (2) on the rest of the hyps.

; So the call graph of this nest is:
; (1) calls
;     (2) to go on to the rest of the hyps and
;     (3) to pursue each choice of free vars
; (2) calls
;     (1) to handle free vars and
;     (2) to go on to the rest of the hyps
; (3) calls
;     (2) to handle a given unify-subst and
;     (3) to handle the rest of the unify-substs.

; All of these functions accumulate suspensions of the newly advanced act0 onto
; suspensions and derived conclusions (in the form of fc-derivations) onto
; fcd-lst.  It is only in the base case of phase (2), when hyps is nil, that we
; convert successful terminal fc-activations into fc-derivations.

; If we're asked to FORCE or CASE-SPLIT on a hyp that contains free variables
; and we are unable to find a true match for it on the type-alist, we
; immediately force or split on it, binding the free variables to variables
; with "UNBOUND-FREE-" prefixed onto the existing names.  In principle we can
; bind the free variables of a hyp to any term.  We chose these names in the
; hope that they catch the eye of the user when they appear in failed proofs.
; The user was warned of this possibility when a forward-chaining rule was
; built with a forced or split hyp containing free variables.  Also, when
; forcing or splitting on a hypothesis containing free vars we don't produce a
; suspension to find new instances because that would just keep spitting out
; UNBOUND-FREE variables.

(mutual-recursion

(defun advance-fc-activation1
  (act0 inst-hyp hyps unify-subst ttree                       ; key args
         fc-round type-alist ens force-flg wrld state oncep-override   ; contextual args
         suspensions fcd-lst)                                 ; answers

; See explanation above the mutual-recursion nest.

  (cond
   ((and (consp inst-hyp)
         (eq (car inst-hyp) :FC-FREE-VARS))

    (let ((forcer-fn (cadr inst-hyp)) ; nil, FORCE, or CASE-SPLIT
          (last-keys-seen (cddr inst-hyp)))

; When inst-hyp is the marker, the hyp we are to relieve is the first one in
; hyps.  Any FORCE or CASE-SPLIT has been removed but recorded in the forcer-fn
; field.  Last-keys-seen is the list of all type-alist keys from which matches
; have already been produced.

      (let* ((hyp (car hyps))
             (rule (access fc-activation act0 :rule))
             (oncep1
              (oncep oncep-override
                     (access forward-chaining-rule rule :match-free)
                     (access forward-chaining-rule rule :rune)
                     (access forward-chaining-rule rule :nume))))

; Hyp is the hypothesis we are stuck on.

; We match hyp/unify-subst against the true terms in type-alist, in all
; possible ways, obtaining lists of the extended unify-substs and their
; respective ttrees, and a list of the key terms from the type-alist
; used to produce these unifications.

        (mv-let (new-unify-subst-list new-ttree-list new-keys-seen)
                (mult-lookup-hyp hyp (cdr hyps)
                                 (access forward-chaining-rule
                                         (access fc-activation act0 :rule)
                                         :concls)
                                 type-alist
                                 wrld unify-subst ttree
                                 oncep1
                                 last-keys-seen
                                 ens)
                (cond
                 (new-unify-subst-list

; We found one or more extensions of unify-subst and pursue all of them.
; Normally we also suspend any activation that is stuck on a free-var hyp in
; case future type-alists permit other matches, but if this rule has explicitly
; been tagged as using the first binding (as now stored in the flag oncep1) or
; if this hyp is to be forced or split upon we don't also suspend it.

                  (advance-fc-activation3
                   act0 (cdr hyps) new-unify-subst-list new-ttree-list
                   fc-round type-alist ens force-flg wrld state oncep-override
                   (if (or oncep1 (and forcer-fn force-flg))
                       suspensions
                       (cons (suspend-fc-activation
                              act0
                              (list* :FC-FREE-VARS
                                     forcer-fn
                                     (append new-keys-seen
                                             last-keys-seen))
                              hyps
                              unify-subst
                              ttree)
                             suspensions))
                   fcd-lst))
                 ((and forcer-fn force-flg)

; In this case, we found no instances of this hyp on type-alist and it
; is supposed to be forced (or case-split).  So we must assume something
; to move forward.  We replace its free vars with UNBOUND-FREE-vars and
; proceed, without saving a suspension.

                  (let ((fully-bound-unify-subst
                         (bind-free-vars-to-unbound-free-vars
                          (all-vars hyp)
                          unify-subst)))
                    (mv-let (new-force-flg ttree)
                            (force-assumption
                             (access forward-chaining-rule
                                     (access fc-activation act0 :rule)
                                     :rune)
                             (access fc-activation act0 :inst-trigger)
                             (sublis-var fully-bound-unify-subst hyp)
                             type-alist nil
                             (immediate-forcep forcer-fn ens)
                             force-flg
                             ttree)
; Force-assumption always returns an unchanged force-flg which we just ignore.
                            (declare (ignore new-force-flg))
                            (advance-fc-activation2
                             act0 (cdr hyps) unify-subst ttree
                             fc-round type-alist ens force-flg wrld state
                             oncep-override
                             suspensions
                             fcd-lst))))
                 (t

; In this case, we are stuck on a hyp with free vars, no match is
; available, and we're not supposed to force it.  So we create a
; suspension.

                  (mv (cons (suspend-fc-activation
                             act0
                             (list* :FC-FREE-VARS
                                    forcer-fn
                                    (append new-keys-seen
                                            last-keys-seen))
                             hyps
                             unify-subst
                             ttree)
                            suspensions)
                      fcd-lst)))))))

   (t

; In this case, we're stuck on a fully instantiated hyp,
; hypn/unify-subst, where hypn had no free variables and is not an
; evaluable ground term, or a FORCE or CASE-SPLIT.  Inst-hyp must be
; true under type-alist to proceed.

    (mv-let
     (ts ttree1)
     (type-set inst-hyp force-flg nil type-alist ens wrld nil
                      nil nil)
     (cond
      ((ts= ts *ts-nil*)

; This hyp has been shown false.  We just let the activation
; evaporate by not including this suspension of act0 in our answer.

       (prog2$
        (filter-satisfying-virtual-fc-activation ; (FC Report)
         act0 inst-hyp hyps unify-subst ttree)
        (mv suspensions
            fcd-lst)))
      ((ts-intersectp ts *ts-nil*)

; The value of hyp is indeterminate.  We suspend it.  It is tempting to
; think of the suspension below as being identical to act0 -- i.e., no
; changes -- but we're in recursion, so who knows?
; Suspend-fc-activation will check if anything changed.

       (mv (cons (suspend-fc-activation act0 inst-hyp hyps
                                        unify-subst ttree)
                 suspensions)
           fcd-lst))
      (t

; Finally!  We're past inst-hyp and begin to work our way down hyps.

       (advance-fc-activation2
        act0 hyps unify-subst (cons-tag-trees ttree1 ttree)
        fc-round type-alist ens force-flg wrld state oncep-override
        suspensions fcd-lst)))))))

(defun advance-fc-activation2
  (act0 hyps unify-subst ttree                               ; key args
        fc-round type-alist ens force-flg wrld state oncep-override   ; contextual args
        suspensions fcd-lst)                                 ; answers

; See explanation above the mutual-recursion nest.

  (cond
   ((null hyps)

; We succeeded in relieving all the hypotheses of this activation.  We
; produce the resultant fc-derivations and add them to fcd-lst.

    (mv suspensions
        (add-fc-derivations (access forward-chaining-rule
                                    (access fc-activation act0 :rule)
                                    :rune)
                            (sublis-var-lst
                             unify-subst
                             (access forward-chaining-rule
                                     (access fc-activation act0 :rule)
                                     :concls))
                            unify-subst
                            (access fc-activation act0 :inst-trigger)
                            fc-round ens wrld state
                            ttree
                            fcd-lst)))
   (t
    (let* ((forcep1 (and (nvariablep (car hyps))
;                        (not (fquotep (car hyps)))
                         (or (eq (ffn-symb (car hyps)) 'force)
                             (eq (ffn-symb (car hyps)) 'case-split))))
           (forcer-fn (and forcep1 (ffn-symb (car hyps))))
           (hyp (if forcep1 (fargn (car hyps) 1) (car hyps))))
      (cond
       ((free-varsp hyp unify-subst)

; To avoid code duplication we let advance-fc-activation1 handle all
; free var situations:
        (advance-fc-activation1
         act0
         (if forcer-fn
             (if (eq forcer-fn 'FORCE)
                 '(:FC-FREE-VARS FORCE . nil)
                 '(:FC-FREE-VARS CASE-SPLIT . nil))
             '(:FC-FREE-VARS nil . nil))
         (cons hyp (cdr hyps))
         unify-subst
         ttree
         fc-round type-alist ens force-flg wrld state oncep-override
         suspensions fcd-lst))
       (t

; Hyp contains no free vars, so we instantiate it and then use any of
; three methods (depending on the instance) to decide if it is true:
; type-set with the current type-alist, ground evaluation, or
; forcing/case splitting.

        (let ((inst-hyp (sublis-var unify-subst hyp)))
          (mv-let (ts ttree1)
                  (type-set inst-hyp force-flg nil type-alist ens wrld nil
                            nil nil)

; Note that ttree1 is the ttree associated with the type-set computation
; and that it does not include ttree.  If we use the type-set
; information, we must add ttree1 to ttree.

                  (cond
                   ((ts= ts *ts-nil*)
; Inst-hyp is false under the current type-alist, so we just
; abandon this activation.
                    (prog2$
                     (filter-satisfying-virtual-fc-activation ; (FC Report)
                      act0 inst-hyp hyps unify-subst ttree)
                     (mv suspensions
                         fcd-lst)))
                    ((ts-intersectp ts *ts-nil*)
                     (cond
                      ((not (free-varsp inst-hyp nil))

; This means that inst-hyp is actually a ground term.  We try to
; evaluate it.  Note that we do not try to eval or even partially eval
; non-ground hyps.  For example, the translation of (OR (NATP '1) (NATP
; A)) will eval non-erroneously to T and the translation of (AND (NATP
; '1) (NATP A)) will eval-ground-subexpressions to (NATP A).  So there
; may be some merit in a fancier treatment of evaluation.  However,
; rewriting a hyp, even via evaluation, might be problematic in this
; setting since the only way we can decide a non-trivial inst-hyp is via
; type-set, which is often just an assoc-equal.  So for the moment we're
; only using evaluation on ground terms where it makes the most sense.

                       (mv-let
                        (erp val latches ttree2)
                        (ev-respecting-ens
                         inst-hyp nil state nil nil ens wrld)
                        (declare (ignore latches))

; Note that ttree2 is the ttree for the evaluation and it does not
; include ttree or ttree1.  We are not using the type-set stuff because
; it only told us that inst-hyp was nil or non-nil.  But the evaluation
; ttree should be added to the original ttree if we use the evaluation
; result.

                        (cond
                         (erp

; This hyp cannot be evaluated, e.g., perhaps it contains a constrained
; function.  So we must either force it or wait for it to come up on the
; type-alist.  Note that in this part be ignore type-set's ttree1 and
; the evaluator's ttree2.

                          (mv-let
                           (force-flg ttree)
                           (cond
                            ((or (not forcep1) (not force-flg))
                             (mv nil ttree))
                            (t
                             (force-assumption
                              (access forward-chaining-rule
                                      (access fc-activation act0 :rule)
                                      :rune)
                              (access fc-activation act0 :inst-trigger)
                              inst-hyp
                              type-alist nil
                              (immediate-forcep forcer-fn ens)
                              force-flg
                              ttree)))
                           (cond
                            (force-flg

; Inst-hyp is ground but cannot be evaluated and is supposed to be forced or
; split upon.  So we did that and the result is in ttree.  Therefore, we
; just move on.
                             (advance-fc-activation2
                              act0 (cdr hyps) unify-subst ttree
                              fc-round type-alist ens force-flg wrld state oncep-override
                              suspensions fcd-lst))
                            (t

; Inst-hyp is ground but cannot be evaluated and is not supposed to be
; forced.  So we just suspend it.  Note that inst-hyp satisfies our
; invariant on fc-activations: it contains no free vars, is not an
; evaluable ground term, and is not a FORCE or CASE-SPLIT.  We just have
; to wait until the type-alist makes it true.

                             (mv (cons (suspend-fc-activation
                                        act0
                                        inst-hyp
                                        (cdr hyps)
                                        unify-subst
                                        ttree)
                                       suspensions)
                                 fcd-lst)))))
                         (val

; Inst-hyp evaluated to non-nil, so we just move on (using the evaluator's
; ttree2) plus the original one.

                          (advance-fc-activation2
                           act0 (cdr hyps) unify-subst
                           (cons-tag-trees ttree2 ttree)
                           fc-round type-alist ens force-flg wrld state oncep-override
                           suspensions fcd-lst))
                         (t

; Inst-hyp evaluated to nil, so we just abandon the activation.
; Forcing considerations are irrelevant here.

                          (prog2$
                           (filter-satisfying-virtual-fc-activation ; (FC Report)
                            act0 inst-hyp hyps unify-subst ttree)
                           (mv suspensions
                               fcd-lst))))))
                      (t

; Inst-hyp contains variables and so we don't even try evaluation --
; even though there are expressions containing variables and IFs that
; evaluate to constants.  Instead, we just see whether we should force
; it.  We ignore type-set's ttree1.

                       (mv-let
                        (force-flg ttree)
                        (cond
                         ((or (not forcep1) (not force-flg))
                          (mv nil ttree))
                         (t
                          (force-assumption
                           (access forward-chaining-rule
                                   (access fc-activation act0 :rule)
                                   :rune)
                           (access fc-activation act0 :inst-trigger)
                           inst-hyp
                           type-alist nil
                           (immediate-forcep forcer-fn ens)
                           force-flg
                           ttree)))
                        (cond
                         (force-flg

; Inst-hyp has been forced.  So just move on.

                          (advance-fc-activation2
                           act0 (cdr hyps) unify-subst ttree
                           fc-round type-alist ens force-flg wrld state oncep-override
                           suspensions fcd-lst))
                         (t

; Inst-hyp ``cannot'' be evaluated and is not supposed to be
; forced.  So we just suspend it.  Note that inst-hyp satisfies our
; invariant on fc-activations: it contains no free vars, is not an
; evaluable ground term, and is not a FORCE or CASE-SPLIT.  We just have
; to wait until the type-alist makes it true.

                          (mv (cons (suspend-fc-activation
                                     act0
                                     inst-hyp
                                     (cdr hyps)
                                     unify-subst
                                     ttree)
                                    suspensions)
                              fcd-lst)))))))
                    (t

; Inst-hyp is true under type-alist.  We add type-set's ttree1 to ttree
; as we move on.

                     (advance-fc-activation2
                      act0 (cdr hyps) unify-subst
                      (cons-tag-trees ttree1 ttree)
                      fc-round type-alist ens force-flg wrld state oncep-override
                      suspensions fcd-lst)))))))))))

(defun advance-fc-activation3
  (act0 hyps unify-subst-lst ttree-lst                       ; key args
        fc-round type-alist ens force-flg wrld state oncep-override   ; contextual args
        suspensions fcd-lst)                                 ; answers
  (cond ((endp unify-subst-lst)
         (mv suspensions fcd-lst))
        (t
         (mv-let (suspensions1 fcd-lst1)
                 (advance-fc-activation2
                  act0
                  hyps (car unify-subst-lst) (car ttree-lst)
                  fc-round type-alist ens force-flg wrld state oncep-override
                  suspensions
                  fcd-lst)
                 (advance-fc-activation3
                  act0
                  hyps (cdr unify-subst-lst) (cdr ttree-lst)
                  fc-round type-alist ens force-flg wrld state oncep-override
                  suspensions1 fcd-lst1)))))

)

; The wrapper for the forward chaining kernel:  advancing an fc-activation.

(defun advance-fc-activation (act fc-round type-alist ens force-flg wrld state oncep-override
                                  suspensions fcd-lst)
  (with-accumulated-persistence
   (access forward-chaining-rule
           (access fc-activation act :rule)
           :rune)
   (suspensions1 fcd-lst1)
   t ; Wart:  We consider all forward-chaining work to be ``useful''
   (advance-fc-activation1
    act
    (access fc-activation act :inst-hyp)
    (access fc-activation act :hyps)
    (access fc-activation act :unify-subst)
    (access fc-activation act :ttree)
    fc-round type-alist ens force-flg wrld state oncep-override
    suspensions
    fcd-lst)))

; Recall the basic data structure of forward chaining, the fc-pot-lst.
; It is a list of fc-pots, each of which is (term act1 ... actn), with a
; pot for every term in the problem pairing all the fc-activations
; triggered by the corresponding term.  We want to advance all the
; activations in every pot.  We start by advancing all the activations
; listed in a single pot.

(defun advance-fc-activations (lst fc-round type-alist ens force-flg wrld state
                                   oncep-override suspensions fcd-lst)

; Lst is of the form (act1 ... actn), where each acti is an fc activation.
; Fcd-lst is a list of fc-derivations onto which we accumulate any derived
; conclusions (as fc-derivations).  Note that the fcds in this list are not
; necessarily ``approved.''  Their conclusions are known to be non-nil but we
; may not actually add them to the type-alist.  We return two results which we
; build by accumulation onto the last two arguments: a new list of possibly
; advanced suspended activations and the fc-derivations produced by successful
; forward chaining.

  (cond ((null lst)
         (mv suspensions fcd-lst))
        (t (mv-let
            (suspensions1 fcd-lst1)
            (advance-fc-activation (car lst)
                                   fc-round type-alist ens force-flg wrld state
                                   oncep-override suspensions fcd-lst)
            (advance-fc-activations (cdr lst)
                                    fc-round type-alist ens force-flg wrld
                                    state oncep-override suspensions1
                                    fcd-lst1)))))

(defun fc-pair-lst (fcd-lst)

; We convert a list of fc-derivations to a list of pairs of the form
; (concl . ttree), where each ttree is fcd-free.  We call such a pair an
; "fc-pair."  These pairs can be sensibly used outside of the
; forward-chaining module.

; Note: It is important that this function return a list in 1:1 correspondence
; with fcd-lst.  The reason is that after forming this list (in
; forward-chain-top) we map over it with fc-pair-lst-type-alist (immediately
; below) while mapping in parallel over the original fcd-lst, assuming that the
; concl being dealt with from the first came from the corresponding element of
; the second.

  (cond ((null fcd-lst) nil)
        (t (cons (cons (access fc-derivation (car fcd-lst) :concl)
                       (push-lemma
                        (access fc-derivation (car fcd-lst) :rune)
                        (expunge-fc-derivations
                         (access fc-derivation (car fcd-lst) :ttree))))
                 (fc-pair-lst (cdr fcd-lst))))))

(defun fc-pair-lst-type-alist (fc-pair-lst fcd-lst type-alist force-flg ens wrld)

; Fc-pair-lst is a list of pairs of the form (concl . ttree).  Fcd-lst is the
; list from which fc-pair-lst was derived and hence is in 1:1 correspondence
; with it.  That is, the (concl . ttree) entry from the first argument came
; from the fcd in the corresponding position of the second argument.

; We extend type-alist by assuming the truth of every concl, tagging each
; type-alist entry with the corresponding ttree, which we assume is fcd-free.
; Assuming the initial type-alist is fcd-free, the final one is too.  We return
; three results, (mv flg type-alist ttree).  If a contradiction is found, flg
; is t, type-alist is nil, and ttree is the fcd-free ttree explaining it.
; Otherwise, type-alist is the resulting type-alist and ttree is nil.

; At one time we assumed that there was no contradiction, causing a hard error
; if we found one.  However, Jared Davis sent the following script that causes
; that hard error, so we changed this function.  A relevant comment, from
; before that change, is given below.

;  (defstub appealp (* *) => *)
;  (defstub appeal-listp (* *) => *)
;  (defstub appeal-structurep (*) => *)
;  (defstub appeal-structure-listp (*) => *)
;  (defstub get-subgoals (*) => *)
;  (defstub appeal-provisionally-okp (* * *) => *)
;  (defstub proofp (* * *) => *)
;  (defstub proof-listp (* * *) => *)
;
;  (defaxiom appeal-structure-listp-forward-to-appeal-structurep-of-car
;     (implies (appeal-structure-listp x)
;              (equal (appeal-structurep (car x))
;                     (if x t nil)))
;     :rule-classes :forward-chaining)
;
;  (defaxiom appealp-listp-forward-to-appealp-of-car
;     (implies (appeal-listp x arity-table)
;              (equal (appealp (car x) arity-table)
;                     (if x t nil)))
;     :rule-classes :forward-chaining)
;
;  (defaxiom appealp-forward-to-appeal-structurep
;     (implies (appealp x arity-table)
;              (appeal-structurep x))
;     :rule-classes :forward-chaining)
;
;  (defaxiom appeal-structure-listp-forward-to-appeal-structure-listp-of-cdr
;     (implies (appeal-structure-listp x)
;              (appeal-structure-listp (cdr x)))
;     :rule-classes :forward-chaining)
;
;  (defaxiom appeal-listp-forward-to-appeal-listp-of-cdr
;     (implies (appeal-listp x arity-table)
;              (appeal-listp (cdr x) arity-table))
;     :rule-classes :forward-chaining)
;
;  (defaxiom appeal-listp-forward-to-appeal-structure-listp
;     (implies (appeal-listp x arity-table)
;              (appeal-structure-listp x))
;     :rule-classes :forward-chaining)
;
;  (defaxiom appeal-structure-listp-forward-to-true-listp
;     (implies (appeal-structure-listp x)
;              (true-listp x))
;     :rule-classes :forward-chaining)
;
;  (defaxiom appeal-listp-when-proofp
;     (implies (proof-listp x database arity-table)
;              (appeal-listp x arity-table))
;     :rule-classes :forward-chaining)
;
;  (defaxiom appealp-when-proofp
;     (implies (proofp x database arity-table)
;              (appealp x arity-table))
;     :rule-classes :forward-chaining)
;
;  (defthm hard-error-in-fc-pair-lst-type-alist
;     (implies (and (proof-listp xs database arity-table)
;                   (not (consp xs)))
;              (equal (proofp (car xs) database arity-table)
;                     nil)))

; Historical Comment:

; Note on the Hard Error below: How might this error arise?  The intuitive
; argument that it doesn't goes like this: This function is called in
; forward-chain, on something produced by forward-chain1.  But inspection of
; forward-chain1 shows that it uses type-alist-fcd-lst to check that approved
; fc derivations are not contradictory.  What can go wrong?  Well, one thing
; that has gone wrong is that type-alist-fcd-lst looks at the derivations in a
; different order than they are looked at by this function.  Hence, the old
; familiar type-alist-clause bugaboo (order of the literals) comes into play.
; We have seen an example where forward-chain1 checked ((< 0 x) (< x 1)
; (integerp x)) and found no contradiction but then passed the reversed list to
; this function which found the contradiction and caused the hard error for the
; first time ever.  Our response to that was to put a reconsider-type-alist
; into type-alist-fcd-lst.  But our "proof" that this hard error never arises
; is now suspect.

  (cond ((null fc-pair-lst) (mv nil type-alist nil))
        (t (mv-let
            (mbt mbf tta fta ttree)
            (assume-true-false (car (car fc-pair-lst))
                               (cdr (car fc-pair-lst))
                               force-flg nil type-alist ens wrld
                               nil nil :fta)
            (declare (ignore fta))
            (cond (mbf (mv t nil ttree))
                  (mbt (prog2$
                        (filter-redundant-approved-fc-derivation (car fcd-lst))
                        (fc-pair-lst-type-alist (cdr fc-pair-lst)
                                                (cdr fcd-lst)
                                                type-alist
                                                force-flg ens wrld)))
                  (t (fc-pair-lst-type-alist (cdr fc-pair-lst)
                                             (cdr fcd-lst)
                                             tta
                                             force-flg ens wrld)))))))

; Now we work on the heuristic for approving fc derivations.  The
; problem is to avoid infinite forward chaining.  So we define a
; predicate that determines whether we wish to keep a given derivation.

(defmacro fcd-runep (rune ttree)

; Rune is the name of a forward chaining rule.  We want to determine if rune
; has been used in any fc-derivation in ttree.  This macro is analogous to
; tag-tree-occur except that it knows that 'fc-derivation tags contain other
; ttrees and it looks recursively into those ttrees too.  It is a macro so that
; fcd-runep-lst can be singly recursive (which could conceivably help
; performance, but at any rate seems very unlikely to hurt).

  `(fcd-runep-lst ,rune (tagged-objects 'fc-derivation ,ttree)))

(defun fcd-runep-lst (rune lst)
  (cond ((endp lst) nil)
        (t (or (equal rune (access fc-derivation (car lst) :rune))
               (fcd-runep rune (access fc-derivation (car lst) :ttree))
               (fcd-runep-lst rune (cdr lst))))))

(defmacro fcd-worse-than-or-equal (concl fn-cnt p-fn-cnt ttree)

; Concl is a term and fn-cnt is its function symbol count.  If there exists a
; concl' with fn count fn-cnt' in an 'fc-derivation of ttree such that fn-cnt
; >= fn-cnt' and concl is worse-than-or-equal to concl', then we return t.
; Otherwise we return nil.  We define a macro so that
; fcd-worse-than-or-equal-lst can be singly recursive (which could conceivably
; help performance, but at any rate seems very unlikely to hurt).

  `(fcd-worse-than-or-equal-lst
    ,concl ,fn-cnt ,p-fn-cnt (tagged-objects 'fc-derivation ,ttree)))

(defun fcd-worse-than-or-equal-lst (concl fn-cnt p-fn-cnt lst)
  (cond ((endp lst) nil)
        (t (or (and (let ((fc-fn-cnt (access fc-derivation (car lst)
                                             :fn-cnt)))
                      (or (> fn-cnt fc-fn-cnt)
                          (and (eql fn-cnt fc-fn-cnt)
                               (>= p-fn-cnt
                                   (access fc-derivation (car lst)
                                           :p-fn-cnt)))))
                    (worse-than-or-equal concl
                                         (access fc-derivation
                                                 (car lst)
                                                 :concl)))
               (fcd-worse-than-or-equal concl fn-cnt p-fn-cnt
                                        (access fc-derivation
                                                (car lst)
                                                :ttree))
               (fcd-worse-than-or-equal-lst concl fn-cnt p-fn-cnt
                                            (cdr lst))))))

; Once upon a time we had heuristics for keeping concl if there was
; a lit of the current clause that was worse than it or if there was a
; concl already kept that was worse than it.  We have
; removed those heuristics and replaced them by the faster check that the
; triggering term occurs in the clause.  But we'll keep the
; definitions in case we want to reinstate the heuristics.

; (defun exists-lit-worse-than-or-equal (cl concl fn-cnt)
;   (cond
;    ((null cl) nil)
;    (t (or (and (>= (fn-count (car cl)) fn-cnt)
;                (worse-than-or-equal (car cl) concl))
;           (exists-lit-worse-than-or-equal (cdr cl)
;                                           concl
;                                           fn-cnt)))))

(defun exists-fcd-worse-than-or-equal (fcd-lst concl fn-cnt p-fn-cnt)
  (cond
   ((null fcd-lst) nil)
   (t (or (and (let ((fcd-fn-cnt (access fc-derivation (car fcd-lst) :fn-cnt)))
                 (or (> fcd-fn-cnt fn-cnt)
                     (and (eql fcd-fn-cnt fn-cnt)
                          (>= (access fc-derivation (car fcd-lst) :p-fn-cnt)
                              p-fn-cnt))))
               (worse-than-or-equal
                (access fc-derivation (car fcd-lst) :concl)
                concl))
          (exists-fcd-worse-than-or-equal (cdr fcd-lst)
                                          concl
                                          fn-cnt
                                          p-fn-cnt)))))

(defun all-dumb-occur-lst (args cl)
  (cond ((endp args) t)
        (t (and (dumb-occur-lst (car args) cl)
                (all-dumb-occur-lst (cdr args) cl)))))

(defun all-args-occur-after-strip-not (term cl)

; One of our heuristics for approving a derivation is that all of the
; arguments appearing in its conclusion occur in cl.  This function
; checks that when term is the :concl of an fc-derivation.  Roughly
; speaking, we check that every arg of term occurs in cl.  However, we
; first strip off any NOTs that surround term.  Rather arbitrarily, if
; the resulting atom is a variable, we return t, and if it is a constant
; we return nil.

  (cond ((variablep term) t)
        ((fquotep term) nil)
        ((eq (ffn-symb term) 'not)
         (all-args-occur-after-strip-not (fargn term 1) cl))
        (t (all-dumb-occur-lst (fargs term) cl))))

(defun approved-fc-derivationp (fcd cl)

; We return t iff we approve fcd as a new fact we will add to fcd-lst
; while forward chaining from clause cl.

; Once upon a time, our heuristic for approving an fc-derivation is
; that one of the following 4 conditions is satisfied. (a) The
; relevant forward-chaining rune has not been used before in this
; derivation. (b) Concl is not worse-than-or-equal any concl in its
; derivation. (c) The triggering term of this fcd is in the current
; clause. (d) All of the args of concl occur in the clause.  However,
; after an improvement to the forward-chaining code to extract new
; trigger terms from all approved conclusions, we found that condition
; (c) was unnecessary and, in fact, could cause forward-chaining to
; loop indefinitely.  So (c) has been commented out below.

  (let ((ttree (access fc-derivation fcd :ttree)))
    (or (not (fcd-runep (access fc-derivation fcd :rune) ttree)) ; (a)
        (not (fcd-worse-than-or-equal (access fc-derivation fcd :concl) ; (b)
                                      (access fc-derivation fcd :fn-cnt)
                                      (access fc-derivation fcd :p-fn-cnt)
                                      ttree))
;       (dumb-occur-lst (access fc-derivation fcd :inst-trigger) cl) ; (c)

; There is one more condition, (d), below, but first a big comment
; explaining it.  If all of the arguments of the conclusion (ignoring
; any leading NOTs) of the forward-chaining rule appear in the clause,
; we approve the result.  Dave Greve has encountered cases where this
; extra flexibility is important for making type-like forward-chaining
; derivations, as illustrated by the following example.

;   (defstub con (x y) nil)
;   (defstub des (x) nil)
;
;   (defstub typec (x) nil)
;   (defstub typeg (x) nil)
;   (defstub typed (x) nil)
;
;   (defaxiom typed-implies-typeg
;     (implies
;      (typed x)
;      (typeg x))
;     :rule-classes (:rewrite :forward-chaining))
;
;   (defaxiom typeg-des
;     (implies
;      (typec x)
;      (typed (des x)))
;     :rule-classes (:rewrite
;                    (:forward-chaining :trigger-terms ((des x)))))
;
;   (defaxiom typec-con
;     (implies
;      (and
;       (natp n)
;       (typeg x))
;      (typec (con x n)))
;     :rule-classes (:rewrite
;                    (:forward-chaining :trigger-terms ((con x n)))))
;
;   (defun several (g)
;     (let* ((c (con g 1))
;            (g (des c))
;            (c (con g 2))
;            (g (des c))
;            (c (con g 3))
;            (g (des c)))
;       (con g 4)))
;
;   (in-theory (disable
;               (:rewrite typec-con)
;               (:rewrite typeg-des)
;               (:rewrite typed-implies-typeg)
;               ))
;
;   ; The following fails without the call below of
;   ; all-args-occur-after-strip-not below unless we remove the
;   ; in-theory event above.
;   (defthm typec-several
;     (implies
;      (typed g)
;      (typec (several g))))

        (all-args-occur-after-strip-not (access fc-derivation fcd :concl) ; (d)
                                        cl))))

(defun approve-fc-derivations (new-fcd-lst cl approved-this-round all-approved)

; We have just derived the fc-derivations in new-fcd-lst, from the
; negations of the literals in cl.  We filter out those new
; fc-derivations that we do not approve.  We add the approved ones to
; both approved-this-round and all-approved.  The former is initially
; nil within a given round and is thus the approved derivations of that
; round.  The latter is cumulative across all rounds.  We return both.

  (cond ((null new-fcd-lst) (mv approved-this-round all-approved))
        ((approved-fc-derivationp (car new-fcd-lst) cl)
         (approve-fc-derivations (cdr new-fcd-lst)
                                 cl
                                 (cons (car new-fcd-lst) approved-this-round)
                                 (cons (car new-fcd-lst) all-approved)))
        (t (approve-fc-derivations (cdr new-fcd-lst)
                                   cl
                                   approved-this-round
                                   all-approved))))

; Once we have a batch of approved derivations, we sort them so the
; ``simpler'' ones appear first.  We will then assume them in that
; order.  The heuristic is that simpler conclusions might strengthen
; what we learn about subsequent ones, as would happen if we assumed
; (integerp x) before we assumed (integerp (foo x)).

(mutual-recursion

(defun max-level-no (term wrld)

; Each defun'd function, except the ones being defund at the moment,
; has a 'level-no property, which is a non-negative integer.  The ACL2
; primitives have no level-no property, which we treat as though it were
; 0.  This function computes the maximum stored level-no of the functions
; appearing in term.  Any fn appearing without a level-no is treated
; as though it had level 0, i.e., it is ignored.

  (cond ((variablep term) 0)
        ((fquotep term) 0)
        (t (max (get-level-no (ffn-symb term) wrld)
                (max-level-no-lst (fargs term)
                                  wrld)))))

(defun max-level-no-lst (args wrld)
  (cond ((null args) 0)
        (t (max (max-level-no (car args) wrld)
                (max-level-no-lst (cdr args) wrld)))))

(defun get-level-no (fn wrld)

; Fn is either a lambda expression or a function symbol.  We return
; its level number.

  (cond ((flambdap fn) (max-level-no (lambda-body fn) wrld))
        ((getpropc fn 'level-no nil wrld))
        (t 0)))

)

(mutual-recursion

(defun sort-fcds1-rating1 (term wrld fc vc)
  (cond ((variablep term) (mv fc (1+ vc)))
        ((fquotep term) (mv fc vc))
        ((flambda-applicationp term)
         (mv-let (fc vc)
                 (sort-fcds1-rating1 (lambda-body term) wrld fc vc)
                 (sort-fcds1-rating1-lst (fargs term) wrld (1+ fc) vc)))
        ((or (eq (ffn-symb term) 'not)
             (= (getpropc (ffn-symb term) 'absolute-event-number 0 wrld)
                0))
         (sort-fcds1-rating1-lst (fargs term) wrld fc vc))
        (t (sort-fcds1-rating1-lst (fargs term) wrld
                                       (+ 1
                                          (get-level-no (ffn-symb term) wrld)
                                          fc)
                                       vc))))

(defun sort-fcds1-rating1-lst (lst wrld fc vc)
  (cond ((null lst) (mv fc vc))
        (t (mv-let (fc vc)
                   (sort-fcds1-rating1 (car lst) wrld fc vc)
                   (sort-fcds1-rating1-lst (cdr lst) wrld fc vc)))))
)

(defun sort-fcds1-rating (term wrld)

; In forward-chaining we assume all the derived concls.  We sort them by the
; ratings computed here, assuming first those terms with the highest rating.
; Therefore, we wish to give high numbers to very type-like terms such as
; (rationalp x) and (not (< x '0)).  Actually, all our ratings are nonpositive
; integers, with 0 thus the highest.  The terms pictured above have ratings of
; -1 because they contain a single variable and are otherwise completely
; primitive.  If you assume no term contains more than 10 variable occurrences
; then the ordering imposed by these ratings is lexicographic, favoring
; low function count and using variable occurrences to break ties.  No
; real consideration has been given this measure beyond that it puts
; the terms above before others!

  (mv-let (fc vc)
          (sort-fcds1-rating1 term wrld 0 0)
          (- (+ (* 10 fc) vc))))

(defun sort-fcds1 (approved wrld)
  (cond ((null approved) nil)
        (t (cons
            (cons (sort-fcds1-rating
                   (access fc-derivation (car approved) :concl)
                   wrld)
                  (car approved))
            (sort-fcds1 (cdr approved) wrld)))))

(defun sort-fcds (fcd-lst wrld)

; Fcd-lst is a list of fc-derivations (which happen to have been approved, but
; that doesn't matter to the sorting algorithm).  Each has a derived :concl.
; We sort fcd-lst so that those with the higher rated :concls come first.

  (strip-cdrs (merge-sort-car-> (sort-fcds1 fcd-lst wrld))))

(defun strip-fcd-concls (fcd-lst)
  (cond ((null fcd-lst) nil)
        (t (cons (access fc-derivation (car fcd-lst) :concl)
                 (strip-fcd-concls (cdr fcd-lst))))))

; Upon obtaining the approved derived conclusions, we need to extend the
; type-alist with them.

(defun type-alist-fcd-lst (fcd-lst type-alist
                                   do-not-reconsiderp force-flg ens wrld)

; We take a list of fc-derivations and assume the truth of each concl,
; extending type-alist.  We return two results.  The first is t or nil
; indicating whether a contradiction was found.  When a contradiction is
; found, the second result is the ttree of that contradiction.  When a
; contradiction is not found, the second is the final type-alist.  In
; both cases, the second result is not fcd-free.

; Note that when we finish, (endp fcd-lst), we reconsider the type-alist.  This
; is analogous to type-alist-clause-finish.  We have seen an example of forward
; chaining where we derived, in order, (< 0 x), (< x 1), (integerp x), and
; failed to recognize the contradiction, just as type-alist-clause-finish1
; fails to recognize that contradiction.

  (cond
   ((endp fcd-lst)
    (if do-not-reconsiderp
        (mv nil type-alist)
        (mv-let (contradictionp xtype-alist ttree)
                (reconsider-type-alist type-alist type-alist nil ens wrld
                                       nil nil)
                (cond
                 (contradictionp (mv t ttree))
                 (t (mv nil xtype-alist))))))
   (t (mv-let
       (mbt mbf tta fta ttree)
       (assume-true-false
        (access fc-derivation (car fcd-lst) :concl)
        (add-to-tag-tree! 'fc-derivation
                          (car fcd-lst)
                          nil)
        force-flg nil type-alist ens wrld nil nil :fta)
       (declare (ignore fta))
       (cond (mbf (mv t ttree))
             (mbt (type-alist-fcd-lst (cdr fcd-lst)
                                      type-alist
                                      do-not-reconsiderp force-flg
                                      ens wrld))
             (t (type-alist-fcd-lst (cdr fcd-lst)
                                    tta
                                    do-not-reconsiderp force-flg ens
                                    wrld)))))))


; Finally, we have to detect ``stability'' as we repeatedly do rounds of
; forward chaining.  One aspect of stability is that every approved
; conclusion is already in the list of trigger terms in the problem.

(defun every-concl-member-equalp (fcd-lst trigger-terms)

; Fcd-lst is a list of fc-derivations.  We return t if the :concl of
; every element of fcd-lst is a member-equal of trigger-terms.

  (cond ((endp fcd-lst) t)
        ((member-equal (access fc-derivation (car fcd-lst) :concl)
                       trigger-terms)
         (every-concl-member-equalp (cdr fcd-lst) trigger-terms))
        (t nil)))

; We now begin the development of code to process disjunctions produced by
; forward chaining.

; Essay on Disjunctions Produced by Forward Chaining

; Disjunction-triples is maintained as a list of triples, (clause ttree . fcd).
; Whenever forward-chain1 derives a new literal, it produces an fc-derivation,
; fcd, to record that fact.  Should the :concl of that fc-derivation be a
; disjunction, like (OR p q r) then it creates a disjunction-triple, ((p q r)
; ttree . fcd) and adds it to the list of disjunction-triples.  Note that the
; first component of a disjunction-triple is in fact a clause.  After extending
; the type-alist with all the newly derived concls and extending
; disjuction-triples as necessary, we map over disjunction-triples and call
; type-set on each literal of each clause.  We throw away any triple whose
; clause contains a true literal; we delete any false literal, accumulate the
; proof of falsity ttree into the ttree of the triple, and, in the event that
; the deletion produces a unit clause, we delete the triple, and extend the
; type-alist by assuming the remaining single literal true with the ttree (and
; we accumulate a new fc-derivation onto fcd-list).  We iterate as long as
; we've produced new triples or type-alist.  One can think of this process as
; ``unit propagation'' except instead of knocking off literals with unit
; clauses we knock them off with type-set.  The function that does all this is
; called process-disjunction-triples and it returns a contradictionp flag, a
; modified list of disjuction-triples, either the ttree associated with the
; contradiction or a new (not fcd-free) type-alist, and the new
; disjunction-triples.  The modified disjunction-triples and type-alist are
; passed on to the next round of forward chaining.

(defun collect-disjuncts (term top-level)
  (case-match term
    (('IF p p q) (cons p (collect-disjuncts q nil)))
    (('IF p *t* q) (cons p (collect-disjuncts q nil)))
    (('IF p q *t*) (cons (dumb-negate-lit p) (collect-disjuncts q nil)))
    (& (and (not top-level) (list term)))))

(defun collect-disjunction-triples (fcd-lst triples)

; Fcd-lst is a list of fc-derivation records.  Each record has a :concl and a
; :ttree and then other things.  We convert each fcd whose :concl is a
; disjunction into a triple, (clause ttree . fcd) where clause is the
; list of disjuncts, e.g., (p q r) from (OR p (OR q r)), ttree is just the
; :ttree field of the fcd, and the cddr of the triple, fcd, is the original fcd
; itself.

; Foreshadowing: The reason we preserve the original fcd is to use it later to
; return a new fc-derivation.  By making the disjunctive processing ultimately
; traffic in fc-derivations we simplify the rest of the forward chaining
; module.  The ``disjunction triples'' we create here will be exploited (by
; exploit-disjunction-triple) as we learn about the individual disjuncts.
; E.g., if disjunct q becomes nil we'll shrink (p q r) to (p r) and change the
; ttree of the triple appropriately.  Eventually we may shrink the disjuncts
; component of the triple to a singleton, e.g., (p), at which point we'll know
; p is non-nil.  If and when that happens we will create a new fc-derivation
; record, fcd', by taking the original fcd of the triple and setting its :concl
; and :ttree to the corresponding components from the triple.

  (cond
   ((endp fcd-lst) triples)
   (t (let* ((fcd (car fcd-lst))
             (concl (access fc-derivation (car fcd-lst) :concl))
             (disjuncts (collect-disjuncts concl t)))
        (cond
         (disjuncts
          (collect-disjunction-triples
           (cdr fcd-lst)
           (cons (list* disjuncts
                        (access fc-derivation fcd :ttree)
                        fcd)
                 triples)))
         (t (collect-disjunction-triples (cdr fcd-lst) triples)))))))

(defun exploit-disjunction-triple (clause ttree fcd type-alist ens wrld
                                          last-lit-kept kept-cnt lit-deletedp)

; The ``disjunction triple'' we're exploiting is (clause ttree . fcd), but
; we've torn it apart here so we can cdr our way down clause modifying ttree
; and, if we manage to deduce a new literal we'll use fcd to create a new
; fc-derivation.

; We apply type-set to each literal of clause, deleting any now-false lits.  If
; we eliminate all but one of the lits, that lit must be true so we assume it.
; But more typically either nothing changes or else we knock a disjunct off.

; Result:
; (mv signal     ; :CONTRADICTION | :DELETE | :UNCHANGED | :NEW
;     ttree      ; only meaningful for :CONTRADICTION or :NEW, else nil
;     clause     ; only meaningful when :NEW signalled, else nil
;     type-alist ; always an extension (possibly weak) of type-alist
;     fcd        ; nil or fc-derivation; non-nil iff new lit derived
;     )

; We might signal :DELETE for one of two reasons: (i) we learned that one of
; the literals of the clause is true under the type-alist, so the disjunction
; tells us nothing, or (ii) we derived a literal from the disjunction and have
; assumed it true in the returned type-alist.

; Some questions we had to ask...  Can we signal a contradiction and have an
; fcd returned?  Quite possibly, but we're not entirely sure! So we program for
; it.  Imagine that we derive lit (thus producing a new fcd), add lit to the
; type alist and get a contradiction with something else already there.  In
; that case we signal a contradiction and return a new fcd.  But see ``Can this
; happen?'' below!  Next question: Wouldn't we also have a new type-alist?  No,
; never with a contradiction.  If we signal contradiction then either all the
; literals were false under the incoming type-alist or else we derived a new
; literal, assumed it, detected a contradiction (via mbf without a new alist).
; Can we get a new type-alist without an fcd?  No.  The only time we change the
; type-alist is when we derive a new lit and assume it, which only happens at
; the end when we realize only lit survived.  Why do we pass the original fcd
; down?  An fc-derivation contains many fields, e.g., the rune and unify-subst
; giving rise to the disjunction originally produced and we use them in our
; eventual fcd answer.  But an fc-derivation is possibly produced only at the
; bottom of our recursion, so fcd is not modified or accumulated or anything
; ``on the way down.''  The ttree is obviously important when we signal
; :contradiction, but why is the ttree meaningful with signal :NEW?  The
; resulting ttree is the one to be associated with the new disjunction created
; from the new (shrunken) clause.

; Efficiency Note: If we take the view that the only way we can help ourselves
; is by knocking off all but one of the literals, then it suffices to apply
; type-set to just the first two literals of the clause.  If neither is NIL,
; then we're not going to knock off all but one!  However, (a) it seems
; unlikely users will forward chain to long lists of disjuncts -- in fact, 2 is
; the most we've seen, (b) if type-set finds a true literal we can stop
; checking that clause, which is an efficiency win even if we didn't learn
; anything useful, and (c) limiting it to just two literals imposes some
; overhead and coding ugliness.  So, we decided to do it this way and just
; record our thoughts for posterity.

  (cond
   ((endp clause)
    (cond
     ((eql kept-cnt 0)
; All lits were false, so this is a contradiction!  We know the type-alist is
; unchanged but we pass it back out of general principle.
      (mv :CONTRADICTION ttree
          nil        ; irrelevant clause
          type-alist ; unchanged
          nil))      ; irrelevant, no new lit deduced
     ((eql kept-cnt 1)
; Exactly one literal survived in this clause and it is last-lit-kept.
      (mv-let (mbt mbf tta fta ttree1)
        (assume-true-false last-lit-kept ttree
                           nil nil ; force-flg and dwp
                           type-alist ens wrld
                           nil nil ; pot-lst and pt
                           :fta)   ; don't bother with false type-alist
        (declare (ignore fta))
        (cond
         (mbf

; Contradiction, with ttree1 including ttree.  Can this happen?  Actually, we
; don't think it can!  Or, at least, it seems unlikely, which is why we program
; for it.  If we detect a contradiction by assuming a literal true, then one
; might hope that we would have detected it is false when we computed its
; type-set on the way down.  But we found the type-set of this lit to be
; indeterminant.  Had we found it false we would have deleted it and been left
; with no kept lits, getting the :CONTRADICTION above.  But type-set and
; assume-true-false are so complicated that we'd rather not depend on the wish
; that everything known by one is known by the other!  There is one efficiency
; implication of this decision.  Search for ``Efficiency Note'' below.

          (mv :CONTRADICTION ttree1
              nil        ; irrelevant clause
              type-alist ; unchanged type-alist

; The new fcd below is implicitly approved because the parent disjunction
; triple was produced from an approved fcd.  Roughly speaking this means that
; if a disjunction is approved, its disjuncts are approved.

              (change fc-derivation fcd
                      :concl last-lit-kept
                      :ttree ttree))) ;  new fc-derivation!
         (mbt
; This literal is already known to be t.
          (mv :DELETE nil
              nil         ; irrelevant clause
              type-alist  ; unchanged type-alist
              nil)) ; no new deduction!  We already knew this lit was true.
         (t
          (mv :DELETE nil ; delete this disjunction since we're done with it
              nil         ; irrelevant clause
              tta         ; new type-alist with assumed lit and ttree

; The new fcd below is implicitly approved because the parent disjunction
; triple was produced from an approved fcd.  Roughly speaking this means that
; if a disjunction is approved, its disjuncts are approved.

              (change fc-derivation fcd
                      :concl last-lit-kept
                      :ttree ttree) ; new fc-derivation!
              )))))
     (lit-deletedp
; We've reached the end of the clause but deleted something.   So cons up a
; new version on the way out.
      (mv :NEW ttree nil type-alist nil))
     (t
; We've reached the end of the clause and deleted nothing; there's nothing to do.
      (mv :UNCHANGED nil ; ttree is irrelevant because we'll keep the original
          nil type-alist nil))))
   (t (let ((lit (car clause)))
        (mv-let (ts ttree1)
          (type-set lit
                    nil nil ; force-flg and dwp
                    type-alist ens wrld ttree
                    nil nil) ; pot-lst and pt
          (cond
           ((ts= ts *ts-nil*)
; This lit is false, so we drop it (by not consing it on to the answer clause).
            (exploit-disjunction-triple (cdr clause) ttree1 fcd
                                        type-alist ens wrld
                                        last-lit-kept kept-cnt
                                        t ; indicate that a lit will be dropped
                                        ))
           ((ts-disjointp ts *ts-nil*)
; This lit is true, so this clause tells us nothing new and we can delete it
; and quit.
            (mv :DELETE nil
                nil type-alist nil))
           (t

; This lit is indeterminant.  It might be the only surviving member of the
; clause when we're done.  The ttree1 that tells us the type of lit is
; irrelevant since we don't need a justification to leave the literal in place.
; Efficiency Note: we know the type-set of lit here and yet we forget it
; and, if lit turns out to be the only surviving lit, we'll do a lot of that
; type-set work again as we assume it true.  We might be able to same some work
; by passing ts and ttree1 down along with lit!

            (mv-let
              (signal new-ttree new-clause new-type-alist new-fcd)
              (exploit-disjunction-triple (cdr clause) ttree fcd
                                          type-alist ens wrld
                                          lit ; last known survivor
                                          (+ 1 kept-cnt)
                                          lit-deletedp)
              (cond
               ((eq signal :NEW)
                (mv :NEW
                    new-ttree
                    (cons lit new-clause)
                    new-type-alist
                    nil))
               (t ; signal = :CONTRADICTION, :DELETE, or :UNCHANGED
                (mv signal new-ttree new-clause new-type-alist new-fcd)))))))))))

; Unit Tests
; (assign fcd0
;         (make fc-derivation
;               :concl '(silly-concl) ; should be irrelevant
;               :ttree 'silly-ttree ; should be irrelevant
;               :fn-cnt 'fn-cnt
;               :p-fn-cnt 'p-fn-cnt
;               :inst-trigger 'trigger
;               :rune 'rune
;               :fc-round 'fc-round
;               :unify-subst 'unify-subst))

; :delete
; (exploit-disjunction-triple '((NOT A) (NOT B) C (NOT D))
;                        (push-lemma '(:FORWARD-CHAINING FC-OR) nil)
;                        (@ fcd0)
;                        `((A ,*ts-t* . ((LEMMA (:FORWARD-CHAINING A))))
;                          (B ,*ts-t* . ((LEMMA (:FORWARD-CHAINING B))))
;                          (D ,*ts-non-nil* . ((LEMMA (:FORWARD-CHAINING D)))))
;                        (ens state) (w state)
;                        nil 0 nil)

; :Contradiction
; (exploit-disjunction-triple '((NOT A) (NOT B) C (NOT D))
;                        (push-lemma '(:FORWARD-CHAINING FC-OR) nil)
;                        (@ fcd0)
;                        `((A ,*ts-t* . ((LEMMA (:FORWARD-CHAINING A))))
;                          (B ,*ts-t* . ((LEMMA (:FORWARD-CHAINING B))))
;                          (C ,*ts-nil* . ((LEMMA (:FORWARD-CHAINING NOT-C))))
;                          (D ,*ts-non-nil* . ((LEMMA (:FORWARD-CHAINING D)))))
;                        (ens state) (w state)
;                        nil 0 nil)

; :unchanged
; (exploit-disjunction-triple '((NOT A1) (NOT B1) C1 (NOT D1))
;                        (push-lemma '(:FORWARD-CHAINING FC-OR) nil)
;                        (@ fcd0)
;                        `((A ,*ts-t* . ((LEMMA (:FORWARD-CHAINING A))))
;                          (B ,*ts-t* . ((LEMMA (:FORWARD-CHAINING B))))
;                          (D ,*ts-non-nil* . ((LEMMA (:FORWARD-CHAINING D)))))
;                        (ens state) (w state)
;                        nil 0 nil)

; new
; (exploit-disjunction-triple '((NOT A1) (NOT B) C (NOT D1))
;                        (push-lemma '(:FORWARD-CHAINING FC-OR) nil)
;                        (@ fcd0)
;                        `((A ,*ts-t* . ((LEMMA (:FORWARD-CHAINING A))))
;                          (B ,*ts-t* . ((LEMMA (:FORWARD-CHAINING B))))
;                          (D ,*ts-non-nil* . ((LEMMA (:FORWARD-CHAINING D)))))
;                        (ens state) (w state)
;                        nil 0 nil)

(defun exploit-disjunction-triples1 (disjunction-triples
                                     type-alist ens wrld
                                     new-approved-fcds all-approved-fcds)

; Map over disjunction-triples and exploit each one, accumulating any new
; fc-derivations onto all-approved-fcds.  Since disjunction triples are produced
; only from approved fcds, the fcds produced from disjunction triples are
; themselves treated as approved.

; Result:
; (mv contradictionp ttree ; or
;      new-disjunction-triples new-type-alist
;      new-new-approved-fcds new-all-approved-fcds)

  (cond
   ((endp disjunction-triples)
    (mv nil nil
        nil type-alist
        new-approved-fcds all-approved-fcds))
   (t (let ((clause (caar disjunction-triples))
            (ttree (cadar disjunction-triples))
            (fcd (cddar disjunction-triples)))
        (mv-let (signal new-ttree new-clause new-type-alist new-fcd)
          (exploit-disjunction-triple clause ttree fcd
                                      type-alist ens wrld
                                      nil 0 nil)

; Signal is one of :CONTRADICTION | :DELETE | :UNCHANGED | :NEW

          (let ((new-approved-fcds
                 (if new-fcd
                     (cons new-fcd new-approved-fcds)
                     new-approved-fcds))
                (all-approved-fcds
                 (if new-fcd
                     (cons new-fcd all-approved-fcds)
                     all-approved-fcds)))
            (case signal
              (:CONTRADICTION
               (mv t new-ttree nil nil
                   new-approved-fcds
                   all-approved-fcds))
              (:DELETE
               (exploit-disjunction-triples1
                (cdr disjunction-triples)
                new-type-alist ens wrld
                new-approved-fcds
                all-approved-fcds))
              (otherwise

; Signal is :UNCHANGED or :NEW.  At first sight one might think that :NEW just
; costs two more conses than :UNCHANGED and so it is probably not worth
; maintaining both signals.  But the truth is that :NEW was implemented so the
; workhorse, exploit-disjunction-triple, did not cons up unchanged clauses.
; Rather than discard it at the interface between that function and this, we
; exploit it to save a couple more.  Note also that new-fcd is guaranteed to be
; nil here: no new fcd was produced when these signals are raised.

               (mv-let
                 (contradictionp ttree
                                 new-disjunction-triples
                                 new-type-alist
                                 new-approved-fcds
                                 all-approved-fcds)
                 (exploit-disjunction-triples1
                  (cdr disjunction-triples)
                  new-type-alist ens wrld new-approved-fcds all-approved-fcds)
                 (cond
                  (contradictionp
                   (mv contradictionp ttree
                       new-disjunction-triples new-type-alist
                       new-approved-fcds all-approved-fcds))
                  (t (mv nil nil
                         (cons (if (eq signal :UNCHANGED)
                                   (car disjunction-triples)
                                   (list* new-clause
                                          new-ttree
                                          fcd))
                               new-disjunction-triples)
                         new-type-alist
                         new-approved-fcds
                         all-approved-fcds))))))))))))

; Unit Tests
; Pump out a Q and delete first disjunction
; (exploit-disjunction-triples1
;  `(((P Q) ((LEMMA (:FORWARD-CHAINING P-OR-Q))) . ,(@ fcd0))
;    ((R S) ((LEMMA (:FORWARD-CHAINING R-OR-S))) . ,(@ fcd0)))
;  `((P ,*ts-nil* . ((LEMMA (:FORWARD-CHAINING NOT-P)))))
;  (ens state) (w state)
;  nil
;  '(fcd1 fcd2 fcd3))

; Pump out a Q and delete second disjunction
; (exploit-disjunction-triples1
;  `(((R S) ((LEMMA (:FORWARD-CHAINING R-OR-S))) . ,(@ fcd0))
;    ((P Q) ((LEMMA (:FORWARD-CHAINING P-OR-Q))) . ,(@ fcd0)))
;  `((P ,*ts-nil* . ((LEMMA (:FORWARD-CHAINING NOT-P)))))
;  (ens state) (w state)
;  nil
;  '(fcd1 fcd2 fcd3))

; Pump out a Q delete first disjunction and shrink second
; (exploit-disjunction-triples1
;  `(((P Q) ((LEMMA (:FORWARD-CHAINING P-OR-Q))) . ,(@ fcd0))
;    ((R P S) ((LEMMA (:FORWARD-CHAINING R-OR-S))) . ,(@ fcd0)))
;  `((P ,*ts-nil* . ((LEMMA (:FORWARD-CHAINING NOT-P)))))
;  (ens state) (w state)
;  nil
;  '(fcd1 fcd2 fcd3))

; contradiction
; (exploit-disjunction-triples1
;  `(((P Q1) ((LEMMA (:FORWARD-CHAINING P-OR-Q1))) . ,(@ fcd0))
;    ((R P S) ((LEMMA (:FORWARD-CHAINING R-OR-S))) . ,(@ fcd0))
;    ((U V W) ((LEMMA (:FORWARD-CHAINING UVW))) . ,(@ fcd0))
;    ((P Q2) ((LEMMA (:FORWARD-CHAINING P-OR-Q2))) . ,(@ fcd0)))
;  `((P ,*ts-nil* . ((LEMMA (:FORWARD-CHAINING NOT-P))))
;    (U ,*ts-nil* . ((LEMMA (:FORWARD-CHAINING NOT-U))))
;    (V ,*ts-nil* . ((LEMMA (:FORWARD-CHAINING NOT-V))))
;    (W ,*ts-nil* . ((LEMMA (:FORWARD-CHAINING NOT-W)))))
;  (ens state) (w state)
;  nil
;  '(fcd1 fcd2 fcd3))

(defun exploit-disjunction-triples (disjunction-triples
                                    type-alist ens wrld
                                    new-approved-fcds all-approved-fcds)

; Repeatedly exploit all the disjunction-triples until nothing changes.  Result:
; (mv contradictionp ttree ; or
;     new-disjunction-triples new-type-alist new-all-approved-fcds)
; Since disjunction triples are produced only from approved fcds, the fcds
; produced from disjunction triples are themselves treated as approved.

  (mv-let
    (contradictionp ttree new-disjunction-triples new-type-alist
                    new-approved-fcds
                    all-approved-fcds)
    (exploit-disjunction-triples1 disjunction-triples
                                  type-alist ens wrld
                                  new-approved-fcds
                                  all-approved-fcds)
    (cond
     (contradictionp
      (mv contradictionp ttree
          new-disjunction-triples new-type-alist
          new-approved-fcds all-approved-fcds))
     ((and (equal new-disjunction-triples disjunction-triples)
           (equal new-type-alist type-alist))
      (mv nil nil new-disjunction-triples new-type-alist
          new-approved-fcds
          all-approved-fcds))
     (t (exploit-disjunction-triples new-disjunction-triples
                                     new-type-alist ens wrld
                                     new-approved-fcds
                                     all-approved-fcds)))))

; Unit Test

; This takes two rounds to derive Q1 and Q2 (round 1) and then to discard (U Q2
; V W) (round 2).  If you replace exploit-disjunction-triples by
; exploit-disjunction-triples1 you'll see no contradiction signalled and (U Q2
; V W) surviving as a disjunction.

; (exploit-disjunction-triples
;  `(((P Q1) ((LEMMA (:FORWARD-CHAINING P-OR-Q1))) . ,(@ fcd0))
;    ((R P S) ((LEMMA (:FORWARD-CHAINING R-OR-S))) . ,(@ fcd0))
;    ((U Q2 V W) ((LEMMA (:FORWARD-CHAINING UVW))) . ,(@ fcd0))
;    ((P Q2) ((LEMMA (:FORWARD-CHAINING P-OR-Q2))) . ,(@ fcd0)))
;  `((P ,*ts-nil* . ((LEMMA (:FORWARD-CHAINING NOT-P)))))
;  (ens state) (w state)
;  nil
;  '(fcd1 fcd2 fcd3))

(defun process-disjunction-triples (approved-this-round disjunction-triples
                                                        type-alist ens wrld
                                                        new-approved-fcds
                                                        all-approved-fcds)

; We collect disjunction-triples among the just-approved concls, add them to
; the existing disjunction-triples, and then exploit all known
; disjunction-triples via type-set, iterating until no new disjunction-triples
; or type-alist is produced.  We return

; (mv contradictionp ttree ; or
;     new-disjunction-triples new-type-alist
;     new-approved-fcds' all-approved-fcds')

; where new-approved-fcds' and all-approved-fcds' extend the corresponding
; incoming one with all the fc-derivations produced by exploiting disjunctions.
; Note that we assume that any disjunct derived from an approved fcd is itself
; approved.

  (exploit-disjunction-triples
   (collect-disjunction-triples approved-this-round disjunction-triples)
   type-alist ens wrld new-approved-fcds all-approved-fcds))

; The following code is used in a hack that prints round-by-round progress
; through forward-chain1.  You have to redefine a system function to get such
; reports.  See the essay in forward-chain1 below.

; Strip-ttrees-from-type-alist strips out the ttrees from a type-alist.  We
; found this important because ttrees containing 'fc-derivation tags are so
; large they impede comprehension.  But for human readability it is convenient
; to see the symbolic counterparts of the numeric type-sets, as produced by
; decode-type-set.  So we introduce a macro that converts the symbolic
; type-sets to numeric ones and then we print type-alists in terms of this
; macro.  Thus, evaluating what we print produces a usable type-alist.

(defun concls-from-fcds (fcd-lst)
  (cond
   ((endp fcd-lst) nil)
   (t (cons (access fc-derivation (car fcd-lst) :concl)
            (concls-from-fcds (cdr fcd-lst))))))

(defmacro make-type-alist (&rest args)
  (cond ((endp args) nil)
        (t `(cons (cons ',(car (car args))
                        ,(cadr (car args)))
                  (make-type-alist ,@(cdr args))))))

(defun strip-ttrees-from-type-alist (ta)
  (cond ((endp ta) nil)
        (t (cons (list (caar ta) (decode-type-set (cadar ta)))
                 (strip-ttrees-from-type-alist (cdr ta))))))

(defun cw-round-by-round-fn (fc-round fcds1 type-alist1 contrap1
                                      fcds2 type-alist2 contrap2)

; This function prints the ``round-by-round'' progress report on forward
; chaining, except it only uses cw printing, is not part of the
; user-controllable fc-report mechanism, and thus is generally irrelevant and
; commented-out of the sources!

; fc-round is the round number in question.  The arguments subscripted with 1
; are the results of advancing all the activations in this round.  Thos
; subscripted with 2 are the results of processing disjunctions in this round.

; Note: Running the fill-format-string Emacs macro from emacs-acl2.el messes up
; this fmt string.  Don't change it!

  (cw "(Round ~x0:~%~
       ~ (new conclusions:~%  ~Y12)~%~
       ~ (new type-alist:~%  ~Y32)~%~
       ~ (disjuncts dislodged:~%  ~Y42)~%~
       ~ (final type-alist:~%  ~Y52)~%~
       ~ )~%"
      fc-round
      (concls-from-fcds fcds1)
      nil
      (if contrap1
          'CONTRADICTION!
; To see the full alist instead of an abbreviated, symbolic version,
; replace this cons expression by type-alist1.
          (cons 'make-type-alist
                (strip-ttrees-from-type-alist type-alist1)))
      (concls-from-fcds fcds2)
      (if contrap2
          'CONTRADICTION!
; To see the full alist instead of an abbreviated, symbolic version,
; replace this cons expression by type-alist2.
          (cons 'make-type-alist
                (strip-ttrees-from-type-alist type-alist2)))))

(defmacro cw-round-by-round (round-by-roundp fc-round
                                             fcds1 type-alist1 contrap1
                                             fcds2 type-alist2 contrap2
                                             form)

; This macro expands to form, ignoring everything else, if round-by-roundp is
; nil.  In any case, it is logically equivalent to form.

  (cond (round-by-roundp
         `(prog2$
           (cw-round-by-round-fn ,fc-round
                                 ,fcds1 ,type-alist1 ,contrap1
                                 ,fcds2 ,type-alist2 ,contrap2)
           ,form))
        (t form)))

(defun forward-chain1 (cl fc-round trigger-terms activations
                          disjunction-triples type-alist force-flg wrld
                          do-not-reconsiderp ens oncep-override state
                          all-approved-fcds)

; Essay on How to Get Round-by-Round Forward Chaining Reports:

; This definition supports round-by-round printing, but only for people willing
; to redefine a system function!  Furthermore, round-by-round printing makes
; the most sense if you also enable full on-the-fly fc-reports.  If you want
; round-by-round do this:

; (set-fc-criteria t)
; (set-fc-report-on-the-fly t)
; (trace$ (forward-chain-top
;          :entry `(forward-chain-top ,caller ,cl ,pts ,force-flg
;                                     ,do-not-reconsiderp
;                                     (w state) (ens state)
;                                     ,oncep-override
;                                     state)
;          :exit `(forward-chain-top ,@values)))
; (redef+)

; and then grab this definition of forward-chain1, change both calls of
; cw-round-by-round below so that the first argument is t instead of nil, and
; redefine forward-chain1.

; The advantage to this full setup is that you'll see the caller (e.g.,
; preprocess-clause, simplify-clause, etc) of forward-chain-top and the
; original clause.  Then you'll see round-by-round reporting for that call,
; then you'll see the summary fc-report for that call, and finally you'll see
; the three results delivered to the caller by forward-chain-top: (mv
; contradictionp type-alist ttree-or-fc-pairs).

; Note that the round-by-round reports abbreviate the type-alists shown,
; dropping the ttrees and printing symbolic type-sets instead of numeric ones.
; Comments in cw-round-by-round-fn above explain how to redefine that function
; to see the actual alists.

; End of essay

; Cl is a clause and fc-round is the current forward chaining round number.
; Trigger-terms is the list of every subterm in the problem whose top function
; symbol has forward chaining rules.  Activations is the list of all
; (suspended) activations.  We first advance every activation, obtaining a new
; list of activations and some derived conclusions represented as fcds.  We
; filter the derived conclusions, throwing out any that, on heuristic grounds,
; we don't like.  The ones we like are said to be ``approved'' and in the
; process of checking their approval we also accumulate the approved ones onto
; all-approved-fcds.  We then assume the newly approved fcds into the
; type-alist.  Some approved conclusions may not give us any new type
; information, e.g., they are already encoded in the type-alist, but we keep
; track of those conclusions anyway because they might give us new trigger
; terms.  We then add activations for all the new trigger terms and
; appropriately extend trigger-terms.  Then we repeat this process until either
; we get a contradiction or we stabilize.

; We return (mv flg x all-approved-fcds fc-round activations).  If flg is t,
; then we found a contradiction and x is a (not fcd-free) ttree.  Otherwise, x
; is the final, extended (not fcd-free) type-alist.  In both cases,
; all-approved-fcds is the accumulated list of all approved fc-derivations
; produced during forward-chaining, fc-round is the final fc-round number, and
; activations is the list of still-suspended activations at the end of the
; process.  These last two are only used in the trace facility for
; forward-chaining.

; Note: The extended type-alist we build here is of no use outside
; forward chaining because it is full of fc-derivations.

  (mv-let (activations1 fcd-lst1)
    (advance-fc-activations
     activations fc-round type-alist ens force-flg
     wrld state oncep-override
     nil ; initial new activations
     nil ; initial new derived concls
     )
    (prog2$
     (filter-all-satisfying-fc-derivations fcd-lst1) ; (FC Reporting)
     (mv-let (new-approved-fcds all-approved-fcds)
       (approve-fc-derivations fcd-lst1
                               cl
                               nil ; initial new approved fcds
                               all-approved-fcds)
       (let ((sorted-fcds
              (sort-fcds new-approved-fcds wrld)))
         (mv-let (contradictionp x)
           (type-alist-fcd-lst
            sorted-fcds
            type-alist do-not-reconsiderp force-flg ens wrld)

; If contradictionp is t, x is a ttree; otherwise, x is a type-alist.
; In any case, x is not fcd-free.

           (cond
            (contradictionp
             (cw-round-by-round
              nil ; change to t to get printing -- and do it below too!
              fc-round
              sorted-fcds nil t
              nil nil nil

; Note:  x, below, is a ttree and is not fcd-free.

              (mv t x all-approved-fcds fc-round activations1)))
            (t

; We now know x is a type-alist produced by assuming the truth of the :concls
; of all the new approved fcds produced by advancing-fc-activations.
; Next we process disjunctions in light of the resulting type-alist.

             (mv-let
               (contradictionp ttree
                               new-disjunction-triples new-type-alist
                               new-approved-fcds1 all-approved-fcds)
               (process-disjunction-triples new-approved-fcds
                                            disjunction-triples
                                            x ; type-alist
                                            ens wrld
                                            new-approved-fcds
                                            all-approved-fcds)
               (cw-round-by-round
                nil ; change to t to get printing
                fc-round
                sorted-fcds x nil
; New-approved-fcds1 is an extension of new-approved-fcds and the difference
; is the set of newly dislodged disjuncts.
                (set-difference-equal new-approved-fcds1
                                      new-approved-fcds)
                new-type-alist contradictionp
                (cond
                 (contradictionp

;;;  Fc-round and activations1 are only used in fc reporting.  But it would be
;;;  good to report the hanging disjunction-triples too!  And it would be a
;;;  good idea to pass up the final type-alist!  But I'm going to leave these
;;;  out for now.

                  (mv t ttree
                      all-approved-fcds fc-round activations1))
                 ((and (equal new-type-alist type-alist)
                       (every-concl-member-equalp new-approved-fcds1
                                                  trigger-terms))
                  (mv nil nil all-approved-fcds fc-round activations1))
                 (t
                  (mv-let (trigger-terms1 activations1)
                    (collect-terms-and-activations-from-fcd-lst
                     new-approved-fcds1 wrld ens
                     trigger-terms activations1)
                    (forward-chain1
                     cl
                     (+ 1 fc-round)
                     trigger-terms1 activations1 new-disjunction-triples
                     new-type-alist
                     force-flg wrld do-not-reconsiderp ens
                     oncep-override state
                     all-approved-fcds))))))))))))))

(defun forward-chain-top (caller cl pts force-flg do-not-reconsiderp wrld ens
                                 oncep-override state)

; The only difference between forward-chain-top and forward-chain is that this
; function allows the caller to identify itself; forward-chain just uses the
; 'miscellaneous caller so that tool books that use forward chaining don't have
; to be changed.

; We forward chain in all possible ways from clause cl.  We return three
; results, (mv flg type-alist ttree-or-fc-pairs), where type-alist is nil if
; flg is t and the last result is either a ttree (flg=t) or fc-pairs (flg=nil)
; as described below.  Thus, the answer is of one of the forms:
; (mv t nil ttree) or (mv nil type-alist fc-pairs).

; Flg is either t or nil indicating whether a contradiction was found.  If so,
; the second result is nil and the third is an fcd-free ttree that encodes the
; 'lemmas and literals used (via 'pt tags).  If no contradiction is found, the
; second result is an fcd-free type-alist obtained by assuming false all of the
; literals of cl (this type-alist is fully tagged with 'pt tags) plus all of
; the conclusions derived from forward chaining; the third is a list of
; fc-pairs, each of the form (concl . ttree), where concl is a truth derived
; from some subset of the negations of literals of cl and ttree is fcd-free and
; tags the :FORWARD-CHAINING 'lemmas used and all parents (via 'pt tags).

; Note: The type-alist returned assumes the falsity of every literal in
; the clause and thus is not suitable for use by rewrite.  We return it
; strictly for the use of setup-simplify-clause-pot-lst and bdd-clause.

; In reading the code below, read (fc-exit a b c ...) as though it
; were (mv a b c).  The stuff in ... is just used in the reporting.

  (prog2$
   (new-fc-call caller cl pts force-flg do-not-reconsiderp wrld ens
                oncep-override)
   (mv-let
    (contradictionp type-alist ttree1)
    (type-alist-clause cl (pts-to-ttree-lst pts) nil nil ens wrld
                       nil nil)

; If a contradiction was found, type-alist is nil and ttree1 is an fcd-free
; tree explaining the contradiction.  Otherwise, type-alist is the type-alist
; produced by assuming all the literals false and ttree1 is nil.

    (cond
     (contradictionp (mv t nil ttree1))
     (t (mv-let
         (trigger-terms activations)
         (collect-terms-and-activations-lst cl nil wrld ens nil nil)

; Trigger-terms is the list of all subterms of cl whose top function
; symbols have fc rules and activations is the list of all (suspended)
; activations triggered by those subterms.

         (mv-let
          (contradictionp ttree2 all-approved-fcds rounds activations1)
          (pstk
           (forward-chain1 cl 1
                           trigger-terms activations nil
                           type-alist force-flg wrld
                           do-not-reconsiderp ens oncep-override
                           state nil))
          (cond (contradictionp

; If a contradiction was found by forward chaining, ttree2 is the ttree that
; derives it.  But it is not fcd-free and we need to make it fcd-free
; before letting it out of the forward-chaining module.

                 (fc-exit t nil (expunge-fc-derivations ttree2)
; We return the three things above but use the following in the report:
                          caller rounds all-approved-fcds activations1))
                (t

; If no contradiction was found, ttree2 is nil.  We need to convert
; all-approved-fcds to a list of pairs of the form (concl . ttree), where each
; ttree is fcd-free.  We have questioned why we create a new data structure
; (``fc-pairs'') instead of just expunging the fc-derivations from the ttrees
; in all-approved-fcds and putting them back into the fcds.  There really isn't
; a good reason.  But the fact is that all we need going forward are the
; conclusions and their corresponding (fcd-free) ttrees.  This list of pairs is
; used in various places, including setting up the linear pot.  While we could
; change the code there to deal with fcds and just access the :concl and :ttree
; fields, it is confusing to (a) pass all the additional information in fcds
; out to the rest of the prover, and (b) to have a set of fcds that are tainted
; with fc-derivations (and thus, hidden assumptions) and other fcds whose
; ttrees are known to be fcd-free.

                 (let ((fc-pair-lst (fc-pair-lst all-approved-fcds)))
                   (mv-let
                    (contradictionp type-alist3 ttree3)
                    (fc-pair-lst-type-alist
                     fc-pair-lst all-approved-fcds type-alist force-flg ens wrld)
                    (cond
                     (contradictionp
                      (fc-exit t nil ttree3
;                         (mv t nil ttree3)
; ... and the stuff we need to do reporting ...
                               caller rounds all-approved-fcds activations1))
                     (t
                      (mv-let
                       (contradictionp type-alist4 ttree4)
                       (type-alist-equality-loop
                        type-alist3 ens wrld
                        *type-alist-equality-loop-max-depth*)
                       (cond
                        (contradictionp
                         (fc-exit t nil ttree4
;                            (mv t nil ttree4)
; ... and the stuff we need to do reporting ...
                                  caller rounds all-approved-fcds activations1))
                        (t
                         (fc-exit nil type-alist4 fc-pair-lst
;                            (mv nil type-alist4 fc-pair-lst)
; ... and the stuff we need to do reporting ...
                                  caller rounds all-approved-fcds activations1)))))))))))))))))

(defun forward-chain (cl pts force-flg do-not-reconsiderp wrld ens
                         oncep-override state)

; This is a version of forward-chain that is backwards compatible with the
; Version_4.1 signature, which did not allow the caller to identify itself.  It
; is defined so it can be used in books like the expander.

  (forward-chain-top 'miscellaneous
                     cl pts force-flg do-not-reconsiderp wrld ens
                     oncep-override state))

; When forward-chain has done its job and produced an fc-pair list,
; we will pass that list to rewrite-clause.  Rewrite-clause rewrites
; each literal in turn, under a type-alist constructed from the remaining
; literals (some of which will have been rewritten since forward-chain
; constructed the type-alist returned above) and from the fc-pair list.
; Here is how we construct the type-alist:

(defun select-forward-chained-concls-and-ttrees (fc-pair-lst pt lits ttree-lst)

; Fc-pair-lst is a list of pairs of the form (concl . ttree).  Each ttree
; contains 'pt tags indicating the parents of concl.  Pt is a parent tree.
; Consider those elements of fc-pair-lst, say fc-pair-lst', whose parents are
; disjoint from pt.  While working on the literals in pt we are permitted to
; assume the truth of every concl in fc-pair-lst'.  This function computes
; fc-pair-lst' and destructures it into two lists which we return in the form
; of (mv lits ttree-lst).  Lits and ttree-lst are in 1:1 correspondence.  Each
; lit is the negation of a concl in fc-pair-lst' and the corresponding ttree is
; the ttree for concl in fc-pair-lst'.  Thus, lits can be thought of as a
; clause segment that can be appended to the other literals we get to assume
; false while working on pt.  The ttrees in ttree-lst may have 'assumption tags
; because forwarding chaining may FORCE or CASE-SPLIT.

  (cond ((null fc-pair-lst) (mv lits ttree-lst))
        ((to-be-ignoredp (cdr (car fc-pair-lst)) pt)
         (select-forward-chained-concls-and-ttrees (cdr fc-pair-lst)
                                                   pt lits ttree-lst))
        (t (select-forward-chained-concls-and-ttrees
            (cdr fc-pair-lst)
            pt
            (cons (dumb-negate-lit (car (car fc-pair-lst)))
                  lits)
            (cons (cdr (car fc-pair-lst))
                  ttree-lst)))))

; Essay on the Construction of the Type-alist to Rewrite the Current Literal

; Simplification sweeps across the literals of a clause, rewriting each in turn
; while assuming the others false.  After rewriting a literal, we clausify the
; result into n clause segments [extending other already-rewritten segments]
; and rewrite the next literal under (the falsity of each literal in) each of
; those segments together with the remaining literals and any available
; conclusions produced by forward chaining.  Thus, to get the type-alist to be
; used while rewriting ``the current literal'' we assume the falsity of three
; lists of literals: new-clause [the clause segment obtained from one path
; through the previously rewritten literals], (cdr tail) [the rest of the
; unrewritten literals], and lits [the literals derived by forward chaining].
; We use the ordinary type-alist-clause to create the new type-alist.  The
; question is: in which order shall we combine these three lists to give to
; type-alist-clause?

; Warning: Note that rearranging the order in which we make these assumptions
; reorders the type-alist!  But this can be a Very Big Deal.  Different rules
; might fire because one type-alist is actually stronger than another,
; different free variable choices may be available because we run into
; different hypotheses (in different orders) suggesting bindings, and the order
; of literals in forced subgoals may be different because we reconstruct forced
; subgoals from converting the governing type-alist into a conjunction of
; terms.  Experimenting with reordering is a costly experiment.

; We have tried three approaches: (append lits new-clause (cdr tail)), (append
; new-clause (cdr tail) lits), and a ``smart'' approach in which we sort the
; literals to put the smaller ones first, thereby allowing their type-sets to
; improve, perhaps, the type-sets computed for larger literals (like disjunctive
; ones (IF a a b)) involving the some of the smaller ones.  The code deleted
; below was part of this ``smart'' approach.  All of these reordering
; strategies must maintain the correspondence between the forward-chained
; literals and the ttrees that produced them and some of the code below deals
; with how to permute two lists so as to order one by size and keep the result
; in 1:1 correspondence with the permuted other.

; Start Experimental Code

;  (mutual-recursion
;   (defun term-size (term)
;
;  ; This computes the number of conses in a term, down to (but not including) the
;  ; quoted constants.  This is just an ``arbitrary'' measure with the following
;  ; two properties: (a) it is fast to compute, though one might someday try to
;  ; speed it up via memoization, and (b) it has the property that if a and b are
;  ; two non-constant terms and term a occurs inside of term b, then the size of a
;  ; is less than the size of b.  This is exploited to reorder a clause so that
;  ; the smaller literals come first during the process of sequentially assuming
;  ; their falsity to construct a type-alist to use in the rewriting of some other
;  ; literal.  See rewrite-clause-type-alist.
;
;     (cond ((variablep term) 1)
;           ((fquotep term) 1)
;           (t (+ 1 (term-size-lst (fargs term))))))
;   (defun term-size-lst (term-lst)
;     (cond ((endp term-lst) 0)
;           (t (+ (term-size (car term-lst))
;                 (term-size-lst (cdr term-lst)))))))
;
;  ; Suppose x is some clause and y is some list of ttrees in 1:1 correspondence
;  ; with x.  We wish to reorder the literals of x according to term-size and to
;  ; apply the same permutation to y, so that the correspondence of literals to
;  ; ttrees is preserved.  We do this by constructing a list of elements (size xi
;  ; . yi), where xi and yi are corresponding elements of x and y, sorting that
;  ; list by its cars, and then stripping out the xi to get the new x' and the yi
;  ; to get the new yi.
;
;  (defun pairlis-with-rankings (x y ans)
;  ; See comment above.  If y is too short, we extend it with nils to match x.
;    (cond ((endp x) ans)
;          (t (pairlis-with-rankings
;              (cdr x) (cdr y)
;              (cons (cons (term-size (car x)) (cons (car x) (car y)))
;                    ans)))))
;
;  (defun reorder-lits-and-ttrees-for-type-alist-clause
;    (lits1 ttree-lst1 lits2 ttree-lst2 lits3 ttree-lst3)
;    (let ((triples
;           (merge-sort-car-<
;            (pairlis-with-rankings
;             lits1 ttree-lst1
;             (pairlis-with-rankings
;              lits2 ttree-lst2
;              (pairlis-with-rankings lits3 ttree-lst3 nil))))))
;      (mv (strip-cadrs triples)
;          (strip-cddrs triples))))

; End Experimental Code

; We started (back in 1989) with the Nqthm idea of just concatenating
; new-clause and (cdr tail); at that time, forward chaining lits didn't exist.
; When forward-chaining was introduced, we experimented and ultimately decided
; to try the order (append lits new-clause (cdr tail)).  We did not use (or
; even have) the function reorder-lits-and-ttrees-for-type-alist-clause and
; simply appended the ttree lists in the same order.  The following comment is
; preserved from versions dating back to the mid-1990s through Version_6.1:

; Historical Comment:

; Observe below that we put the forward-chained concls first.  The problem that
; led us to do this was the toy example shown below (extracted from a harder
; failed proof attempt).  The thm below fails if you process the literals in
; the order (append new-clause (cdr tail) lits).

;  (defstub p (x) t)
;  (defstub r (x) t)
;  (defaxiom p->r
;   (implies (p x)
;            (r x))
;   :rule-classes :forward-chaining)
;  (defstub my-assoc (name l) t)
;  (defaxiom blob
;   (implies (r l)
;            (or (consp (my-assoc name l))
;                (equal (my-assoc name l) nil)))
;   :rule-classes :type-prescription)
;  (thm
;   (implies (p l)
;            (or (consp (my-assoc name l))
;                (equal (my-assoc name l) nil))))

; As a clause the theorem is
; (implies (and (p l)
;               (not (consp (my-assoc name l))))
;          (equal (my-assoc name l) nil)).

; Consider what happens when we rewrite the conclusion assuming the hyps.  We
; have (p l) and (not (consp (my-assoc name l))).  We do indeed forward chain
; and get (r l) also.  But the (not (consp (my-assoc name l))) puts the
; following pair on the type-alist:

; ((my-assoc name l) -1537) ; ts-complement of consp

; Thus, when we go to get the type-set of (my-assoc name l) we don't even look
; at the rules about my-assoc, we just return -1537.

; Three fixes are possible.  First, process lits first so that (r l) is
; available when we do the (consp (my-assoc name l)).  Second, change type-set
; so that it uses rules about my-assoc even if the term (my-assoc name l) is
; bound on the type-alist.  Third, modify type-alist-clause so that it iterates
; as long as the type-alist changes so that it is not important in what order
; the lits are processed.  The second alternative seems potentially very slow,
; though we have done no experiments.  The third alternative is hard because
; one must ignore known types on the type-alist when reprocessing the lits.

; Feb 9, 1995.  We are trying a version of the third alternative, with
; reconsider-type-alist and the double whammy flag.

; End of Historical Comment

; In April, 2013, we experimented with the ``smart'' approach and temporarily
; introduced reorder-lits-and-ttrees-for-type-alist-clause into what would
; become Version_6.2.  In all the examples we looked at, the type-alists
; produced by this method were at least as strong as those produced by the
; earlier method.  Sometimes they are actually better, especially when the
; conclusions produced by forward-chained are disjunctions, e.g., (IF a a b),
; where earlier assumptions about a or b may give us stronger type-sets about b
; or a.

; The warning above about the effects of changing the order of the type-alist
; came to the fore in this experiment.  We found that 500 of the 3100+ books
; failed the regression.  (Of course, presumably many failed because they
; merely depended on books that failed for type-alist reasons.)  In any case,
; we abandoned the smart approach.

; But then we moved back to the (append new-clause (cdr tail) lits) approach
; dismissed earlier in the Historical Comment above.  The reasons for this
; ordering are fairly compelling: if one is to forward-chain to disjunctions
; they ought to be processed last so we can take advantage of known-false
; disjuncts within them.  We tried the old example cited in the Historical
; Comment above and it works under this approach -- presumably because in the
; ~20 years since that example was recorded, the system has changed in other
; ways (e.g., the sophistication now in assume-true-false-if and
; reconsider-type-alist).  But, not withstanding the Warning above about the
; dangers of reordering the type-alist, only three contemporary (April, 2013)
; books failed due to reordering reasons:

; books/centaur/bitops/congruences.lisp
; books/models/y86/y86-basic/common/read-over-write-proofs.lisp
; books/demos/modeling/network-state.lisp

; We decided to ``patch'' these proof scripts and stay with the ``forward-chained
; lits last'' reordering strategy.

; Search those books for: "; Reordering the rewrite-clause-type-alist" to see
; the three patched events.  Only one event in each book had to modified.  In
; two of the books one rune had to be disabled in each event (because that rule
; was able to fire in the new reordering but the proof had been designed when
; that rule was not firing).  The runes are obscure (if trying to reconstruct
; the proof via The Method) but were obtained simply by determining the runes
; for the failed subgoal under reordering that were not fired by the successful
; proof of that same subgoal.  Once the set of such runes was identified we
; could experiment to determine a ``minimal'' sufficient set (in each case a
; set of size 1).  In the third book (network-state.lisp) we proved a lemma
; that drastically simplified the affected proof.

; Our decision to change after Version_6.1 to using (append new-clause (cdr
; tail) lits) instead of the former (append lits new-clause (cdr tail)) was
; motivated by the following example from Dave Greve.  In this example, Dave
; expected the rewrite rule to suffice, but it did not.  It does now.

;    (defstub a-p (x) nil)
;    (defstub b-p (x) nil)
;    (defstub c-p (x) nil)
;    (defstub d-p (x) nil)
;
;    (defun x-p (x)
;      (or (a-p x)
;          (b-p x)
;          (c-p x)
;          (d-p x)))
;
;    (defthm forward
;      (implies
;       (x-p x)
;       (or (a-p x)
;           (b-p x)
;           (c-p x)
;           (d-p x)))
;      :rule-classes (:forward-chaining))
;
;    (in-theory (disable x-p))
;
;    (defun z-p (x)
;      (c-p x))
;
;    (defthm goo
;      (implies
;       (c-p x)
;       (z-p x))
;      :rule-classes (:rewrite :type-prescription))
;
;    (in-theory (disable z-p))
;
;    (in-theory (disable (:type-prescription goo)))
;
;    ; Fails, but Dave expected that (:rewrite goo) would suffice.
;
;    (defthm zoo
;      (implies
;       (and
;        (x-p x)
;        (not (a-p x))
;        (not (b-p x))
;        (not (d-p x)))
;       (z-p x)))

(defun rewrite-clause-type-alist (tail new-clause fc-pair-lst rcnst wrld
                                       pot-lst pt)

; We construct a type alist in which we assume (a) the falsity of every literal
; in tail except the first, (b) the falsity of every literal in new-clause, and
; (c) the truth of every concl in fc-pair-lst that is not dependent upon
; any literal noted in the parent tree (:pt) of rcnst.
; We do this by constructing a clause containing the literals in question
; (negating the concls in fc-pair-lst) and calling our general purpose
; type-alist-clause.  As of v2-8, we also pass in the simplify-clause-pot-lst
; to aid in the endeavor since type-set and assume-true-false can now
; (weakly) use linear arithmetic.

; We return a four-tuple, (mv contradictionp type-alist ttree current-clause),
; where contradictionp is t or nil and indicates whether we derived a
; contradiction.  Type-alist is the constructed type-alist (or nil if we got a
; contradiction).  Ttree is a ttree explaining the contradiction (or nil if got
; no contradiction).  Current-clause is the clause used in the computation
; described immediately above.

; Note: The type-alist returned may contain 'assumption tags.  In addition, the
; type-alist may contain some 'pt tags -- the conclusions derived by forward
; chaining will have their respective ttrees attached to them and these will
; have 'pt tags and could have 'assumptions.  We could throw out the 'pt tags
; if we wanted -- we are allowed to use everything in this type-alist because
; we only put accessible assumptions in it -- but we don't.  We must record the
; ttrees because of the possible 'assumption tags.

  (mv-let
   (lits ttree-lst)
   (select-forward-chained-concls-and-ttrees fc-pair-lst
                                             (access rewrite-constant rcnst :pt)
                                             nil nil)
   (mv-let (current-clause current-ttree-lst)
; The ``smart'' approach was this:
;           (reorder-lits-and-ttrees-for-type-alist-clause new-clause nil
;                                                          (cdr tail) nil
;                                                          lits ttree-lst)
; See the essay above for explanations.

           (mv (append new-clause (cdr tail) lits)
               (make-list-ac (+ (len new-clause) (len (cdr tail)))
                             nil
                             ttree-lst))
           (mv-let (contradictionp type-alist ttree)
                   (type-alist-clause
                    current-clause
                    current-ttree-lst
                    nil ; force-flg
                    nil ; initial type-alist
                    (access rewrite-constant rcnst :current-enabled-structure)
                    wrld
                    pot-lst pt)
                   (mv contradictionp type-alist ttree current-clause)))))

; Historical Plaque on Forward Chaining

; General purpose forward chaining was not implemented in Nqthm, although
; the linear arithmetic package and :COMPOUND-RECOGNIZER lemmas were (and
; still are) examples of forward-chaining reasoning.  The first two
; implementations of general purpose forward chaining in ACL2 occurred
; last week (April 9-13, 1990).  They were both implemented one level
; below where the current forward chaining module sits: we did forward
; chaining just before rewriting each literal of the clause, rather
; than doing all the forward chaining once and tracking dependencies.
; They were both abandoned because of inefficiency.  The killer was -- we
; think -- the repeated duplication of forward chaining derivations.  For
; example, if the clause to be rewritten was {~a ~b c1 ... ck} and an
; elaborate forward chaining tree can be built from a and b, then that
; tree was built when we began to rewrite c1 and that tree was built
; again when we began to rewrite c2, etc.  In addition, the old forward
; chaining scheme did not include the idea of triggers, it forward
; chained off the first hypothesis of a :FORWARD-CHAINING rule.  Finally,
; the old scheme used full fledged relieve-hyps to relieve the other hyps
; of the rules -- another potential killer but one that didn't get us
; simply because we had no forward chaining rules with more than one hyp
; in our tests.

; However, in an effort to help software archaeologists (not to mention
; the possibility that we might help ourselves avoid repetition of past
; mistakes) we inscribe here an extensive comment written last week:

; The Forward Chaining Essay - Version II (This essay is of at most historic
; interest.  For the current version of forward chaining, search for
; Forward Chaining from the top of this file.)

; We are about to start rewriting the current literal under the
; assumption of the negations of the literals in clause-seg.  We wish to
; forward chain off of these assumptions to generate a type-alist
; suitable for use during the rewriting.

; We return three values: t or nil indicating whether a contradiction was
; found while forward chaining, a new type-alist, and a ttree recording
; the forward-chaining-rules used.

; The form of a :FORWARD-CHAINING rule is:

; (defrec forward-chaining-rule
;   ((rune . nume) key-hyp other-hyps . concls) nil)

; If a lemma such as

; (implies (and hyp1 hyp2 ... hypn) (and concl1 ... conclk))

; is processed as a :FORWARD-CHAINING rule named name we will generate:

; (make forward-chaining-rule
;       :rune rune
;       :nume &
;       :key-hyp hyp1
;       :other-hyps (hyp2 ... hypn)
;       :concls (concl1 ... conclk)
;       :match-free once_or_all)

; which is stored under the 'forward-chaining-rules property of the top
; function symbol of hyp1.  By "top function symbol" we mean the outer
; most function symbol after stripping away any top-level NOT.

; When we apply a forward-chaining-rule we have a context defined by the
; set of assumptions off of which we are forward chaining (which is
; initially obtained by negating the literals of clause-seg) and a
; type-alist encoding those assumptions.  Our main result is, of course,
; the final type-alist.  But the set of assumptions is represented
; explicitly (indeed, somewhat elaborately) to support heuristics
; designed to avoid infinite loops while permitting the desired forward
; chaining.

; The list of assumptions is more properly thought of as the history of
; this forward chaining problem and is held in the variable fc-history.
; More on its structure later.

; Roughly speaking, one applies a :FORWARD-CHAINING rule to a term, hyp1',
; as follows: unify :key-hyp with hyp1' and then relieve-hyps the
; :other-hyps.  If those two steps do not succeed, the application fails.
; If they work, then make a heuristic decision about whether the
; resulting instance of :concls is worthwhile.  If it is not, the
; application fails.  If it is, add concl to the fc-history and
; type-alist and say the application succeeded.

; The structure of fc-history sufficient to support our current
; heuristics has evolved from a naive structure that just listed the
; assumptions made so far.  Initially, our heuristic decision was simply
; whether the candidate concl was worse-than any existing assumption.
; But imagine that among the initial hypotheses are (ASSOC & &) and
; (STATE-P1 S).  And imagine that some forward chaining rule lets you
; pump forward from (STATE-P1 S) to (P (CDR (ASSOC & &))).  Then you
; wouldn't get to use that rule because its conclusion is worse than
; (ASSOC & &).  This was the first indication that worse-than alone was
; too restrictive.  We fixed this by distinguishing the initial
; assumptions from those produced by forward chaining and we did the
; worse-than check only on the newly added ones.

; However, the next problem was illustrated by having two forward
; chaining rules:
;   name1: (state-p1 x) -> (p (nth 2 state))
;   name2: (state-p1 x) -> (p (nth 3 state)),
; that can get in each other's way.  If the first is used to add its
; conclusion then the second cannot be used because its conclusion is
; worse than that just added.

; So the structure of fc-history is now a list of pairs, each of the form
; (term . hist), where term is one of our assumptions and hist is the
; history of term.  If term is among the initial assumptions, then hist
; is nil.  If term was produced by the rule named name from some term'
; with history hist', then hist is (name term' . hist').

; Thus, another way to view it is that each entry in fc-history is of the
; form (term namek termk ... name2 term2 name1 term1) and means that term
; was produced by a chain of k forward chaining steps: starting with
; term1 (which is in the initial set of assumptions) use name1 to derive
; term2, use name2 to derive term3, ..., and use namek to derive term.

; Our heuristic for deciding whether to keep a conclusion, concl, is if
; namek has not been used in this chain, keep concl; otherwise, if namek
; has been used, then concl must be worse than nor equal to no termi in
; its chain.

; It is very inefficient to repeatedly hit all the assumptions with all
; the rules until no change occurs.  We have therefore taken steps to
; avoid unnecessary work.  First, if a rule has been successfully applied
; to a term then there is no need to apply it again (only to learn that
; its conclusion is rejected).  Second, if a conclusion has ever been
; produced before, there is no need to add it again (although technically
; it is probably possible to rederive it in a way that permits further
; chaining not permitted by the original derivation).  Third, if a rule
; named name is applied to a term term with derivation d and produces a
; concl that is rejected because of its ancestry, then don't apply name
; to term and d again.  To support this heuristic we have to keep track
; of the failed applications, which we do in the variable bad-appls.

; End of Historical Plaque

; Essay on Lambda Abstraction

; We will do some lambda abstraction when we rewrite literals.  That
; is implemented here.

; The original idea here was to expand lambdas by ordinary rewriting
; and then to fold them back up, removing duplicate occurrences of
; subterms.  Consider

; ((lambda (x y) (foo x (car y) x))
;  alpha
;  (cons b c))

; This would normally expand to

; (foo alpha b alpha)

; Suppose alpha is very large.  Then this is a problem.  I will
; fold it back up, to get:

; (let* ((u alpha))
;   (foo u b u))

; I have abandoned this idea as far as rewriting goes, though it
; probably still bears a closer look.  But I have adopted it as an
; option for prettyprinting clauses.

; The first sub-problem is identifying the common subterms (e.g.,
; alpha in (foo alpha b alpha)) to abstract away.  I call this the
; multiple subterm problem.

; We say that x is a "multiple subterm" of y if x occurs more than
; once in y.  We say x is a "maximal multiple subterm" of y if x is a
; multiple subterm of y and no other multiple subterm of y contains an
; occurrence of x.

; Our interest in maximal subterms is illustrated by (f (g (m x)) (g
; (m x))).  (M x) is a multiple subterm.  We might abstract this term
; to (let* ((v1 (m x)) (v2 (g v1))) (f v2 v2)).  But if (g (m x)) is
; identified as the first multiple subterm, then we get (let ((v1 (g
; (m x)))) (f v1 v1)) and there is only one let-binding, which we
; prefer.  So we wish to find a maximal multiple subterm.  We will
; eliminate them one at a time.  That way we will find smaller
; terms that still appear more than once.  For example:

; The term (f (g (m x)) (h (m x)) (g (m x))) may give rise first
; to (let* ((v1 (g (m x)))) (f v1 (h (m x)) v1)), but upon abstracting
; that we get (let* ((v2 (m x)) (v1 (g v2))) (f v1 v2 v1)).

; We are only interested in "non-atomic" multiple subterms, i.e.,
; function applications.  Our interest in non-atomic subterms is
; because otherwise we will infinitely recur ``eliminating'' multiple
; occurrences of variable symbols by introducing new variable symbols
; that occur multiple times.

; So to do lambda abstraction on term we will find a non-atomic
; maximal multiple subterm, e1, in term.  If successful, we will
; replace all occurrences of e1 in term by some new variable, say v1,
; producing, say, term1.  Now consider (f e1 term1), where f is some
; irrelevant made-up symbol.  This term has one less non-atomic
; multiple subterm, since e1 occurs only once in it and v1 is atomic.
; Repeat the process on this term until no multiple subterms are
; found.  The result is (f ek ... (f e1 termk)), which we can abstract
; to (let ((vk ek) ... (v1 e1)) termk).

; We would like to carry out this process without manufacturing the
; irrelevant function symbol f.  So we are really interested in
; multiple occurrences of a term in a list of terms.

(mutual-recursion

(defun foccurrences (term1 term2 ans)

; We ``count'' the number of occurrences of term1 in term2,
; ``summing'' the result into ans to be tail recursive, except:

; ans = nil means we've seen 0
; ans = t   means we've seen 1
; ans = >   means we've seen 2 or more

; Thus, nil + 1 = t
;       t + 1   = >
;       > + 1   = >
; so (+ ans 1) is (if ans '> t) and we can short-circuit whenever ans
; is >.

; Observe that if (eq (foccurrences term1 term2 t) '>) is t, then term1
; occurs at least once in term2.  This could also be tested by asking
; whether (foccurrences term1 term2 nil) is non-nil, but that idiom is
; less efficient because the former short-circuits as soon as the
; first occurrence is found, while the latter doesn't short-circuit
; until the second occurrence (if any) is found.

  (cond
   ((equal term1 term2) (if ans '> t))
   ((eq ans '>) '>)
   ((variablep term2) ans)
   ((fquotep term2) ans)
   (t (foccurrences-lst term1 (fargs term2) ans))))

(defun foccurrences-lst (term lst ans)
  (cond ((endp lst) ans)
        ((eq ans '>) '>)
        (t (foccurrences-lst term
                             (cdr lst)
                             (foccurrences term (car lst) ans))))))

(mutual-recursion

(defun maximal-multiple (x term-lst winner)

; In this definition, x is a term, but I am using it as though it were
; just the set of all of its subterms.  I wish to find a non-atomic
; subterm, e, of x that is a maximal multiple subterm in the list of
; terms term-lst.  Winner is either nil or the maximal multiple found
; so far.

  (cond
   ((or (variablep x)
        (fquotep x))
    winner)
   ((eq (foccurrences-lst x term-lst nil) '>)
    (cond ((equal winner nil) x)
          ((eq (foccurrences x winner t) '>) winner)
          ((eq (foccurrences winner x t) '>) x)
          (t winner)))
   (t (maximal-multiple-lst (fargs x) term-lst winner))))

(defun maximal-multiple-lst (x-lst term-lst winner)
  (cond ((endp x-lst) winner)
        (t (maximal-multiple-lst (cdr x-lst)
                                 term-lst
                                 (maximal-multiple (car x-lst)
                                                   term-lst
                                                   winner))))))

; So, to find a non-atomic maximal multiple subterm of a single term,
; term, do (maximal-multiple term (list term) nil).  More generally,
; to find a non-atomic maximal multiple in a list of terms, lst, do
; (maximal-multiple lst lst nil).  If the result is nil, there is no
; such subterm.  Otherwise, the result is one.

; To carry out the algorithm sketched above, we must iteratively
; find and replace the maximal multiples by new variable symbols.

(defun maximal-multiples1 (term-lst new-vars avoid-vars pkg-witness)
  (let ((e (maximal-multiple-lst term-lst term-lst nil)))
    (cond
     ((equal e nil)
      (mv new-vars term-lst))
     (t (let ((var (genvar pkg-witness "V"
                           (+ 1 (len new-vars))
                           avoid-vars)))
          (maximal-multiples1
           (cons e (subst-expr1-lst var e term-lst))
           (cons var new-vars)
           (cons var avoid-vars)
           pkg-witness))))))

(defun maximal-multiples (term pkg-witness)

; This function returns (mv vars terms), where terms is one longer
; than vars.  Suppose vars is (v3 v2 v1) and terms is (e3 e2 e1
; term3).  Then term is equivalent to

; (let* ((v3 e3) (v2 e2) (v1 e1)) term3).

; Observe that if vars is nil there are no multiple subterms and terms
; is the singleton containing term.

  (maximal-multiples1 (list term) nil (all-vars term) pkg-witness))

; We also will clean up certain IF-expressions.

(defun mutually-exclusive-tests (a b)

; We return t if terms (and a b) cannot be true.  We just recognize
; the case where each is (EQUAL x 'constant) for different constants.

  (and (ffn-symb-p a 'equal)
       (ffn-symb-p b 'equal)
       (or (and (quotep (fargn a 1))
                (quotep (fargn b 1))
                (not (equal (cadr (fargn a 1)) (cadr (fargn b 1))))
                (equal (fargn a 2) (fargn b 2)))

           (and (quotep (fargn a 2))
                (quotep (fargn b 2))
                (not (equal (cadr (fargn a 2)) (cadr (fargn b 2))))
                (equal (fargn a 1) (fargn b 1)))

           (and (quotep (fargn a 1))
                (quotep (fargn b 2))
                (not (equal (cadr (fargn a 1)) (cadr (fargn b 2))))
                (equal (fargn a 2) (fargn b 1)))

           (and (quotep (fargn a 2))
                (quotep (fargn b 1))
                (not (equal (cadr (fargn a 2)) (cadr (fargn b 1))))
                (equal (fargn a 1) (fargn b 2))))))

(defun mutually-exclusive-subsumptionp (a b c)

; This is a generalized version of (if x y y).  Suppose we wish to
; form (if a b c) but that b is c.  Then clearly, the result is equal
; to c.  Now imagine that c is (if c1 c2 c3) and that a and c1 are
; mutually exclusive.  Then we could form (if c1 c2 (if a b c3))
; instead.  This would be a win if it turns out that after rippling
; down we find that b is equal to ck: (if a b c) is just c.

  (cond
   ((equal b c) t)
   ((and (ffn-symb-p c 'IF)
         (mutually-exclusive-tests a (fargn c 1)))
    (mutually-exclusive-subsumptionp a b (fargn c 3)))
   (t nil)))

(mutual-recursion

(defun cleanup-if-expr (x trues falses)
  (cond
   ((variablep x) x)
   ((fquotep x) x)
   ((eq (ffn-symb x) 'IF)
    (let ((a (cleanup-if-expr (fargn x 1) trues falses)))
      (cond
       ((quotep a)
        (if (cadr a)
            (cleanup-if-expr (fargn x 2) trues falses)
          (cleanup-if-expr (fargn x 3) trues falses)))
       ((member-equal a trues)
        (cleanup-if-expr (fargn x 2) trues falses))
       ((member-equal a falses)
        (cleanup-if-expr (fargn x 3) trues falses))
       (t (let ((b (cleanup-if-expr (fargn x 2) (cons a trues) falses))
                (c (cleanup-if-expr (fargn x 3) trues (cons a falses))))
            (cond ((equal b c) b)
                  ((mutually-exclusive-subsumptionp a b c)
                   c)
                  (t (mcons-term* 'if a b c))))))))
   (t (mcons-term (ffn-symb x)
                  (cleanup-if-expr-lst (fargs x) trues falses)))))

(defun cleanup-if-expr-lst (x trues falses)
  (cond ((endp x) nil)
        (t (cons (cleanup-if-expr (car x) trues falses)
                 (cleanup-if-expr-lst (cdr x) trues falses)))))
)

(defun all-type-reasoning-tags-p1 (lemmas)
  (cond ((endp lemmas) t)
        ((or (eq (car (car lemmas)) :FAKE-RUNE-FOR-TYPE-SET)
             (eq (car (car lemmas)) :TYPE-PRESCRIPTION))
         (all-type-reasoning-tags-p1 (cdr lemmas)))
        (t nil)))

(defun all-type-reasoning-tags-p (ttree)
  (all-type-reasoning-tags-p1 (tagged-objects 'lemma ttree)))

(defun try-clause (atm clause wrld)

; We assume that atm rewrites to t or nil.  We return t if we are to keep that
; rewrite, else nil.

  (cond ((endp clause)
         nil)
        ((and (eq (fn-symb (car clause)) 'not)
              (equal-mod-commuting atm (fargn (car clause) 1) wrld))
         t)
        ((equal-mod-commuting atm (car clause) wrld)
         t)
        (t
         (try-clause atm (cdr clause) wrld))))

(defconst *trivial-non-nil-ttree*
  (puffert nil))

(defun make-non-nil-ttree (ttree)
  (or ttree
      *trivial-non-nil-ttree*))

(defun try-type-set-and-clause (atm ans ttree ttree0 current-clause wrld ens
                                    knownp)

; We are finishing off a call to rewrite-atm on atm that is about to return ans
; with associated ttree, which is assumed to extend ttree0.  Ans is *t* or
; *nil*, but in a context in which this would produce a removal of ans rather
; than a win.  We have found it heuristically useful to disallow such removals
; except when atm is trivially known to be true or false.  We return the
; desired rewritten value of atm and associated justifying ttree that extends
; ttree0.

  (mv-let (ts ttree1)
          (type-set atm nil nil nil ens wrld nil nil nil)
          (cond ((ts= ts *ts-nil*)

; Type-set was able to reduce atm to nil, by examining atm in isolation.  This
; would happen, for instance to an atm such as (not (acl2-numberp (+ x y))) or
; (not (consp (cons x y))).  We want to allow such trivial facts to be removed
; from the clause to reduce clutter.  We certainly do not lose anything by
; allowing such removals.

                 (mv *nil* (cons-tag-trees ttree1 ttree0) nil))
                ((ts-subsetp ts *ts-non-nil*)
                 (mv *t* (cons-tag-trees ttree1 ttree0) nil))
                ((try-clause atm current-clause wrld)
                 (mv ans ttree nil))
                (t
                 (mv atm ttree0 (and knownp (make-non-nil-ttree ttree)))))))

(mutual-recursion

(defun lambda-subtermp (term)

; We determine whether some lambda-expression is used as a function in term.

  (declare (xargs :guard (pseudo-termp term)))
  (if (or (variablep term)
          (fquotep term))
      nil
    (or (flambdap (ffn-symb term))
        (lambda-subtermp-lst (fargs term)))))

(defun lambda-subtermp-lst (termlist)
  (declare (xargs :guard (pseudo-term-listp termlist)))
  (if (consp termlist)
      (or (lambda-subtermp (car termlist))
          (lambda-subtermp-lst (cdr termlist)))
    nil))

)

(defun rewrite-atm (atm not-flg bkptr gstack type-alist wrld
                        simplify-clause-pot-lst rcnst current-clause state
                        step-limit ttree0)

; This function rewrites atm with rewrite, in the given context, maintaining
; iff.

; Note that not-flg is only used heuristically, as it is the responsibility of
; the caller to account properly for it.  Current-clause is also used only
; heuristically.

; It is used to rewrite the atoms of a clause as we sweep across.  It is
; essentially a call of rewrite -- indeed, it didn't exist in Nqthm and rewrite
; was called in its place -- but with a couple of exceptions.  For one thing,
; it first gives type-set a chance to decide things.

; But a more complex exception is that instead of the usual result from
; rewrite, (mv step-limit rewritten-atm ttree), we return a fourth value as
; well: when non-nil, it is a ttree justifying the rewriting of atm to *t* or
; *nil* according to not-flg having value t or nil, respectively.  We use this
; additional information to rewrite a clause to *false-clause* when every
; literal simplifies to nil even when our heuristics (documented rather
; extensively below) would normally refuse to simplify at least one of those
; literals; see parameter fttree in rewrite-clause.  The following example from
; Pete Manolios illustrates this situation: (thm (<= (+ 1 (acl2-count x)) 0)).
; In this case, there is only one literal, which simplifies to nil; and our
; heuristics would normally refuse to take advantage of that simplification.
; But since every literal (i.e., this one) simplifies to nil, then even if we
; wouldn't normally take advantage of that information, we nevertheless rewrite
; the clause to false.  As Pete points out, this helps the user to see the
; likely falsehood of the conjecture, which otherwise can trigger a useless but
; distracting proof by induction.

; Another example like the one above, but involving two literals, is:
; (thm (or (<= (+ 1 (acl2-count x)) -1) (< (acl2-count x) 0))).  It seems not
; quite trivial to come up with such two-literal examples that generate
; inductions in Version_3.6.1, before this improvement; for example, the thm
; just above fails to be such an example if we switch the order of arguments to
; OR.

  (mv-let (knownp nilp ttree)
          (known-whether-nil atm type-alist
                             (access rewrite-constant rcnst
                                     :current-enabled-structure)
                             (ok-to-force rcnst)

; The use of dwp = t here, together with the passing of dwp down to
; the calls of type-set-with-rules in type-set-rec, enables the proof of the
; thm below to go through.  This example is a distillation of an example that
; arose during a proof attempt by Matt Kaufmann.

;   (defstub f1 (x) t)
;   (defstub f2 (x) t)
;   (defstub f3 (x) t)
;   (defaxiom ax1
;     (implies (f1 x)
;              (f2 x)))
;   (defaxiom ax2
;     (implies (force (f2 x))
;              (natp (f3 x)))
;     :rule-classes :type-prescription)
;   (thm (implies (and (f1 x)
;                      (f3 x))
;                 (<= 0 (f3 x))))

                             t ; dwp
                             wrld
                             ttree0)
          (cond

; Before Version  2.6 we had

;           (knownp
;            (cond (nilp (mv *nil* ttree))
;                  (t (mv *t* ttree))))

; but this allowed type-set to remove ``facts'' from a theorem which
; may be needed later.  The following transcript illustrates the previous
; behavior:

;  ACL2 !>(defthm fold-consts-in-+
;           (implies (and (syntaxp (consp c))
;                         (syntaxp (eq (car c) 'QUOTE))
;                         (syntaxp (consp d))
;                         (syntaxp (eq (car d) 'QUOTE)))
;                    (equal (+ c d x)
;                           (+ (+ c d) x))))
;  ACL2 !>(defthm helper
;           (implies (integerp x)
;                    (integerp (+ 1 x))))
;  ACL2 !>(thm
;           (implies (integerp (+ -1/2 x))
;                    (integerp (+ 1/2 x)))
;           :hints (("Goal" :use ((:instance helper
;                                            (x (+ -1/2 x)))))))
;
;  [Note:  A hint was supplied for our processing of the goal above.
;  Thanks!]
;
;  ACL2 Warning [Use] in ( THM ...):  It is unusual to :USE an enabled
;  :REWRITE or :DEFINITION rule, so you may want to consider disabling
;  (:REWRITE HELPER).
;
;
;  We now augment the goal above by adding the hypothesis indicated by
;  the :USE hint.  The hypothesis can be derived from HELPER via instantiation.
;  The augmented goal is shown below.
;
;  Goal'
;  (IMPLIES (IMPLIES (INTEGERP (+ -1/2 X))
;                    (INTEGERP (+ 1 -1/2 X)))
;           (IMPLIES (INTEGERP (+ -1/2 X))
;                    (INTEGERP (+ 1/2 X)))).
;
;  By case analysis we reduce the conjecture to
;
;  Goal''
;  (IMPLIES (AND (OR (NOT (INTEGERP (+ -1/2 X)))
;                    (INTEGERP (+ 1 -1/2 X)))
;                (INTEGERP (+ -1/2 X)))
;           (INTEGERP (+ 1/2 X))).
;
;  This simplifies, using primitive type reasoning, to
;
;  Goal'''
;  (IMPLIES (INTEGERP (+ -1/2 X))
;           (INTEGERP (+ 1/2 X))).
;
;  Normally we would attempt to prove this formula by induction.  However,
;  we prefer in this instance to focus on the original input conjecture
;  rather than this simplified special case.  We therefore abandon our
;  previous work on this conjecture and reassign the name *1 to the original
;  conjecture.  (See :DOC otf-flg.)
;
;  No induction schemes are suggested by *1.  Consequently, the proof
;  attempt has failed.
;
;  Summary
;  Form:  ( THM ...)
;  Rules: ((:DEFINITION IMPLIES)
;          (:DEFINITION NOT)
;          (:FAKE-RUNE-FOR-TYPE-SET NIL))
;  Warnings:  Use
;  Time:  0.03 seconds (prove: 0.02, print: 0.01, other: 0.00)
;
;  ******** FAILED ********  See :DOC failure  ******** FAILED ********
;  ACL2 !>

; Note that in the transition from Goal'' to Goal''', the needed
; fact --- (INTEGERP (+ 1 -1/2 X)) --- was removed by type reasoning.
; This is not good.  We now only use type reasoning at this point if
; it will give us a win.

; One might ask why we only disallow type-set from removing facts here.
; Why not elsewhere, and what about rewrite?  We do it this way because
; it is only here that the user cannot prevent this removal from
; happening by manipulating the enabled structure.

           ((and knownp not-flg nilp)

; We have reduced the atm to nil but it occurs negated in the
; clause and so we have reduced the literal to t, proving the clause.
; So we report this reduction.

            (mv step-limit *nil* ttree nil))
           ((and knownp (not not-flg) (not nilp))
            (mv step-limit *t* ttree nil))
           (t
            (let ((lemmas0 (tagged-objects 'lemma ttree0))
                  (ttree00 (remove-tag-from-tag-tree 'lemma ttree0)))
              (sl-let (ans1 ans2)
                      (rewrite-entry
                       (rewrite atm
                                nil
                                bkptr)
                       :rdepth (rewrite-stack-limit wrld)
                       :step-limit step-limit
                       :type-alist type-alist
                       :obj '?
                       :geneqv *geneqv-iff*
                       :pequiv-info nil
                       :wrld wrld
                       :fnstack nil
                       :ancestors nil
                       :backchain-limit (access rewrite-constant rcnst
                                                :backchain-limit-rw)
                       :simplify-clause-pot-lst simplify-clause-pot-lst
                       :rcnst rcnst
                       :gstack gstack
                       :ttree ttree00)
                      (let* ((old-lemmas lemmas0)
                             (new-lemmas (tagged-objects 'lemma ans2))
                             (final-lemmas (if old-lemmas
                                               (union-equal new-lemmas
                                                            old-lemmas)
                                             new-lemmas))
                             (ttree (maybe-extend-tag-tree
                                     'lemma
                                     final-lemmas
                                     (remove-tag-from-tag-tree 'lemma ans2))))

; But we need to do even more work to prevent type-set from removing
; ``facts'' from the goal.  Here is another (edited) transcript:

;  ACL2 !>(defun foo (x y)
;    (if (acl2-numberp x)
;        (+ x y)
;      0))
;
;  ACL2 !>(defthm foo-thm
;    (implies (acl2-numberp x)
;             (equal (foo x y)
;                    (+ x y))))
;  ACL2 !>(in-theory (disable foo))
;  ACL2 !>(thm
;   (implies (and (acl2-numberp x)
;                 (acl2-numberp y)
;                 (equal (foo x y) x))
;            (equal y 0)))
;
;  This simplifies, using the :type-prescription rule FOO, to
;
;  Goal'
;  (IMPLIES (AND (ACL2-NUMBERP Y)
;                (EQUAL (FOO X Y) X))
;           (EQUAL Y 0)).
;
;  Name the formula above *1.
;
;  No induction schemes are suggested by *1.  Consequently, the proof
;  attempt has failed.
;
;  Summary
;  Form:  ( THM ...)
;  Rules: ((:TYPE-PRESCRIPTION FOO))
;  Warnings:  None
;  Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
;
;  ******** FAILED ********  See :DOC failure  ******** FAILED ******** ; |

; Note that in the transition from Goal to Goal' we removed the critical fact
; that x was an acl2-numberp.  This fact can be derived from the third
; hypothesis --- (equal (foo x y) x) --- via :type-prescription rule FOO as
; indicated.  However, when we then go on to rewrite the third hypothesis, we
; are not able to rederive this fact, since the type-alist used at that point
; does not use use the third hypothesis so as to prevent tail biting.

; Robert Krug has seen this sort of behavior in reasoning about floor and mod.
; In fact, that experience motivated him to provide the original version of the
; code below not to remove certain additional facts.

; Finally, note that even before this additional care, the lemma

;  (thm
;   (implies (and (acl2-numberp y)
;                 (equal (foo x y) x)
;                 (acl2-numberp x))
;            (equal y 0)))

; does succeed, since the (acl2-numberp x) hypothesis now appears after the
; (equal (foo x y) x) hypothesis, hence does not get removed until after it has
; been used to relieve the hypothesis of foo-thm.  This kind of situation in
; which a proof succeeds or fails depending on the order of hypotheses really
; gets Robert's goat.

                        (cond ((not (or (equal ans1 *nil*)
                                        (equal ans1 *t*)))

; We have, presumably, not removed any facts, so we allow this rewrite.

                               (mv step-limit ans1 ttree
                                   (and knownp *trivial-non-nil-ttree*)))
                              ((and (nvariablep atm)
                                    (not (fquotep atm))
                                    (equivalence-relationp (ffn-symb atm)
                                                           wrld))

; We want to blow away equality (and equivalence) hypotheses, because for
; example there may be a :use or :cases hint that is intended to blow away (by
; implication) such hypotheses.

                               (mv step-limit ans1 ttree nil))
                              ((equal ans1 (if not-flg *nil* *t*))

; We have proved the original literal from which atm is derived; hence we have
; proved the clause.  So we report this reduction.

                               (mv step-limit ans1 ttree nil))
                              ((all-type-reasoning-tags-p ans2)

; Type-reasoning alone has been used, so we are careful in what we allow.

                               (cond ((lambda-subtermp atm)

; We received an example from Jared Davis in which a hypothesis of the form
; (not (let ...)) rewrites to true with a tag-tree of nil, and hence was kept
; without this lambda-subtermp case.  The problem with keeping that hypothesis
; is that it has calls of IF in a lambda body, which do not get eliminated by
; clausification -- and this presence of IF terms causes the :force-info field
; to be set to 'weak in the rewrite constant generated under simplify-clause.
; That 'weak setting prevented forced simplification from occurring that was
; necessary in order to make progress in Jared's proof!

; A different solution would be to ignore IF calls in lambda bodies when
; determining whether to set :force-info to 'weak.  However, that change caused
; a regression suite failure: in community book
; books/symbolic/tiny-fib/tiny-rewrites.lisp, theorem next-instr-pop.  The
; problem seemed to be premature forcing, of just the sort we are trying to
; prevent with the above-mentioned check for IF terms.

; Robert Krug points out to us, regarding the efforts here to keep hypotheses
; that rewrote to true, that for him the point is simply not to lose Boolean
; hypotheses like (acl2-numberp x) in the example above.  Certainly we do not
; expect terms with lambda calls to be of that sort, or even to make any sorts
; of useful entries in type-alists.  If later we find other reasons to keep *t*
; or *nil*, we can probably feel comfortable in adding conditions as we have
; done with the lambda-subtermp test above.

                                      (mv step-limit ans1 ttree nil))
                                     ((eq (fn-symb atm) 'implies)

; We are contemplating throwing away the progress made by the above call of
; rewrite.  However, we want to keep progress made by expanding terms of the
; form (IMPLIES x y), so we do that expansion (again) here.  It seems
; reasonable to keep this in sync with the corresponding use of subcor-var in
; rewrite.

                                      (prepend-step-limit
                                       3
                                       (try-type-set-and-clause
                                        (subcor-var (formals 'implies wrld)
                                                    (list (fargn atm 1)
                                                          (fargn atm 2))
                                                    (bbody 'implies))
                                        ans1 ttree ttree0 current-clause wrld
                                        (access rewrite-constant rcnst
                                                :current-enabled-structure)
                                        knownp)))
                                     (t

; We make one last effort to allow removal of certain ``trivial'' facts from
; the goal.

                                      (prepend-step-limit
                                       3
                                       (try-type-set-and-clause
                                        atm
                                        ans1 ttree ttree0 current-clause wrld
                                        (access rewrite-constant rcnst
                                                :current-enabled-structure)
                                        knownp)))))
                              (t
                               (mv step-limit ans1 ttree nil))))))))))

; Now we develop the functions for finding trivial equivalence hypotheses and
; stuffing them into the clause, transforming {(not (equal n '27)) (p n x)},
; for example, into {(p '27 x)} and running p if x is constant too.

(mutual-recursion

(defun every-occurrence-equiv-hittablep1
  (equiv old geneqv term in-hide-flg ens wrld)

; This function determines whether every occurrence of old in term is ``equiv
; hittable'' while maintaining geneqv.  This is just an optimization of a call
; to subst-equiv-expr followed by an occur check.

; NOTE:  We ignore occurrences of old inside arguments to HIDE.

  (cond ((equal term old)

; If term is old, then we return non-nil or nil according to whether
; equiv refines geneqv.  If it does refine geneqv, this occurrence
; will be hit; if not, this occurrence won't be hit.  Actually, if
; we are inside a call of hide then this occurrence won't be hit
; either way.

         (and (not in-hide-flg)
              (geneqv-refinementp equiv geneqv wrld)))
        ((or (variablep term)
             (fquotep term))

; If term is different from old and doesn't contain old, e.g., term is a
; variable or a quote, then all occurrences of old in term are equiv
; hittable.  Hide is handled below.

         t)
        (t (every-occurrence-equiv-hittablep1-listp
            equiv
            old
            (geneqv-lst (ffn-symb term)
                        geneqv
                        ens
                        wrld)
            (fargs term)
            (or in-hide-flg
                (eq (ffn-symb term) 'hide))
            ens wrld))))

(defun every-occurrence-equiv-hittablep1-listp
  (equiv old geneqv-lst args in-hide-flg ens wrld)
  (cond ((null args) t)
        (t (and
            (every-occurrence-equiv-hittablep1
             equiv old
             (car geneqv-lst)
             (car args)
             in-hide-flg
             ens wrld)
            (every-occurrence-equiv-hittablep1-listp
             equiv old
             (cdr geneqv-lst)
             (cdr args)
             in-hide-flg
             ens wrld)))))
)

(defun every-occurrence-equiv-hittablep (equiv old geneqv term ens wrld)

; This function determines whether every occurrence of old in term is ``equiv
; hittable'' while maintaining geneqv.  This means that (subst-equiv-expr equiv
; new old geneqv term ens wrld state ttree) will remove all occurrences of old
; from term (assuming there are no occurrences of old in new and old is a
; variable).

; We here enforce the rule that we don't know how to substitute for explicit
; constants.  We also build in the fact that everything is equal-hittable
; (i.e., equal refines all equivalence relations).

; NOTE:  We ignore occurrences of old inside arguments to HIDE.

  (cond
   ((and (nvariablep old)
         (fquotep old))
    (subst-expr-error old))
   ((eq equiv 'equal) t)
   (t (every-occurrence-equiv-hittablep1 equiv old geneqv term nil ens wrld))))

(defun every-occurrence-equiv-hittablep-in-clausep (equiv old cl ens wrld)

; This checks that every occurrence of old in cl is equiv hittable
; while maintaining 'iff on each literal.  This is just a special case
; in which we are checking every-occurrence-equiv-hittablep1-listp where
; geneqv-lst is a list, as long as cl, of *geneqv-iff*s.  Rather than
; manufacture the suitable geneqv-lst we just supply *geneqv-iff* as
; needed.

  (cond ((null cl) t)
        (t (and
            (every-occurrence-equiv-hittablep1
             equiv old
             *geneqv-iff*
             (car cl)
             nil
             ens wrld)
            (every-occurrence-equiv-hittablep-in-clausep
             equiv old (cdr cl) ens wrld)))))

(mutual-recursion

(defun some-occurrence-equiv-hittablep1 (equiv old geneqv term ens wrld)

; This function determines whether there exists an equiv-hittable occurrence of
; old in term maintaining geneqv.

  (cond ((equal term old)

; If term is old, then we return non-nil or nil according to whether
; equiv refines geneqv.  If it does refine geneqv, this occurrence
; will be hit; if not, this occurrence won't be hit.

         (geneqv-refinementp equiv geneqv wrld))
        ((or (variablep term)
             (fquotep term)
             (eq (ffn-symb term) 'hide))

; If term is different from old and doesn't contain old, e.g., term is
; a variable or a quote, then there is no occurrence of old in term.
; Calls of hide are included, since substitution (subst-equiv-expr)
; does not go inside calls of hide.

         nil)
        (t (some-occurrence-equiv-hittablep1-listp
            equiv
            old
            (geneqv-lst (ffn-symb term)
                        geneqv
                        ens
                        wrld)
            (fargs term)
            ens wrld))))

(defun some-occurrence-equiv-hittablep1-listp
  (equiv old geneqv-lst args ens wrld)
  (cond ((null args) nil)
        (t (or
            (some-occurrence-equiv-hittablep1
             equiv old
             (car geneqv-lst)
             (car args)
             ens wrld)
            (some-occurrence-equiv-hittablep1-listp
             equiv old
             (cdr geneqv-lst)
             (cdr args)
             ens wrld)))))
)

(defun some-occurrence-equiv-hittablep (equiv old geneqv term ens wrld)

; This function determines whether some occurrence of old in term is ``equiv
; hittable'' while maintaining geneqv.  This means that (subst-equiv-expr equiv
; new old geneqv term ens wrld state ttree) changes term.

; We here enforce the rule that we don't know how to substitute for explicit
; constants.

; NOTE:  We ignore occurrences of old inside arguments to HIDE.

  (cond
   ((and (nvariablep old)
         (fquotep old))
    (subst-expr-error old))
   (t (some-occurrence-equiv-hittablep1 equiv old geneqv term ens wrld))))

(defun equiv-hittable-in-some-other-lit (equiv term n cl i ens wrld)

; We determine whether term occurs in an equiv-hittable slot (maintaining iff)
; in some lit of clause cl other than the nth.  The number of the first literal
; of cl is i.

  (cond ((null cl) nil)
        ((int= n i)
         (equiv-hittable-in-some-other-lit equiv term n (cdr cl) (1+ i) ens wrld))
        ((some-occurrence-equiv-hittablep equiv term *geneqv-iff* (car cl) ens wrld)
         t)
        (t (equiv-hittable-in-some-other-lit equiv term n (cdr cl) (1+ i) ens wrld))))

(defun find-trivial-equivalence1
  (not-just-quotep-flg tail i cl ens wrld avoid-lst)

; Cl is a clause.  Tail is a tail of cl and i is the position number
; of its first literal, starting from 0 for the first lit in cl.  See
; find-trivial-equivalence for the rest of the spec.

; It is important to keep in mind that the clause upon which we are working has
; not necessarily been rewritten.  Indeed, it is often the product of previous
; substitutions by the driver of this very function.  (Aside: once upon a time,
; the driver did not evaluate literals as they got stuffed with constants.  At
; the moment it does evaluate enabled fns on constant args.  But that may
; change and so this function is written in a way that assumes the worst: there
; may be reducible terms in the clause.)  Thus, for example, a clause like
;    {(not (equal x 'a)) (not (equal y 'b)) (not (equal x y)) y ...}
; may first produce
;    {(not (equal y 'b)) (not (equal 'a y)) y ...}
; and then
;    {(not (equal 'a 'b)) 'b ...}
; which contains two unexpected sorts of literals: an equivalence with constant
; args and a constant literal.  We must therefore not be surprised by such
; literals.  However, we do not expect them to arise often enough to justify
; making our caller cope with the possibility that we've proved the clause.  So
; if we find such a literal and can decide the clause, we will just immediately
; report that there are no more usable equivalences and let the simplifier
; rediscover the literal.  If we find such a literal and can't decide the
; clause quickly based on equal and iff facts (we are not going to eval
; user-defined equivs) then we will just continue looking for usable
; equivalences.  The idea is that if the discovered lit makes the clause true,
; we don't expect to have screwed it up by continuing to substitute; and if the
; discovered lit just drops out, then our continued substitution is what we
; should have done.  (Aside: If we persist in our decision to reduce literals
; when they are stuffed with constants, then these cases will not arise and all
; of the above is irrelevant.)

; Recall our output spec from find-trivial-equivalence.  The six results we
; return are the name of the condition detected (disposable or keeper), the
; location i of the literal, equiv, lhs, rhs and the literal itself.  Otherwise
; we return 6 nils.  (When we succeed, the "lhs" of our result is the term for
; which we are to substitute and "rhs" is the term by which we replace lhs.
; They may in fact come from the opposite sides of the equivalence term.)

  (cond ((null tail) (mv nil nil nil nil nil nil))
        ((member-equal (car tail) avoid-lst)
         (find-trivial-equivalence1
          not-just-quotep-flg (cdr tail) (1+ i) cl ens wrld avoid-lst))

; Handle variable V as though it is the literal (not (equal V nil)).

        ((quotep (car tail))

; If the discovered lit is nil, then we just ignore it because it will drop
; out.  If the discovered lit is non-nil, this clause is true.  So we signal
; that there are no more usable equivs and let the simplifier get its hands
; on the clause to rediscover that it is true.

         (if (equal (car tail) *nil*)
             (find-trivial-equivalence1
              not-just-quotep-flg (cdr tail) (1+ i) cl ens wrld avoid-lst)
             (mv nil nil nil nil nil nil)))
        ((or (variablep (car tail))
             (and (eq (ffn-symb (car tail)) 'not)
                  (or (variablep (fargn (car tail) 1))
                      (and (not (fquotep (fargn (car tail) 1)))
                           (equivalence-relationp (ffn-symb (fargn (car tail) 1)) wrld)))))
         (let* ((atm
                 (if (variablep (car tail))
                     (fcons-term* 'equal (car tail) *nil*)
                   (fargn (car tail) 1)))
                (equiv (if (variablep atm)
                           'iff
                         (ffn-symb atm)))
                (lhs (if (variablep atm)
                         atm
                       (fargn atm 1)))
                (rhs (if (variablep atm)
                         *t*
                       (fargn atm 2))))

; We have discovered an equiv hyp (not (equiv lhs rhs)) that is not on avoid-lst.

           (cond ((and (quotep lhs)
                       (quotep rhs))

; Oh! It has constant args.  If equiv is equal we decide which way this lit
; goes and act accordingly, as we did for a quotep lit above.  If the equiv is
; not equal then we just assume this lit will eventually drop out (we bet it is
; nil) and go on looking for other usable equivs before giving the result to
; the simplifier to decide.

                  (cond ((eq equiv 'equal)
                         (if (equal lhs rhs)
                             (find-trivial-equivalence1
                              not-just-quotep-flg
                              (cdr tail) (1+ i) cl ens wrld avoid-lst)
                             (mv nil nil nil nil nil nil)))
                        (t (find-trivial-equivalence1
                            not-just-quotep-flg
                            (cdr tail) (1+ i) cl ens wrld avoid-lst))))

; So below we know that if one side is a quotep then the other side is not (but
; we don't yet know that either side is a quotep).  Observe that if one side is
; a quotep we are always safe in answering that we can equiv substitute for the
; other side and it is only a question of whether we have a disposable lit or a
; keeper.

                 ((and not-just-quotep-flg
                       (variablep lhs)
                       (every-occurrence-equiv-hittablep-in-clausep
                        equiv lhs cl ens wrld)
                       (not (dumb-occur lhs rhs)))

; The 'disposable condition is met:  lhs is an everywhere hittable variable not in rhs.
; But it could be that rhs is also an everywhere hittable variable not in lhs.
; If so, we'll substitute the term-order smaller for the bigger just so the
; user knows which way the substitutions will go.

                  (cond ((and (variablep rhs)
                              (every-occurrence-equiv-hittablep-in-clausep
                               equiv rhs cl ens wrld))
                         (cond
                          ((term-order lhs rhs)
                           (mv 'disposable i equiv rhs lhs (car tail)))
                          (t (mv 'disposable i equiv lhs rhs (car tail)))))
                        (t (mv 'disposable i equiv lhs rhs (car tail)))))
                 ((and not-just-quotep-flg
                       (variablep rhs)
                       (every-occurrence-equiv-hittablep-in-clausep
                        equiv rhs cl ens wrld)
                       (not (dumb-occur rhs lhs)))

; This is the case symmetric to that above.

                  (mv 'disposable i equiv rhs lhs (car tail)))
                 ((and (quotep rhs) ; thus lhs is a non-quotep
                       (equiv-hittable-in-some-other-lit equiv lhs i cl 0 ens wrld))

; The 'keeper conditions are met:  lhs is a non-quote with at least one
; equiv-hittable occurrence in another lit and rhs is a quote.  Note that in
; the case that not-just-quotep-flg is nil, we might be giving the ``wrong''
; first answer, since if lhs is a variable then 'keeper should be 'disposable.
; However, if not-just-quotep-flg is nil, then we will be ignoring that answer
; anyhow; see the call of subst-equiv-and-maybe-delete-lit in
; remove-trivial-equivalences.

                  (mv 'keeper i equiv lhs rhs (car tail)))
                 ((and (quotep lhs) ; thus rhs is a non-quotep
                       (equiv-hittable-in-some-other-lit equiv rhs i cl 0 ens wrld))
                  (mv 'keeper i equiv rhs lhs (car tail)))
                 (t (find-trivial-equivalence1
                     not-just-quotep-flg
                     (cdr tail) (1+ i) cl ens wrld avoid-lst)))))
        (t (find-trivial-equivalence1
            not-just-quotep-flg
            (cdr tail) (1+ i) cl ens wrld avoid-lst))))

(defun find-trivial-equivalence (not-just-quotep-flg cl ens wrld avoid-lst)

; We look for a literal of cl of the form (not (equiv lhs rhs)) where
; either of two conditions apply.
;    name          condition
; disposable:    lhs is a variable, all occurrences of lhs in cl
;                 are equiv-hittable, and rhs does not contain lhs.
; keeper:        lhs is any non-quotep and rhs is a quotep and lhs has
;                 an equiv-hittable occurrence in some other literal
;                 of the clause

; Note that in the keeper case, there may be some non-hittable occurrences of
; lhs in the clause.  In addition, we accept commuted version of the equivalence
; and we treat each variablep literal, var, as the trivial equivalence (not
; (equal var 'NIL)).

; If we find such a literal we return 6 values: the name of the condition
; detected, the location i of the literal, equiv, lhs, rhs and the literal
; itself.  Otherwise we return 6 nils.

; The driver of this function, remove-trivial-equivalences, will substitute rhs
; for lhs throughout cl, possibly delete the literal, and then call us again to
; look for the next trivial equivalence.  This raises a problem.  If the driver
; doesn't delete the literal, then we will return the same one again and loop.
; So the driver supplies us with a list of literals to avoid, avoid-lst, and
; will put onto it each of the literals that has been used but not deleted.

; So consider a clause like
; (implies (and (equal (foo b) 'evg)   [1]
;               (equal a b))           [2]
;          (p (foo a) (foo b)))

; The first trivial equivalence is [1].  The driver substitutes 'evg
; for (foo b) but doesn't delete the literal.  So we get:
; (implies (and (equal (foo b) 'evg)   [1]
;               (equal a b))           [2]
;          (p (foo a) 'evg))
; and the admonition against using (equal (foo b) 'evg).  But now we see
; [2] and the driver substitutes a for b (because a is smaller) and deletes
; [2].  So we get:
; (implies (equal (foo a) 'evg)        [1]
;          (p (foo a) 'evg))
; and the old admonition against using (equal (foo b) 'evg).  Here we find [1]
; ``again'' because it is no longer on the list of things to avoid.  Indeed, we
; can even use it to good effect.  Of course, once it is used both it and the
; old avoided literal are to be avoided.

; So can this loop?  No.  Every substitution reduces term-order.

  (find-trivial-equivalence1 not-just-quotep-flg cl 0 cl ens wrld avoid-lst))

(defun add-literal-and-pt1 (cl-tail pt cl pt-lst)

; Imagine that lit is a literal with pt as its parent tree.  Cl is a clause and
; the parent tree of each literal is given by the corresponding element of
; pt-lst.  We were about to add lit to cl when we noticed that lit (possibly
; commuted) is already an element of cl, namely the one in the car of cl-tail,
; which is a tail of cl.  Thus, we wish to update pt-lst so that the
; corresponding parent tree in the new pt-lst includes pt.

  (cond
   ((null cl)
    (er hard 'add-literal-and-pt1 "We failed to find the literal!"))
   ((equal cl-tail cl)
    (cond ((null (car pt-lst)) (cons pt (cdr pt-lst)))
          (t (cons (cons pt (car pt-lst)) (cdr pt-lst)))))
   (t (cons (car pt-lst)
            (add-literal-and-pt1 cl-tail pt (cdr cl) (cdr pt-lst))))))

(defun add-literal-and-pt (lit pt cl pt-lst ttree)

; Very roughly speaking, this is just:
; (mv (add-literal lit cl nil)      ; add lit to clause cl
;     (cons pt pt-lst)              ; add lit's parent ttree to pt-lst
;     ttree)                        ; and pass up the ttree
; But it is complicated by the fact that the add-literal might not actually
; cons lit onto cl but reduce the clause to {t} or merge the literal with
; another.  If that happened and we had actually used the code above, then the
; pt-lst returned would no longer be in 1:1 correspondence with the new
; clause.

  (cond
   ((quotep lit)
    (cond ((equal lit *nil*) (mv cl pt-lst ttree))
          (t (mv *true-clause* nil ttree))))
   ((or (equal cl *true-clause*)
        (member-complement-term lit cl))
    (mv *true-clause* nil ttree))
   (t (let ((cl0 (member-term lit cl)))
        (cond
         ((null cl0)
          (mv (cons lit cl)
              (cons pt pt-lst)
              ttree))
         ((null pt)
          (mv cl pt-lst ttree))
         (t (mv cl
                (add-literal-and-pt1 cl0 pt cl pt-lst)
                ttree)))))))

(defun add-binding-to-tag-tree (var term ttree)

; Note that var need not be a variable; see the call in fertilize-clause1.

  (let* ((tag 'binding-lst)
         (binding (cons var term))
         (old (tagged-object tag ttree)))
    (cond (old (extend-tag-tree tag
                                (list (cons binding old))
                                (remove-tag-from-tag-tree! tag ttree)))
          (t (extend-tag-tree tag
                              (list (cons binding nil))
                              ttree)))))

(defun subst-equiv-and-maybe-delete-lit
  (equiv new old n cl i pt-lst delete-flg ens wrld state ttree)

; Substitutes new for old (which are equiv) in every literal of cl (maintaining
; iff) except the nth one.  The nth literal is deleted if delete-flg is t and
; is skipped but included in the if delete-flg is nil.  Pt-lst is in 1:1
; correspondence with cl.  We return the new clause, a new pt-lst and a ttree
; recording the congruence and executable-counterpart rules used.  It is
; possible that this fn will return a clause dramatically shorter than cl,
; because lits may evaporate upon evaluation or merge with other literals.  We
; may also prove the clause.

  (cond
   ((null cl) (mv nil nil ttree))
   ((int= n i)
    (mv-let (cl1 pt-lst1 ttree)
            (subst-equiv-and-maybe-delete-lit equiv new old n
                                              (cdr cl) (1+ i)
                                              (cdr pt-lst)
                                              delete-flg
                                              ens wrld state ttree)
            (cond
             (delete-flg (mv cl1
                             pt-lst1
                             (add-binding-to-tag-tree old new ttree)))
             (t (add-literal-and-pt (car cl) (car pt-lst)
                                    cl1 pt-lst1 ttree)))))
   ((dumb-occur old (car cl))
    (mv-let (hitp lit ttree)
            (subst-equiv-expr equiv new old
                              *geneqv-iff*
                              (car cl)
                              ens wrld state ttree)
            (declare (ignore hitp))

; Hitp may be nil even though old occurs in the lit, because it may not occur
; in an equiv-hittable place.  But we don't really care whether it's t or nil.

            (mv-let (cl1 pt-lst1 ttree)
                    (subst-equiv-and-maybe-delete-lit equiv new old n
                                                      (cdr cl) (1+ i)
                                                      (cdr pt-lst)
                                                      delete-flg
                                                      ens wrld state ttree)
                    (add-literal-and-pt lit (car pt-lst)
                                        cl1 pt-lst1 ttree))))
   (t (mv-let (cl1 pt-lst1 ttree)
              (subst-equiv-and-maybe-delete-lit equiv new old n
                                                (cdr cl) (1+ i)
                                                (cdr pt-lst)
                                                delete-flg
                                                ens wrld state ttree)
              (add-literal-and-pt (car cl) (car pt-lst)
                                  cl1 pt-lst1 ttree)))))

(defstub remove-trivial-equivalences-enabled-p () t)
(defattach remove-trivial-equivalences-enabled-p constant-t-function-arity-0)

(defun remove-trivial-equivalences-rec
  (cl pt-lst remove-flg ens wrld state ttree hitp avoid-lst)

; This function looks for two kinds of equivalence hypotheses in cl and uses
; them to do substitutions.  By "equivalence hypothesis" we mean a literal of
; the form (not (equiv lhs rhs)) that is not on avoid-lst.  The two kinds are
; called "trivial var equivalences" and "trivial quote equivalences."  If we
; find an equation of the first sort we substitute one side for the other and
; delete the equivalence (provided remove-flg is t).  If we find an equation of
; the second sort, we substitute one side for the other but do not delete the
; equivalence.  See find-trivial-equivalence for more details, especially
; concerning avoid-lst.  Hitp is an accumulator that records whether we did
; anything.

; Pt-lst is a list of parent trees in 1:1 correspondence with cl.  Since we
; return a modified version of cl in which some literals may have been deleted,
; we must also return a modified version of pt-lst giving the parent trees for
; the surviving literals.

; The justification for deleting (not (equiv var term)) when var occurs nowhere
; in the clause is (a) it is always sound to throw out a literal, and (b) it is
; heuristically safe here because var is isolated and equiv is reflexive: if
; (implies (equiv var term) p) is a theorem so is p because (equiv term term).

; We return four values:  hitp, cl, pt-lst and ttree.

; No Change Loser.

; Note: We have briefly considered the question of whether we should do
; anything with hypotheses of the form (equiv var term), where var does not
; occur in term, and some (but not all) occurrences of var are equiv-hittable.
; Perhaps we should hit those occurrences but not delete the hypothesis?  We
; think not.  After all, if term is larger than var (as it generally is here),
; why should we replace some occurrences of the small term by the big one?
; They will just be zapped back by rewrite-solidify if the hyp is not deleted.
; However, an exception to this rule is if we see a hypothesis of the form
; (equal lhs 'const) where not every occurrence of lhs is equiv-hittable.
; Such a hyp is not a trivial var equivalence, even if lhs is a variable,
; because of the un-hittable occurrence of var.  But we do count it as a
; trivial quote equivalence and hit var where we can (but don't delete the
; hypothesis).

  (mv-let (condition lit-position equiv lhs rhs lit)
    (find-trivial-equivalence remove-flg cl ens wrld avoid-lst)
    (cond
     (lit-position
      (mv-let (new-cl new-pt-lst ttree)
              (subst-equiv-and-maybe-delete-lit
               equiv rhs lhs lit-position cl 0 pt-lst
               (and remove-flg (eq condition 'disposable))
               ens wrld state ttree)
              (remove-trivial-equivalences-rec new-cl new-pt-lst remove-flg
                                               ens wrld state
                                               ttree t
                                               (cons lit avoid-lst))))
     (t (mv hitp cl pt-lst ttree)))))

(defun remove-trivial-equivalences (cl pt-lst remove-flg ens wrld state ttree)
  (cond
   ((remove-trivial-equivalences-enabled-p)
    (remove-trivial-equivalences-rec cl pt-lst remove-flg ens wrld state ttree
                                     nil nil))
   (t (mv nil cl pt-lst ttree))))

; In a break with nqthm, we implement a really trivial theorem prover which
; gets the first shot at any conjecture we have to prove.  The idea is to build
; into this function whatever is necessary for boot-strap to work.  It will
; also speed up the acceptance of commonly used recursive schemas.  The idea is
; simply to recognize instances of a small number of known truths, stored in
; clausal form on the world global 'built-in-clauses, whose initial value is
; set up below.

; To be predictable, we have to include commutative variants of the
; recognized clauses.  In addition, because subsumption works by first
; trying to find (an instance of) the first literal and then trying to
; find the rest, it is faster to put the most unusual literal first in
; each built-in clause.

; The following is now defined in rewrite.lisp.

; (defrec built-in-clause ((nume . all-fnnames) clause . rune) t)

; Note:  The :all-fnnames field must be set as it would be by
; all-fnnames-subsumer.  This setting cannot be done automatically because we
; do not know the initial world until we have set up the built-in-clauses.  But
; we do check, with chk-initial-built-in-clauses which is called and reported
; in check-built-in-constants, that the setting below is correct for the actual
; initial world.  When adding new records, it is best to use
; (all-fnnames-subsumer cl (w state)) to get the :all-fnnames field below.

;; Historical Comment from Ruben Gamboa:
;; I changed the clauses about e0-ord-< [v2-8 and beyond: o<] reducing on
;; complex-rationalps to reducing on any complexp.

(defconst *initial-built-in-clauses*
  (list

; acl2-count is an ordinal.

   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o-p (acl2-count x)))
         :all-fnnames '(o-p acl2-count))

; Car and cdr decrease on consps.
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (car x))
                       (acl2-count x))
                   (not (consp x)))
         :all-fnnames '(acl2-count car o< consp not))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (cdr x))
                       (acl2-count x))
                   (not (consp x)))
         :all-fnnames '(acl2-count cdr o< consp not))

; Car and cdr decrease on non-atoms.
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (car x))
                       (acl2-count x))
                   (atom x))
         :all-fnnames '(acl2-count car o< atom))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (cdr x))
                       (acl2-count x))
                   (atom x))
         :all-fnnames '(acl2-count cdr o< atom))

; Car and cdr decrease on non-endps.
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (car x))
                       (acl2-count x))
                   (endp x))
         :all-fnnames '(acl2-count car o< endp))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (cdr x))
                       (acl2-count x))
                   (endp x))
         :all-fnnames '(acl2-count cdr o< endp))

; 1- decreases on positives and on non-negatives other than 0.  But we
; represent (1- x) three different ways: (1- x), (+ x -1) and (+ -1 x).  And to
; say "other than 0" we can use (not (zp x)) or (integerp x) together
; with the negations of any one of (equal x 0), (= x 0) or (= 0 x).  The
; symmetry of equal is built into unification, but not so =, so we have
; two versions for each =.

; However, in Version 1.8 we made 1- a macro.  Therefore, we have deleted the
; two built-in-clauses for 1-.  If we ever make 1- a function again, we should
; add them again.

   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (binary-+ x '-1))
                       (acl2-count x))
                   (zp x))
         :all-fnnames '(acl2-count o< zp))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (binary-+ '-1 x))
                       (acl2-count x))
                   (zp x))
         :all-fnnames '(acl2-count o< zp))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (binary-+ x '-1))
                       (acl2-count x))
                   (not (integerp x))
                   (not (< '0 x)))
         :all-fnnames '(acl2-count o< integerp < not))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (binary-+ x '-1))
                       (acl2-count x))
                   (not (integerp x))
                   (< x '0)
                   (= x '0))
         :all-fnnames '(acl2-count o< integerp not < =))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (binary-+ x '-1))
                       (acl2-count x))
                   (not (integerp x))
                   (< x '0)
                   (= '0 x))
         :all-fnnames '(acl2-count o< integerp not < =))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (binary-+ x '-1))
                       (acl2-count x))
                   (not (integerp x))
                   (< x '0)
                   (equal x '0))
         :all-fnnames '(acl2-count o< integerp not < equal))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (binary-+ '-1 x))
                       (acl2-count x))
                   (not (integerp x))
                   (not (< '0 x)))
         :all-fnnames '(acl2-count o< integerp < not))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (binary-+ '-1 x))
                       (acl2-count x))
                   (not (integerp x))
                   (< x '0)
                   (= x '0))
         :all-fnnames '(acl2-count o< integerp not < =))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (binary-+ '-1 x))
                       (acl2-count x))
                   (not (integerp x))
                   (< x '0)
                   (= '0 x))
         :all-fnnames '(acl2-count o< integerp not < =))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (binary-+ '-1 x))
                       (acl2-count x))
                   (not (integerp x))
                   (< x '0)
                   (equal x '0))
         :all-fnnames '(acl2-count o< integerp not < equal))

; Realpart and imagpart decrease on complexps.
   #+:non-standard-analysis
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (realpart x))
                       (acl2-count x))
                   (not (complexp x)))
         :all-fnnames
         '(acl2-count realpart o< complexp not))
   #-:non-standard-analysis
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (realpart x))
                       (acl2-count x))
                   (not (complex-rationalp x)))
         :all-fnnames
         '(acl2-count realpart o< complex-rationalp not))
   #+:non-standard-analysis
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (imagpart x))
                       (acl2-count x))
                   (not (complexp x)))
         :all-fnnames
         '(acl2-count imagpart o< complexp not))
   #-:non-standard-analysis
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (imagpart x))
                       (acl2-count x))
                   (not (complex-rationalp x)))
         :all-fnnames
         '(acl2-count imagpart o< complex-rationalp not))

; Finally, cdr decreases on non-nil true-listps, but we can say
; "non-nil" as (eq x nil), (eq nil x), (null x) or (equal x nil)
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (cdr x))
                       (acl2-count x))
                   (not (true-listp x))
                   (eq x 'nil))
         :all-fnnames '(acl2-count cdr o< true-listp not eq))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (cdr x))
                       (acl2-count x))
                   (not (true-listp x))
                   (null x))
         :all-fnnames '(acl2-count cdr o< true-listp not null))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (cdr x))
                       (acl2-count x))
                   (not (true-listp x))
                   (eq 'nil x))
         :all-fnnames '(acl2-count cdr o< true-listp not eq))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2-count (cdr x))
                       (acl2-count x))
                   (not (true-listp x))
                   (equal x 'nil))
         :all-fnnames '(acl2-count cdr o< true-listp not equal))))

(defun built-in-clausep2 (bic-lst cl fns ens)

; Ens is either nil or an enabled structure.  If ens is nil, then we consider
; only the rules specified by *initial-built-in-clauses* to be enabled.

  (cond ((null bic-lst) nil)
        ((and (let ((nume (access built-in-clause (car bic-lst) :nume)))
                (if (null ens)
                    (null nume)
                  (enabled-numep nume ens)))
              (subsetp-eq (access built-in-clause (car bic-lst) :all-fnnames)
                          fns)
              (eq (subsumes *init-subsumes-count*
                            (access built-in-clause (car bic-lst) :clause)
                            cl nil)
                  t))
         (access built-in-clause (car bic-lst) :rune))
        (t (built-in-clausep2 (cdr bic-lst) cl fns ens))))

(defun built-in-clausep1 (bic-alist cl fns ens)

; Ens is either nil or an enabled structure.  If ens is nil, then we consider
; only the rules specified by *initial-built-in-clauses* to be enabled.

; Bic-alist is the alist of built-in clauses, organized via top fnname.  Cl is
; a clause and fns is the all-fnnames-lst of cl.  This function is akin to
; some-member-subsumes in the sense of some built-in clause subsumes cl.  We
; only try subsumption on enabled built-in clauses whose :all-fnnames field is
; a subset of fns.  We return the rune of the subsuming clause, or nil.

  (cond ((null bic-alist) nil)
        ((or (null (caar bic-alist))
             (member-eq (caar bic-alist) fns))

; All the built-in clauses in this pot have the same top-fnname and that name
; occurs in cl.  So these guys are all candidate subsumers.  Note:  if (car
; bic-alist) is null then this is the special pot into which we have put all
; the built-in clauses that have no "function symbols" in them, as computed by
; all-fnnames-subsumer.  I don't see how this can happen, but if it does we're
; prepared!

         (or (built-in-clausep2 (cdr (car bic-alist)) cl fns ens)
             (built-in-clausep1 (cdr bic-alist) cl fns ens)))
        (t (built-in-clausep1 (cdr bic-alist) cl fns ens))))

(defun possible-trivial-clause-p (cl)

; Warning: Keep this list below of function names in sync with those in
; tautologyp; see comment below.

  (if (null cl)
      nil
    (mv-let (not-flg atm)
            (strip-not (car cl))
            (declare (ignore not-flg))

; Keep the following list of function names in sync with those in tautologyp.
; It should be, in fact, just the list in tautologyp plus IF and NOT.  Note
; that although tautologyp does not expand NOT, if-tautologyp (and hence
; tautologyp) knows about NOT, so we look for it here.

            (or (ffnnamesp '(if not
                             iff
                             ;not
                             implies eq atom eql = /= null

; If we ever make 1+ and 1- functions again, they should go back on this list.

                             zerop plusp minusp listp mv-list cons-with-hint
                             return-last wormhole-eval force case-split
                             double-rewrite)
                           atm)
                (possible-trivial-clause-p (cdr cl))))))

(defun trivial-clause-p (cl wrld)
  (or (member-equal *t* cl)
      (and (possible-trivial-clause-p cl)
           (tautologyp (disjoin cl) wrld))))

(defun built-in-clausep (caller cl ens match-free-override wrld state)

; Ens is either nil or an enabled structure.  If ens is nil, then we consider
; only the rules specified by *initial-built-in-clauses* to be enabled.

; We return two results.  The first indicates whether cl is a ``built
; in clause,'' i.e., a known truth.  The second is the supporting
; ttree (or nil).  This ttree is guaranteed to be assumption-free.

; Caller is just a token that indicates what function (possibly indirectly) is
; responsible for calling built-in-clausep.

; Once upon a time, this function used force-flg = t in the
; type-alist-clause call below.  Thus, the callers of this function
; anticipate splitting.  We have backed off force-flg = t here because
; it seems likely to cause loops due to assuming literals that are
; explicitly denied later in the clause (see the warning in
; type-alist-clause).  But this condition has never been witnessed and
; the change was made without significant testing of the force-flg = t
; case.  However, the callers of this function do not now anticipate
; the presence of 'assumption tags in the ttree.  Thus, if you make
; this function force or case-split, you must change its callers!

; Starting with Version_2.7, this function uses forward-chaining.  This idea
; arose when changing translate-declaration-to-guard to output calls of
; signed-byte-p, unsigned-byte-p, and integer-range-p.  Suddenly some guards
; proofs needed to be done that formerly were handled by built-in-clausep.  But
; that problem is reduced or eliminated when we forward-chain and have suitable
; forward-chaining rules from those new predicates.

; When this function is allowed to return t, it is also allowed to return nil.
; In particular, the limit on one-way-unify1 calls in the call of subsumes in
; built-in-clausep2 can cause this predicate to fail.

  (let ((rune (built-in-clausep1 (global-val 'built-in-clauses wrld)
                                 cl
                                 (all-fnnames-lst cl)
                                 ens)))
    (cond
     (rune (mv t (push-lemma rune nil)))
     ((null ens) ; then skip forward-chaining
      (cond ((trivial-clause-p cl wrld) (mv t nil))
            (t (mv nil nil))))
     (t (mv-let (contradictionp type-alist ttree)
                (forward-chain-top caller
                                   cl
                                   nil ; pts
                                   nil ; ok-to-force
                                   nil ; do-not-reconsiderp
                                   wrld
                                   ens
                                   match-free-override
                                   state)
                (declare (ignore type-alist))
                (cond ((not contradictionp)

; At one time we checked trivial-clause-p before doing anything else.  But Sol
; Swords sent an example defun whose body was a big if-then-else term that
; generated 42 guard obligations, some of which were very expensive to check
; with trivial-clause-p, but all of which were very quickly found contradictory
; by forward-chain.

                       (cond ((trivial-clause-p cl wrld) (mv t nil))
                             (t (mv nil nil))))
                      ((tagged-objectsp 'assumption ttree)
                       (mv (er hard 'built-in-clausep
                               "It was thought that the forward-chain call in ~
                                this function could not produce an ~
                                'assumption but it did!  Try running ~
                                forward-chain on ~X01 with ~
                                match-free-override = ~x2.  The ens and wrld ~
                                used here must be recovered by other means if ~
                                (ens state) and (w state) don't work."
                               (kwote cl)
                               nil
                               (kwote match-free-override))
                           nil))
                      (t (mv t ttree))))))))

(defun crunch-clause-segments1 (seg1 pts1 cl pts)

; This function reverses seg1 and appends it to cl, and does the analogous
; thing to pts1 and pts.  However, if a literal in seg1 already occurs in
; cl, it is merged into that literal and its pt is consed onto the
; pt of the literal in cl.

; Note: It is a mystery how the opportunity for this merging should arise.  It
; appears to be impossible because seg1 was rewritten under the assumption of
; the falsity of the literals in cl and hence any such literal of seg1 would
; have evaporated.  Nevertheless, in the days before we used pts this function
; had been modified from the rev-append approach to a careful use of
; member-equal and hence duplicate literals do, apparently, arise.

; Note: In normal use, the first literal in cl at the beginning will be the
; marker literal dealt with by crunch-clause-segments2 and
; crunch-clause-segments.  Observe that the pts of literals occurring after
; that marker in cl are completely irrelevant to the behavior of
; crunch-clause-segment, even though we are here careful to move pts from pts1
; into that section of pts when merging occurs.  They are irrelevant because
; crunch-clause-segments2 just collects the pts up to the marker.  It might
; still be important for us to catch merges, since it is possible that two
; literals within seg1 itself will merge and thus we will create a consp pt for
; that literal and that consp pt will be collected by crunch-clause-segments2
; and find its way into the main computation.  Stranger things have happened in
; this code!

  (cond ((null seg1) (mv cl pts))
        (t (mv-let (cl pts ttree)
                   (add-literal-and-pt (car seg1) (car pts1) cl pts nil)

; Add-literal-and-pt just passes its last argument through as the ttree and we
; simply ignore the resulting nil.  This is just an easy way to cons the first
; literal of seg1 onto cl and the first pt of pts1 onto pts -- provided the
; literal doesn't already occur in cl -- and to merge the pt into the
; appropriate element of pts if it does.

                   (declare (ignore ttree))
                   (crunch-clause-segments1 (cdr seg1) (cdr pts1) cl pts)))))

(defun crunch-clause-segments2 (cl pts seg1 pts1)

; See crunch-clause-segments.

  (cond ((null cl) (mv seg1 pts1 nil))
        ((and (consp (car cl))
              (eq (ffn-symb (car cl)) 'car)
              (eq (fargn (car cl) 1) :crunch-clause-segments-marker))
         (mv seg1 pts1 (cdr cl)))
        (t (crunch-clause-segments2 (cdr cl)
                                    (cdr pts)
                                    (cons (car cl) seg1)
                                    (cons (car pts) pts1)))))

(defun crunch-clause-segments (seg1 pts1 seg2 ens wrld state ttree)

; This function is a special purpose subroutine of rewrite-clause.  Seg1 and
; seg2 are just lists of literals.  Pts1 is in weak 1:1 correspondence with
; seg1 and enumerates the parent trees of the corresponding literals of seg1.
; Consider the clause obtained by appending these two segments.

; {lit4 ... lit7 lit1' ... lit2' lit3a ... lit3z}    ; cl

; |  <- seg1 -> | <- seg2 ->                   |

;  unrewritten  |  rewritten

; Context: The rewriter is sweeping through this clause, rewriting each literal
; and assembling a new clause.  It has rewritten none of the seg1 literals and
; all of the seg2 literals.  It has just rewritten some literal called lit3.
; After clausifying the result (and getting in this case lit3a ... lit3z) it is
; about to start rewriting the first literal of seg1, lit4.  It has already
; rewritten lit1'...lit2'.  The rewriter actually keeps the unrewritten part of
; the clause (seg1) separate from the rewritten part (seg2) so that it knows
; when it is done.  In the old days, it would just proceed to rewrite the first
; literal of seg1.

; But we are trying something new.  Suppose lit3 was something like (not
; (member x '(...))).  Then we will get lots of segs, each of the form (equal x
; '...).  We are trying to optimize our handling of this by actually stuffing
; the constant into the clause and running any terms we can.  We do this in
; what we think is a very elegant way: We actually create cl and call
; remove-trivial-equivalences on it.  Then we recover the two parts,
; unrewritten and rewritten.  The trick is how we figure out which is which.
; We put a marker literal into the clause, after seg1 and before
; seg2.  Remove-trivial-equivalences may do a lot of literal evaluation
; and deletion.  But then we find the marker literal and consider everything to
; its left unrewritten and everything else rewritten.

; We return three values: The unrewritten part of cl, the rewritten part of cl,
; and an extension of ttree.

  (let ((marker '(car :crunch-clause-segments-marker)))
    (mv-let (cl pts)
            (crunch-clause-segments1 seg1 pts1 (cons marker seg2) nil)
            (mv-let (hitp cl pts ttree)
                    (remove-trivial-equivalences cl pts nil ;;; see Note
                                                 ens wrld state ttree)

; Note: In the call of remove-trivial-equivalences above we use remove-flg =
; nil.  At one time, we used remove-flg = t, thinking that our cl here was the
; entire problem and thus we could delete the literal after using it.  However,
; because of the fc-pair-lst and the simplify-clause-pot-lst -- both of which
; may contain terms that mention the "eliminated" variable and both of which
; may introduce such terms into the clause later -- we believe it best to keep
; the equality until we are at the top of the waterfall again.

                    (cond
                     ((null hitp)
                      (mv seg1 pts1 seg2 ttree))
                     (t (mv-let (seg1 pts1 seg2)
                                (crunch-clause-segments2 cl pts nil nil)
                                (mv seg1 pts1 seg2 ttree))))))))

; We now develop code to deal with the unrewritten assumptions generated by
; rewriting a literal of a clause.  We would like to implement the illusion
; that all 'assumptions produced while rewriting a literal have actually been
; rewritten.  We achieve that by stripping such assumptions out of the returned
; ttree, rewriting them, and putting them back.  See
; resume-suspended-assumption-rewriting1, below, for the details.

(defun strip-non-rewrittenp-assumptions1 (recs acc)

; See strip-non-rewrittenp-assumptions.  We move non-rewritten assumptions from
; recs to acc to obtain recs' and acc, and return (mv recs' acc').

  (cond ((endp recs) (mv nil acc))
        (t (mv-let (rest acc)
                   (strip-non-rewrittenp-assumptions1 (cdr recs) acc)
                   (cond ((access assumption (car recs) :rewrittenp)
                          (cond (acc ; a record was removed: (cdr recs) != rest
                                 (mv (cons (car recs) rest)
                                     acc))
                                (t (mv recs nil))))
                         (t (mv rest (cons (car recs) acc))))))))

(defun strip-non-rewrittenp-assumptions (ttree)

; Strip out all 'assumption records that have :rewrittenp nil and accumulate
; them into ans.  Return (mv ttree' ans'), where ttree' is the result of
; removing the records in ans from ttree.

  (let ((recs (tagged-objects 'assumption ttree)))
    (cond (recs
           (let ((ttree0 (remove-tag-from-tag-tree! 'assumption ttree)))
             (mv-let (rewritten unrewritten)
                     (strip-non-rewrittenp-assumptions1 recs nil)
                     (mv (cond (rewritten
                                (extend-tag-tree 'assumption rewritten ttree0))
                               (t ttree0))
                         unrewritten))))
          (t (mv ttree nil)))))

(defun assumnote-list-to-token-list (assumnote-list)
  (if (null assumnote-list)
      nil
    (cons (access assumnote (car assumnote-list) :rune)
          (assumnote-list-to-token-list (cdr assumnote-list)))))

(defun resume-suspended-assumption-rewriting1
  (assumptions ancestors gstack simplify-clause-pot-lst rcnst wrld state
               step-limit ttree)

; A simple view of this function then is that it rewrites each assumption in
; assumptions and puts the rewritten version into ttree, reporting the first
; false assumption if finds.

; Assumptions is a list of unrewritten assumptions that were generated while
; rewriting with the rewrite arguments given to this function.  We return two
; results, (mv bad-ass ttree), where bad-ass is either nil or an assumption
; whose :term can be rewritten to false in the current context and ttree is a
; ttree extending the input tree, justifying all the rewriting done (including
; that to false, if bad-ass), containing 'assumption tags for all the
; assumptions in assumptions, and containing no unrewritten assumptions
; (assuming the initial ttree contained no unrewritten assumptions).

; The complication is that rewriting an assumption generates assumptions which
; we must also rewrite.  The process could in principle loop if rewriting an
; assumption can re-generate the assumption.  We break this potential loop via
; the use of ancestors.  We imagine we are just backchaining.

; It is perhaps worth reminding the reader that these assumptions cannot be
; rewritten before they are forced because they come from type-set, which is
; defined before the rewriter is defined.  Thus, we are really implementing a
; kind of delayed mutual recursion: type-set is reporting some assumptions it
; would like rewritten and we are doing it.

  (cond
   ((endp assumptions) (mv step-limit nil ttree))
   (t (let* ((assn (car assumptions))
             (term (access assumption assn :term)))
        (mv-let
         (on-ancestorsp assumed-true)
         (ancestors-check term ancestors
                          (assumnote-list-to-token-list
                           (access assumption assn :assumnotes)))
         (cond
          (on-ancestorsp

; If the assumption's term is assumed true, we may omit it from the answer.  If
; it is not assumed-true, we don't know that it is false: it might merely be
; worse than some ancestor.  We therefore just move the now rewritten
; assumption into the ttree and go on.  Once upon a time we considered
; aborting, reporting assn as a bad-ass.  Observe that if the complement of
; term is on ancestors, then term is being assumed nil (because (not term) is
; assumed true).  Doesn't that mean we could rewrite term to nil?  No.  All we
; really know is that term is impossible to prove by rewriting using whatever
; lemmas we did this time.  Term might be provable.  Consider the fact that
; the user could have proved (implies term term) for any term, even a provable
; one.  Then in trying to prove term we'd assume it false by putting (not term)
; on ancestors and backchain to term, which would lead us here, with the
; complement of term on ancestors.  That doesn't mean term can't be proved!

           (resume-suspended-assumption-rewriting1
              (cdr assumptions)
              ancestors gstack simplify-clause-pot-lst rcnst
              wrld state step-limit
              (if assumed-true
                  ttree
                (add-to-tag-tree 'assumption
                                 (change assumption assn
                                         :rewrittenp term)
                                 ttree))))
          (t

; We are about to rewrite term, just as in relieve-hyp, and so we add its
; negation to ancestors.  This is equivalent to assuming term false.

           (let ((new-ancestors
                  (push-ancestor (dumb-negate-lit term)
                                 (assumnote-list-to-token-list
                                  (access assumption assn :assumnotes))
                                 ancestors
                                 nil)))
             (mv-let
              (not-flg atm)
              (strip-not term)
              (sl-let
               (val ttree1)
               (rewrite-entry (rewrite atm nil 'forced-assumption)
                              :rdepth (rewrite-stack-limit wrld)
                              :step-limit step-limit
                              :type-alist (access assumption assn :type-alist)
                              :obj '?
                              :geneqv *geneqv-iff*
                              :pequiv-info nil
                              :wrld wrld
                              :fnstack nil
                              :ancestors new-ancestors
                              :backchain-limit (access rewrite-constant rcnst
                                                       :backchain-limit-rw)
                              :simplify-clause-pot-lst simplify-clause-pot-lst
                              :rcnst rcnst
                              :gstack gstack
                              :ttree nil)
               (let ((val (if not-flg (dumb-negate-lit val) val)))
                 (cond
                  ((equal val *nil*)

; If term rewrote to nil, we return assn as a bad assumption.  We
; assume the proof attempt is doomed.  We accumulate into ttree the
; ttree supporting the final rewrite to nil.  This is a little odd.
; The bad-ass returned is the unrewritten assumption generated by
; (force term) or (case-split term).  But the ttree returned may
; contain work done on other forces as well as the work done to show
; that term reduces to nil, even though we are returning term, not
; nil.

                   (mv step-limit assn (cons-tag-trees ttree1 ttree)))
                  (t

; If term rewrote to non-nil, we must process the unrewritten assumptions in
; the ttree, ttree1, produced by rewriting term.  We do that with a separate
; recursive call of this function, because we must pass in the new-ancestors so
; that we don't loop.  Think of us as having assumed term false, rewritten it
; while making certain assumptions, and now -- still in that context of having
; assumed it false -- we will work on those assumptions.

                   (mv-let
                    (ttree1 assumptions1)
                    (strip-non-rewrittenp-assumptions ttree1)

; Observe that if ttree1 contains any assumptions, they are of the rewrittenp t
; variety.  We accumulate ttree1 into our answer ttree.  Unless term rewrote to
; t, we accumulate the rewritten version of assn into our answer.  Note that
; since the :geneqv used above is iff, we can rely on the fact that if val is
; known not to be nil then it is actually t.  Finally, we rewrite all of the
; unrewritten assumptions (assumptions1) generated by rewriting term to val
; accumulate them into our answer as well.

                    (sl-let
                     (bad-ass ttree)
                     (resume-suspended-assumption-rewriting1
                      assumptions1
                      new-ancestors ; the critical difference
                      gstack simplify-clause-pot-lst rcnst
                      wrld state step-limit
                      (cons-tag-trees
                       ttree1
                       (if (equal val *t*)
                           ttree
                           (add-to-tag-tree 'assumption
                                            (change assumption assn
                                                    :term val
                                                    :rewrittenp term)
                                            ttree))))
                     (cond
                      (bad-ass (mv step-limit bad-ass ttree))
                      (t

; Having taken care of assn and all the unrewritten assumptions generated when
; we rewrote it, we now do the rest of assumptions.

                       (resume-suspended-assumption-rewriting1
                        (cdr assumptions)
                        ancestors gstack simplify-clause-pot-lst rcnst
                        wrld state step-limit
                        ttree))))))))))))))))))

(defun resume-suspended-assumption-rewriting
  (ttree ancestors gstack simplify-clause-pot-lst rcnst wrld state step-limit)

; We copy ttree and rewrite all the non-rewrittenp assumptions in it, deleting
; any thus established.  We return (mv bad-ass ttree'), where bad-ass is either
; nil or an assumption in ttree whose :term can be rewritten to nil.  Ttree' is
; an extension of the result of removing all non-rewrittenp assumptions from
; ttree and then replacing them by their rewritten versions plus the ttrees
; produced by that rewriting.  There are no non-rewrittenp assumptions in
; ttree'.

  (mv-let (ttree assumptions)
          (strip-non-rewrittenp-assumptions ttree)
          (resume-suspended-assumption-rewriting1
           assumptions
           ancestors gstack simplify-clause-pot-lst rcnst wrld state step-limit
           ttree)))

; Essay on Case Limit

; The case-limit component in the case-split-limitations is a number
; used by rewrite-clause to shut down case splitting after a certain
; point is reached.

; The informal heuristic implemented here is ``don't continue to
; rewrite literals once the estimated number of output clauses exceeds
; some limit.''  We call the limit the ``case-limit.''  There are many
; interpretations of this heuristic.  We discuss them here.  In this
; discussion we abstract away from the particulars of given call of
; rewrite-clause and instead consider all the calls of that function
; on the Common Lisp control stack.  Each of those calls can be
; characterized by a picture like this {h1 ... hk ! lit1 ... litn}
; where the hi are already-rewritten terms generated by splitting on
; the literals that we've already rewritten, the ! signifies where we
; are in this case, and the liti are the unrewritten literals from the
; tail of the original clause.  Suppose there are now more than
; case-limit of these cases; we will handle each with the same
; approach.  Here are the approaches that come to mind.  We have
; chosen to implement (1) after some experimentation with (3).

; (0) Stop now and process no further literals.  Return the clause
;     {h1 ... hk lit1 ... litn}.

; The advantage to (0) is that it is the cheapest thing we could do.
; But it dooms us to revisit each of the hi with the rewriter before
; we even look at their combination or their effects on the liti.  The
; other interpretations below all do some work on the liti in hopes
; that we will have less work to do later.

; (1) It is possible that -h1 ... -hk is contradictory, or that -h1
;     ... -hk together with -lit2, ..., -litn, are contradictory.
;     Such contradictions will be found by type-set when we try to
;     assume all of them false in order to rewrite lit1.  So we could
;     proceed to do the type-alist work to set up the ``rewrite'' of
;     each liti, detect the contradiction if it happens, but
;     short-circuit the rewrite at the last minute if no contradiction
;     arises.  In the short-circuit we would just have the rewrite-atm
;     call return liti (i.e., each liti would rewrite to itself).
;     This is actually the simplest change to the code.

; As noted above, if we find a type-set contradiction in (1), we won't
; have to rewrite the hi again for this case.  Otherwise, we will.
; This kind of observation applies to the other ideas below.

; (2) Build the type-alist and actually rewrite each liti while we have
;     all this context in our hands.  If rewriting liti generates an IF-free
;     term (e.g., T or no change or simple normalization), just proceed.
;     But if it generates an IF, pretend we did nothing and rewrite it
;     to itself.

; (3) As (2) above, but if it generates an IF, use the IF without clausifying
;     it.  This has the effect of possibly stripping out of liti all the
;     cases that are precluded by the hi, without generating any more cases.
;     We will eventually see the IFs in this literal again and split them
;     out.

; Once upon a time we implemented a ``creep up to the limit''
; heuristic here: If we have not yet exceeded the case limit but the
; current literal's clausification does exceed the limit, then we left
; that literal in IF form and went on.  We are afraid that when the
; limit is exceeded it is exceeded by some hideous amount, e.g., 2^32
; clauses are produced.  We call such a literal a ``big splitter.''
; The IF form probably tells the user more about what opened than the
; clauses do.  Furthermore, little splitters further on down the
; clause might be allowed to open and may ultimately allow us to
; simplify the big splitter.  This heuristic had to be implemented in
; such a way that the big splitter was eventually split out.  (The
; user might have set the case limit rather low and might be using it
; to introduce cases slowly.)  Our idea was just to allow the split
; when it is the first literal to split.  It eventually will be.  We
; abandoned this creepy idea because it put unsplit big-splitters on
; the type-alist, where they were essentially useless, and then all
; the downstream literals simplified in the empty context, introducing
; many bogus case splits.

(defun helpful-little-ecnt-msg (case-limit ecnt)
  (cond
   ((and (null case-limit)
         (> ecnt 1000))
    (prog2$
     (cw "~%~%Helpful Little Message:  The simplifier is now expected to ~
          produce approximately ~n0 subgoals.  See :DOC ~
          case-split-limitations and see :DOC splitter.~%~%"
         ecnt)
     ecnt))
   (t ecnt)))

(mutual-recursion

(defun rewrite-clause (tail pts bkptr gstack new-clause fc-pair-lst wrld
                            simplify-clause-pot-lst rcnst flg ecnt ans ttree
                            fttree splitp state step-limit)

; In nqthm this function was called SIMPLIFY-CLAUSE1.

; We are to rewrite the literals of the clause cl formed by appending tail to
; new-clause.  We assume rcnst has the correct top-clause and pt and the
; current-clause is the correct clause.  We assume the simplify-clause-pot-lst
; is set up for the current-clause.  We assume fc-pair-lst is a list of pairs
; of the form (concl . ttree) of conclusions derived by forward chaining from
; negations of literals in current-clause.  The ttrees indicate dependence on
; parents (via 'pt tags) and we may use any concl not dependent upon the
; literals contained in the :pt of rcnst (to which we add the current literal's
; pt).  Ecnt is the estimated number of output clauses.  We refine it as we go
; and it is ultimately returned and is the length of ans.  Fttree (``false
; tag-tree'') is either nil or else is a non-nil tag-tree justifying the
; falsity of every literal in new-clause; see the comment in rewrite-atm about
; the third argument returned by that function.  Note that it is always legal
; to return the false clause in place of any other clause, so our use of fttree
; may be viewed as heuristic, i.e., it is clearly sound.

; We return 5 values: a new step-limit; a flag indicating whether anything was
; done; the final ecnt; a set, ans, of clauses whose conjunction implies cl
; under our assumptions; and a ttree that describes what we did.  Our answers
; are accumulated onto flg, ecnt, ans, and ttree as we recur through the
; literals of tail.

; Finally, we comment on parameter splitp, which controls the rw-cache in the
; case that the rw-cache-state is t.  (See the Essay on Rw-cache.)  This
; parameter is true when we are part of a split into two or more clauses, which
; case (if the rw-cache-state is t) we think of the split into children the way
; we think of entering branches of an IF expression, discarding the "any" cache
; since we do not trust its use in a stronger context.  If there is just one
; child, our heuristic is to keep the rw-cache, with the (perhaps bold)
; expectation that because there is no case-split, we can continue to trust its
; full rw-cache.  While this assumption may be bold, it might be true in many
; cases, and we are willing to make it since the default rw-cache-state is
; :atom, not t.

  (cond
   ((null tail)
    (let ((rune
           (built-in-clausep1 (global-val 'built-in-clauses wrld)
                              new-clause
                              (all-fnnames-lst new-clause)
                              (access rewrite-constant rcnst
                                      :current-enabled-structure))))

      (cond
       (rune
        (mv step-limit t (- ecnt 1) ans (push-lemma rune ttree)))
       ((and fttree

; Avoid considering it a "change" to rewrite the empty (false) clause to
; itself.  Note that we already know (null tail) in this context.

             (not (and (null ans)
                       (null new-clause))))
        (mv step-limit t 1
            (list *false-clause*)
            (cons-tag-trees fttree ttree)))
       (t (mv step-limit flg ecnt (cons new-clause ans) ttree)))))
   (t
    (mv-let
     (not-flg atm)
     (strip-not (car tail))
     (let* ((new-pts (cons (car pts)
                           (access rewrite-constant rcnst :pt)))
            (local-rcnst
             (change rewrite-constant rcnst
                     :current-literal
                     (make current-literal
                           :not-flg not-flg
                           :atm atm)
                     :pt
                     new-pts))
            (case-split-limitations (access rewrite-constant rcnst
                                            :case-split-limitations))

; Warning: Keep the following bindings in sync with the definitions of macros
; case-limit and sr-limit.

            (case-limit (cadr case-split-limitations))
            (sr-limit   (car  case-split-limitations)))

; Note that in local-rcnst we declared inactive the polys descending
; from the current lit.

; The use of simplify-clause-pot-lst below is new to Version_2.8.  This
; is in support of type-set using linear arithmetic --- we use the
; simplify-clause-pot-lst when building the type-alist.  Note that we
; also pass in a parent-tree to declare inactive the polys descending
; from the current lit.

       (mv-let
        (contradictionp type-alist ttree0 current-clause)
        (rewrite-clause-type-alist tail
                                   new-clause
                                   fc-pair-lst
                                   local-rcnst
                                   wrld
                                   simplify-clause-pot-lst
                                   new-pts)

; Ttree0 is relevant only if we got a contradiction.

        (cond
         (contradictionp
          (mv step-limit
              t
              (- ecnt 1)
              ans
              (cons-tag-trees ttree0 ttree)))
         (t
          (let ((skip-rewrite-atm (and case-limit
                                       (> ecnt case-limit)))
                (rw-cache-state (access rewrite-constant rcnst
                                        :rw-cache-state)))
            (sl-let
             (val ttree1 fttree1)

; Note: Nqthm used a call of (rewrite atm ...) here, while we now look on the
; type-alist for atm and then rewrite.  See the Nqthm note below.

; Note: Here is our ``short circuit'' implementation of case limit
; interpretation (2).  We just bail out if we have exceeded the case
; limit.

             (if skip-rewrite-atm
                 (mv step-limit
                     atm
                     (add-to-tag-tree! 'case-limit t ttree)
                     nil)
               (pstk
                (rewrite-atm atm not-flg bkptr gstack type-alist wrld
                             simplify-clause-pot-lst local-rcnst
                             current-clause state step-limit
                             (cond ((eq rw-cache-state :atom)
                                    (erase-rw-cache ttree))
                                   ((and (eq rw-cache-state t)
                                         splitp)
                                    (rw-cache-enter-context ttree))
                                   (t ttree)))))
             (let* ((ttree1 (cond (skip-rewrite-atm ttree1)
                                  ((eq rw-cache-state :atom)
                                   (erase-rw-cache ttree1))
                                  ((and (eq rw-cache-state t)
                                        splitp)
                                   (rw-cache-exit-context ttree ttree1))
                                  (t ttree1)))
                    (val (if not-flg
                             (dumb-negate-lit val)
                           val))
                    (branches (pstk
                               (clausify val
                                         (convert-clause-to-assumptions
                                          (cdr tail)
                                          (convert-clause-to-assumptions
                                           new-clause nil))
                                         nil
                                         sr-limit)))
                    (ttree1 (if (and sr-limit
                                     (> (length branches)
                                        sr-limit))
                                (add-to-tag-tree 'sr-limit
                                                 t
                                                 ttree1)
                              ttree1))
                    (action (rewrite-clause-action (car tail) branches))
                    (segs

; Perhaps we can simply use branches below.  But that requires some thought,
; because the form below handles true clauses (including *true-clause*) with
; special care.  This issue arose as we removed old-style-forcing from the
; code.

                     (disjoin-clause-segment-to-clause-set nil branches))
                    (nsegs (length segs)))
               (sl-let
                (bad-ass ttree1)
                (resume-suspended-assumption-rewriting
                 ttree1
                 nil ;ancestors - the fact that this isn't what it was when
;we pushed the assumption could let rewriting go deeper
                 gstack
                 simplify-clause-pot-lst
                 local-rcnst
                 wrld
                 state
                 step-limit)
                (cond
                 (bad-ass

; When we rewrote the current literal of the clause we made an assumption
; that we now know to be false.  We must abandon that rewrite.  We
; act just as though the literal rewrote to itself:  we pretend we have just
; done the rewrite-atm above and obtained atm instead of val.  We just
; reproduce the code, except we don't worry about assumptions.

                  (let* ((val (if not-flg (dumb-negate-lit atm) atm))
                         (branches (pstk
                                    (clausify val
                                              (convert-clause-to-assumptions
                                               (cdr tail)
                                               (convert-clause-to-assumptions
                                                new-clause nil))
                                              nil
                                              sr-limit)))
                         (ttree2 (if (and sr-limit
                                          (> (length branches)
                                             sr-limit))
                                     (add-to-tag-tree 'sr-limit
                                                      t
                                                      ttree)
                                   ttree))
                         (action (rewrite-clause-action (car tail) branches))
                         (segs branches)
                         (nsegs (length segs)))

; For an explanation of the following call of rewrite-clause-lst, see
; the standard call below.  This is just like it, except we are ignoring
; ttree1.  Note that ttree2 is an extension of ttree.

                    (rewrite-clause-lst segs
                                        (1+ bkptr)
                                        gstack
                                        (cdr tail)
                                        (cdr pts)
                                        new-clause
                                        fc-pair-lst
                                        wrld
                                        simplify-clause-pot-lst
                                        (if (eq action 'shown-false)
                                            local-rcnst
                                          rcnst)
                                        (or flg (not (eq action 'no-change)))
                                        (helpful-little-ecnt-msg
                                         case-limit
                                         (+ ecnt -1 nsegs))
                                        ans
                                        ttree2
                                        nil ; literal is not known to be false
                                        (cdr segs) ; splitp
                                        state
                                        step-limit)))

; Here, once upon a time, we implemented the ``creep up on the limit''
; twist of case limit interpretation (3).  Instead of short-circuiting
; above we rewrote the atm.  We either clausified the result or just
; turned it into a singleton clause possibly containing IFs, depending
; on whether we were already above the case-limit.  We had to handle
; ttree1 appropriately to record the case limit restriction.  We then
; continued on to here.

; The following test determines that we're about to exceed the
; case-limit.

;               (and case-limit
;                    (<= ecnt case-limit)
;                    (< case-limit (+ ecnt -1 nsegs))
;                    (< 1 ecnt))

; It says we are currently at or below the case limit but the segs
; generated for this literal would push us over it.  Furthermore, this
; is not the very first literal to produce segs (ecnt exceeds 1).  In
; this case, we ignored segs.  That is, we just put the un-clausified
; val in as a single literal.  We hold ecnt the fixed and show the
; user this rewritten goal in IF form.  Eventually this IF would
; become the first literal that produces segs and the (< 1 ecnt) would
; fail, so we would split it out then.

; But as we've abandoned the whole idea of rewriting after the limit
; has been exceeded, we no longer implement this creepy idea.
; Instead, we just blast past the limit and then shut 'er down.

                 (t

; In the case that there is no bad assumption, then ttree1 is a ttree in which
; all assumptions have been rewritten.

                  (rewrite-clause-lst segs
                                      (1+ bkptr)
                                      gstack
                                      (cdr tail)
                                      (cdr pts)
                                      new-clause
                                      fc-pair-lst
                                      wrld
                                      simplify-clause-pot-lst

; If the current lit rewrote to false, or even if it rewrote at all
; (since critical information may be lost), then we should continue to
; ignore polys and forward-chaining facts that descend from it.  We
; therefore pass to lower level calls the local-rcnst, which has the
; current literal's index in its :pt.  The current-literal in that
; local-rcnst will be reset and the :pt will be extended locally
; there.  If the current lit did not change upon rewrite, then we want
; to restore :pt to what it was at entry, so we pass the original
; rcnst.  One could consider this as (change rewrite-constant rcnst
; :pt ...)  to add to the old rcnst the pt of the literal just
; rewritten.  Before v2-9, we only used local-rcnst when action is
; 'shown-false, which resulted in dropping important information, as
; shown in the following example derived from one provided by Art
; Flatau.  Before the change, the goal ("Goal'") produced was
; (IMPLIES (AND (< 30 N) (<= 30 N)) (FOO N)); after the change, the
; (INTEGERP N) hypothesis was preserved.

; (defstub foo (n) t)
; (defthm natp-fc-2
;   (implies (natp x) (integerp x))
;   :rule-classes :forward-chaining)
; (thm (implies (and (not (or (not (natp n)) (<= n 30)))
;                    (integerp n)
;                    (<= 30 n))
;               (foo n)))

                                      (if (eq action 'no-change)
                                          rcnst
                                        local-rcnst)
                                      (or flg
                                          (not (eq action 'no-change)))

; Prior to this literal, we estimated the number of output clauses to
; be ecnt.  This literal of this clause rewrote to nsegs segments.  So
; now we have ecnt-1+nsegs clauses.  This will be correct if no other
; literal (anywhere on the call stack) splits.

; We could estimate differently.  We could suppose that this literal
; will split nsegs ways every time it occurs in the call stack.
; Essentially we would let the new ecnt be (* ecnt (max 1 nsegs)).
; (Note that if nsegs is 0, we keep ecnt fixed; the lit rewrote to
; nil.)  That estimate will grow faster and probably is an upper bound
; on the actual number that would be created (e.g., some would almost
; certainly be tautologies).  If we used such a method, we would start
; to cut off case splitting earlier, we would get more literals with
; IFs in them, and fewer overall clauses because the estimate would be
; too large and kick in even though some of the previous splitting was
; tautologous.

                                      (helpful-little-ecnt-msg
                                       case-limit
                                       (+ ecnt -1 nsegs))
                                      ans
                                      (if (eq action 'no-change)
                                          (if (eq rw-cache-state :atom)
                                              ttree
                                            (accumulate-rw-cache t
                                                                 ttree1
                                                                 ttree))
                                        ttree1)
                                      (and fttree1
                                           fttree
                                           (cons-tag-trees fttree1 fttree))
                                      (cdr segs) ; splitp
                                      state
                                      step-limit)))))))))))))))

(defun rewrite-clause-lst (segs bkptr gstack cdr-tail cdr-pts new-clause
                                fc-pair-lst wrld simplify-clause-pot-lst rcnst
                                flg ecnt ans ttree fttree splitp state
                                step-limit)

; Fttree is either nil or else is a tag-tree justifying the falsity of every
; literal in segs and every literal in new-clause; see the comment in
; rewrite-atm about the third argument returned by that function.

; Splitp is true when we do not want to trust the "any" cache of ttree; for
; more explanation, see rewrite-clause.

  (cond ((null segs)
         (mv step-limit flg ecnt ans ttree))
        (t
         (sl-let (flg1 ecnt1 ans1 ttree1)
           (rewrite-clause-lst (cdr segs)
                               bkptr
                               gstack
                               cdr-tail
                               cdr-pts
                               new-clause
                               fc-pair-lst
                               wrld
                               simplify-clause-pot-lst
                               rcnst
                               flg
                               ecnt
                               ans
                               ttree
                               fttree
                               splitp
                               state
                               step-limit)
           (mv-let (unrewritten unwritten-pts rewritten ttree2)
                   (crunch-clause-segments
                    cdr-tail
                    cdr-pts
                    (append new-clause
                            (set-difference-equal (car segs)
                                                  new-clause))
                    (access rewrite-constant rcnst
                            :current-enabled-structure)
                    wrld state ttree1)
                   (rewrite-clause unrewritten
                                   unwritten-pts
                                   bkptr
                                   gstack
                                   rewritten
                                   fc-pair-lst
                                   wrld
                                   simplify-clause-pot-lst
                                   rcnst
                                   flg1
                                   ecnt1
                                   ans1
                                   ttree2
                                   fttree
                                   splitp
                                   state
                                   step-limit))))))

)

; After removing trivial equations, simplify-clause must set up
; the context in which the rewriting of the clause is done.  This
; mainly means setting up the simplify-clause-pot-lst.

(defun setup-simplify-clause-pot-lst1 (cl ttrees type-alist rcnst wrld state
                                          step-limit)
  (sl-let (contradictionp simplify-clause-pot-lst)
          (let ((gstack (initial-gstack 'setup-simplify-clause-pot-lst
                                        nil cl)))
            (rewrite-entry
             (add-terms-and-lemmas cl ;term-lst to assume
                                   ttrees ;corresponding tag-trees
                                   nil ;positivep (terms assumed false)
                                   )
             :rdepth (rewrite-stack-limit wrld)
             :step-limit step-limit
             :type-alist type-alist
             :obj nil
             :geneqv nil
             :pequiv-info nil
             :wrld wrld
             :fnstack nil
             :ancestors nil
             :backchain-limit (access rewrite-constant rcnst
                                      :backchain-limit-rw)
             :simplify-clause-pot-lst nil
             :pot-lst-terms nil
             :rcnst rcnst
             :gstack gstack
             :ttree nil))
          (cond
           (contradictionp
            #-acl2-loop-only (dmr-flush t)
            (mv step-limit contradictionp nil))
           (t
            #-acl2-loop-only (dmr-flush t)
            (mv step-limit nil simplify-clause-pot-lst)))))

(defun setup-simplify-clause-pot-lst (cl ttrees fc-pair-lst
                                      type-alist rcnst wrld state step-limit)

; We construct the initial value of the simplify-clause-pot-lst in preparation
; for rewriting clause cl.  We assume rcnst contains the user's hint settings,
; the correct top-clause and current clause, and a null :pt.

; We return three values.  The first is a new step-limit.  If the second is
; non-nil it indicates that we have proved cl and the other value is
; irrelevant.  In the case that we prove clause the second result is a poly,
; meaning it was proved by linear arithmetic.  The assumptions in the ttree of
; that poly must be considered before cl is declared proved.  When the second
; answer is nil the third is the constructed simplify-clause-pot-lst.

; As of Version_2.8, we start by adding the (negations of) any forward-chaining
; conclusions to the head of cl and the corresponding ttrees to ttrees.  We
; then call the original setup-simplify-clause-pot-lst on the resultant
; expanded clause.  This will allow us to use forward-chaining conclusions in
; linear arithmetic.

; Here is one example of why we might want to do this:

;  (defun bytep (n)
;    (and (integerp n)
;         (<= -128 n)
;         (< n 128)))
;
;  (defthm bytep-thm
;    (implies (and (integerp n)
;                  (<= -128 n)
;                  (< n 128))
;             (bytep n)))
;
;  (defthm bytep-fc-thm
;    (implies (bytep n)
;             (and (integerp n)
;                  (<= -128 n)
;                  (< n 128)))
;    :rule-classes :forward-chaining)
;
;  (in-theory (disable bytep))
;
;  (defthm tricky
;   (implies (and (bytep n)
;                 (bytep (+ 7 n)))
;            (bytep (+ 3 n))))

; Before linear arithmetic used the conclusions of forward-chaining rules, one
; would have to re-enable the definition of bytep in order to prove tricky.
; But if this appeared in a larger context, in which one had proved a bunch of
; lemmas about bytep, one could find oneself in a pickle.  By enabling bytep,
; one loses the ability to use all the lemmas about it.  Without enabling
; bytep, tricky is hard to prove.

; And here is another example:

;  (defun bvecp (x n)
;    (and (integerp x)
;         (<= 0 x)
;         (< x (expt 2 n))))
;
;  (defthm bvecp-2-<-4
;           (implies (bvecp x 2)
;                    (and (integerp x)
;                         (<= 0 x)
;                         (< x 4)))
;    :rule-classes :forward-chaining)
;
;  (in-theory (disable bvecp))
;
;  (thm (implies (and (bvecp x 2)
;                     (not (equal x 0))
;                     (not (equal x 1))
;                     (not (equal x 2)))
;                (equal x 3)))

  (cond ((null fc-pair-lst)
         (setup-simplify-clause-pot-lst1 cl ttrees type-alist rcnst wrld state
                                         step-limit))
        (t
         (setup-simplify-clause-pot-lst (cons (dumb-negate-lit
                                               (caar fc-pair-lst)) cl)
                                        (cons (cdar fc-pair-lst) ttrees)
                                        (cdr fc-pair-lst)
                                        type-alist rcnst wrld state
                                        step-limit))))

(defun sequential-subst-var-term (alist term)

; Each element of alist is of the form (vari . termi).  We replace
; vari by termi in term and then sequentially apply the remaining
; pairs to the result.

  (cond ((null alist) term)
        (t (sequential-subst-var-term (cdr alist)
                                      (subst-var (cdar alist)
                                                 (caar alist)
                                                 term)))))

(defun process-equational-polys
  (cl hist rcnst type-alist wrld pot-lst flg ttree)

; We deduce from pot-lst all the interesting equations in it and add
; them to cl unless they have already been generated and recorded in
; hist.  The flg and ttree are merely accumulators where we construct
; our answers.  In the top-level call, flg should be nil and ttree
; should be any ttree we want to infect with our answer.  Nil would do.

; We return three results, flg, cl and ttree.  The first indicates
; whether we did anything.  The second is the final value of cl and
; the third is the final ttree.  That ttree will record the equations
; we generated and used in this step.  It should become part of the
; history of our output cl so that we do not loop.

; We merely scan down pot-lst.  At every pot we find the first
; acceptable equational poly (if any) and change flg, cl and ttree
; appropriately.

; Historical note: Previous to Version_2.7, rather than add certain
; equalities to cl we performed the substitution suggested by that
; equality.  This substitution forced us to carry along another
; argument, which was the list of all such substitutions made to date.
; That was called var-term-substs.  Here is a Historical Comment that
; deals with the necessity for this now eliminated argument.

; Historical Comment
; The argument var-term-substs is a list of pairs of the form (var
; . term).  These represent some of the equations already found, with
; the first pair on the list representing the earliest such equation.
; (That is, the list is in chronology order, not reverse chronological
; order.)  When a new equation is found and that equation relates a
; var to a term (instead of two non-var terms), we do not really add
; the equation to the clause but rather just substitute the term for
; the var, eliminating that variable.  This can raise problems if, for
; example, we find A = B and replace all the B's by A, and then later
; find B = C.  Had we actually added (equal A B) in response to the
; first equation, this would not be a problem.  But since we didn't
; add that equation but just eliminated all the B's in favor of A, we
; now find B = C unconnected to A.  So every time we find a new
; equation from the pot we first apply each of the substitution pairs
; to it, sequentially.

; Here is an example that failed under Version_2.4 (which did not
; have the var-term-substs argument) but succeeded in Version_2.5
; (which introduced the argument to fix such problems).

;   (defstub bar (x) t)
;
;   (thm (implies (and (rationalp a)(rationalp b)(rationalp c)
;                      (<= a b) (<= b a)
;                      (<= b c) (<= c b))
;                 (equal (bar a) (bar c))))

; End of Historical Comment

; We think we avoid the need for this argument by eliminating all
; substitutions from this function and instead producing the literal
; equalities we deduce.

  (cond ((null pot-lst)
         (mv flg cl ttree))
        (t
         (mv-let (ttree1 lhs rhs)
           (find-equational-poly (car pot-lst) hist)
           (if (null ttree1) ; no equation was found
               (process-equational-polys cl hist rcnst type-alist wrld
                                         (cdr pot-lst) flg ttree)

; From lhs <= rhs and rhs <= lhs we can actually derive the equality
; of their fixes, (fix lhs) = (fix rhs).  We could generate that
; equation and let the system split on the numericity of the two sides
; by conventional opening of fix.  But we don't do that, partly for
; cosmetic reasons but mainly because it is possible the two sides
; have been assumed numeric in ttree1 and rather than force a
; premature split, we just use the existing mechanism to cause the
; split later on below, and thus avoid an identical split.

; The derived-equation, below, is used for two purposes: It is
; advertised as the :target of the assumnote we generate to force an
; assumption, and it is possibly added to the clause.  (We say "possibly"
; because the equality may be manifest in some sense.  See hitp below.)
; The :target of an assumnote is used just in reporting the force.

           (let ((derived-equation ; orient the equality
                  (cond ((and (variablep lhs)
                              (not (dumb-occur lhs rhs)))
                         (cons-term 'equal (list lhs rhs)))
                        ((and (variablep rhs)
                              (not (dumb-occur rhs lhs)))
                         (cons-term 'equal (list rhs lhs)))
                        (t (cons-term 'equal (list lhs rhs)))))
                 (ok-to-force (ok-to-force rcnst))
                 (ens (access rewrite-constant rcnst
                              :current-enabled-structure)))
             (mv-let (flag1 ttree2)
               (add-linear-assumption derived-equation
                                      (mcons-term* 'acl2-numberp lhs)
                                      type-alist ens
                                      (immediate-forcep nil ens)
                                      ok-to-force wrld ttree1)
               (mv-let
                (flag2 ttree3)
                (cond
                 ((eq flag1 :failed)
                  (mv :failed ttree1))
                 (t (add-linear-assumption derived-equation
                                           (mcons-term* 'acl2-numberp rhs)
                                           type-alist ens
                                           (immediate-forcep nil ens) ok-to-force wrld
                                           ttree2)))

; Note lhs and rhs below are bogus if flag2 is :failed; they should not be
; used.  Also, note that up through Version_2.9.3, lhs was set to 0 even when
; (acl2-numberp lhs) was indeterminate with forcing off, but now we do not set
; to 0 in that case (flag1 = :failed); similarly for rhs.

                (let* ((lhs (if (eq flag1 :known-false) *0* lhs))
                       (rhs (if (eq flag2 :known-false) *0* rhs))
                       (new-lit (dumb-negate-lit (mcons-term* 'equal lhs rhs)))

; So at this point, if either side is definitely nonnumeric, it has
; defaulted to 0, just as though we generated (equal (fix lhs) (fix
; rhs)) and then opened the corresponding fix to 0.  Furthermore,
; ttree3 contains the assumptions that both are numeric (when those
; assumptions are not trivially true or trivially false).  In addition
; ttree3 extends ttree1.

; If hitp, below, is true then we will change the cl we are working on.  In
; particular, we will NOT change it if either of our numeric assumptions
; :failed or if both lhs and rhs are trivially 0 -- e.g., as would happen if
; one was 0 and the other was known non-numeric.

                       (hitp (not (or (eq flag2 :failed)

; The following case is new after ACL2_2.9.3.  The following example was
; provided by Robert Krug, inspired by an example from Dave Greve.  Dave didn't
; want a bogus forcing round in such cases (i.e., cases where we don't know
; that at least one side is numeric).

; (thm (implies (and (equal (foo z) (foo y))
;                    (equal (foo x) (foo z)))
;               (foo (+ x y z))))

                                      (and (eq flag1 :added)
                                           (eq flag2 :added))
                                      (and (equal lhs *0*)
                                           (equal rhs *0*))
                                      (member-term new-lit cl)))))

; Note: Robert Krug found a soundness bug in an earlier version of
; this code.  We used derived-equation instead of (mcons-term* 'equal
; lhs rhs) below.  But derived-equation has the original lhs and rhs
; in them, not the FIXed versions!

                  (process-equational-polys
                   (if hitp
                       (add-literal new-lit cl nil)
                     cl)
                   hist rcnst type-alist wrld
                   (cdr pot-lst)

; We got a hit if either we already had a hit or we hit this time.

                   (or flg hitp)
                   (cons-tag-trees (cond
                                    (hitp ttree3)
                                    (t

; If we do not change the clause, we do not record a dependence on the
; type-set information recorded in ttree3.  However, we still record
; ttree1 because it contains the note that prevents us from rederiving
; this same inequality.  Recall that ttree3 includes ttree1.

                                     ttree1))
                                   ttree)))))))))))

; We are finally ready to begin the final assault on simplify-clause.

(defun enumerate-elements (lst i)
  (cond ((null lst) nil)
        (t (cons i (enumerate-elements (cdr lst) (1+ i))))))

(defun already-used-by-fertilize-clausep (lit hist get-clause-id)

; We determine whether the literal lit, which is presumably of the form (not
; (equiv lhs rhs)), has already been used by fertilization in the history hist
; of the current clause.  If not, then we return nil.  Otherwise, we return the
; clause id of that previous use if get-clause-id is true, else we return t.

  (cond ((null hist) nil)
        ((and (eq (access history-entry (car hist) :processor)
                  'fertilize-clause)
              (tag-tree-occur 'literal lit
                              (access history-entry (car hist) :ttree)))
         (or get-clause-id
             (tagged-object 'clause-id (access history-entry (car hist)
                                              :ttree))))
        (t (already-used-by-fertilize-clausep lit (cdr hist) get-clause-id))))

(defun unhidden-lit-info (hist clause pos wrld)
  (cond
   ((null clause)
    (mv nil nil nil))
   (t (let ((lit (car clause)))
        (case-match lit
          (('not ('hide (equiv & &))) ; (not (hide (equiv x y)))
           (cond ((equivalence-relationp equiv wrld)
                  (let* ((new-lit (fcons-term* 'not (fargn (fargn lit 1) 1)))
                         (cl-id
                          (already-used-by-fertilize-clausep
                           new-lit
                           hist nil)))
                    (cond (cl-id (mv pos new-lit cl-id))
                          (t (unhidden-lit-info hist (cdr clause) (1+ pos)
                                                wrld)))))
                 (t (unhidden-lit-info hist (cdr clause) (1+ pos) wrld))))
          (& (unhidden-lit-info hist (cdr clause) (1+ pos) wrld)))))))

(defun tilde-@-hyp-phrase (len-tail cl)

; This tilde-@ phrase describes a literal of the given clause, cl, as a
; hypothesis in the prettyification of cl, where len-tail is the length of the
; tail of cl following that literal (but if somehow the literal is in cl, this
; function acts like it is the last element).  This phrase will, for example,
; complete the sentence "We now use ~@0."  One possible completion is "We now
; use the hypothesis."  Another is, "We now use the conclusion."  A more common
; one is "We now use the third hypothesis."

; Warning: The function fertilize-clause-msg knows that this function
; either refers to the lit as a "conclusion" or as a "hypothesis" and
; can tell which by asking whether the result here is a consp whose
; cdr is nil!  So don't change this function without considering that.

  (let* ((len (length cl))
         (n (- len len-tail)))
    (cond
     ((int= n len)

; See the warning above.

      '("the conclusion"))
     ((and (int= len 2)
           (int= n 1))
      "the hypothesis")
     (t (msg "the ~n0 hypothesis"
             (cons n 'th))))))

(defun simplify-clause1 (top-clause hist rcnst wrld state step-limit)

; In Nqthm, this function was called SIMPLIFY-CLAUSE0.

; Top-clause is a clause with history hist.  We assume that rcnst has a null pt
; and contains whatever hint settings the user wants in it, as well as the
; :force-info based on whether there is a call of IF in top-clause.

; We return 4 values.  The first is a new step-limit.  The next indicates
; whether we changed top-clause and, if so, whether we went through the
; rewriter; it will help determine signal returned by simplify-clause (and
; hence will be used, ultimately, to create the 'simplify-clause hist entry).
; If we did not change top-clause, the third is; otherwise, it is a list of new
; clauses whose conjunction implies top-clause.  The last argument is a ttree
; that explains what we did, and is used in the 'simplify-clause hist entry.

  (mv-let (hitp current-clause pts remove-trivial-equivalences-ttree)
          (remove-trivial-equivalences top-clause
                                       nil
                                       t
                                       (access rewrite-constant rcnst
                                               :current-enabled-structure)
                                       wrld state nil)
          (declare (ignore pts))
          (let ((local-rcnst (change rewrite-constant rcnst
                                     :top-clause top-clause
                                     :current-clause current-clause))
                (current-clause-pts (enumerate-elements current-clause 0)))
            (mv-let
             (contradictionp type-alist fc-pair-lst)
             (forward-chain-top 'simplify-clause
                                current-clause
                                current-clause-pts
                                (ok-to-force local-rcnst)
                                nil ; do-not-reconsiderp
                                wrld
                                (access rewrite-constant rcnst
                                        :current-enabled-structure)
                                (access rewrite-constant rcnst
                                        :oncep-override)
                                state)

; Either we forward chained to a contradiction, in which case we are
; done, or else we have a type-alist assuming the negation of every
; literal in the current-clause and a list of pairs of the form (concl
; .  ttree) indicating that each concl can be derived from the parent
; literals indicated by the 'pt tags.

             (cond
              (contradictionp

; Note: When forward-chain returns with contradictionp = t, then the
; "fc-pair-lst" is really a ttree.  We must add the remove-trivial-
; equivalences ttree to the ttree returned by forward-chain and we must
; remember our earlier case splits.

               (mv step-limit
                   'hit
                   nil
                   (cons-tag-trees
                    remove-trivial-equivalences-ttree
                    fc-pair-lst)))
              (t

; We next construct the initial simplify-clause-pot-lst.
; The construction might prove current-clause, in which case the
; contradictionp answer is non-nil.

               (sl-let
                (contradictionp simplify-clause-pot-lst)
                (pstk
                 (setup-simplify-clause-pot-lst current-clause
                                                (pts-to-ttree-lst
                                                 current-clause-pts)
                                                fc-pair-lst
                                                type-alist
                                                local-rcnst wrld state
                                                step-limit))
                (cond
                 (contradictionp

; A non-nil contradictionp is a poly meaning linear proved current-clause
; (modulo the assumptions in the tag-tree of the poly).

                  (mv step-limit
                      'hit
                      nil
                      (cons-tag-trees
                       remove-trivial-equivalences-ttree
                       (push-lemma
                        *fake-rune-for-linear*
                        (access poly contradictionp :ttree)))))
                 (t
                  (mv-let
                   (flg new-current-clause ttree)
                   (pstk
                    (process-equational-polys
                     current-clause hist local-rcnst type-alist wrld
                     simplify-clause-pot-lst nil
                     remove-trivial-equivalences-ttree))
                   (cond
                    (flg

; Here is where we now perform the substitutions previously done
; within process-equational-polys.  See the historical remarks in that
; function.

                     (mv-let
                      (hitp newest-current-clause pts ttree1)
                      (pstk
                       (remove-trivial-equivalences
                        new-current-clause
                        nil
                        t
                        (access rewrite-constant local-rcnst
                                :current-enabled-structure)
                        wrld state ttree))
                      (declare (ignore pts hitp))
                      (mv step-limit
                          'hit
                          (list newest-current-clause)
                          (push-lemma *fake-rune-for-linear*
                                      ttree1))))
                    (t

; When we call rewrite-clause, below, we pass in as the initial value
; of its ``did we change anything?'' accumulator the flg, hitp, that
; indicates whether remove-trivial-equations changed anything.  Thus,
; this call may answer ``yes, something was changed'' when in fact,
; nothing was done by rewrite-clause itself.  Note that since we are
; calling rewrite-clause here, we return 'hit-rewrite rather than 'hit
; if we return a non-nil signal; see the comments in simplify-clause.

                     (sl-let
                      (flg ecnt ans ttree)
                      (rewrite-clause current-clause
                                      current-clause-pts
                                      1
                                      (initial-gstack 'simplify-clause
                                                      nil current-clause)
                                      nil fc-pair-lst wrld
                                      simplify-clause-pot-lst
                                      local-rcnst
                                      hitp
                                      1
                                      nil
                                      remove-trivial-equivalences-ttree
                                      *trivial-non-nil-ttree*
                                      nil ; splitp
                                      state
                                      step-limit)
                      (declare (ignore ecnt))
                      (cond
                       ((null flg)
                        #-acl2-loop-only (dmr-flush t)
                        (mv-let
                         (pos unhidden-lit old-cl-id)
                         (unhidden-lit-info hist top-clause 0 wrld)
                         (cond (pos (let ((tail (nthcdr (1+ pos) top-clause)))
                                      (mv step-limit
                                          'hit-rewrite
                                          (list (append (take pos top-clause)
                                                        (cons unhidden-lit
                                                              tail)))
                                          (add-to-tag-tree!
                                           'hyp-phrase
                                           (tilde-@-hyp-phrase (len tail)
                                                               top-clause)
                                           (add-to-tag-tree!
                                            'clause-id old-cl-id
                                            (push-lemma (fn-rune-nume 'hide nil
                                                                      nil wrld)
                                                        (rw-cache ttree)))))))
                               (t (mv step-limit nil ans ttree)))))
                       (t
                        #-acl2-loop-only (dmr-flush t)
                        (mv step-limit 'hit-rewrite ans ttree))))))))))))))))

(defun some-element-dumb-occur-lst (lst1 lst2)
  (cond ((null lst1) nil)
        ((dumb-occur-lst (car lst1) lst2) t)
        (t (some-element-dumb-occur-lst (cdr lst1) lst2))))

; The Spec Vars of Prove -- pspv

; The theorem prover, prove, uses so many special variables that are rarely
; modified that we bundle them up.  Because simplify-clause, below, is a
; clause processor in the waterfall, it is the first function in this
; development that is high enough up in the hierarchy to see prove's
; bundle of variables.  So it is time to lay out prove's spec vars:

(defrec prove-spec-var

; Warning: Keep this in sync with #+acl2-par function
; pspv-equal-except-for-tag-tree-and-pool.

; WARNING: If you change the layout of the prove-spec-var in a way that affects
; the position on :rewrite-constant you must change the guard on the
; definitions of nonlinearp-default-hint in (at least) the following community
; books:

; books/arithmetic-5/lib/basic-ops/default-hint.lisp  -- one occurrence
; books/hints/basic-tests.lisp -- two occurrences

; Note: displayed-goal might no longer be necessary in our own sources.  But
; community books have been using them, in particular, books/acl2s/ccg/ccg.lisp.
; So we keep that field.  To search the community books for "displayed-goal"
; (or other strings, by analogy):

; find . -name '*.l*sp' -exec fgrep -i -H displayed-goal {} \;
; find . -name '*.acl2' -exec fgrep -i -H displayed-goal {} \;

  ((rewrite-constant induction-hyp-terms . induction-concl-terms)
   (tag-tree hint-settings . tau-completion-alist)
   (pool . gag-state)
   user-supplied-term displayed-goal orig-hints . otf-flg)
  t)

; The orig-hints setting is the list of clause-ids and hint-settings supplied
; to prove.  The hint-settings is the particular hint settings for the current
; clause.  The only reason we have the orig-hints field is so that we can
; compute the hints appropriate for the top-level goal if we have to abandon
; the initial work and revert to the user-supplied term.  To understand the
; need for the tau-completion-alist read mini-essay On the Tau Completion Alist
; (calist) in tau.lisp.

(defrec gag-info

; This record corresponds to a key checkpoint, but not necessarily the active
; checkpoint.  Suppose for example we see a goal that is hit by an elim before
; any other checkpoint.  Then we push an instance of this record on the
; appropriate stack.  When a goal is pushed for induction and this record is
; for the active checkpoint, then we add the clause-id and pool-lst for that
; goal.

; At one time we thought that clause-id can be nil, but as of August 2016 we do
; not see evidence of that.  We also thought that clause is nil if and only if
; clause-id is nil, but that is false: clause can be nil for a valid clause-id
; because we have generated the empty clause, nil, which implies that the proof
; has failed.

  (clause-id
   clause
   .
   pushed ; list of pairs (clause-id . pool-lst); see above
   )
  t)

(defrec gag-state
  ((top-stack . sub-stack)  ; each a list of gag-info records
   (active-cl-id            ; for active key checkpoint if any, else nil
    . active-printed-p)     ; true when active key checkpoint has been printed
   forcep                   ; true after next forcing round has been announced
   . abort-stack)           ; top-stack when reverting; non-nil symbol on abort
  t)

(defconst *initial-gag-state*
  (make gag-state
        :top-stack nil
        :sub-stack nil
        :active-cl-id nil
        :active-printed-p nil
        :forcep nil))

(defconst *empty-prove-spec-var*
  (make prove-spec-var
        :rewrite-constant nil
        :induction-hyp-terms nil
        :induction-concl-terms nil
        :tag-tree nil
        :hint-settings nil
        :tau-completion-alist nil
        :orig-hints nil
        :pool nil
        :gag-state *initial-gag-state*
        :user-supplied-term *t*
        :displayed-goal nil
        :otf-flg nil))

(defun controller-unify-subst2 (vars acc)
  (cond ((endp vars) acc)
        ((assoc-eq (car vars) acc)
         acc)
        (t (controller-unify-subst2 (cdr vars)
                                    (acons (car vars) (car vars) acc)))))

(defun controller-unify-subst1 (actuals controllers acc)
  (cond ((endp actuals) acc)
        ((car controllers)
         (controller-unify-subst2
          (all-vars (car actuals))
          (controller-unify-subst1 (cdr actuals) (cdr controllers) acc)))
        (t (controller-unify-subst1 (cdr actuals) (cdr controllers) acc))))

(defun controller-unify-subst (name term def-body)
  (let* ((controller-alist (access def-body def-body :controller-alist))
         (controllers (cdr (assoc-eq name controller-alist))))
    (cond (controllers
           (controller-unify-subst1 (fargs term) controllers nil))
          (t :none))))

(defun filter-disabled-expand-terms (terms ens wrld)

; We build expand hint structures, throwing certain terms out of terms.
; Variables and constants are kept (but they should never be there).  Lambda
; applications are kept.  Function symbol applications are kept provided the
; symbol has a non-nil, enabled def-body.  There is no point in keeping on
; :expand-lst a term whose function symbol has no def-body, because it is there
; that we go when we decide to force an expansion (from other than
; user-provided :expand hints).

; Note: It is good that HIDE has a body because we allow HIDE terms to be put
; on :expand-lst and we wouldn't want to throw them off.

  (cond
   ((null terms)
    nil)
   ((or (variablep (car terms))
        (fquotep (car terms)))
    nil)
   (t
    (cond ((flambdap (ffn-symb (car terms)))
           (cons (make expand-hint
                       :pattern (car terms)
                       :alist :none
                       :rune nil
                       :equiv 'equal
                       :hyp nil
                       :lhs (car terms)
                       :rhs (subcor-var (lambda-formals (ffn-symb (car terms)))
                                        (fargs (car terms))
                                        (lambda-body (ffn-symb (car terms)))))
                 (filter-disabled-expand-terms (cdr terms) ens wrld)))
          (t
           (let* ((term (car terms))
                  (name (ffn-symb term))
                  (def-body (def-body name wrld))
                  (formals (access def-body def-body :formals)))
             (cond
              ((and def-body
                    (enabled-numep (access def-body def-body :nume)
                                   ens))
               (cons (make expand-hint
                           :pattern term
                           :alist

; Starting after Version_5.0, we use a more generous expansion heuristic during
; induction, in which only actuals in the controller positions must match
; exactly the actuals in induction terms; otherwise the latter may be instances
; of the former.  With our first attempt at such a change, 8 proofs failed in
; an ACL2(h) regression, not including possible additional proofs that were not
; attempted because of include-book failures.  That attempt didn't remove the
; expand hint when applying it, a heuristic discussed in a long comment in
; expand-permission-result.

; We restored that removal heuristic and the number of failures decreased from
; 8 to 5.  But one of those failures was pretty nasty, still with the same
; behavior (as judging by output from :gag-mode :goals) and the same prove
; time: MAIN-LEMMA-3 in community book
; books/data-structures/memories/memtree.lisp.  The prove time increased from
; 17 seconds for a successful proof to 20 seconds for (both versions of) this
; failure, with a notably different proof as compared to the successful proof
; (Subgoal *1/2' split into 15 subgoals in the failed proof but only generated
; one subgoal in the successful proof).

; So in addition to restoring the removal heuristic, we now limit the
; application of the expand-hint to instances for which each variable is bound
; either to itself or to a constant (a quotep).  That is probably the common
; case in which users had supplied :expand hints because of the formerly weaker
; expand-hint created by the system, say because some non-controller argument
; in the pattern had simplified to 0 or nil.

                           (cons :constants
                                 (controller-unify-subst name term def-body))
                           :rune (access def-body def-body :rune)
                           :equiv (access def-body def-body :equiv)
                           :hyp (access def-body def-body :hyp)
                           :lhs (cons-term name formals)
                           :rhs (access def-body def-body :concl))
                     (filter-disabled-expand-terms (cdr terms) ens wrld)))
              (t (filter-disabled-expand-terms (cdr terms) ens wrld)))))))))

(defun found-hit-rewrite-hist-entry (hist)

; Hist is a list of history-entry records.  We search it to find a history
; entry with 'hit-rewrite or 'hit-rewrite2 signal.  Note that if we
; find 'hit-rewrite, we know that no previous entry (i.e., later in
; hist when viewed as a list) has signal 'hit-rewrite2, due to the way
; we return signals in simplify-clause.

  (if (endp hist)
      nil
    (or (car (member-eq (access history-entry (car hist) :signal)
                        '(hit-rewrite hit-rewrite2)))
        (found-hit-rewrite-hist-entry (cdr hist)))))

(defun simplify-clause (cl hist pspv wrld state step-limit)

; Warning: Keep this in sync with function simplify-clause-rcnst defined in
; community book books/misc/computed-hint-rewrite.lisp.

; This is a "clause processor" of the waterfall.  Its input and output spec is
; consistent with that of all such processors.  See the waterfall for a general
; discussion.

; Cl is a clause with history hist.  We can obtain a rewrite-constant from the
; prove spec var pspv.  We assume nothing about the rewrite-constant except
; that it has the user's hint settings in it and that the pt is nil.  We
; install our top-clause and current-clause when necessary.

; We return five values.  The first is a new step-limit.  The second is a
; signal that in general is 'miss, 'abort, 'error, or a "hit".  In this case,
; it is always either 'miss or one of 'hit, 'hit-rewrite, or 'hit-rewrite2 (as
; described further below).  When the signal is 'hit, the third result is the
; list of new clauses, the fourth is a ttree that will become that component of
; the history-entry for this simplification, and the fifth is the unmodified
; pspv.  (We return the fifth thing to adhere to the convention used by all
; clause processors in the waterfall (q.v.).)  When the signal is 'miss, the
; third and fifth results are irrelevant, but we return a ttree whose rw-cache
; may extend the ttree of the input pspv.

; If the second result is a "hit" then the conjunction of the new clauses
; returned implies cl.  Equivalently, under the assumption that cl is false, cl
; is equivalent to the conjunction of the new clauses.

; On Tail Biting by Simplify-clause:

; Tail biting can occur at the simplify-clause level, i.e., we can return a set
; of clauses that is a generalization of the clause cl, e.g., a set whose
; conjunction is false even though cl is not.  This is because of the way we
; manage the simplify-clause-pot-lst and pts.  We build a single pot-lst and
; use parent trees to render inactive those polys that we wish to avoid.  To
; arrange to bite our own tail, put two slightly different versions of the same
; inequality literal into cl.  The poly arising from the second can be used to
; rewrite the first and the poly arising from first can be used to rewrite the
; second.  If the first rewrites to false immediately our use of parent trees
; (as arranged by passing local-rcnst to the recursive call of rewrite-clause
; in rewrite-clause) will wisely prevent the use of its poly while rewriting
; the second.  But if the first rewrites to some non-linear term (which will be
; rewritten to false later) then we'll permit ourselves to use the first's poly
; while working on the second and we could bite our tail.

; This would not happen if we produced a new linear pot-lst for each literal --
; a pot-lst in which the literal to be rewritten was not assumed false.  Early
; experiments with that approach led us to conclude it was too expensive.

; If the specification of rewrite is correct, then tail biting cannot happen
; except via the involvement of linear arithmetic.  To see this, consider the
; assumptions governing the rewriting of each literal in the clause and ask
; whether the literal being rewritten in in rewrite-clause is assumed false via
; any of those assumptions.  There are five sources of assumptions in the
; specification of rewrite: (a) the type-alist (which is constructed so as to
; avoid that literal), (b) the assumptions in ancestors (which is initially
; empty), (c) the assumptions in the pot-lst (which we are excepting), and (d)
; 'assumptions in ttree (which we are excepting).  Thus, the only place that
; assumption might be found is simplify-clause-pot-lst.  If linear is
; eliminated, the only assumptions left are free of the literal being worked
; on.

; This is really an interface function between the rewriter and the rest of the
; prover.  It has three jobs.

; The first is to convert from the world of pspv to the world of rcnst.  That
; is, from the package of spec vars passed around in the waterfall to the
; package of constants known to the rewriter.

; The second job of this function is to control the expansion of the
; induction-hyp-terms and induction-concl terms (preventing the expansion of
; the former and forcing the expansion of the latter) by possibly adding them
; to terms-to-be-ignored-by-rewrite and expand-lst, respectively.  This is done
; as part of the conversion from pspv (where induction hyps and concl are
; found) to rcnst (where terms-to-be-ignored-by-rewrite and expand-lst are
; found).  They are so controlled as long as we are in the first simplification
; stages after induction.  As soon as the clause has gone through the rewriter
; with some change, with input free of induction-concl-terms, we stop
; interfering.  The real work horse of clause level simplification is
; simplify-clause1.

; The third job is to convert the simplify-clause1 answers into the kind
; required by a clause processor in the waterfall.  The work horse doesn't
; return an pspv and we do.

 (prog2$
  (initialize-brr-stack state)
  (cond ((assoc-eq 'settled-down-clause hist)

; The clause has settled down under rewriting with the induction-hyp-terms
; initially ignored and the induction-concl-terms forcibly expanded.  We now
; stop treating those terms specially and continue simplifying.

; At one time we sometimes avoided simplifying again, in order to save a little
; time, when the clause just settled down -- i.e., the most recent hist entry
; is the one we just found.

; (eq 'settled-down-clause (access history-entry (car hist) :processor))

; In that case, we avoided simplifying again when no specially treated term
; occurs in the clause:

; (not (some-element-dumb-occur-lst
;       (access prove-spec-var
;               pspv
;               :induction-hyp-terms)
;       cl)))

; (Note that the induction-concl-terms also don't occur in the clause -- they
; would have been expanded.  Or at least: if they do occur in the clause, then
; still, removing them from the expand-lst should not help the rewriter!)

; Later, we added a second condition that must also hold in order to avoid
; simplifying again.  If the rw-cache-state is :disabled immediately after a
; hit from settled-down-clause, then we wanted to do the work of making a
; last-ditch attempt at simplification.  So the following needed to be true in
; order to avoid simplifying again.

; (not (eq (access rewrite-constant
;                  (access prove-spec-var pspv :rewrite-constant)
;                  :rw-cache-state)
;          :disabled))

; But now, we always make the extra pass through the simplifier immediately
; after settling down, in order to apply desperation heuristics.  At this time
; the only such desperation heuristic is to arrange that add-linear-lemma
; always linearizes the unrewritten conclusion, even when normally only the
; rewritten conclusion would be linearized.  See add-linear-lemma, where
; examples may be found that motivated this change.

         (let* ((rcnst0 (access prove-spec-var pspv :rewrite-constant))
                (local-rcnst (if (eq 'settled-down-clause
                                     (access history-entry (car hist) :processor))
                                 (change rewrite-constant
                                         rcnst0
                                         :force-info
                                         (if (ffnnamep-lst 'if cl)
                                             'weak
                                           t)
                                         :rewriter-state 'settled-down)
                               (change rewrite-constant
                                       rcnst0
                                       :force-info
                                       (if (ffnnamep-lst 'if cl)
                                           'weak
                                         t)))))
           (sl-let (changedp clauses ttree)
                   (simplify-clause1 cl hist local-rcnst wrld state step-limit)
                   (cond (changedp

; Note: It is possible that our input, cl, is a member-equal of our output,
; clauses!  Such simplifications are said to be "specious."  But we do not
; bother to detect that here because we want to report the specious
; simplification as though everything were ok and then pretend nothing
; happened.  This gives the user some indication of where the loop is.  In the
; old days, we just signaled a 'miss if (member-equal cl clauses) and that
; caused a lot of confusion among experienced users, who saw simplifiable
; clauses being passed on to elim, etc.  See :DOC specious-simplification.

                          (mv step-limit 'hit clauses ttree pspv))
                         (t (mv step-limit 'miss nil ttree nil))))))
        (t

; The clause has not settled down yet.  So we arrange to ignore the
; induction-hyp-terms when appropriate, and to expand the induction-concl-terms
; without question.  The local-rcnst created below is not passed out of this
; function.

         (let* ((rcnst (access prove-spec-var pspv :rewrite-constant))
                (new-force-info (if (ffnnamep-lst 'if cl)
                                    'weak
                                  t))
                (induction-concl-terms
                 (access prove-spec-var pspv :induction-concl-terms))
                (hist-entry-hit (found-hit-rewrite-hist-entry hist))
                (hit-rewrite2 (or (eq hist-entry-hit 'hit-rewrite2)
                                  (and (eq hist-entry-hit 'hit-rewrite)
                                       (not (some-element-dumb-occur-lst
                                             induction-concl-terms
                                             cl)))))

; We arrange to expand the induction-concl-terms and ignore the
; induction-hyp-terms unless hit-rewrite2 above is set.

                (local-rcnst
                 (cond (hit-rewrite2

; We have previously passed through the rewriter, and either a predecessor goal
; or this one is free of induction-concl-terms.  In that case we stop meddling
; with the rewriter by inhibiting rewriting of induction-hyp-terms and forcing
; expansion of induction-concl-terms.  Before Version_2.8 we waited until
; 'settled-down-clause before ceasing our meddling.  However, Dave Greve and
; Matt Wilding reported an example in which that heuristic slowed down the
; prover substantially by needlessly delaying the rewriting of
; induction-hyp-terms.  Notice that this heuristic nicely matches the induction
; heuristics: both consider only the goal, not the result of rewriting it.  (We
; however ignore rewriting by preprocess-clause for the present purpose: we
; want to wait for a full-blown rewrite before allowing rewriting of
; induction-hyp-terms.)

; Initially we attempted to fix the slowdown mentioned above (the one reported
; by Greve and Wilding) by eliminating completely the special treatment of
; induction-hyp-terms.  However, lemma pseudo-termp-binary-op_tree in community
; book books/meta/pseudo-termp-lemmas.lisp showed the folly of this attempt.
; The relevant goal was as follows.

; Subgoal *1/5'
; (IMPLIES (AND (CONSP L)
;               (CONSP (CDR L))
;               (CONSP (CDDR L))
;               (PSEUDO-TERMP (BINARY-OP_TREE BINARY-OP-NAME
;                                             CONSTANT-NAME FIX-NAME (CDR L)))
;               (PSEUDO-TERM-LISTP L)
;               (SYMBOLP BINARY-OP-NAME)
;               (SYMBOLP FIX-NAME)
;               (NOT (EQUAL BINARY-OP-NAME 'QUOTE))
;               (NOT (CONSP CONSTANT-NAME)))
;          (PSEUDO-TERMP (BINARY-OP_TREE BINARY-OP-NAME
;                                        CONSTANT-NAME FIX-NAME L)))

; In this case induction-hyp-terms contained the single term (binary-op_tree
; binary-op-name constant-name fix-name (cdr l)).  Without special treatment of
; induction-hyp-terms, the above binary-op_tree term was rewritten, and hence
; so was the pseudo-termp hypothesis.  The result seemed to give permission to
; the next hypothesis, (pseudo-term-listp l), to be rewritten much more
; aggressively than it was formerly, which bogged down the rewriter (perhaps
; even in an infinite loop).

; A later attempt used the simple algorithm that we stop meddling once we have
; made a pass through the rewriter, even if there are still
; induction-concl-terms around.  Lemma flip-eq-subst-commute in community book
; books/workshops/1999/ivy/ivy-v2/ivy-sources/flip.lisp showed the problem with
; that approach.  Subgoal *1/2' below was produced by preprocess-clause.  It
; produces goal Subgoal *1/2.16, which has a new occurrence in the conclusion
; of the induction-concl-term (SUBST-FREE F X TM):

;  Subgoal *1/2'
;  (IMPLIES (AND (NOT (WFNOT F))
;                (CONSP F)
;                (CONSP (CDR F))
;                (CONSP (CDDR F))
;                (NOT (CDDDR F))
;                (OR (EQUAL (CAR F) 'AND)
;                    (EQUAL (CAR F) 'OR)
;                    (EQUAL (CAR F) 'IMP)
;                    (EQUAL (CAR F) 'IFF))
;                (EQUAL (SUBST-FREE (FLIP-EQ (CADR F) (CDR POS))
;                                   X TM)
;                       (FLIP-EQ (SUBST-FREE (CADR F) X TM)
;                                (CDR POS)))
;                (EQUAL (SUBST-FREE (FLIP-EQ (CADDR F) (CDR POS))
;                                   X TM)
;                       (FLIP-EQ (SUBST-FREE (CADDR F) X TM)
;                                (CDR POS))))
;           (EQUAL (SUBST-FREE (FLIP-EQ F POS) X TM)
;                  (FLIP-EQ (SUBST-FREE F X TM) POS))).
;
;  This simplifies, using the :definitions FLIP-EQ, LEN, LIST2P, LIST3P,
;  SUBST-FREE, TRUE-LISTP, WFBINARY, WFEQ and WFNOT, the :executable-
;  counterparts of BINARY-+, EQUAL, LEN and TRUE-LISTP, primitive type
;  reasoning and the :rewrite rules CAR-CONS and CDR-CONS, to the following
;  16 conjectures.
;
;  Subgoal *1/2.16
;  (IMPLIES (AND (CONSP F)
;                (CONSP (CDR F))
;                (CONSP (CDDR F))
;                (NOT (CDDDR F))
;                (EQUAL (CAR F) 'AND)
;                (EQUAL (SUBST-FREE (FLIP-EQ (CADR F) (CDR POS))
;                                   X TM)
;                       (FLIP-EQ (SUBST-FREE (CADR F) X TM)
;                                (CDR POS)))
;                (EQUAL (SUBST-FREE (FLIP-EQ (CADDR F) (CDR POS))
;                                   X TM)
;                       (FLIP-EQ (SUBST-FREE (CADDR F) X TM)
;                                (CDR POS)))
;                (NOT (CONSP POS)))
;           (EQUAL (SUBST-FREE F X TM)
;                  (LIST 'AND
;                        (SUBST-FREE (CADR F) X TM)
;                        (SUBST-FREE (CADDR F) X TM))))

; If we stop meddling after Subgoal *1/2', then hypothesis rewriting in Subgoal
; *1/2.16 is so severe that we are subject to case-split-limitations and never
; reach the conclusion!  If memory serves, an attempt to turn off
; case-split-limitations just led the prover off the deep end.

                        (change rewrite-constant
                                rcnst
                                :force-info new-force-info

; We also tried a modification in which we use the same :expand-lst as below,
; thus continuing to meddle with induction-concl-terms even after we are done
; meddling with induction-hyp-terms.  However, that caused problems with, for
; example, the proof of exponents-add-1 in community book
; books/arithmetic-2/pass1/expt-helper.lisp.  Apparently the forced expansion
; of (EXPT R J) looped with rule exponents-add-2 (rewriting r^(i+j)).  At any
; rate, it seems reasonable enough to keep suppression of induction-hyp-terms
; rewriting in sync with forced expansion of induction-concl-terms.

; And we tried one more idea: removing the test on whether the clause had been
; rewritten.  We got one failure, on collect-times-3b in v2-8 in community book
; books/arithmetic-2/meta/common-meta.lisp.

; What happens in the proof attempt is that the induction-concl-terms have been
; eliminated in Subgoal *1/7''.  If we check for rewriting, no further meddling
; occurs, and the next subgoal (Subgoal *1/7''') is pushed for proof by
; induction.  That's what we want in this case.

; But if we don't check for rewriting then when the induction-concl-term (EXPT
; X J) surprisingly reappears in Subgoal *1/7''', we again expand it.  It
; continues to appear in every other goal, causing a loop.

; Now, the suggestion was not to check whether the goal was rewritten, and
; we've given that one interpretation.  Another interpretation is to record in
; the history the first time we see a disappearance of induction-concl-terms,
; so that we never again try to expand them (or ignore induction-hyp-terms).
; But it seems that the natural way to record such information still involves
; saving extra information (e.g., the signal) in a history entry.  So even
; though it may be redundant, we might as well check that we've done some
; rewriting.  That way we don't have to rely on the immediate appearance of
; induction-concl-terms, and yet we are still guaranteed at least one pass
; through the rewriter before stopping the "meddling".

                                ))
                       (t
                        (change rewrite-constant
                                rcnst
                                :force-info new-force-info
                                :terms-to-be-ignored-by-rewrite
                                (append
                                 (access prove-spec-var
                                         pspv :induction-hyp-terms)
                                 (access rewrite-constant
                                         rcnst
                                         :terms-to-be-ignored-by-rewrite))
                                :expand-lst
                                (append? (access rewrite-constant
                                                 rcnst :expand-lst)

; We give the user's expand-lst priority, in case it specifies :with for a term
; that is also an enabled call in induction-concl-terms.

                                         (filter-disabled-expand-terms
                                          induction-concl-terms
                                          (access rewrite-constant
                                                  rcnst
                                                  :current-enabled-structure)
                                          wrld)))))))
           (sl-let (hitp clauses ttree)
                   (simplify-clause1 cl hist local-rcnst wrld state step-limit)
                   (cond
                    (hitp (mv step-limit
                              (if hit-rewrite2 'hit-rewrite2 hitp)
                              clauses ttree pspv))
                    (t (mv step-limit 'miss nil ttree nil)))))))))

; Inside the waterfall, the following clause processor immediately follows
; simplify-clause.

(defun settled-down-clause (clause hist pspv wrld state)

; This is the processor in the waterfall just after simplify-clause.
; Its presence in the waterfall causes us to add a
; 'settled-down-clause hist-entry to the history of the clause when
; simplify-clause finishes with it.  The "hit state" of the waterfall
; leads back to the simplifier, where the code above detects this
; settling down and turns off the handling of the induction hyp and
; concl terms.  The "miss state" of the waterfall leads to the next
; processor.

; Note: There has been some consideration given to the question
; ``should this function claim a 'hit after SPECIOUS
; simplify-clauses?''  We say ``yes'' in the comment in
; previous-process-was-speciousp.

  (declare (ignore wrld state))
  (cond ((assoc-eq 'settled-down-clause hist)
         (mv 'miss nil nil nil))
        (t (mv 'hit (list clause) nil pspv))))

; We now develop the functions for reporting on the output of simplify.

(defun member-class-name-runes (class name runes)
  (cond ((endp runes) nil)
        ((let ((rune (car runes)))
           (and (eq (car rune) class)
                (eq (base-symbol rune) name)))
         t)
        (t (member-class-name-runes class name (cdr runes)))))

(defun extract-and-classify-lemmas2 (names class ignore-lst if-intro case-split
                                           immed-forced forced-runes)
  (cond ((endp names) nil)
        ((member-eq (car names) ignore-lst)
         (extract-and-classify-lemmas2 (cdr names) class ignore-lst if-intro
                                       case-split immed-forced forced-runes))
        (t
         (let ((name (car names)))
           (acons name
                  (append (if (member-class-name-runes class name if-intro)
                              '("if-intro")
                            nil)
                          (if (member-class-name-runes class name case-split)
                              '("case-split")
                            nil)
                          (if (member-class-name-runes class name immed-forced)
                              '("immed-forced")
                            nil)
                          (if (member-class-name-runes class name forced-runes)
                              '("forced")
                            nil))
                  (extract-and-classify-lemmas2 (cdr names) class ignore-lst
                                                if-intro case-split
                                                immed-forced forced-runes))))))

(defun extract-and-classify-lemmas1 (class-alist ignore-lst if-intro case-split
                                                 immed-forced forced-runes)
  (cond ((endp class-alist) nil)
        (t (let* ((class (caar class-alist))
                  (symbol-alist
                   (extract-and-classify-lemmas2
                    (cdar class-alist) ; names
                    class ignore-lst if-intro case-split immed-forced
                    forced-runes))
                  (rest
                   (extract-and-classify-lemmas1
                    (cdr class-alist) ignore-lst if-intro case-split
                    immed-forced forced-runes)))
             (cond
              (symbol-alist (acons class symbol-alist rest))
              (t rest))))))

(defun runes-to-class-alist1 (runes alist)
  (cond ((endp runes) alist)
        (t (let* ((rune (car runes))
                  (type (car rune))
                  (sym (base-symbol rune))
                  (old (cdr (assoc-eq type alist))))
             (runes-to-class-alist1 (cdr runes)
                                    (put-assoc-eq type
                                                  (cons sym old)
                                                  alist))))))

; We admit the following sorting functions in :logic mode, verify their guards,
; and prove properties of them in community book books/misc/sort-symbols.lisp.

(defun strict-merge-symbol-< (l1 l2 acc)

; If l1 and l2 are strictly ordered by symbol-< and above acc, which is also
; thus strictly ordered, then the result is strictly ordered by symbol-<.

  (declare (xargs :guard (and (symbol-listp l1)
                              (symbol-listp l2)
                              (true-listp acc))

; We admit this to the logic and prove termination in community book
; books/misc/sort-symbols.lisp.

                  :mode :program))
  (cond ((endp l1) (revappend acc l2))
        ((endp l2) (revappend acc l1))
        ((eq (car l1) (car l2))
         (strict-merge-symbol-< (cdr l1) (cdr l2) (cons (car l1) acc)))
        ((symbol-< (car l1) (car l2))
         (strict-merge-symbol-< (cdr l1) l2 (cons (car l1) acc)))
        (t (strict-merge-symbol-< l1 (cdr l2) (cons (car l2) acc)))))

(defun strict-merge-sort-symbol-< (l)

; Produces a result with the same elements as the list l of symbols, but
; strictly ordered by symbol-name.

  (declare (xargs :guard (symbol-listp l)

; We admit this to the logic and prove termination in community book
; books/misc/sort-symbols.lisp.

                  :mode :program))
  (cond ((endp (cdr l)) l)
        (t (strict-merge-symbol-<
            (strict-merge-sort-symbol-< (evens l))
            (strict-merge-sort-symbol-< (odds l))
            nil))))

(defun sort-symbol-listp (x)
  (declare (xargs :guard (symbol-listp x)))
  (cond ((strict-symbol-<-sortedp x)
         x)
        (t (strict-merge-sort-symbol-< x))))

; Now that sort-symbol-listp has been defined, we can define
; set-ruler-extenders.

#+acl2-loop-only
(defmacro set-ruler-extenders (x)
  `(state-global-let*
    ((inhibit-output-lst (list* 'event 'summary (@ inhibit-output-lst))))
    (er-progn
     (chk-ruler-extenders ,x soft 'set-ruler-extenders (w state))
     (progn
       (table acl2-defaults-table :ruler-extenders
              (let ((x0 ,x))
                (case x0

; If keywords other than :ALL, :BASIC, and :LAMBDAS are supported, then also
; change get-ruler-extenders1.

                  (:all :all)
                  (:lambdas *basic-ruler-extenders-plus-lambdas*)
                  (:basic *basic-ruler-extenders*)
                  (otherwise (sort-symbol-listp x0)))))
       (table acl2-defaults-table :ruler-extenders)))))

#-acl2-loop-only
(defmacro set-ruler-extenders (x)
  (declare (ignore x))
  nil)

(defun strict-merge-sort-symbol-<-cdrs (alist)
  (cond ((endp alist) nil)
        (t (acons (caar alist)
                  (strict-merge-sort-symbol-< (cdar alist))
                  (strict-merge-sort-symbol-<-cdrs (cdr alist))))))

(defun runes-to-class-alist (runes)
  (strict-merge-sort-symbol-<-cdrs
   (runes-to-class-alist1
    runes
    (pairlis$ (strict-merge-sort-symbol-< (strip-cars runes))
              nil))))

(defun extract-and-classify-lemmas (ttree ignore-lst forced-runes)

; We essentially partition the set of runes tagged as 'lemmas in ttree into
; partitions based on the type (i.e., the keyword token) for each rune.  In
; addition, we indicate whether the rune was applied as a splitter rune, and if
; so, of which types.  In our partitioning we actually throw away the runes and
; just report the corresponding base symbols.

; In particular, scan ttree for all the 'lemma tags and return an alist
; associating each type of rune used in the ttree with an alist associating
; runes with types of splitters, except that we ignore runes whose whose base
; symbols are in ignore-lst.

; An example alist returned is
; '((:DEFINITION (APP) (REV FORCED))
;   (:REWRITE (LEMMA1) (LEMMA2 IF-INTRO FORCED) (LEMMA3 CASE-SPLIT))
;   (:TYPE-PRESCRIPTION (FN1 FORCED) (FN2 FORCED) (FN3)))
; indicating that three :REWRITE runes were used, with base symbols
; LEMMA1, LEMMA2 (which was forced and also introduced a call of IF), and
; LEMMA3, etc.

; The alist is sorted by car.  Each value is itself an alist that is itself
; sorted by car.

  (extract-and-classify-lemmas1
   (runes-to-class-alist (tagged-objects 'lemma ttree))
   ignore-lst
   (tagged-objects 'splitter-if-intro ttree)
   (tagged-objects 'splitter-case-split ttree)
   (tagged-objects 'splitter-immed-forced ttree)
   forced-runes))

(defun tilde-*-conjunction-of-possibly-forced-names-phrase1 (alist)
  (cond
   ((null alist) nil)
   (t (cons (let ((name (caar alist))
                  (splitter-types (cdar alist)))
              (cond ((null splitter-types)
                     (msg "~x0" name))
                    (t (msg "~x0 (~*1)"
                            name
                            (list "" "~s*" "~s*," "~s*,"
                                  splitter-types)))))
            (tilde-*-conjunction-of-possibly-forced-names-phrase1
             (cdr alist))))))

(defun tilde-*-conjunction-of-possibly-forced-names-phrase (lst)

; Lst is a list of pairs of the form (flg . name).  We build a tilde-* phrase
; that will print a conjoined list of names, with the parenthetical remark "forced"
; occurring just after those with flg t.

; For example, if lst is
; ((NIL . APP) (T . REV) (NIL . LEN) (T . MEM) (T . SQ))
; and the output of this function is bound to the fmt variable
; #\D, then ~*D prints "APP, REV (forced), LEN, MEM (forced) and SQ
; (forced)".

  (list "" "~@*" "~@* and " "~@*, "
        (tilde-*-conjunction-of-possibly-forced-names-phrase1 lst)))

(defconst *fake-rune-for-cert-data*
  '(:FAKE-RUNE-FOR-CERT-DATA nil))

(defconst *fake-rune-alist*

; We use this constant for dealing with fake runes in tag-trees.  We ignore
; *fake-rune-for-anonymous-enabled-rule*, because push-lemma is careful not to
; put it into any tag-trees.

  (list (cons (car *fake-rune-for-linear*)
              "linear arithmetic")
        (cons (car *fake-rune-for-type-set*)
              "primitive type reasoning")
        (cons (car *fake-rune-for-cert-data*)
              "previously-computed data")))

(defun rune-< (x y)
  (cond
   ((eq (car x) (car y))
    (or (symbol-< (cadr x) (cadr y))
        (and (eq (cadr x) (cadr y))
             (cond ((null (cddr x))
                    (cddr y))
                   ((null (cddr y))
                    nil)
                   (t (< (cddr x) (cddr y)))))))
   ((symbol-< (car x) (car y))
    t)
   (t
    nil)))

(defun merge-runes (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((rune-< (car l1) (car l2))
         (cons (car l1) (merge-runes (cdr l1) l2)))
        (t (cons (car l2) (merge-runes l1 (cdr l2))))))

(defun merge-sort-runes (l)
  (cond ((null (cdr l)) l)
        (t (merge-runes (merge-sort-runes (evens l))
                        (merge-sort-runes (odds l))))))

(defun tilde-*-simp-phrase1 (alist abbreviations-flg)
  (cond
   ((null alist) (mv nil nil))
   (t
    (let ((pair (assoc-eq (caar alist) *fake-rune-alist*)))
      (cond
       (pair
        (mv-let (rest-msgs rest-pairs)
                (tilde-*-simp-phrase1 (cdr alist) abbreviations-flg)
                (mv (cons (cdr pair) rest-msgs)
                    rest-pairs)))
       (t
        (let ((names
               (tilde-*-conjunction-of-possibly-forced-names-phrase
                (cdar alist)))

; Note: Names is a tilde-* object that will print a conjoined list of names
; (possibly followed by parenthetical remarks for splitters).  We must
; determine whether there is more than one name in the list.  The names printed
; are just those in (cdar alist), which we know is a non-empty true list of
; pairs.  Below we set pluralp to t if two or more names will be printed and to
; nil if exactly one name will be printed.

              (pluralp (if (cdr (cdar alist)) t nil)))
          (mv-let
           (msg pair)
           (case (caar alist)
             (:DEFINITION
              (mv (if abbreviations-flg
                      (if pluralp
                          "the simple :definitions ~*D"
                        "the simple :definition ~*D")
                    (if pluralp
                        "the :definitions ~*D"
                      "the :definition ~*D"))
                  (cons #\D names)))
             (:EXECUTABLE-COUNTERPART
              (mv (if pluralp
                      "the :executable-counterparts of ~*X"
                    "the :executable-counterpart of ~*X")
                  (cons #\X names)))
             (:REWRITE
              (mv (if abbreviations-flg
                      (if pluralp
                          "the simple :rewrite rules ~*R"
                        "the simple :rewrite rule ~*R")
                    (if pluralp
                        "the :rewrite rules ~*R"
                      "the :rewrite rule ~*R"))
                  (cons #\R names)))
             (:LINEAR
              (mv (if pluralp
                      "the :linear rules ~*L"
                    "the :linear rule ~*L")
                  (cons #\L names)))
             (:BUILT-IN-CLAUSE
              (mv (if pluralp
                      "the :built-in-clause rules ~*B"
                    "the :built-in-clause rule ~*B")
                  (cons #\B names)))
             (:COMPOUND-RECOGNIZER
              (mv (if pluralp
                      "the :compound-recognizer rules ~*C"
                    "the :compound-recognizer rule ~*C")
                  (cons #\C names)))

; We do not expect the following three cases to arise in the
; simplifier, but this function finds wider use.

             (:ELIM
              (mv (if pluralp
                      "the :elim rules ~*e"
                    "the :elim rule ~*e")
                  (cons #\e names)))
             (:GENERALIZE
              (mv (if pluralp
                      "the :generalize rules ~*G"
                    "the :generalize rule ~*G")
                  (cons #\G names)))
             (:INDUCTION
              (mv (if pluralp
                      "the :induction rules ~*I"
                    "the :induction rule ~*I")
                  (cons #\I names)))
             (:META
              (mv (if pluralp
                      "the :meta rules ~*M"
                    "the :meta rule ~*M")
                  (cons #\M names)))
             (:FORWARD-CHAINING
              (mv (if pluralp
                      "the :forward-chaining rules ~*F"
                    "the :forward-chaining rule ~*F")
                  (cons #\F names)))
             (:EQUIVALENCE
              (mv (if pluralp
                      "the :equivalence rules ~*E"
                    "the :equivalence rule ~*E")
                  (cons #\E names)))
             (:REFINEMENT
              (mv (if pluralp
                      "the :refinement rules ~*r"
                    "the :refinement rule ~*r")
                  (cons #\r names)))
             (:CONGRUENCE
              (mv (if pluralp
                      "the :congruence rules ~*c"
                    "the :congruence rule ~*c")
                  (cons #\c names)))
             (:TYPE-PRESCRIPTION
              (mv (if pluralp
                      "the :type-prescription rules ~*T"
                    "the :type-prescription rule ~*T")
                  (cons #\T names)))
             (:TYPE-SET-INVERTER
              (mv (if pluralp
                      "the :type-set-inverter rules ~*t"
                    "the :type-set-inverter rule ~*t")
                  (cons #\t names)))
             (otherwise
              (mv (er hard 'tilde-*-simp-phrase1
                      "We did not expect to see the simplifier report a rune ~
                       of type ~x0."
                      (caar alist))
                  nil)))
           (mv-let (rest-msgs rest-pairs)
                   (tilde-*-simp-phrase1 (cdr alist) abbreviations-flg)
                   (mv (cons msg rest-msgs)
                       (cons pair rest-pairs)))))))))))

(defun tilde-*-raw-simp-phrase1 (runes forced-runes punct ignore-lst phrase
                                       acc)
  (cond
   ((null runes)
    (cond ((null acc)
           (mv nil (list (cons #\p (if phrase
                                       (msg "  " phrase)
                                     "")))))
          (t (mv (list (concatenate 'string
                                    "~@Fthe list of runes,~|~% ~YRe"
                                    (case punct
                                      (#\, ",~|~%")
                                      (#\. ".~|")
                                      (otherwise "~|"))
                                    "~@p"))
                 (list (cons #\F
                             (if forced-runes
                                 (msg "(forcing with ~&0) "
                                      forced-runes)
                               ""))
                       (cons #\p (if phrase
                                     (msg "~@0~|" phrase)
                                   ""))
                       (cons #\R (merge-sort-runes (reverse acc)))
                       (cons #\e nil))))))
   (t
    (let ((pair (assoc-eq (caar runes) *fake-rune-alist*)))
      (cond
       (pair
        (mv-let (rest-msgs rest-pairs)
                (tilde-*-raw-simp-phrase1 (cdr runes) forced-runes punct
                                          ignore-lst phrase acc)
                (mv (cons (if (null rest-msgs)
                              (concatenate 'string
                                           (cdr pair)
                                           (case punct
                                             (#\, ",")
                                             (#\. ".")
                                             (otherwise "")))
                            (cdr pair))
                          rest-msgs)
                    rest-pairs)))
       (t (tilde-*-raw-simp-phrase1 (cdr runes) forced-runes
                                    punct ignore-lst phrase
                                    (if (member-eq (base-symbol (car runes))
                                                   ignore-lst)
                                        acc
                                      (cons (car runes) acc)))))))))

(defun recover-forced-runes1 (recs ans)
  (cond
   ((endp recs) ans)
   (t (recover-forced-runes1
       (cdr recs)
       (let ((rune (access assumnote
                           (car (access assumption (car recs) :assumnotes))
                           :rune)))
         (cond ((not (symbolp rune))
                (add-to-set-equal rune ans))
               (t ans)))))))

(defun recover-forced-runes (ttree)

; Every assumption in ttree has exactly one assumnote.  Let the ":rune" of the
; assumption be the :rune field of the car of its assumnotes.

; We scan the tag-tree ttree for all occurrences of the 'assumption tag and
; collect into ans the :rune of each assumption, when the :rune is a rune.  We
; ignore the symbolp :runes because we will be searching the resulting list for
; genuine runes and thus need not clutter it with symbols.

  (recover-forced-runes1 (tagged-objects 'assumption ttree) nil))

(defun tilde-*-raw-simp-phrase (ttree punct phrase)

; See tilde-*-simp-phrase.  But here, we print for the case that state global
; 'raw-proof-format is true.  We supply the concluding punctuation msg, punct.

  (let ((forced-runes (recover-forced-runes ttree)))
    (let ((runes (all-runes-in-ttree ttree nil)))
      (mv-let (message-lst char-alist)
              (tilde-*-raw-simp-phrase1
               runes
               forced-runes
               punct
               nil
               phrase
               nil)
              (list* (concatenate 'string "trivial ob~-ser~-va~-tions"
                                  (case punct
                                    (#\, ", ") ; Space not always needed?
                                    (#\. ".")
                                    (otherwise "")))
                     "~@*"
                     "~@* and "
                     "~@*, "
                     message-lst
                     char-alist)))))

(defun tilde-*-simp-phrase (ttree)

; This function determines from ttree whether linear arithmetic and/or
; primitive type reasoning was used and what lemmas and function symbols were
; used.  Then it constructs and returns a tuple suitable for giving to the ~*
; fmt directive.  I.e., if you fmt the string "The proof depends upon ~*S."
; and #\S is bound to the output of this function, then you will get something
; like:
;                        v
; The proof depends upon linear arithmetic, the lemma ASSOC-OF-APP
; (forced), and the definitions of APP (forced) and REVERSE.
;                                                         ^
; Note that the msg actually starts at the v above and stops at the ^.
; I.e., no space will be printed at the beginning, and no space or
; punctuation will be printed at the end.

; Note: Several functions know that if (nth 4 output) is nil, where
; output is the result of this function, then essentially nothing was
; done (i.e., "trivial observations" would be printed).

  (let ((forced-runes (recover-forced-runes ttree)))
    (mv-let (message-lst char-alist)
            (tilde-*-simp-phrase1
             (extract-and-classify-lemmas ttree nil forced-runes)
             nil)
            (list* "trivial ob~-ser~-va~-tions"
                   "~@*"
                   "~@* and "
                   "~@*, "
                   message-lst
                   char-alist))))

(defun tilde-@-pool-name-phrase (forcing-round pool-lst)

; We use this function to create the printed representation from the
; forcing-round and pool-lst.  This function actually has two uses.  First,
; pool-names are used within a single round to refer to local goals, such as
; when we say "Name the formula above *1." or, more suggestively "Name the
; formula above [2]*1.3.4."  In such use, the forcing round is placed just
; before the star, in square brackets.  But pool-names also play a role in
; "clause ids" such as [2]Subgoal *1.3.4/1.1'''.  Observe that in clause ids
; the pool-name is printed here   ^^^^^^          but the forcing-round is
; not printed in the normal place but before the word "Subgoal."  Basically,
; the forcing-round is always leading.  Thus, we need two versions of this
; function, one that puts the forcing-round in and another that does not.
; Confusingly but conveniently, if the forcing round is 0, we do not display it
; and so the two uses of this function -- to generate stand-alone pool names
; and to generate parts of clause ids -- appear somewhat hidden.  But you will
; find calls of this function where the forcing-round supplied is 0 --
; signaling that we want a pool name to use within a clause id -- even though
; the actual forcing-round at the time of call is non-0.

  (cond
   ((= forcing-round 0)

; Notes:
; 1.  This asterisk is the one that appears in the printed name.
; 2.  If you wanted trailing punctuation, you could put it before
;     this close double gritch.
; 3.  These two dots are the ones that separate numbers in the name.
;          1   2                             3      3
;          !   !                             !      !

    (cons "*~*0"
          (list (cons #\0 (list "" "~x*" "~x*." "~x*." pool-lst)))))
   (t
    (cons "[~xr]*~*0"
          (list (cons #\r forcing-round)
                (cons #\0 (list "" "~x*" "~x*." "~x*." pool-lst)))))))

(defun tilde-@-pool-name-phrase-lst (forcing-round lst)
  (cond ((null lst) nil)
        (t (cons (tilde-@-pool-name-phrase forcing-round (car lst))
                 (tilde-@-pool-name-phrase-lst forcing-round (cdr lst))))))

(defun tilde-@-clause-id-phrase (id)

; Warning: Keep this in sync with string-for-tilde-@-clause-id-phrase (and its
; subfunctions).

; Id is a clause-id.  This function builds a tilde-@ object that when printed
; will display the clause id in its external form.

; Warning: If this function is changed so as to print differently, change the
; associated parser, parse-clause-id.  Also change the clone of
; this function, string-for-tilde-@-clause-id-phrase.

; For example, if id is
; (make clause-id
;       :forcing-round 3
;       :pool-lst '(2 1)
;       :case-lst '(5 7 9 11)
;       :primes 3)
; then the result of a tilde-@ on the returned object will be:

; [3]Subgoal *2.1/5.7.9.11'''

; The parser noted above will parse "[3]Subgoal *2.1/5.7.9.11'''" into the
; clause-id above.  Will wonders never cease?  Boyer and Moore wrote a parser?

; If the forcing-round is 0, then we do not print the [...] displaying the forcing-round.

; The sequence of id's printed as the primes field goes from 0 to 11 is

; Subgoal *2.1/5.7.9.11
; Subgoal *2.1/5.7.9.11'
; Subgoal *2.1/5.7.9.11''
; Subgoal *2.1/5.7.9.11'''
; Subgoal *2.1/5.7.9.11'4'
; Subgoal *2.1/5.7.9.11'5'
; Subgoal *2.1/5.7.9.11'6'
; Subgoal *2.1/5.7.9.11'7'
; Subgoal *2.1/5.7.9.11'8'
; Subgoal *2.1/5.7.9.11'9'
; Subgoal *2.1/5.7.9.11'10'
; Subgoal *2.1/5.7.9.11'11'

; If the pool-lst is nil (which is not a pool list ever produced by
; pool-lst but which is used before we have pushed anything into the
; pool), then we print

; Subgoal 5.7.9.11'''

; or

; [3]Subgoal 5.7.9.11'''

; depending on the forcing-round.

; And if the pool-lst is nil and the case-lst is nil we print

; Goal'''

; or

; [3]Goal'''

  (cons (cond
         ((= (access clause-id id :forcing-round) 0)
          (cond ((null (access clause-id id :pool-lst))
                 (cond ((null (access clause-id id :case-lst))
                        "Goal~#q~[~/'~/''~/'''~/'~xn'~]")
                       (t "Subgoal ~@c~#q~[~/'~/''~/'''~/'~xn'~]")))
                (t "Subgoal ~@p/~@c~#q~[~/'~/''~/'''~/'~xn'~]")))
         (t
          (cond ((null (access clause-id id :pool-lst))
                 (cond ((null (access clause-id id :case-lst))
                        "[~xr]Goal~#q~[~/'~/''~/'''~/'~xn'~]")
                       (t "[~xr]Subgoal ~@c~#q~[~/'~/''~/'''~/'~xn'~]")))
                (t "[~xr]Subgoal ~@p/~@c~#q~[~/'~/''~/'''~/'~xn'~]"))))
        (list
         (cons #\r (access clause-id id :forcing-round))
         (cons #\p
               (tilde-@-pool-name-phrase 0 (access clause-id id :pool-lst)))
         (cons #\c
               (cons "~*0"
                     (list (cons #\0 (list "" "~x*" "~x*." "~x*."
                                           (access clause-id id :case-lst))))))
         (cons #\q
               (cond ((> (access clause-id id :primes) 3) 4)
                     (t (access clause-id id :primes))))
         (cons #\n
               (access clause-id id :primes)))))

(defrec bddnote
  (cl-id goal-term mx-id err-string fmt-alist cst term bdd-call-stack ttree)
  nil)

(defun tilde-@-bddnote-phrase (x)

; Bddnote is either a tagged bddnote pair or nil.  This function returns a ~@
; phrase to be used just after "But simplification" or "This simplifies".

  (cond ((null x) "")
        (t (msg " with BDDs (~x0 nodes)"
                (access bddnote x :mx-id)))))

; Clause-ids are typed as strings by the user when he wants to
; identify a clause to which some hint settings are attached.  We now
; develop the machinery for parsing the user's strings into clause-id
; records.

(defun parse-natural1 (str i maximum ans)

; Starting at the ith position of string str we parse a natural
; number.  We return the number read (or nil, if the first char we see
; is not a digit) and the position of the first non-digit.  Ans should
; be initially nil.

  (cond ((>= i maximum) (mv ans maximum))
        (t (let* ((c (char str i))
                  (d (case c
                       (#\0 0)
                       (#\1 1)
                       (#\2 2)
                       (#\3 3)
                       (#\4 4)
                       (#\5 5)
                       (#\6 6)
                       (#\7 7)
                       (#\8 8)
                       (#\9 9)
                       (otherwise nil))))
             (cond (d (parse-natural1 str (1+ i) maximum
                                      (cond ((null ans) d)
                                            (t (+ (* 10 ans) d)))))
                   (t (mv ans i)))))))

(defun parse-natural (dflg str i maximum)

; If dflg is nil, this is just parse-natural1, i.e., starting at the
; ith position of string str we parse a natural number.  We return the
; number read (or nil, if the first char we see is not a digit) and
; the position of the first non-digit.

; If dflg is non-nil, we allow an initial D, which we add to the final
; answer with packn, thus returning a symbol rather than a natural.
; Thus, if D123 parses as that symbol, if dflg is non-nil.

  (cond
   ((>= i maximum) (mv nil maximum))
   ((and dflg (eql (char str i) #\D))
    (mv-let (ans k)
            (parse-natural1 str (+ 1 i) maximum nil)
            (cond ((null ans)
                   (mv nil i))
                  (t (mv (packn (list 'D ans)) k)))))
   (t (parse-natural1 str i maximum nil))))

(defun parse-dotted-naturals (dflg str i maximum ans)

; For now, assume dflg is nil.
; Starting at the ith position of string str we parse a list of
; naturals separated by dots.  We return the list of naturals (which
; may be nil) and the position of the first character not parsed.
; Here are some examples.  In all cases, assume the initial i is 1.

; "*2.1.3 abc..."   => (2 1 3) and 6 (which points to the #\Space)
; " Subgoal..."     => nil and 1 (which points to the #\S)
; " 5.7.9"          => (5 7 9) and 6 (which is just off the end)
; " 5.7ABC"         => (5 7) and 4 (which points to the #\A)
; " 5.7.ABC"        => (5 7) and 4 (which points to the #\.)

; The last example bears thinking about.

; If dflg is non-nil, we allow Dn where naturals are expected above.
; I.e., "*2.1.D23.4 abc" would parse to (2 1 D23 4).  Thus, the
; variable nat below may sometimes hold a symbol, e.g., D23.

  (cond
   ((>= i maximum) (mv (reverse ans) maximum))
   (t (mv-let (nat j)
              (parse-natural dflg str i maximum)
              (cond ((null nat) (mv (reverse ans) i))
                    ((>= j maximum) (mv (reverse (cons nat ans)) maximum))
                    ((and (eql (char str j) #\.)
                          (< (1+ j) maximum)
                          (or (member
                               (char str (1+ j))
                               '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
                              (and dflg (eql (char str (1+ j)) #\D))))
                     (parse-dotted-naturals dflg str (1+ j) maximum
                                            (cons nat ans)))
                    (t (mv (reverse (cons nat ans)) j)))))))

(defun parse-match (pat j patmax str i strmax)

; Starting at the ith char of string str we match each against its
; counterpart in pat, starting at j.  If we exhaust pat we return the
; position of the first character in str past the match.  Otherwise we
; return nil.  This matching is case-insensitive.

  (cond ((>= j patmax) i)
        ((>= i strmax) nil)
        ((or (eql (char pat j) (char str i))
             (eql (char-downcase (char pat j)) (char-downcase (char str i))))
         (parse-match pat (1+ j) patmax str (1+ i) strmax))
        (t nil)))

(defun parse-primes (str i maximum)

; Starting at the ith char of string str we count the "number of primes."
; ', '', and ''' are 1, 2, and 3, respectively.  '4' is 4, '5' is 5, etc.
; We return nil if the string we find is not of this form.  We also return
; the index of the first character not parsed.

  (cond
   ((>= i maximum) (mv 0 maximum))
   ((eql (char str i) #\')
    (cond ((= (+ 1 i) maximum) (mv 1 maximum))
          ((eql (char str (+ 1 i)) #\')
           (cond ((= (+ 2 i) maximum) (mv 2 maximum))
                 ((eql (char str (+ 2 i)) #\') (mv 3 (+ 3 i)))
                 (t (mv 2 (+ 2 i)))))
          (t (mv-let
              (nat j)
              (parse-natural nil str (+ 1 i) maximum)
              (cond
               ((null nat) (mv 1 (+ 1 i)))
               ((< nat 4) (mv 1 (+ 1 i)))
               ((= j maximum) (mv 1 (+ 1 i)))
               ((eql (char str j) #\') (mv nat (+ 1 j)))
               (t (mv 1 (+ 1 i))))))))
   (t (mv 0 i))))

(defun parse-clause-id2 (forcing-round pool-lst str i maximum)

; Assume that pool-lst is a pool-lst.  Suppose that at position i in
; string str there is a case-lst followed by some primes, e.g.,
; "...5.7.9.11'''".  We parse them out and check that the string ends
; at the end of the primes.  We return a clause-id composed of the
; pool-lst supplied above and the parsed case-lst and primes.  If the
; parse fails, we return nil.

  (mv-let
   (case-lst j)
   (parse-dotted-naturals t str i maximum nil)  ; Allow D's.
   (cond ((member 0 case-lst)
          nil)
         (t

; So we've seen "...5.7.9.11..." where ... may be empty.
; We look for the primes.

          (mv-let
           (n j)
           (parse-primes str j maximum)
           (cond ((= j maximum)
                  (make clause-id
                        :forcing-round forcing-round
                        :pool-lst pool-lst
                        :case-lst case-lst
                        :primes n))
                 (t nil)))))))

(defun parse-clause-id1 (forcing-round str i maximum)

; This function takes a string, e.g., "...Subgoal *2.1/5.7.9.11'''" and an
; index i into it to indicate the terminal substring of interest.  We parse
; that terminal substring into the internal clause id with forcing-round as its
; :forcing-round.  For example, if i points to the S in subgoal above, then the
; result is

; (make clause-id
;       :forcing-round forcing-round
;       :pool-lst '(2 1)
;       :case-lst '(5 7 9 11)
;       :primes 3)
; We return nil if the substring does not parse.

  (cond
   ((< maximum (+ i 4)) nil)
   ((member (char str i) '(#\G #\g))

; The only thing this string could be is something of the form "Goal'...".  In
; particular, we know that the pool-lst and the case-lst are both nil and it is
; merely a question of counting primes.

    (let ((k (parse-match "Goal" 0 4 str i maximum)))
      (cond (k
             (mv-let (n j)
                     (parse-primes str k maximum)
                     (cond ((= j maximum)
                            (make clause-id
                                  :forcing-round forcing-round
                                  :pool-lst nil
                                  :case-lst nil
                                  :primes n))
                           (t nil))))
            (t nil))))
   (t
    (let ((k (parse-match "Subgoal " 0 8 str i maximum)))
      (cond ((null k) nil)
            ((>= k maximum) nil)
            ((eql (char str k) #\*)
             (mv-let
              (pool-lst j)
              (parse-dotted-naturals nil str (1+ k) maximum nil) ; disallow D's
              (cond
               ((or (null pool-lst)
                    (member 0 pool-lst)
                    (> (+ 1 j) maximum)
                    (not (eql (char str j) #\/)))

; So we've seen "Subgoal *junk" and we return nil.

                nil)
               (t

; So we've seen "Subgoal *2.1/..." where ... is non-empty.  We look for the
; case-lst now.

                (parse-clause-id2 forcing-round pool-lst str (+ 1 j) maximum)))))
            (t

; So we've seen "Subgoal ..." where ... doesn't begin with #\*.  Thus it can
; only be a case-lst followed by primes.

             (parse-clause-id2 forcing-round nil str k maximum)))))))

(defun parse-clause-id (str)

; This function takes a string, e.g., "[3]Subgoal *2.1/5.7.9.11'''" and either
; parses it into an internal clause id or returns nil.  For example, on the
; string above the result is
; (make clause-id
;       :forcing-round 3
;       :pool-lst '(2 1)
;       :case-lst '(5 7 9 11)
;       :primes 3)

; We are case insensitive, but totally rigid about whitespace.  We
; expect that the user will most often obtain these strings by
; grabbing the fmt output of a tilde-@-clause-id-phrase object.  Users
; sometimes use Emacs to lowercase whole regions of events and that is
; why we are case insensitive.

; We recognize two special cases of clause-id's that are never printed
; by prove.  "Goal" and the symbol T both denote the top-level
; clause-id.

  (cond
   ((stringp str)
    (let* ((maximum (length str)))
      (cond
       ((< maximum 4) nil)
       ((eql (char str 0) #\[)
        (mv-let (forcing-round i)
                (parse-natural nil str 1 maximum)
                (cond
                 ((and forcing-round
                       (eql (char str i) #\]))
                  (parse-clause-id1 forcing-round str (1+ i) maximum))
                 (t nil))))
       (t (parse-clause-id1 0 str 0 maximum)))))
   ((eq str t) *initial-clause-id*)
   (t nil)))

(defun tilde-@-case-split-limitations-phrase (sr-flg case-flg prefix)
  (if (or sr-flg case-flg)
      (msg "~@0(By the way, the ~@1 affected this analysis.  See :DOC ~
            case-split-limitations.)"
           prefix
           (if sr-flg
               (if case-flg
                   "subsumption/replacement and case limits"
                 "subsumption/replacement limit")
             "case limit"))
    ""))

; And now we can define the output routine for simplify-clause, which is also
; used in apply-top-hints-clause-msg1.

(defun simplify-clause-msg1 (signal cl-id clauses speciousp ttree pspv state)

; The arguments to this function are NOT the standard ones for an
; output function in the waterfall because we are prepared to print a
; message about the simplification being specious and as of this
; writing simplification is the only process that may be specious.
; Exception:  OBDD processing also uses this function, and can also
; produce specious simplification.  Note that our current treatment of
; OBDDs does not create 'assumptions; however, we check for them
; anyhow here, both in order to share this code between
; simplify-clause and OBDD processing and in order to be robust (in
; case forcing enters the realm of OBDD processing later).

; See the discussion of the waterfall for more details about the
; standard arguments for processors.

  (declare (ignore signal pspv))
  (let ((raw-proof-format (f-get-global 'raw-proof-format state)))
    (cond
     (speciousp

; At one time had access to the clauses and could print a little more
; information here.  But apparently the code was reorganized in Version_3.3
; such that clauses is nil at this point.  It seems unimportant to report how
; many clauses there are in the specious case.

      (fms "This ~#0~[~/forcibly ~]simplifies~@b, using ~*1~@pto a set of ~
            conjectures including ~@3 itself!  Therefore, we ignore this ~
            specious simp~-li~-fi~-ca~-tion.  See :DOC ~
            specious-simplification.~@c~|"
           (list (cons #\0 (if (tagged-objectsp 'assumption ttree) 1 0))
                 (cons #\1 (if raw-proof-format
                               (tilde-*-raw-simp-phrase ttree #\, "")
                             (tilde-*-simp-phrase ttree)))
                 (cons #\p (if raw-proof-format "" ", "))
                 (cons #\3 (tilde-@-clause-id-phrase cl-id))
                 (cons #\b (tilde-@-bddnote-phrase
                            (tagged-object 'bddnote ttree)))
                 (cons #\c (tilde-@-case-split-limitations-phrase
                            (tagged-objects 'sr-limit ttree)
                            (tagged-objects 'case-limit ttree)
                            "  ")))
           (proofs-co state)
           state
           (term-evisc-tuple nil state)))
     ((null clauses)
      (cond
       (raw-proof-format
        (fms "But ~#0~[~/forced ~]simplification~@b reduces this to T, using ~
              ~*1~|"
             (list (cons #\0 (if (tagged-objectsp 'assumption ttree) 1 0))
                   (cons #\1 (tilde-*-raw-simp-phrase
                              ttree
                              #\.
                              (tilde-@-case-split-limitations-phrase
                               (tagged-objects 'sr-limit ttree)
                               (tagged-objects 'case-limit ttree)
                               "")))
                   (cons #\b (tilde-@-bddnote-phrase
                              (tagged-object 'bddnote ttree))))
             (proofs-co state)
             state
             (term-evisc-tuple nil state)))
       (t
        (fms "But ~#0~[~/forced ~]simplification~@b reduces this to T, using ~
              ~*1.~@c~|"
             (list (cons #\0 (if (tagged-objectsp 'assumption ttree) 1 0))
                   (cons #\1 (tilde-*-simp-phrase ttree))
                   (cons #\b (tilde-@-bddnote-phrase
                              (tagged-object 'bddnote ttree)))
                   (cons #\c (tilde-@-case-split-limitations-phrase
                              (tagged-objects 'sr-limit ttree)
                              (tagged-objects 'case-limit ttree)
                              "  ")))
             (proofs-co state)
             state
             (term-evisc-tuple nil state)))))
     (t
      (let ((hyp-phrase (tagged-object 'hyp-phrase ttree)))
        (cond (hyp-phrase
               (fms "We remove HIDE from ~@0, which was used heuristically to ~
                     transform ~@1 by substituting into the rest of that ~
                     goal.  This produces~|"
                    (list (cons #\0 hyp-phrase)
                          (cons #\1 (tilde-@-clause-id-phrase
                                     (tagged-object 'clause-id ttree))))
                    (proofs-co state)
                    state
                    (term-evisc-tuple nil state)))
              (raw-proof-format
               (fms "This ~#0~[~/forcibly ~]simplifies~@b, using ~*1~
                     to~#2~[~/ the following ~n3 conjectures.~@c~]~|"
                    (list (cons #\0 (if (tagged-objectsp 'assumption ttree) 1 0))
                          (cons #\1 (tilde-*-raw-simp-phrase ttree #\, ""))
                          (cons #\2 clauses)
                          (cons #\3 (length clauses))
                          (cons #\b (tilde-@-bddnote-phrase
                                     (tagged-object 'bddnote ttree)))
                          (cons #\c (tilde-@-case-split-limitations-phrase
                                     (tagged-objectsp 'sr-limit ttree)
                                     (tagged-objectsp 'case-limit ttree)
                                     "  ")))
                    (proofs-co state)
                    state
                    (term-evisc-tuple nil state)))
              (t
               (fms "This ~#0~[~/forcibly ~]simplifies~@b, using ~*1, ~
                     to~#2~[~/ the following ~n3 conjectures.~@c~]~|"
                    (list (cons #\0 (if (tagged-objectsp 'assumption ttree) 1 0))
                          (cons #\1 (tilde-*-simp-phrase ttree))
                          (cons #\2 clauses)
                          (cons #\3 (length clauses))
                          (cons #\b (tilde-@-bddnote-phrase
                                     (tagged-object 'bddnote ttree)))
                          (cons #\c (tilde-@-case-split-limitations-phrase
                                     (tagged-objectsp 'sr-limit ttree)
                                     (tagged-objectsp 'case-limit ttree)
                                     "  ")))
                    (proofs-co state)
                    state
                    (term-evisc-tuple nil state)))))))))

(defun settled-down-clause-msg1 (signal clauses ttree pspv state)

; The arguments to this function are the standard ones for an output
; function in the waterfall.  See the discussion of the waterfall.

  (declare (ignore signal clauses ttree pspv))
  state)

