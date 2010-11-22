; ACL2 Version 4.1 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2010  University of Texas at Austin

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
; Department of Computer Sciences
; University of Texas at Austin
; Austin, TX 78712-1188 U.S.A.

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

(defun dumb-negate-lit-lst (lst)
  (cond ((null lst) nil)
        (t (cons (dumb-negate-lit (car lst))
                 (dumb-negate-lit-lst (cdr lst))))))

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
          (known-whether-nil term type-alist ens force-flg wrld nil)
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
          (known-whether-nil term type-alist ens force-flg wrld nil)
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
              (nvariablep (fargn lit 1))
              (not (fquotep (fargn lit 1)))
              (eq (ffn-symb (fargn lit 1)) 'integerp)
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
; cl2.  So we have (equal A 'const2).  Backchain with cl1.  We msut prove (not
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
             ((and (nvariablep (car cl1))
                   (not (fquotep (car cl1)))
                   (eq (ffn-symb (car cl1)) 'EQUAL))
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
  (cond ((eql count 0) 0)
        ((null tl2) (-f count))
        ((extra-info-lit-p (car tl2))
         (subsumes1-equality-with-const count lit x const1 tl1 (cdr tl2) cl2 alist))
        ((and (nvariablep (car tl2))
              (not (fquotep (car tl2)))
              (eq (ffn-symb (car tl2)) 'NOT)
              (nvariablep (fargn (car tl2) 1))
              (not (fquotep (fargn (car tl2) 1)))
              (eq (ffn-symb (fargn (car tl2) 1)) 'EQUAL))
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
                        (t (subsumes1-equality-with-const (-f new-count) lit x const1 tl1 (cdr tl2) cl2 alist))))))))))

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
        ((and (nvariablep (car cl1))
              (not (fquotep (car cl1)))
              (eq (ffn-symb (car cl1)) 'EQUAL))
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
        ((and (nvariablep (car tl2))
              (not (fquotep (car tl2)))
              (eq (ffn-symb (car tl2)) 'NOT)
              (nvariablep (fargn (car tl2) 1))
              (not (fquotep (fargn (car tl2) 1)))
              (eq (ffn-symb (fargn (car tl2) 1)) 'EQUAL))
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
; seconds to return '? (signalling that we have done 1,000,000 calls of
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
   ((time-limit4-reached-p
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
        ((member-equal cl cl-set) cl-set)
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

#|| ; See comment in disjoin-clause-segment-to-clause-set.
(defun disjoin-clause-segment-to-clause-set-rec (segment cl-set acc)
  (cond ((null cl-set) acc)
        (t (disjoin-clause-segment-to-clause-set-rec
            segment
            (cdr cl-set)
            (conjoin-clause-to-clause-set
             (disjoin-clauses segment (car cl-set))
             acc)))))
||#

(defun disjoin-clause-segment-to-clause-set (segment cl-set)

; This code is not tail-recursive, but it could be.  At one time it caused
; stack overflow problems in Lispworks 4.2.0.  Below is some alternate code,
; with a reverse call in order to provide unchanged functionality.  Would we
; gain efficiency by eliminating tail recursion at the cost of that reverse
; call?  Maybe.  A clearer win would be to avoid the reverse call, which should
; be logically OK but could change the prover's behavior, thus invaliding huge
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

; ACL2 implements a rudimentary form of forward chaining -- though it
; is getting less rudimentary as time goes on!  It sits at the
; top-level of clause simplification.  Before we begin to rewrite the
; literals of a clause, in the same place we set up the
; simplify-clause-pot-lst, we forward chain from the negations of the
; literals of the clause and construct a list of all the
; (heuristically approved) conclusions we can derive.  Each concl is
; paired with a tree that contains the 'lemma and 'pt dependencies.
; That list of pairs is passed down to the rewrite-clause level, where
; it is used to augment the type-alist before rewriting any given
; literal.

; This is the third version of forward chaining.  For an extensive
; comment on version II, see the historical plaque after the definition
; of forward-chain.

; A forward chaining rule is

(defrec forward-chaining-rule
  ((rune . nume) trigger hyps concls . match-free) nil)

; One of the main inefficiencies in our earlier forward chaining schemes
; was that if a rule began to fire but misfired because some hyp could
; not be relieved, we would reconsider firing it later and redo the work
; associated with the misfire.  We avoid that by storing what we call a
; "forward chaining activation" record which permits us to suspend the
; attempt to fire a rule and resume it later.

(defrec fc-activation
  (inst-hyp (hyps . ttree)
            unify-subst inst-trigger . rule) t)

; Warning: If you reorder the fields recode suspend-fc-activation, which
; exploits the layout to conserve conses when modifying instances.

; An fc-activation represents an attempt to apply the given
; forward-chaining-rule.  Suppose a term of interest unifies with the
; trigger term of some rule.  Then we try to relieve the hypotheses of
; that rule, using the current set of assumptions.  Imagine that we
; relieve all those up to but not including hypn, producing an extended
; unify substitution and a ttree recording the dependencies.  But then we
; learn that hypn is not yet definitely nil or definitely non-nil.  Since
; the list of assumptions is growing, we may be able eventually to
; establish hypn.  Therefore, instead of just quitting and starting over
; we suspend the attempted application of rule by producing an
; fc-activation record that records our current state.

; The current unify-subst, ttree and rule are stored in the slots of
; those names.  The inst-trigger is the term in the current problem
; that fired this rule.  What about inst-hyps and hyps?  What do they
; hold?  There are two cases of interest: either hypn -- the hyp we
; are trying to establish -- contains free variables under unify-subst
; or it does not.  If it does, then in the fc-activation, inst-hyp is
; *t* and hyps is the cdr of the hyps of the rule that starts with
; hypn.  If it does not, then inst-hyp is hypn/unify-subst and hyps is
; the cdr of the rule that starts immediately after hypn.  (Because we
; make an activation simply to begin processing a rule, there is the
; unusual case in which the rule has no hyps.  In that case, inst-hyp
; is *t* and hyps is nil.)

(defun fc-activation (term rule ttree force-flg ens)

; If rule is enabled and the trigger of rule can be instantiated with some
; substitution unify-subst to be term, then we make an fc-activation for this
; pair, otherwise we return nil.

; The initial ttree of the activation is ttree.  When we are building an
; activation for a term in the initial clause, this ttree will be nil.  When we
; are building an activation for a term derived by some fc derivation, the
; ttree will contain just that 'fc-derivation.  The presence of that derivation
; in this activation will mean that the conclusion we eventually derive cannot
; be worse than the conclusion of the derivation from which this term sprang.
; Once upon a time this function did not take the ttree arg and just used nil.
; But that gave rise to infinite loops that were not stopped by our worse-than
; hacks because the terms from which the bad terms were derived were not
; logically dependent on their parents.

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
                            (cond ((or (null rule-hyps)
                                       (free-varsp (car rule-hyps)
                                                   unify-subst)
                                       (and (nvariablep (car rule-hyps))
                                            (not (fquotep (car rule-hyps)))
                                            (or (eq (ffn-symb (car rule-hyps))
                                                    'force)
                                                (eq (ffn-symb (car rule-hyps))
                                                    'case-split))
                                            force-flg))
                                   (make fc-activation
                                         :inst-hyp *t*
                                         :hyps rule-hyps
                                         :ttree ttree
                                         :unify-subst unify-subst
                                         :inst-trigger term
                                         :rule rule))
                                  (t (make fc-activation
                                           :inst-hyp
                                           (sublis-var unify-subst
                                                       (car rule-hyps))
                                           :hyps (cdr rule-hyps)
                                           :ttree ttree
                                           :unify-subst unify-subst
                                           :inst-trigger term
                                           :rule rule))))))))))

(defun fc-activation-lst (term rule-lst ttree force-flg ens)

; We create a list of all the possible forward chaining activations for
; term.

  (cond ((null rule-lst) nil)
        (t (let ((act
                  (fc-activation term (car rule-lst) ttree force-flg ens))
                 (rst
                  (fc-activation-lst term (cdr rule-lst) ttree force-flg ens)))
             (if act (cons act rst) rst)))))

; A basic data structure of the forward chaining process is what we
; call the fc-pot-lst.  It is a structure that enumerates all of the
; subterms of the current problem -- the clause and all our derived
; conclusions -- that have any forward chaining rules at all together
; with their still suspended fc-activations.  It is important that the
; list include every term that has rules, even if the rules give rise
; to no activations.  If we omitted a subterm because it gave rise to
; no activations then every time we generated a new subterm we would
; have to scan its rules to see if it permits any activations.  Rather
; than do that, we keep all possible activations (even the empty list)
; and then only note that the subterm is not new.

(mutual-recursion

(defun add-new-fc-pots (term ttree force-flg wrld ens fc-pot-lst)

; A term consed onto the list of all fc activations for the term is
; called an "fc pot".  We sweep term looking for every subterm of the
; form (fn ...) where fn is not a lambda or NOT and has at least one
; forward-chaining-rule associated with it.  We add an fc pot for each
; such subterm to fc-pot-lst.

  (cond ((variablep term) fc-pot-lst)
        ((fquotep term) fc-pot-lst)
        ((flambda-applicationp term)
         (add-new-fc-pots (lambda-body (ffn-symb term))
                          ttree force-flg wrld ens
                          (add-new-fc-pots-lst (fargs term)
                                               ttree force-flg wrld ens
                                               fc-pot-lst)))
        ((eq (ffn-symb term) 'not)

; Because some of the NOTs in clauses are not really present, we think it
; is confusing to allow a NOT to trigger a forward chaining.

         (add-new-fc-pots (fargn term 1) ttree force-flg wrld ens fc-pot-lst))
        ((assoc-equal term fc-pot-lst) fc-pot-lst)
        (t (let ((fc-pot-lst (add-new-fc-pots-lst (fargs term)
                                                  ttree force-flg wrld ens
                                                  fc-pot-lst))
                 (rules (getprop (ffn-symb term)
                                 'forward-chaining-rules
                                 nil
                                 'current-acl2-world
                                 wrld)))
             (cond ((null rules) fc-pot-lst)
                   (t
                    (cons (cons term
                                (fc-activation-lst term
                                                   rules
                                                   ttree
                                                   force-flg
                                                   ens))
                          fc-pot-lst)))))))

(defun add-new-fc-pots-lst (term-lst ttree force-flg wrld ens fc-pot-lst)
  (cond ((null term-lst) fc-pot-lst)
        (t (add-new-fc-pots-lst (cdr term-lst)
                                ttree force-flg wrld ens
                                (add-new-fc-pots (car term-lst)
                                                 ttree force-flg wrld ens
                                                 fc-pot-lst)))))

)

(defun add-new-fc-pots-lst-lst
  (term-lst ttree-lst force-flg wrld ens fc-pot-lst)
  (cond ((null term-lst) fc-pot-lst)
        (t (add-new-fc-pots-lst-lst
            (cdr term-lst)
            (cdr ttree-lst)
            force-flg wrld ens
            (add-new-fc-pots (car term-lst)
                             (car ttree-lst)
                             force-flg wrld ens
                             fc-pot-lst)))))

; The above functions let us create a list of fc-pots, each pot
; containing a list of activations.  We now develop the code to fire up
; an activation and (a) derive a new conclusion, (b) abort and abandon
; the activation, or (c) replace it by a modified activation after
; possibly relieving some but not all of the hyps.

(defun suspend-fc-activation (act inst-hyp hyps unify-subst ttree)

; This function is equivalent to

; (change fc-activation act
;         :inst-hyp inst-hyp
;         :hyps hyps
;         :unify-subst unify-subst
;         :ttree ttree)

; i.e., change all the fields but :inst-trigger and :rule.  But this
; function sometimes does fewer conses.  The cases it tries to
; optimize are based on knowledge of how we change certain fields, but
; the correctness of its answer is independent of usage.

  (cond ((equal unify-subst (access fc-activation act :unify-subst))

         (cond ((and (equal hyps (access fc-activation act :hyps))
                     (equal inst-hyp (access fc-activation act :inst-hyp))
                     (equal ttree (access fc-activation act :ttree)))
                act)
               (t (change fc-activation act
                          :inst-hyp inst-hyp
                          :hyps hyps
                          :ttree ttree))))
        (t (change fc-activation act
                   :inst-hyp inst-hyp
                   :hyps hyps
                   :unify-subst unify-subst
                   :ttree ttree))))

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

(defun mult-search-type-alist (rest-hyps concls term typ type-alist unify-subst
                                         ttree oncep)

; This function is a variant of search-type-alist, instead searching for all
; instances of term that bind to a subset of typ.  It returns a list of
; substitutions (which produce those instances) together with a corresponding
; list of tag-trees each extending ttree.

  (cond ((null type-alist)
         (mv nil nil))
        ((ts-subsetp (cadr (car type-alist)) typ)
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
                                                     ttree))))

; We found a new unify-subst but there may be additional interesting ones out
; there.

                          (t (mv-let (other-unifies other-ttrees)
                                     (mult-search-type-alist rest-hyps concls
                                                             term
                                                             typ
                                                             (cdr type-alist)
                                                             unify-subst
                                                             ttree
                                                             oncep)
                                     (mv (cons new-unify-subst other-unifies)
                                         (cons (cons-tag-trees 
                                                (cddr (car type-alist)) ttree)
                                               other-ttrees)))))))
                       
; We didn't find any new substitutions; try again.

                  (t (mult-search-type-alist rest-hyps concls term
                                             typ
                                             (cdr type-alist)
                                             new-unify-subst
                                             ttree
                                             oncep)))))
        (t (mult-search-type-alist rest-hyps concls term
                                   typ
                                   (cdr type-alist)
                                   unify-subst
                                   ttree
                                   oncep))))

(defun mult-lookup-hyp (hyp rest-hyps concls type-alist wrld unify-subst ttree
                            oncep)

; This function is a variant of lookup-hyp, instead returning a list of
; unify-substs and a corresponding list of tag trees.  See the comment in
; mult-search-type-alist.

  (mv-let (term typ)
          (term-and-typ-to-lookup hyp wrld)
          (mult-search-type-alist rest-hyps concls term typ type-alist
                                  unify-subst ttree oncep)))

(mutual-recursion

(defun ev-respecting-ens (form alist state latches ttree ens wrld)

; This is a variant of ev (see also ev-rec) that avoids calling functions whose
; executable counterparts are disabled.  Thus, here we return (mv erp val
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

(mutual-recursion

(defun mult-relieve-fc-hyps
  (rune target hyps concls unify-subst type-alist ens force-flg wrld state
        ttree
        acc1 acc2 acc3 acc4 oncep)

; We map over hyps and try to relieve each one.  The idea is to return four
; results: new values for inst-hyp, hyps, unify-subst, and ttree.  If we prove
; all the hyps, the new inst-hyp is *t* and the new hyps is nil.  If we show
; some hyp false, the new inst-hyp is *nil*.

; However, each of these results is given as a list since a free variable may
; be bound in several ways, each of which generates a different conclusion.
; The four lists are in lock step with each other (e.g., the first result is
; the first element of each list).  Thus, the lists will always have the same
; length.  Moreover, for efficiency we accumulate into the four result lists
; that are passed in:  acc1, acc2, acc3, acc4.

; We decided not to structure this function like relieve-hyps (giving
; rise to a relieve-fc-hyp) because the answer is so complicated since it
; is involved with state saving.

; We know four ways to relieve a hyp.  If it has no free vars, we try
; type-set and we use evaluation (if it is ground).  If it has free
; vars, we look it up in the type-alist.  In both cases we respect
; FORCEd and CASE-SPLITd hyps.  The way we fail determines what we return.

; Note: Forward chaining was first coded before type-set could force
; 'assumptions.  Thus, splitting on 'assumptions was uncommon, indeed,
; it was only done for the output of linear arithmetic, where we first
; used the idea in the late 70's.  Thus, the forward chaining
; mechanism was designed so as not to produce any 'assumptions, i.e.,
; so as not to call rewrite.  When type-set was extended, assumption
; generation and handling became more wide-spread.  In particular,
; this function can generate assumptions due to the call of type-set
; below and those assumptions are handled by the caller of the
; forward-chaining module.  So now, except for these historical
; comments, there is no rationale behind this function's abstinence
; from rewrite.  Mixing forward and backward chaining so intimately
; might be interesting.  It might also be a can of worms.  It might
; also be inevitable.  It just isn't the most important thing to do
; just yet.

  (cond
   ((null hyps) (mv (cons *t* acc1)
                    (cons nil acc2)
                    (cons unify-subst acc3)
                    (cons ttree acc4)))
   (t (let* ((forcep1 (and (nvariablep (car hyps))
                           (not (fquotep (car hyps)))
                           (or (eq (ffn-symb (car hyps)) 'force)
                               (eq (ffn-symb (car hyps)) 'case-split))))
             (forcer-fn (and forcep1 (ffn-symb (car hyps))))
             (hyp (if forcep1 (fargn (car hyps) 1) (car hyps))))
        (cond
         ((free-varsp hyp unify-subst)
          (mv-let (unify-subst-list ttree-list)
                  (mult-lookup-hyp hyp (cdr hyps) concls
                                   type-alist wrld unify-subst ttree
                                   oncep)
                  (cond
                   (unify-subst-list
                    (mult-relieve-all-fc-hyps
                     rune target (cdr hyps) concls unify-subst-list type-alist
                     ens force-flg wrld state ttree-list acc1 acc2 acc3 acc4
                     oncep))
                   (t
                    (mv-let
                     (force-flg ttree)
                     (cond
                      ((or (not forcep1) (not force-flg))
                       (mv nil ttree))
                      (t
                       (force-assumption
                        rune
                        target
                        (sublis-var-and-mark-free unify-subst hyp)
                        type-alist nil
                        (immediate-forcep forcer-fn ens)
                        force-flg
                        ttree)))
                     (cond
                      (force-flg
                       (mult-relieve-fc-hyps
                        rune target (cdr hyps) concls unify-subst type-alist
                        ens force-flg wrld state ttree
                        acc1 acc2 acc3 acc4 oncep))
                      (t (mv (cons *t* acc1)
                             (cons hyps acc2)
                             (cons unify-subst acc3)
                             (cons ttree acc4)))))))))
         (t (let ((inst-hyp (sublis-var unify-subst hyp)))
              (mv-let (ts ttree1)
                      (type-set inst-hyp force-flg nil type-alist ens wrld nil
                                nil nil)
                      (cond ((ts= ts *ts-nil*)
                             (mv (cons *nil* acc1)
                                 (cons nil acc2)
                                 (cons unify-subst acc3)
                                 (cons ttree acc4)))
                            ((ts-intersectp ts *ts-nil*)
                             (cond
                              ((free-varsp inst-hyp nil)
                               (mv-let
                                (force-flg ttree)
                                (cond
                                 ((or (not forcep1) (not force-flg))
                                  (mv nil ttree))
                                 (t (force-assumption
                                     rune target inst-hyp type-alist nil
                                     (immediate-forcep forcer-fn ens)
                                     force-flg ttree)))
                                (cond
                                 (force-flg
                                  (mult-relieve-fc-hyps
                                   rune target (cdr hyps) concls unify-subst
                                   type-alist ens force-flg wrld state ttree
                                   acc1 acc2 acc3 acc4 oncep))
                                 (t (mv (cons inst-hyp acc1)
                                        (cons (cdr hyps) acc2)
                                        (cons unify-subst acc3)
                                        (cons ttree acc4))))))
                              ((program-termp inst-hyp wrld)
                               (mv (cons inst-hyp acc1)
                                   (cons (cdr hyps) acc2)
                                   (cons unify-subst acc3)
                                   (cons ttree acc4)))
                              (t
                               (mv-let
                                (erp val latches ttree1)
                                (ev-respecting-ens
                                 inst-hyp nil state nil nil ens wrld)
                                (declare (ignore latches))

; If the evaluation is non-erroneous and produces a non-nil val, we
; succeeded.  But if the hyp caused an error or if it produced nil, we
; not only fail but report that this hyp was disproved.

                                (cond
                                 ((and (not erp) val)
                                  (mult-relieve-fc-hyps
                                   rune target (cdr hyps) concls unify-subst
                                   type-alist ens force-flg wrld state
                                   (scons-tag-trees ttree1 ttree)
                                   acc1 acc2 acc3 acc4 oncep))
                                 (t (mv (cons *nil* acc1)
                                        (cons nil acc2)
                                        (cons unify-subst acc3)
                                        (cons ttree acc4))))))))
                            (t (mult-relieve-fc-hyps
                                rune target (cdr hyps) concls unify-subst
                                type-alist ens force-flg wrld state
                                (scons-tag-trees ttree1 ttree) acc1 acc2 acc3
                                acc4 oncep)))))))))))

(defun mult-relieve-all-fc-hyps (rune target hyps concls unify-subst-list
                                      type-alist ens force-flg wrld state
                                      ttree-list
                                      acc1 acc2 acc3 acc4 oncep)

; This function is a helper for mult-relieve-fc-hyps.  It calls
; mult-relieve-fc-hyps once for each element of unify-subst-list and
; corresponding element of ttree-list, appending the respective return values
; of mult-relieve-fc-hyps.

  (if (not (consp unify-subst-list))
      (mv acc1 acc2 acc3 acc4)
    (mv-let (acc1 acc2 acc3 acc4)
            (mult-relieve-fc-hyps
             rune target hyps concls (car unify-subst-list) type-alist ens
             force-flg wrld state (car ttree-list) acc1 acc2 acc3 acc4 oncep)
            (mult-relieve-all-fc-hyps
             rune target hyps concls (cdr unify-subst-list) type-alist ens
             force-flg wrld state (cdr ttree-list) acc1 acc2 acc3 acc4
             oncep))))
)

; Forward Chaining Derivations - fc-derivation - fcd

; To implement forward chaining, especially to implement the heuristic
; controls on which derived conclusions to keep, we have to use ttrees in
; a rather subtle way that involves embedding a ttree in a tagged object
; in another ttree.  These tagged objects holding ttrees are called
; "fc-derivations".  We motivate and discuss them here.  However, no
; fc-derivation gets out of the forward chaining module.  That is, once
; forward-chain has done its job, the ttrees seen throughout the rest of
; the system are free of 'fc-derivations.

; When we finally relieve all the hyps we will create the instantiated
; conclusion, concl.  However, we do not just turn it loose in the world.
; We need to track it for two reasons.  The first reason concerns the
; ultimate use of such derived conclusions: when we have finished all our
; forward chaining and go into the rewriting of literals we will need to
; choose from among the available forward chained concls those that don't
; depend upon the literal we are rewriting.  For this it is sufficient to
; have the ttree of the conclusion.  The second reason is closer to home:
; before we even get out of forward chaining we have to decide whether
; this derived concl is worth keeping.  This is a heuristic decision,
; aimed primarily at preventing infinite forward chaining while
; permitting "desirable" forward chaining.  Our heuristic is based on
; consideration of how the concl was derived.  Roughly put, we will keep
; it unless it is worse than some concl in its derivation.  So we need to
; record its derivation.  That derivation must contain the names of the
; rules used and the derived conclusions used.

; The obvious thing to do is to add to the ttree of concl the name of the
; rule used and concl itself.  That ttree will attach itself to every
; deduction using concl and by inspecting it we will see concl itself in
; the tree, and by induction, all the concls upon which it depends.
; Unfortunately, this is tricky because ttrees represent sets of all the
; things with a given tag.  Thus, for example, if we were to tag the rule
; name with 'lemma and add it to the tree, we would not record the fact
; that name had perhaps been used twice; the previous occurrence of
; (lemma . name) in the tree would prevent add-to-tag-tree from changing
; the tree.  Similarly, while each concl used would be in the set of all
; things tagged 'concl, we couldn't tell which had been used where, how
; many times, or by which rules.

; So we do something very odd (because it results in a ttree being a
; component of an object stored in a ttree).  We make what we call an
; "fc-derivation" which is a structure of the form:

; (defrec fc-derivation
;   ((rune . concl) (fn-cnt . p-fn-cnt) (inst-trigger . ttree))
;   t)

; Rune is the name of the rule applied, concl is the instantiated conclusion.
; Fn-cnt is the function symbol count of concl (as computed by fn-count) and
; p-fn-cnt is the pseudo-function count (see term-order).  These are used in
; our heuristic for deciding whether to keep a concl.  Ttree is the ttree that
; derived concl from name.  Inst-trigger is the term in the current problem
; that fired this rule.

; If we decide to keep concl then we make a ttree that contains its
; fc-derivation as its only object, tagged 'fc-derivation.  That ttree is
; attached to the assumption of concl in the new type-alist and will
; attach itself to all uses of concl.  Given an fc-derivation we can
; reconstruct the derivation of its concl as follows: concl was derived
; by applying name to all of the derived concls in all of the
; 'fc-derivations in its ttree.

; When the internal forward chaining process is complete we will have
; collected a list of fc-derivations deduced from the given clause.
; The ttree in each derivation will indicate the parent literals via
; 'pt tags.  We can also recover the names of the forward chaining
; rules used.  However, all of this information is not visible to the
; standard ttree scanners because there are ttrees nested inside of
; tagged 'fc-derivations.  For example, if during rewriting we were to
; assume the concl of some fcd and tag it with the ttree in that fcd,
; then that ttree might find its way into the ttree eventually
; returned by rewrite.  That would in turn be looked at by the printer
; to determine which lemmas got used.  And unless we coded the
; printer's sweep to know about the ttrees inside of 'fc-derivations,
; it would miss the forward chaining rules.  Similarly, the sweep to
; determine if a given 'pt is used would have to go into
; 'fc-derivations.  We have decided it is better if, upon finishing
; our forward chaining, we convert the recursively nested ttrees in
; 'fc-derivations to standard ttrees.  This destroys the information
; about exactly how concl was derived from its supporters but it lifts
; out and makes visible the 'lemmas and 'pt upon which the concl is
; based.

(defun make-ttrees-from-fc-derivations (fc-derivations)
  (cond ((null fc-derivations) nil)
        (t (cons (add-to-tag-tree 'fc-derivation (car fc-derivations) nil)
                 (make-ttrees-from-fc-derivations (cdr fc-derivations))))))

(defun expunge-fc-derivations (ttree)

; We copy ttree, replacing each 'fc-derivation in it by a new node which tags
; the rule name with 'lemma and lifts out the interior ttrees and expunges
; them.  Thus, when we are done we have a ttree with no 'fc-derivation tags,
; but which has 'lemma tags on the set of names in the 'fc-derivations and
; which has all of the 'pt objects and 'assumptions (for example) that were
; recursively embedded in 'fc-derivations.

; Note: This function must be able to find 'fc-derivations anywhere within the
; ttree.  In particular, before we removed ttrees from the type-alists in
; 'assumptions, we had to expunge the fc-derivations within the type-alists.
; See the comment in force-assumptions.  Remember that 'fc-derivations are for
; heuristic use only, except that they may contain 'pt and 'assumption objects
; that we must lift out.  So we should be ruthless about finding and expunging
; all 'fc-derivations.

; Once upon a time we detected an 'fc-derivation at the end of prove.  It
; slipped into the final proof tree as follows: Forward chaining made two
; passes.  During the first, hyp1 was concluded.  During the second, hyp2 was
; concluded and forced an assumption.  That assumption contained the type-alist
; produced from the first pass, which had the 'fc-derivation for hyp1.  Now if
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

#|
 (er-progn
  (defstub hyp1 (x) t)
  (defstub hyp2 (x) t)
  (defstub trig (x) t)
  (defstub assumptionp (x) t)
  (defstub concl (x) t)

  (defaxiom fc-to-hyp1
    (hyp1 (trig x))
    :rule-classes ((:forward-chaining :trigger-terms ((trig X)))))

  (defaxiom then-fc-to-hyp2
    (implies (and (hyp1 x) (force (assumptionp x)))
             (hyp2 x))
    :rule-classes :forward-chaining)

  (defaxiom in-rewrite-use-hyp2-thus-raising-the-assumption
    (implies (hyp2 x) (concl x)))

  (defaxiom and-relieve-the-assumption-by-appeal-to-hyp1-sucking-in-the-fc-deriv
    (implies (hyp1 x) (assumptionp x)))

  (thm (concl (trig a))))
|#

  (cond ((null ttree) nil)
        ((symbolp (caar ttree))
         (cond ((eq (caar ttree) 'fc-derivation)
                (push-lemma
                 (access fc-derivation (cdar ttree) :rune)
                 (cons-tag-trees
                  (expunge-fc-derivations
                   (access fc-derivation (cdar ttree) :ttree))
                  (expunge-fc-derivations (cdr ttree)))))
               (t (add-to-tag-tree (caar ttree)
                                   (cdar ttree)
                                   (expunge-fc-derivations (cdr ttree))))))
        (t (cons-tag-trees (expunge-fc-derivations (car ttree))
                           (expunge-fc-derivations (cdr ttree))))))

; This completes the discussion of fc-derivations and we now proceed to
; use them in the forward chaining process.  We resume mainline
; development by coding the functions that resume a suspended activation
; of a forward chaining rule.

(defun add-fc-derivations (rune concls inst-trigger ens wrld state ttree
                                fcd-lst)

; For each concl in concls we generate an fc-derivation with the given
; rune and ttree.  We add each fc-derivation to the list fcd-lst and
; return the final fcd-lst.

  (cond ((null concls) fcd-lst)
        (t (mv-let
            (flg concl new-ttree)
            (eval-ground-subexpressions (car concls) ens wrld state ttree)
            (declare (ignore flg))
            (mv-let
             (fn-cnt p-fn-cnt)
             (fn-count concl)
             (add-fc-derivations rune (cdr concls) inst-trigger
                                 ens wrld state ttree
                                 (cons
                                  (make fc-derivation
                                        :rune rune
                                        :concl concl
                                        :fn-cnt fn-cnt
                                        :p-fn-cnt p-fn-cnt
                                        :inst-trigger inst-trigger
                                        :ttree new-ttree)
                                  fcd-lst)))))))

(defun mult-advance-each-fc-activation1 (new-inst-hyp-list new-hyps-list
                                                           new-unify-subst-list
                                                           new-ttree-list
                                                           act ens wrld 
                                                           state fcd-lst)

; This function assumes we have gotten past the :inst-hyp of fc-activation act
; (either because it is *t* or because we relieved it with the given ttree).
; For each element in new-inst-hyp-list (and the corresponding elements of the
; other lists), we work our way through the :hyps of act.  We eventually return
; the two results promised by our superiors, mult-advance-fc-activation1 and
; mult-advance-fc-activation (q.v.): a list of suspended activations to use in
; place of act, which is nil if act is to be discontinued either because it
; terminated or aborted; and an extended fcd-lst containing the derived
; conclusions.

  (if (endp new-inst-hyp-list) ; shouldn't happen the first time
      (mv nil fcd-lst)
    (mv-let (new-act new-fcd-lst)
            (let ((new-inst-hyp (car new-inst-hyp-list))
                  (new-hyps (car new-hyps-list))
                  (new-unify-subst (car new-unify-subst-list))
                  (new-ttree (car new-ttree-list)))
              (cond ((equal new-inst-hyp *t*)
                     (cond ((null new-hyps)
                            (let* ((rule (access fc-activation act :rule)))
                              (mv nil
                                  (add-fc-derivations
                                   (access forward-chaining-rule rule :rune)
                                   (sublis-var-lst new-unify-subst
                                                   (access forward-chaining-rule
                                                           rule
                                                           :concls))
                                   (access fc-activation act :inst-trigger)
                                   ens wrld state
                                   new-ttree
                                   fcd-lst))))
                           (t (mv (suspend-fc-activation act
                                                         *t*
                                                         new-hyps
                                                         new-unify-subst
                                                         new-ttree)
                                  fcd-lst))))
                    ((equal new-inst-hyp *nil*)

; This is the signal that we have disproved a hyp (or at least have
; chosen to abandon this activation).

                     (mv nil fcd-lst))
                    (t (mv (suspend-fc-activation act
                                                  new-inst-hyp
                                                  new-hyps
                                                  new-unify-subst
                                                  new-ttree)
                           fcd-lst))))
            (mv-let (new-acts new-fcd-lst2)
                    (mult-advance-each-fc-activation1 (cdr new-inst-hyp-list) 
                                                      (cdr new-hyps-list)
                                                      (cdr new-unify-subst-list) 
                                                      (cdr new-ttree-list)
                                                      act ens wrld 
                                                      state new-fcd-lst)

                    (mv (if new-act (cons new-act new-acts) new-acts) 
                        new-fcd-lst2)))))

(defun mult-advance-fc-activation1
  (act ttree type-alist ens oncep-override force-flg wrld state fcd-lst)

; This function assumes we have gotten past the :inst-hyp of fc-activation act
; (either because it is *t* or because we relieved it with the given ttree).
; It attempts to relieve the remaining hypotheses of the forward-chaining-rule
; of act, then passes the results to mult-advance-each-fc-activation1 to return
; a new list of fc-activations and a new fcd-lst.

  (mv-let (new-inst-hyp-list new-hyps-list new-unify-subst-list new-ttree-list)
    (let ((rule (access fc-activation act :rule)))
      (mult-relieve-fc-hyps (access forward-chaining-rule
                                    rule
                                    :rune)
                            (access fc-activation act :inst-trigger)
                            (access fc-activation act :hyps)
                            (access forward-chaining-rule
                                    rule
                                    :concls)
                            (access fc-activation act :unify-subst)
                            type-alist
                            ens force-flg wrld state
                            (scons-tag-trees ttree
                                             (access fc-activation act
                                                     :ttree))
                            nil nil nil nil
                            (oncep oncep-override
                                   (access forward-chaining-rule
                                           rule
                                           :match-free)
                                   (access forward-chaining-rule
                                           rule
                                           :rune)
                                   (access forward-chaining-rule
                                           rule
                                           :nume))))
    (mult-advance-each-fc-activation1 new-inst-hyp-list new-hyps-list
                                      new-unify-subst-list new-ttree-list act
                                      ens wrld state fcd-lst)))

(defun mult-advance-fc-activation (act type-alist ens oncep-override force-flg
                                       wrld state fcd-lst)

; Act is an fc activation.  Fcd-lst is a list of all of the
; fc-derivations made so far (this pass).  We try to relieve the hyps of
; act.  We return two results.  The first is either an activation to use
; in place of act or else is nil meaning act is being discontinued.  The
; second is an extension of fcd-lst containing all the newly derived
; conclusions (as fc-derivations).

  (with-accumulated-persistence
   (access forward-chaining-rule
           (access fc-activation act :rule)
           :rune)
   (act-out fcd-lst-out)
   t ; wart: always marked as ``useful''
   (let ((inst-hyp (access fc-activation act :inst-hyp)))
     (cond
      ((equal inst-hyp *t*)
       (mult-advance-fc-activation1
        act nil type-alist ens oncep-override force-flg wrld state fcd-lst))
      (t (mv-let (ts ttree)
                 (type-set inst-hyp force-flg nil type-alist ens wrld nil nil
                           nil)
                 (cond ((ts= ts *ts-nil*)
                        (mv nil fcd-lst))
                       ((ts-intersectp ts *ts-nil*)
                        (mv (list act) fcd-lst))
                       (t (mult-advance-fc-activation1
                           act ttree type-alist ens oncep-override force-flg
                           wrld state fcd-lst)))))))))

(defun advance-fc-activations (lst type-alist ens oncep-override force-flg wrld
                                   state fcd-lst)

; Lst is of the form (act1 ... actn), where each acti is an fc
; activation.  fcd-lst is a list of fc-derivations onto which we
; accumulate any derived conclusions (as fc-derivations).  We return two
; results: a new list of possibly advanced suspended activations and the
; accumulated fcd-lst.

  (cond ((null lst) (mv nil fcd-lst))
        (t (mv-let (acts fcd-lst)
                   (advance-fc-activations (cdr lst)
                                           type-alist
                                           ens
                                           oncep-override
                                           force-flg
                                           wrld
                                           state
                                           fcd-lst)
                   (mv-let (new-acts fcd-lst)
                           (mult-advance-fc-activation
                            (car lst) type-alist
                            ens oncep-override force-flg wrld state fcd-lst)
                           (mv (append new-acts acts)
                               fcd-lst))))))

(defun advance-fc-pot-lst
  (fc-pot-lst type-alist ens oncep-override force-flg wrld state fcd-lst)

; Fc-pot-lst is a list of fc-pots, each of the form (term act1 ...
; actn).  We advance all the activations, producing a new fc-pot-lst and
; an accumulated list of fc-derivations containing the derived
; conclusions.

  (cond ((null fc-pot-lst) (mv nil fcd-lst))
        (t (mv-let
            (acts fcd-lst)
            (advance-fc-activations (cdr (car fc-pot-lst))
                                    type-alist ens oncep-override force-flg
                                    wrld state fcd-lst)
            (mv-let
             (rst-fc-pot-lst fcd-lst)
             (advance-fc-pot-lst (cdr fc-pot-lst) type-alist ens oncep-override
                                 force-flg wrld state fcd-lst)
             (mv (cons (cons (car (car fc-pot-lst)) acts)
                       rst-fc-pot-lst)
                 fcd-lst))))))

; So by applying the above function we can make one pass over an fc pot
; list and derive a new pot list and a set of conclusions.  We now
; develop the code for processing those conclusions.  We want to assume
; each conclusion, tagged with a ttree that records its fc-derivation, on
; an extension of type-alist.

(defun type-alist-fcd-lst (fcd-lst type-alist mbt-fc-derivations
                                   do-not-reconsiderp force-flg ens wrld)

; We take a list of fc histories and assume the truth of each concl, extending
; type-alist.  We return three results.  The first is t or nil indicating
; whether a contradiction was found.  When a contradiction is found, the second
; result is the ttree of that contradiction.  It may mention 'fc-derivations
; that contain rule names that should be reported and other ttrees with
; fc-derivations in them.  When no contradiction is found, the second result is
; the final type-alist.  The third result is a list of ``mbt fc-derivations,''
; which are fc-derivations whose :concls were derived by forward chaining (of
; course) but which can be determined to be true by type-set reasoning.  These
; mbt-fc-derivations are not reflected in the new type-alist but are reported
; so that further forward chaining can be done from them.

; Note that when we finish, (null fcd-lst), we reconsider the type-alist.  This
; is analogous to type-alist-clause-finish.  We have seen an example of forward
; chaining where we derived, in order, (< 0 x), (< x 1), (integerp x), and
; failed to recognize the contradiction, just as type-alist-clause-finish1
; fails to recognize that contradiction.

  (cond
   ((null fcd-lst)
    (if do-not-reconsiderp
        (mv nil type-alist mbt-fc-derivations)
      (mv-let (contradictionp xtype-alist ttree)
              (reconsider-type-alist type-alist type-alist nil ens wrld nil
                                     nil)
              (cond
               (contradictionp (mv t ttree nil))
               (t (mv nil xtype-alist mbt-fc-derivations))))))
   (t (mv-let
       (mbt mbf tta fta ttree)
       (assume-true-false
        (access fc-derivation (car fcd-lst) :concl)
        (add-to-tag-tree 'fc-derivation
                         (car fcd-lst)
                         nil)
        force-flg nil type-alist ens wrld nil nil :fta)
       (declare (ignore fta))
       (cond (mbf (mv t ttree mbt-fc-derivations))
             (mbt (type-alist-fcd-lst (cdr fcd-lst)
                                      type-alist
                                      (add-to-set-equal (car fcd-lst)
                                                        mbt-fc-derivations)
                                      do-not-reconsiderp force-flg
                                      ens wrld))
             (t (type-alist-fcd-lst (cdr fcd-lst)
                                    tta
                                    mbt-fc-derivations
                                    do-not-reconsiderp force-flg ens
                                    wrld)))))))

; When we have obtained a list of fc histories from forward chaining we
; get the opportunity to filter it on heuristic grounds.  The problem is
; to avoid infinite forward chaining.  So we define a predicate that
; determines whether we wish to keep a given derivation, given the
; current fcd-lst.

(defun fcd-runep (rune ttree)

; Rune is the name of a forward chaining rule.  We want to determine if
; rune has been used in any fc-derivation in ttree.  This function is
; analogous to tag-tree-occur except that it looks for the tag
; 'fc-derivation and it recursively looks into the ttrees contained
; therein.

  (cond ((null ttree) nil)
        ((symbolp (caar ttree))
         (cond ((eq (caar ttree) 'fc-derivation)
                (or (equal rune (access fc-derivation (cdar ttree) :rune))
                    (fcd-runep rune
                               (access fc-derivation
                                       (cdar ttree)
                                       :ttree))
                    (fcd-runep rune (cdr ttree))))
               (t (fcd-runep rune (cdr ttree)))))
        (t (or (fcd-runep rune (car ttree))
               (fcd-runep rune (cdr ttree))))))

(defun fcd-worse-than-or-equal (concl fn-cnt p-fn-cnt ttree)

; Concl is a term and fn-cnt is its function symbol count.  If there
; exists a concl' with fn count fn-cnt' in an 'fc-derivation of ttree
; such that fn-cnt >= fn-cnt' and concl is worse-than-or-equal to concl',
; then we return t.  Otherwise we return nil.

  (cond ((null ttree) nil)
        ((symbolp (caar ttree))
         (cond ((eq (caar ttree) 'fc-derivation)
                (or (and (let ((fc-fn-cnt (access fc-derivation (cdar ttree)
                                                  :fn-cnt)))
                           (or (> fn-cnt fc-fn-cnt)
                               (and (eql fn-cnt fc-fn-cnt)
                                    (>= p-fn-cnt
                                        (access fc-derivation (cdar ttree)
                                                :p-fn-cnt)))))
                         (worse-than-or-equal concl
                                              (access fc-derivation
                                                      (cdar ttree)
                                                      :concl)))
                    (fcd-worse-than-or-equal concl fn-cnt p-fn-cnt
                                             (access fc-derivation
                                                     (cdar ttree)
                                                     :ttree))
                    (fcd-worse-than-or-equal concl fn-cnt p-fn-cnt
                                             (cdr ttree))))
               (t (fcd-worse-than-or-equal concl fn-cnt p-fn-cnt
                                           (cdr ttree)))))
        (t (or (fcd-worse-than-or-equal concl fn-cnt p-fn-cnt (car ttree))
               (fcd-worse-than-or-equal concl fn-cnt p-fn-cnt (cdr ttree))))))

; Once upon a time we had heuristics for keeping concl if it there was
; a lit of the current clause that was worse than it or if there was a
; concl already kept that was worse than it.  We have temporarily
; removed those and replaced them by the faster check that the
; triggering term occurs in the clause.  But we'll keep the
; definitions in case we want to reinstate the heuristics.

#|
(defun exists-lit-worse-than-or-equal (cl concl fn-cnt)
  (cond
   ((null cl) nil)
   (t (or (and (>= (fn-count (car cl)) fn-cnt)
               (worse-than-or-equal (car cl) concl))
          (exists-lit-worse-than-or-equal (cdr cl)
                                          concl
                                          fn-cnt)))))
|#

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

; Term is any term, though we are motivated by the case that it is the :concl of
; an fc-derivation.  We return true when, after stripping off any leading calls
; of NOT from term, if the result is a function call then all its arguments
; occur in the given clause, cl.  If the result of stripping NOTs is not a
; function call, then we rather arbitrarily return t for a variable and nil for
; a constant.

  (cond ((variablep term) t)
        ((fquotep term) nil)
        ((eq (ffn-symb term) 'not)
         (all-args-occur-after-strip-not (fargn term 1) cl))
        (t (all-dumb-occur-lst (fargs term) cl))))

(defun approved-fc-derivationp (fcd cl fcd-lst)

; We return t iff we approve fcd as a new fact we will add to fcd-lst
; while forward chaining from clause cl.  Fc-pot-lst is the current
; pot list and hence exhibits all the terms in the current problem.

; Our heuristic for approving an fc-derivation is that either (a) name
; not have been used before in this derivation or (b) concl is not
; worse-than-or-equal any concl in the derivation, or (c) the
; triggering term of this fcd is in the current clause.

  (declare (ignore fcd-lst))
  (let ((ttree (access fc-derivation fcd :ttree)))
    (or (not (fcd-runep (access fc-derivation fcd :rune) ttree))
        (not (fcd-worse-than-or-equal (access fc-derivation fcd :concl)
                                      (access fc-derivation fcd :fn-cnt)
                                      (access fc-derivation fcd :p-fn-cnt)
                                      ttree))
        (dumb-occur-lst (access fc-derivation fcd :inst-trigger) cl)

; If all of the arguments of the conclusion (ignoring any leading NOTs) of the
; forward-chaining rule appear in the clause, we approve the result.  Dave
; Greve has encountered cases where this extra flexibility is important for
; making type-like forward-chaining derivations, as illustrated by the
; following example.

#||

 (defstub con (x y) nil)
 (defstub des (x) nil)

 (defstub typec (x) nil)
 (defstub typeg (x) nil)
 (defstub typed (x) nil)

 (defaxiom typed-implies-typeg
   (implies
    (typed x)
    (typeg x))
   :rule-classes (:rewrite :forward-chaining))

 (defaxiom typeg-des
   (implies
    (typec x)
    (typed (des x)))
   :rule-classes (:rewrite 
                  (:forward-chaining :trigger-terms ((des x)))))

 (defaxiom typec-con
   (implies
    (and
     (natp n)
     (typeg x))
    (typec (con x n)))
   :rule-classes (:rewrite 
                  (:forward-chaining :trigger-terms ((con x n)))))

 (defun several (g)
   (let* ((c (con g 1))
          (g (des c))
          (c (con g 2))
          (g (des c))
          (c (con g 3))
          (g (des c)))
     (con g 4)))

 (in-theory (disable
             (:rewrite typec-con)
             (:rewrite typeg-des)
             (:rewrite typed-implies-typeg)
             ))

 ; The following fails without the call below of all-args-occur-after-strip-not
 ; below unless we remove the in-theory event above.
 (defthm typec-several
   (implies
    (typed g)
    (typec (several g))))

||#

        (all-args-occur-after-strip-not (access fc-derivation fcd :concl)
                                        cl))))

(defun approve-fc-derivations (new-fcd-lst cl approved fcd-lst)

; We have just derived the fc-derivations in new-fcd-lst, from the
; negations of the literals in cl and the fc-derivations in fcd-lst.  We
; wish to filter out those new fc-derivations that we do not wish to
; pursue.  We return two values, the approved new fc-derivations and a
; modified version of fcd-lst to which the approved new fc-derivations
; have been added.  The reason we do the apparently extraneous job of
; adding the approved ones to the existing ones is so that the
; determination of whether we approve of a given new one can be made in
; the context of all those we've already approved.

  (cond ((null new-fcd-lst) (mv approved fcd-lst))
        ((approved-fc-derivationp (car new-fcd-lst) cl fcd-lst)
         (approve-fc-derivations (cdr new-fcd-lst)
                                 cl
                                 (cons (car new-fcd-lst) approved)
                                 (cons (car new-fcd-lst) fcd-lst)))
        (t (approve-fc-derivations (cdr new-fcd-lst)
                                   cl
                                   approved
                                   fcd-lst))))

; So we are now almost ready to put it all together.

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
        ((getprop fn 'level-no nil
                  'current-acl2-world wrld))
        (t 0)))

)

(mutual-recursion

(defun sort-approved1-rating1 (term wrld fc vc)
  (cond ((variablep term) (mv fc (1+ vc)))
        ((fquotep term) (mv fc vc))
        ((flambda-applicationp term)
         (mv-let (fc vc)
                 (sort-approved1-rating1 (lambda-body term) wrld fc vc)
                 (sort-approved1-rating1-lst (fargs term) wrld (1+ fc) vc)))
        ((or (eq (ffn-symb term) 'not)
             (= (getprop (ffn-symb term) 'absolute-event-number 0
                         'current-acl2-world wrld)
                0))
         (sort-approved1-rating1-lst (fargs term) wrld fc vc))
        (t (sort-approved1-rating1-lst (fargs term) wrld
                                       (+ 1
                                          (get-level-no (ffn-symb term) wrld)
                                          fc)
                                       vc))))

(defun sort-approved1-rating1-lst (lst wrld fc vc)
  (cond ((null lst) (mv fc vc))
        (t (mv-let (fc vc)
                   (sort-approved1-rating1 (car lst) wrld fc vc)
                   (sort-approved1-rating1-lst (cdr lst) wrld fc vc)))))
)

(defun sort-approved1-rating (term wrld)

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
          (sort-approved1-rating1 term wrld 0 0)
          (- (+ (* 10 fc) vc))))

(defun sort-approved1 (approved wrld)
  (cond ((null approved) nil)
        (t (cons
            (cons (sort-approved1-rating
                   (access fc-derivation (car approved) :concl)
                   wrld)
                  (car approved))
            (sort-approved1 (cdr approved) wrld)))))

(defun sort-approved (approved wrld)

; Approved is a list of fc-derivations which have derived certain :concls.
; We sort that list so that those with the higher rated :concls come first.

  (strip-cdrs (merge-sort-car-> (sort-approved1 approved wrld))))

(defun strip-fcd-concls (fcd-lst)
  (cond ((null fcd-lst) nil)
        (t (cons (access fc-derivation (car fcd-lst) :concl)
                 (strip-fcd-concls (cdr fcd-lst))))))

(defun every-concl-assoc-equalp (fcd-lst fc-pot-lst)

; Fcd-lst is a list of fc-derivations.  We return t if the :concl of
; every element of fcd-lst already has a pot in fc-pot-lst.

  (cond ((null fcd-lst) t)
        ((assoc-equal (access fc-derivation (car fcd-lst) :concl)
                      fc-pot-lst)
         (every-concl-assoc-equalp (cdr fcd-lst) fc-pot-lst))
        (t nil)))

(defun forward-chain1 (cl fc-pot-lst type-alist force-flg wrld
                          do-not-reconsiderp ens oncep-override state fcd-lst)

; We first advance every fc-activation in fc-pot-lst, obtaining a new pot-lst
; and some derived fc-derivations.  We filter the derived fc-derivations,
; throwing out any that, on heuristic grounds, we don't like.  We then assume
; the approved derived fc-derivations, updating the type-alist.  We keep track
; of the derived :concls that are not added to the type-alist.  We extend
; fc-pot-lst with any new subterms -- including those from derived :concls that
; were already true under type-set and hence no added to the type-alist -- and
; their associated activations, and we loop until either we get a contradiction
; or we stabilize.  We repeatedly extend type-alist as we go, but the extended
; type-alist is of no use outside forward chaining because it is full of
; fc-derivations.  We return two results.  The first is a t or nil indicating
; whether a contradiction was found.  The second is a ttree if a contradiction
; was found and is the final fcd-lst otherwise.

  (mv-let (fc-pot-lst new-fcd-lst)
          (advance-fc-pot-lst fc-pot-lst type-alist ens oncep-override
                              force-flg wrld state nil)
          (mv-let (approved fcd-lst)
                  (approve-fc-derivations new-fcd-lst
                                          cl
                                          nil
                                          fcd-lst)
                  (mv-let (contradictionp x mbt-fc-derivations)
                          (type-alist-fcd-lst
                           (sort-approved approved wrld)
                           type-alist nil do-not-reconsiderp force-flg ens wrld)
                          (let ((xapproved (append mbt-fc-derivations approved)))
                            (cond (contradictionp (mv t x))
                                  ((and (equal x type-alist)
                                        (every-concl-assoc-equalp mbt-fc-derivations
                                                                  fc-pot-lst))
                                   (mv nil fcd-lst))
                                  (t (forward-chain1
                                      cl
                                      (add-new-fc-pots-lst-lst
                                       (strip-fcd-concls xapproved)
                                       (make-ttrees-from-fc-derivations xapproved)
                                       force-flg wrld ens fc-pot-lst)
                                      x force-flg wrld do-not-reconsiderp ens
                                      oncep-override state fcd-lst))))))))

(defun fc-pair-lst (fcd-lst)

; We convert a list of fc-derivations to a list of pairs of the form
; (concl . ttree), where each ttree is expunged of fc-derivations.  We
; call such a pair an "fc-pair."  These pairs can be sensibly used
; outside of the forward-chaining module because the ttrees are free
; of fc-derivations.

  (cond ((null fcd-lst) nil)
        (t (cons (cons (access fc-derivation (car fcd-lst) :concl)
                       (push-lemma
                        (access fc-derivation (car fcd-lst) :rune)
                        (expunge-fc-derivations
                         (access fc-derivation (car fcd-lst) :ttree))))
                 (fc-pair-lst (cdr fcd-lst))))))

(defun fc-pair-lst-type-alist (fc-pair-lst type-alist force-flg ens wrld)

; Fc-pair-lst is a list of pairs of the form (concl . ttree).  We extend
; type-alist by assuming the truth of every concl, tagging each type-alist
; entry with the ttree, which we assume has already been expunged of
; 'fc-derivations.  Assuming the initial type-alist had no 'fc-derivations in
; it, the final one doesn't either.  We return the resulting type-alist unless
; a contradiction arises, in which case we return the resulting ttree.

; At one time we assumed that there was no contradiction, causing a hard error
; if we found one.  However, Jared Davis sent the following script that causes
; that hard error, so we changed this function.  A relevant comment, from
; before that change, is given below.

#|
 (defstub appealp (* *) => *)
 (defstub appeal-listp (* *) => *)
 (defstub appeal-structurep (*) => *)
 (defstub appeal-structure-listp (*) => *)
 (defstub get-subgoals (*) => *)
 (defstub appeal-provisionally-okp (* * *) => *)
 (defstub proofp (* * *) => *)
 (defstub proof-listp (* * *) => *)

 (defaxiom appeal-structure-listp-forward-to-appeal-structurep-of-car
    (implies (appeal-structure-listp x)
             (equal (appeal-structurep (car x))
                    (if x t nil)))
    :rule-classes :forward-chaining)

 (defaxiom appealp-listp-forward-to-appealp-of-car
    (implies (appeal-listp x arity-table)
             (equal (appealp (car x) arity-table)
                    (if x t nil)))
    :rule-classes :forward-chaining)

 (defaxiom appealp-forward-to-appeal-structurep
    (implies (appealp x arity-table)
             (appeal-structurep x))
    :rule-classes :forward-chaining)

 (defaxiom appeal-structure-listp-forward-to-appeal-structure-listp-of-cdr
    (implies (appeal-structure-listp x)
             (appeal-structure-listp (cdr x)))
    :rule-classes :forward-chaining)

 (defaxiom appeal-listp-forward-to-appeal-listp-of-cdr
    (implies (appeal-listp x arity-table)
             (appeal-listp (cdr x) arity-table))
    :rule-classes :forward-chaining)

 (defaxiom appeal-listp-forward-to-appeal-structure-listp
    (implies (appeal-listp x arity-table)
             (appeal-structure-listp x))
    :rule-classes :forward-chaining)

 (defaxiom appeal-structure-listp-forward-to-true-listp
    (implies (appeal-structure-listp x)
             (true-listp x))
    :rule-classes :forward-chaining)

 (defaxiom appeal-listp-when-proofp
    (implies (proof-listp x database arity-table)
             (appeal-listp x arity-table))
    :rule-classes :forward-chaining)

 (defaxiom appealp-when-proofp
    (implies (proofp x database arity-table)
             (appealp x arity-table))
    :rule-classes :forward-chaining)

 (defthm hard-error-in-fc-pair-lst-type-alist
    (implies (and (proof-listp xs database arity-table)
                  (not (consp xs)))
             (equal (proofp (car xs) database arity-table)
                    nil)))
|#

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

  (cond ((null fc-pair-lst) (mv nil type-alist))
        (t (mv-let
            (mbt mbf tta fta ttree)
            (assume-true-false (car (car fc-pair-lst))
                               (cdr (car fc-pair-lst))
                               force-flg nil type-alist ens wrld
                               nil nil :fta)
            (declare (ignore fta))
            (cond (mbf (mv t ttree))
                  (mbt (fc-pair-lst-type-alist (cdr fc-pair-lst)
                                               type-alist
                                               force-flg ens wrld))
                  (t (fc-pair-lst-type-alist (cdr fc-pair-lst)
                                             tta
                                             force-flg ens wrld)))))))

(defun forward-chain (cl pts force-flg do-not-reconsiderp wrld ens
                         oncep-override state)

; We forward chain in all possible ways from clause cl.  We return
; three results.  The first is either t or nil indicating whether a
; contradiction was found.  If so, the second result is nil and the
; third is a ttree that encodes the 'lemmas and literals used (via 'pt
; tags).  If no contradiction is found, the second result is a
; type-alist obtained by assuming false all of the literals of cl
; (this type-alist is fully tagged with 'pt tags) plus all of the
; conclusions derived from forward chaining; the third is a list of
; fc-pairs, each of the form (concl . ttree), where concl is a truth
; derived from some subset of the negations of literals of cl and
; ttree tags the :FORWARD-CHAINING 'lemmas used and all parents (via
; 'pt tags).

; Note: The type-alist returned assumes the falsity of every literal
; in the clause and thus is not suitable for use by rewrite.  We
; return it strictly for the use of setup-simplify-clause-pot-lst
; and bdd-clause.

  (mv-let
   (contradictionp type-alist ttree)
   (type-alist-clause cl (pts-to-ttree-lst pts) nil nil ens wrld
                      nil nil)
   (cond (contradictionp (mv t nil ttree))
         (t (mv-let (contradictionp x)
                    (pstk
                     (forward-chain1 cl
                                     (add-new-fc-pots-lst-lst
                                      cl nil force-flg wrld ens nil)
                                     type-alist force-flg wrld
                                     do-not-reconsiderp ens oncep-override
                                     state nil))
                    (cond (contradictionp

; If a contradiction was found by forward chaining, x is the ttree that
; derives it.  We need to expunge the fc-derivations in x before letting
; it out of the forward-chaining module.

                           (mv t nil (expunge-fc-derivations x)))
                          (t

; If no contradiction was found, x is an fcd-lst.  We need to convert it
; to a list of pairs of the form (concl . ttree), where each ttree is
; expunged of fc-derivations.

                           (let ((fc-pair-lst (fc-pair-lst x)))
                             (mv-let
                              (contradictionp type-alist)
                              (fc-pair-lst-type-alist
                               fc-pair-lst type-alist force-flg ens wrld)
                              (cond
                               (contradictionp
                                (mv t nil type-alist)) ; type-alist is a ttree
                               (t
                                (mv-let
                                 (contradictionp type-alist ttree)
                                 (type-alist-equality-loop
                                  type-alist ens wrld
                                  *type-alist-equality-loop-max-depth*)
                                 (cond
                                  (contradictionp
                                   (mv t nil ttree))
                                  (t
                                   (mv nil type-alist
                                       fc-pair-lst)))))))))))))))

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

; Observe below that we put the forward-chained concls first.  The problem that
; led us to do this was the toy example shown below (extracted from a harder
; failed proof attempt).  The thm below fails if you process the literals in
; the order (append new-clause (cdr tail) lits).
#|
 (defstub p (x) t)
 (defstub r (x) t)
 (defaxiom p->r
  (implies (p x)
           (r x))
  :rule-classes :forward-chaining)
 (defstub my-assoc (name l) t)
 (defaxiom blob
  (implies (r l)
           (or (consp (my-assoc name l))
               (equal (my-assoc name l) nil)))
  :rule-classes :type-prescription)
 (thm
  (implies (p l)
           (or (consp (my-assoc name l))
               (equal (my-assoc name l) nil))))
|#
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

   (let ((current-clause (append lits new-clause (cdr tail))))
     (mv-let (contradictionp type-alist ttree)
       (type-alist-clause
	current-clause
	ttree-lst ; we could extend this with |new-clause|+|(cdr tail)| nils
	nil				; force-flg
	nil				; initial type-alist
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

; However, in an effort to help software archeologists (not to mention
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
; that can get in eachother's way.  If the first is used to add its
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
; term2, use name2 to dervie term3, ..., and use namek to derive term.

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

; Rockwell Addition: The nu-rewriter is applied to literals.  So
; rewrite-atm is changed below.  In addition, we optionally lambda
; abstract the result.  We also clean up in certain ways.  New code
; extends all the way to the defun of rewrite-atm.

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

(defun lambda-abstract1 (vars terms)
  (cond
   ((endp vars) (car terms))
   (t (let* ((body (lambda-abstract1 (cdr vars) (cdr terms)))
             (new-vars (remove1-eq (car vars) (all-vars body))))
        (cons-term (make-lambda (cons (car vars) new-vars)
                                body)
                   (cons (car terms) new-vars))))))

(defun lambda-abstract (term pkg-witness)

; Rockwell Addition:  Non-equivalent read conditionals!

  #-acl2-loop-only ; Rockwell Addition
  (cond (*lambda-abstractp*
         (mv-let (vars terms)
                 (maximal-multiples term pkg-witness)
                 (lambda-abstract1 vars terms)))
        (t term))
  #+acl2-loop-only ; Rockwell Addition
  (mv-let (vars terms)
          (maximal-multiples term pkg-witness)
          (lambda-abstract1 vars terms)))

; We also will clean up certain IF-expressions.

(defun mutually-exclusive-tests (a b)

; We return t if terms (and a b) cannot be true.  We just recognize
; the case where each is (EQUAL x 'constant) for different constants.

  (and (not (variablep a))
       (not (fquotep a))
       (eq (ffn-symb a) 'equal)
       (not (variablep b))
       (not (fquotep b))
       (eq (ffn-symb b) 'equal)
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
   ((and (nvariablep c)
         (not (fquotep c))
         (eq (ffn-symb c) 'IF)
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

(defun all-type-reasoning-tags-p (ttree)
  (cond
   ((null ttree) t)
   ((symbolp (caar ttree))
    (and (or (not (eq (car (car ttree)) 'LEMMA))
             (eq (cadr (car ttree)) :FAKE-RUNE-FOR-TYPE-SET)
             (eq (cadr (car ttree)) :TYPE-PRESCRIPTION))
         (all-type-reasoning-tags-p (cdr ttree))))
   (t (and (all-type-reasoning-tags-p (car ttree))
	   (all-type-reasoning-tags-p (cdr ttree))))))

(defun equal-mod-commuting (x y wrld)

; If this function returns t, then either x and y are the same term, or they
; are provably equal by virtue of the commutativity of their common binary
; function symbol.

; Recall that we do not track the use of equivalence relations; so we do not
; report their use here.  When we do that, read the Note on Tracking
; Equivalence Runes in subst-type-alist1.

  (cond ((variablep x)
	 (eq x y))
        ((variablep y)
         nil)
	((or (fquotep x) (fquotep y))
	 nil) ; quotes are handled elsewhere
	((equal x y)
	 t)
	(t (and (eq (ffn-symb x) (ffn-symb y))
                (equivalence-relationp (ffn-symb x) wrld)
                (equal (fargn x 1) (fargn y 2))
                (equal (fargn x 2) (fargn y 1))))))

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

(defun try-type-set-and-clause (atm ans ttree current-clause wrld ens knownp)

; We are finishing off a call to rewrite-atm on atm that is about to return ans
; with associated ttree.  Ans is *t* or *nil*, but in a context in which this
; would produce a removal of ans rather than a win.  We have found it
; heuristically useful to disallow such removals except when atm is trivially
; known to be true or false.  We return the desired rewritten value of atm and
; associated justifying ttree.

  (mv-let (ts ttree1)
          (type-set atm nil nil nil ens wrld nil nil nil)
          (cond ((ts= ts *ts-nil*)

; Type-set was able to reduce atm to nil, by examining atm in isolation.  This
; would happen, for instance to an atm such as (not (acl2-numberp (+ x y))) or
; (not (consp (cons x y))).  We want to allow such trivial facts to be removed
; from the clause to reduce clutter.  We certainly do not lose anything by
; allowing such removals.

                 (mv *nil* ttree1 nil))
                ((ts-subsetp ts *ts-non-nil*)
                 (mv *t* ttree1 nil))
                ((try-clause atm current-clause wrld)
                 (mv ans ttree nil))
                (t
                 (mv atm nil (and knownp (make-non-nil-ttree ttree)))))))

(mutual-recursion

(defun lambda-subtermp (term)

; We determine whether some lambda-expression is used as a function in term.

  (if (or (variablep term)
          (fquotep term))
      nil
    (or (flambdap (ffn-symb term))
        (lambda-subtermp-lst (fargs term)))))

(defun lambda-subtermp-lst (termlist)
  (if termlist
      (or (lambda-subtermp (car termlist))
          (lambda-subtermp-lst (cdr termlist)))
    nil))

)

(defun rewrite-atm (atm not-flg bkptr gstack type-alist wrld
                        simplify-clause-pot-lst rcnst current-clause state)

; This function rewrites atm with nth-update-rewriter, recursively.  Then it
; rewrites the result with rewrite, in the given context, maintaining iff.

; Note that not-flg is only used heuristically, as it is the responsibility of
; the caller to account properly for it.  Current-clause is also used only
; heuristically.

; It is used to rewrite the atoms of a clause as we sweep across.  It is
; essentially a call of rewrite -- indeed, it didn't exist in Nqthm and rewrite
; was called in its place -- but with a couple of exceptions.  For one thing,
; it first gives type-set a chance to decide things.

; But a more complex exception is that instead of the usual result from
; rewrite, (mv rewritten-atm ttree), we return a third value as well: when
; non-nil, it is a ttree justifying the rewriting of atm to *t* or *nil*
; according to not-flg having value t or nil, respectively.  We use this
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
                             wrld
                             nil)
          (cond

; Before Version  2.6 we had

;           (knownp
;            (cond (nilp (mv *nil* ttree))
;                  (t (mv *t* ttree))))

; but this allowed type-set to remove ``facts'' from a theorem which
; may be needed later.  The following transcript illustrates the previous
; behavior:
#|
 ACL2 !>(defthm fold-consts-in-+
          (implies (and (syntaxp (consp c))
                        (syntaxp (eq (car c) 'QUOTE))
                        (syntaxp (consp d))
                        (syntaxp (eq (car d) 'QUOTE)))
                   (equal (+ c d x)
                          (+ (+ c d) x))))
 ACL2 !>(defthm helper
          (implies (integerp x)
                   (integerp (+ 1 x))))
 ACL2 !>(thm
          (implies (integerp (+ -1/2 x))
                   (integerp (+ 1/2 x)))
          :hints (("Goal" :use ((:instance helper
                                           (x (+ -1/2 x)))))))

 [Note:  A hint was supplied for our processing of the goal above. 
 Thanks!]

 ACL2 Warning [Use] in ( THM ...):  It is unusual to :USE an enabled
 :REWRITE or :DEFINITION rule, so you may want to consider disabling
 (:REWRITE HELPER).


 We now augment the goal above by adding the hypothesis indicated by
 the :USE hint.  The hypothesis can be derived from HELPER via instantiation.
 The augmented goal is shown below.

 Goal'
 (IMPLIES (IMPLIES (INTEGERP (+ -1/2 X))
                   (INTEGERP (+ 1 -1/2 X)))
          (IMPLIES (INTEGERP (+ -1/2 X))
                   (INTEGERP (+ 1/2 X)))).

 By case analysis we reduce the conjecture to

 Goal''
 (IMPLIES (AND (OR (NOT (INTEGERP (+ -1/2 X)))
                   (INTEGERP (+ 1 -1/2 X)))
               (INTEGERP (+ -1/2 X)))
          (INTEGERP (+ 1/2 X))).

 This simplifies, using primitive type reasoning, to

 Goal'''
 (IMPLIES (INTEGERP (+ -1/2 X))
          (INTEGERP (+ 1/2 X))).

 Normally we would attempt to prove this formula by induction.  However,
 we prefer in this instance to focus on the original input conjecture
 rather than this simplified special case.  We therefore abandon our
 previous work on this conjecture and reassign the name *1 to the original
 conjecture.  (See :DOC otf-flg.)

 No induction schemes are suggested by *1.  Consequently, the proof
 attempt has failed.

 Summary
 Form:  ( THM ...)
 Rules: ((:DEFINITION IMPLIES)
         (:DEFINITION NOT)
         (:FAKE-RUNE-FOR-TYPE-SET NIL))
 Warnings:  Use
 Time:  0.03 seconds (prove: 0.02, print: 0.01, other: 0.00)

 ******** FAILED ********  See :DOC failure  ******** FAILED ********
 ACL2 !>
|#

; Note that in the transition from Goal'' to Goal''', the needed
; fact --- (INTEGERP (+ 1 -1/2 X)) --- was removed by type reasoning.
; This is not good.  We now only use type reasoning at this point if
; it will give us a win.

; One might ask why we only disallow type-set from removing facts here.
; Why not elswhere, and what about rewrite?  We do it this way because
; it is only here that the user cannot prevent this removal from
; happening by manipulating the enabled structure.

           ((and knownp not-flg nilp)

; We have reduced the atm to nil but it occurs negated in the
; clause and so we have reduced the literal to t, proving the clause.
; So we report this reduction.

            (mv *nil* ttree nil))
           ((and knownp (not not-flg) (not nilp))
            (mv *t* ttree nil))
           (t
            (mv-let
             (hitp atm1 ttree1)
; Rockwell Addition
             (cond
              ((eq (nu-rewriter-mode wrld) :literals)
               (nth-update-rewriter t atm nil
                                    (access rewrite-constant rcnst
                                            :current-enabled-structure)
                                    wrld state))
              (t (mv nil nil nil)))
             (let ((atm2 (if hitp
                             (lambda-abstract
                              (cleanup-if-expr atm1 nil nil)
                              (pkg-witness (current-package state)))
                           atm)))
               (mv-let (ans1 ans2)
                       (rewrite-entry
                        (rewrite atm2
                                 nil
                                 bkptr)
                        :rdepth (rewrite-stack-limit wrld)
                        :type-alist type-alist
                        :obj '?
                        :geneqv *geneqv-iff*
                        :wrld wrld
                        :fnstack nil
                        :ancestors nil
                        :backchain-limit (access rewrite-constant rcnst
                                                 :backchain-limit-rw)
                        :simplify-clause-pot-lst simplify-clause-pot-lst
                        :rcnst rcnst
                        :gstack gstack
                        :ttree (if hitp ttree1 nil))

; But we need to do even more work to prevent type-set from removing
; ``facts'' from the goal.  Here is another (edited) transcript:

#|
 ACL2 !>(defun foo (x y)
   (if (acl2-numberp x)
       (+ x y)
     0))

 ACL2 !>(defthm foo-thm
   (implies (acl2-numberp x)
            (equal (foo x y)
                   (+ x y))))
 ACL2 !>(in-theory (disable foo))
 ACL2 !>(thm
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (equal (foo x y) x))
           (equal y 0)))

 This simplifies, using the :type-prescription rule FOO, to

 Goal'
 (IMPLIES (AND (ACL2-NUMBERP Y)
               (EQUAL (FOO X Y) X))
          (EQUAL Y 0)).

 Name the formula above *1.

 No induction schemes are suggested by *1.  Consequently, the proof
 attempt has failed.

 Summary
 Form:  ( THM ...)
 Rules: ((:TYPE-PRESCRIPTION FOO))
 Warnings:  None
 Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)

 ******** FAILED ********  See :DOC failure  ******** FAILED ********
|# ; |

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

#|
 (thm
  (implies (and (acl2-numberp y)
                (equal (foo x y) x)
                (acl2-numberp x))
           (equal y 0)))
|# ;|

; does succeed, since the (acl2-numberp x) hypothesis now appears after the
; (equal (foo x y) x) hypothesis, hence does not get removed until after it has
; been used to relieve the hypothesis of foo-thm.  This kind of situation in
; which a proof succeeds or fails depending on the order of hypotheses really
; gets Robert's goat.

		 (cond ((not (or (equal ans1 *nil*)
                                 (equal ans1 *t*)))

; We have, presumably, not removed any facts, so we allow this rewrite.

                        (mv ans1 ans2 (and knownp *trivial-non-nil-ttree*)))
                       ((and (nvariablep atm2)
                             (not (fquotep atm2))
                             (equivalence-relationp (ffn-symb atm2)
                                                    wrld))

; We want to blow away equality (and equivalence) hypotheses, because for
; example there may be a :use or :cases hint that is intended to blow away (by
; implication) such hypotheses.

                        (mv ans1 ans2 nil))
                       ((equal ans1 (if not-flg *nil* *t*))

; We have proved the original literal from which atm is derived; hence we have
; proved the clause.  So we report this reduction.

                        (mv ans1 ans2 nil))
                       ((all-type-reasoning-tags-p ans2)

; Type-reasoning alone has been used, so we are careful in what we allow.

			(cond ((lambda-subtermp atm2)

; We received an example from Jared Davis in which a hypothesis of the form
; (not (let ...)) rewrites to true with a tag tree of nil, and hence was kept
; without this lambda-subtermp case.  The problem with keeping that hypothesis
; is that it has calls of IF in a lambda body, which do not get eliminated by
; clausification -- and this presence of IF terms causes the :force-info field
; to be set to 'weak in the rewrite constant generated under simplify-clause.
; That 'weak setting prevented forced simplification from occurring that was
; necessary in order to make progress in Jared's proof!

; A different solution would be to ignore IF calls in lambda bodies when
; determining whether to set :force-info to 'weak.  However, that change caused
; a regression suite failure: in books/symbolic/tiny-fib/tiny-rewrites.lisp,
; theorem next-instr-pop.  The problem seemed to be premature forcing, of just
; the sort we are trying to prevent with the above-mentioned check for IF
; terms.

; Robert Krug points out to us, regarding the efforts here to keep hypotheses
; that rewrote to true, that for him the point is simply not to lose Boolean
; hypotheses like (acl2-numberp x) in the example above.  Certainly we do not
; expect terms with lambda calls to be of that sort, or even to make any sorts
; of useful entries in type-alists.  If later we find other reasons to keep *t*
; or *nil*, we can probably feel comfortable in adding conditions as we have
; done with the lambda-subtermp test above.

                               (mv ans1 ans2 nil))
                              ((eq (fn-symb atm2) 'implies)

; We are contemplating throwing away the progress made by the above call of
; rewrite.  However, we want to keep progress made by expanding terms of the
; form (IMPLIES x y), so we do that expansion (again) here.  It seems
; reasonable to keep this in sync with the corresponding use of subcor-var in
; rewrite.

                               (try-type-set-and-clause
                                (subcor-var (formals 'implies wrld)
                                            (list (fargn atm2 1)
                                                  (fargn atm2 2))
                                            (body 'implies t wrld))
                                ans1 ans2 current-clause wrld
                                (access rewrite-constant rcnst
                                        :current-enabled-structure)
                                knownp))
			      (t

; We make one last effort to allow removal of certain ``trivial'' facts from
; the goal.

			       (try-type-set-and-clause
                                atm2
                                ans1 ans2 current-clause wrld
                                (access rewrite-constant rcnst
                                        :current-enabled-structure)
                                knownp))))
		       (t
			(mv ans1 ans2 nil))))))))))

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
; new old genequv term ens wrld state ttree) will remove all occurrences of old
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
; when they are suffed with constants, then these cases will not arise and all
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
; and the old admotion against using (equal (foo b) 'evg).  Here we find [1]
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
;     (cons pt pt-lst)              ; add lit's parent tnree to pt-lst
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

(defun get-and-delete-tag-in-ttree (tag ttree)

; Return (mv val new-ttree), where val is a non-nil value associated with tag
; in ttree and new-ttree is the result of removing that association.  Except,
; if tag is not associated with a non-nil value in ttree, then return (mv nil
; ttree).  We avoid unnecessary consing.

  (cond ((null ttree) (mv nil nil))
        ((and (eq tag (caar ttree))
              (caar ttree))
         (mv (cdar ttree) (cdr ttree)))
        ((symbolp (caar ttree))
         (mv-let (val cdr-ttree)
                 (get-and-delete-tag-in-ttree tag (cdr ttree))
                 (cond (val (mv val (cons (car ttree) cdr-ttree)))
                       (t (mv nil ttree)))))
        (t (mv-let
            (val car-ttree)
            (get-and-delete-tag-in-ttree tag (car ttree))
            (cond (val (mv val (cons car-ttree (cdr ttree))))
                  (t (mv-let
                      (val cdr-ttree)
                      (get-and-delete-tag-in-ttree tag (cdr ttree))
                      (cond (val (mv val (cons (car ttree) cdr-ttree)))
                            (t (mv nil ttree))))))))))

(defun add-binding-to-tag-tree (var term ttree)

; Note that var need not be a variable; see the call in fertilize-clause1.

  (let ((tag 'binding-lst)
        (binding (cons var term)))
    (mv-let (lst ttree)
            (get-and-delete-tag-in-ttree tag ttree)

; The following is just (add-to-tag-tree tag (cons binding lst) ttree), but
; optimized so that we don't waste time calling tag-tree-occur, since we know
; that the tag does not occur in tttree, as binding-lst occurs at most once in
; the input ttree.

            (cons (cons tag (cons binding lst)) ttree))))

(defun subst-equiv-and-maybe-delete-lit
  (equiv new old n cl i pt-lst delete-flg ens wrld state ttree)

; Substitutes new for old (which are equiv) in every literal of cl (maintaining
; iff) except the nth one.  The nth literal is deleted if delete-flg is t and
; is skipped but included in the if delete-flg is nil.  Pt-lst is in 1:1
; correspondence with cl.  We return the new clause, a new pt-lst and a ttree
; recording the congruence and executable counterpart rules used.  It is
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

(defun remove-trivial-equivalences
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
              (remove-trivial-equivalences new-cl new-pt-lst remove-flg
                                           ens wrld state
                                           ttree t
                                           (cons lit avoid-lst))))
     (t (mv hitp cl pt-lst ttree)))))

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

(defrec built-in-clause ((nume . all-fnnames) clause . rune) t)

; Note:  The :all-fnnames field must be set as it would be by
; all-fnnames-subsumer.  This setting cannot be done automatically because we
; do not know the initial world until we have set up the built-in-clauses.  But
; we do check, with chk-initial-built-in-clauses which is called and reported
; in check-built-in-constants, that the setting below is correct for the actual
; initial world.  When adding new records, it is best to use
; (all-fnnames-subsumer cl (w state)) to get the :all-fnnames field below.

;; RAG - I changed the clauses about e0-ord-< [v2-8 and beyond: o<] reducing on
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
  (cond ((null bic-lst) nil)
        ((and (enabled-numep (access built-in-clause (car bic-lst) :nume)
                             ens)
              (subsetp-eq (access built-in-clause (car bic-lst) :all-fnnames)
                          fns)
              (eq (subsumes *init-subsumes-count*
                            (access built-in-clause (car bic-lst) :clause)
                            cl nil)
                  t))
         (access built-in-clause (car bic-lst) :rune))
        (t (built-in-clausep2 (cdr bic-lst) cl fns ens))))
                         
(defun built-in-clausep1 (bic-alist cl fns ens)

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

                             zerop plusp minusp listp mv-list return-last
                             wormhole-eval force case-split double-rewrite)
                           atm)
                (possible-trivial-clause-p (cdr cl))))))

(defun trivial-clause-p (cl wrld)
  (or (member-equal *t* cl)
      (and (possible-trivial-clause-p cl)
           (tautologyp (disjoin cl) wrld))))

(defun built-in-clausep (cl ens match-free-override wrld state)

; We return two results.  The first indicates whether cl is a ``built
; in clause,'' i.e., a known truth.  The second is the supporting
; ttree (or nil).  This ttree is guaranteed to be assumption-free.

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
     (t (mv-let (contradictionp type-alist ttree)
                (forward-chain cl
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
                      ((tagged-object 'assumption ttree)
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
                                                 ens wrld state ttree nil nil)

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

(defun strip-non-rewrittenp-assumptions (ttree ans)

; Copy ttree and strip out all 'assumption records that have :rewrittenp nil.
; Accumulate those unrewritten records onto ans.  Return (mv ttree' ans').

; Picky Note: Some of the conses below are used in place of the official tag
; tree constructors, e.g., (add-to-tag-tree 'assumption & &) and
; (cons-tag-trees & &).  See the picky note in set-cl-ids-in-assumptions.

  (cond
   ((null ttree) (mv nil ans))
   ((symbolp (caar ttree))
    (cond
     ((eq (caar ttree) 'assumption)
      (cond
       ((not (access assumption (cdar ttree) :rewrittenp))
        (strip-non-rewrittenp-assumptions (cdr ttree)
                                          (cons (cdar ttree) ans)))
       ((tagged-object 'assumption (cdr ttree))
        (mv-let (ttree2 ans)
                (strip-non-rewrittenp-assumptions (cdr ttree) ans)
                (mv (cons (car ttree) ttree2) ans)))
       (t (mv ttree ans))))
     ((tagged-object 'assumption (cdr ttree))
      (mv-let (ttree2 ans)
              (strip-non-rewrittenp-assumptions (cdr ttree) ans)
              (mv (cons (car ttree) ttree2) ans)))
     (t (mv ttree ans))))
   ((tagged-object 'assumption ttree)
    (mv-let (ttree1 ans)
            (strip-non-rewrittenp-assumptions (car ttree) ans)
            (mv-let (ttree2 ans)
                    (strip-non-rewrittenp-assumptions (cdr ttree) ans)
                    (mv (cons-tag-trees ttree1 ttree2) ans))))
   (t (mv ttree ans))))

(defun assumnote-list-to-token-list (assumnote-list)
  (if (null assumnote-list)
      nil
    (cons (access assumnote (car assumnote-list) :rune)
          (assumnote-list-to-token-list (cdr assumnote-list)))))

(defun resume-suspended-assumption-rewriting1
  (assumptions ancestors gstack simplify-clause-pot-lst rcnst wrld state
               ttree)

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
   ((null assumptions) (mv nil ttree))
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
; assumed true).  Doesn't that mean we coul rewrite term to nil?  No.  All we
; really know is that term is impossible to prove by rewriting using whatever
; lemmas we did this time.  Term might be provable.  Consider the fact that
; the user could have proved (implies term term) for any term, even a provable
; one.  Then in trying to prove term we'd assume it false by putting (not term)
; on ancestors and backchain to term, which would lead us here, with the
; complement of term on ancestors.  That doesn't mean term can't be proved!

           (resume-suspended-assumption-rewriting1
              (cdr assumptions)
              ancestors gstack simplify-clause-pot-lst rcnst
              wrld state
              (if assumed-true
                  ttree
                  (cons (cons 'assumption
                              (change assumption assn
                                      :rewrittenp term))
                        ttree))))
          (t

; We are about to rewrite term, just as in relieve-hyp, and so we add its
; negation to ancestors.  This is equivalent to assuming term false.

           (let ((new-ancestors
                  (push-ancestor (dumb-negate-lit term)
                                 (assumnote-list-to-token-list
                                  (access assumption assn :assumnotes))
                                 ancestors)))
             (mv-let
              (not-flg atm)
              (strip-not term)
              (mv-let
               (val ttree1)
               (rewrite-entry (rewrite atm nil 'forced-assumption)
                              :rdepth (rewrite-stack-limit wrld)
                              :type-alist (access assumption assn :type-alist)
                              :obj '?
                              :geneqv *geneqv-iff*
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

                   (mv assn (cons-tag-trees ttree1 ttree)))
                  (t

; If term rewrote to non-nil, we must process the unrewritten assumptions in
; the ttree, ttree1, produced by rewriting term.  We do that with a separate
; recursive call of this function, because we must pass in the new-ancestors so
; that we don't loop.  Think of us as having assumed term false, rewritten it
; while making certain assumptions, and now -- still in that context of having
; assumed it false -- we will work on those assumptions.

                   (mv-let
                    (ttree1 assumptions1)
                    (strip-non-rewrittenp-assumptions ttree1 nil)

; Observe that if ttree1 contains any assumptions, they are of the rewrittenp t
; variety.  We accumulate ttree1 into our answer ttree.  Unless term rewrote to
; t, we accumulate the rewritten version of assn into our answer.  Note that
; since the :geneqv used above is iff, we can rely on the fact that if val is
; known not to be nil then it is actually t.  Finally, we rewrite all of the
; unrewritten assumptions (assumptions1) generated by rewriting term to val
; accumulate them into our answer as well.

                    (mv-let
                     (bad-ass ttree)
                     (resume-suspended-assumption-rewriting1
                      assumptions1
                      new-ancestors ; the critical difference
                      gstack simplify-clause-pot-lst rcnst
                      wrld state
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
                      (bad-ass (mv bad-ass ttree))
                      (t

; Having taken care of assn and all the unrewritten assumptions generated when
; we rewrote it, we now do the rest of assumptions.

                       (resume-suspended-assumption-rewriting1
                        (cdr assumptions)
                        ancestors gstack simplify-clause-pot-lst rcnst
                        wrld state
                        ttree))))))))))))))))))

(defun resume-suspended-assumption-rewriting
  (ttree ancestors gstack simplify-clause-pot-lst rcnst wrld state)

; We copy ttree and rewrite all the non-rewrittenp assumptions in it, deleting
; any thus established.  We return (mv bad-ass ttree'), where bad-ass is either
; nil or an assumption in ttree whose :term can be rewritten to nil.  Ttree' is
; an extension of the result of removing all non-rewrittenp assumptions from
; ttree and then replacing them by their rewritten versions plus the ttrees
; produced by that rewriting.  There are no non-rewrittenp assumptions in
; ttree'.

  (mv-let (ttree assumptions)
          (strip-non-rewrittenp-assumptions ttree nil)
          (resume-suspended-assumption-rewriting1
           assumptions
           ancestors gstack simplify-clause-pot-lst rcnst wrld state
           ttree)))

(defun cons-into-ttree (ttree1 ttree2)
  (cond
   ((null ttree1) ttree2)
   ((symbolp (caar ttree1))
    (if (tag-tree-occur (caar ttree1) (cdar ttree1) ttree2)
        (cons-into-ttree (cdr ttree1)
                         ttree2)
      (cons-into-ttree (cdr ttree1)
                       (cons (car ttree1) ttree2))))
   (t (cons-into-ttree (cdr ttree1)
                       (cons-into-ttree (car ttree1) ttree2)))))

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
     (cw "~%~%Helpful Little Message:  The simplifier is now expected ~
          to produce approximately ~n0 subgoals.  ~
          See :DOC case-split-limitations.~%~%"
         ecnt)
     ecnt))
   (t ecnt)))

(mutual-recursion

(defun rewrite-clause (tail pts bkptr gstack new-clause fc-pair-lst wrld
                            simplify-clause-pot-lst
                            rcnst flg ecnt ans ttree fttree state)

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
; and it is ultimately returned and is the length of of ans.  Fttree (``false
; tag tree'') is either nil or else is a non-nil tag tree justifying the
; falsity of every literal in new-clause; see the comment in rewrite-atm about
; the third argument returned by that function.  Note that it is always legal
; to return the false clause in place of any other clause, so our use of fttree
; is clearly sound.

; We return 4 values: a flag indicating whether anything was done, the
; final ecnt, a set, ans, of clauses whose conjunction implies cl
; under our assumptions, and a ttree that describes what we did.  Our
; answers are accumulated onto flg, ecnt, ans, and ttree as we recur
; through the literals of tail.

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
        (mv t (- ecnt 1) ans (push-lemma rune ttree)))
       ((and fttree

; Avoid considering it a "change" to rewrite the empty (false) clause to
; itself.  Note that we already know (null tail) in this context.

             (not (and (null ans)
                       (null new-clause))))
        (mv t
            1
            (list *false-clause*)
            (cons-tag-trees fttree ttree)))
       (t (mv flg ecnt (cons new-clause ans) ttree)))))
   (t
    (mv-let
     (not-flg atm)
     (strip-not (car tail))
     (let* ((new-pts (cons (car pts)
                           (access rewrite-constant rcnst :pt)))
            (local-rcnst
             (change rewrite-constant rcnst
                     :pt
                     new-pts
                     :current-literal
                     (make current-literal
                           :not-flg not-flg
                           :atm atm)))
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
          (mv t
              (- ecnt 1)
              ans
              (cons-tag-trees ttree0 ttree)))
         (t
          (mv-let
           (val ttree1 fttree1)

; Note: Nqthm used a call of (rewrite atm ...) here, while we now look on the
; type-alist for atm and then rewrite.  See the Nqthm note below.

; Note: Here is our ``short circuit'' implementation of case limit
; interpretation (2).  We just bail out if we have exceeded the case
; limit.

           (if (and case-limit
                    (> ecnt case-limit))
               (mv atm
                   (add-to-tag-tree 'case-limit t nil)
                   nil)
             (pstk
              (rewrite-atm atm not-flg bkptr gstack type-alist wrld
                           simplify-clause-pot-lst local-rcnst
			   current-clause state)))
           (let* ((val (if not-flg
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
             (mv-let
              (bad-ass ttree1)
              (resume-suspended-assumption-rewriting
               ttree1
               nil ;ancestors - the fact that this isn't what it was when
                   ;we pushed the assumption could let rewriting go deeper
               gstack
               simplify-clause-pot-lst
               local-rcnst
               wrld
               state)
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
                                      state)))

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
                                        ttree
                                      (cons-into-ttree ttree1 ttree))
                                    (and fttree1
                                         fttree
                                         (cons-tag-trees fttree1 fttree))
                                    state))))))))))))))

(defun rewrite-clause-lst (segs bkptr gstack cdr-tail cdr-pts new-clause fc-pair-lst
                                wrld simplify-clause-pot-lst
                                rcnst flg ecnt ans ttree fttree state)

; Fttree is either nil or else is a tag tree justifying the falsity of every
; literal in segs and every literal in new-clause; see the comment in
; rewrite-atm about the third argument returned by that function.

  (cond ((null segs)
         (mv flg ecnt ans ttree))
        (t
         (mv-let (flg1 ecnt1 ans1 ttree1)
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
                               state)
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
                                   state))))))

)

; After removing trivial equations, simplify-clause must set up
; the context in which the rewriting of the clause is done.  This
; mainly means setting up the simplify-clause-pot-lst.

(defun setup-simplify-clause-pot-lst1 (cl ttrees type-alist rcnst wrld state)
  (mv-let (contradictionp simplify-clause-pot-lst)
          (let ((gstack (initial-gstack 'setup-simplify-clause-pot-lst
                                        nil cl)))
            (rewrite-entry
             (add-terms-and-lemmas cl ;term-lst to assume
                                   ttrees ;corresponding tag trees
                                   nil ;positivep (terms assumed false)
                                   )
             :rdepth (rewrite-stack-limit wrld)
             :type-alist type-alist
             :obj nil
             :geneqv nil
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
            (mv contradictionp nil))
           (t
            #-acl2-loop-only (dmr-flush t)
            (mv nil simplify-clause-pot-lst)))))

(defun setup-simplify-clause-pot-lst (cl ttrees fc-pair-lst
                                      type-alist rcnst wrld state)

; We construct the initial value of the simplify-clause-pot-lst in
; preparation for rewriting clause cl.  We assume rcnst contains the
; user's hint settings, the correct top-clause and current clause, and a
; null :pt.

; We return two values.  If the first is non-nil it indicates that we
; have proved cl and the other value is irrelevant.  In the case that we
; prove clause the first result is a poly, meaning it was proved by
; linear arithmetic.  The assumptions in the ttree of that poly must be
; considered before cl is declared proved.  When the first answer is nil
; the second is the constructed simplify-clause-pot-lst.

; As of Version_2.8, we start by adding the (negations of) any
; forward-chaining conclusions to the head of cl and the corresponding
; ttrees to ttrees.  We then call the original
; setup-simplify-clause-pot-lst on the resultant expanded clause.
; This will allow us to use forward-chaining conclusions in linear
; arithmetic.

; Here is one example of why we might want to do this:
#|
 (defun bytep (n)
   (and (integerp n)
        (<= -128 n)
        (< n 128)))

 (defthm bytep-thm
   (implies (and (integerp n)
                 (<= -128 n)
                 (< n 128))
            (bytep n)))

 (defthm bytep-fc-thm
   (implies (bytep n)
            (and (integerp n)
                 (<= -128 n)
                 (< n 128)))
   :rule-classes :forward-chaining)

 (in-theory (disable bytep))

 (defthm tricky
  (implies (and (bytep n)
                (bytep (+ 7 n)))
           (bytep (+ 3 n))))
|#
; Before linear arithmetic used the conclusions of forward-chaining
; rules, one would have to re-enable the definition of bytep in order
; to prove tricky.  But if this appeared in a larger context, in which
; one had proved a bunch of lemmas about bytep, one could find oneself
; in a pickle.  By enabling bytep, one loses the ability to use all
; the lemmas about it.  Without enabling bytep, tricky is hard to
; prove.
;
; And here is another example:
#|
 (defun bvecp (x n)
   (and (integerp x) 
        (<= 0 x) 
        (< x (expt 2 n))))

 (defthm bvecp-2-<-4
          (implies (bvecp x 2)
                   (and (integerp x)
                        (<= 0 x)
                        (< x 4)))
   :rule-classes :forward-chaining)

 (in-theory (disable bvecp))

 (thm (implies (and (bvecp x 2)
                    (not (equal x 0))
                    (not (equal x 1))
                    (not (equal x 2)))
               (equal x 3)))
|#

  (cond ((null fc-pair-lst)
         (setup-simplify-clause-pot-lst1 cl ttrees type-alist rcnst wrld state))
        (t
         (setup-simplify-clause-pot-lst (cons (dumb-negate-lit
                                               (caar fc-pair-lst)) cl)
                                        (cons (cdar fc-pair-lst) ttrees) 
                                        (cdr fc-pair-lst)
                                        type-alist rcnst wrld state))))

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
 
  #|
  (defstub bar (x) t)

  (thm (implies (and (rationalp a)(rationalp b)(rationalp c)
                     (<= a b) (<= b a)
                     (<= b c) (<= c b))
                (equal (bar a) (bar c))))
  |#

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
             (cdr (tagged-object 'clause-id (access history-entry (car hist)
                                                    :ttree)))))
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

(defun simplify-clause1 (top-clause hist rcnst wrld state)

; In Nqthm, this function was called SIMPLIFY-CLAUSE0.

; Top-clause is a clause with history hist.  We assume that rcnst has
; a null pt and contains whatever hint settings the user
; wants in it, as well as the :force-info based on whether there is a
; call of IF in top-clause.

; We return 3 values.  The first indicates whether we changed top-clause and,
; if so, whether we went through the rewriter; it will help determine signal
; returned by simplify-clause (and hence will be used, ultimately, to create
; the 'simplify-clause hist entry).  If we did not change top-clause, the
; second and third are nil.  If we did change top-clause, the second is a list
; of new clauses whose conjunction implies top-clause and the third is a ttree
; explaining what we did.  This ttree will be used to create the
; 'simplify-clause hist entry.

  (mv-let (hitp current-clause pts remove-trivial-equivalences-ttree)
          (remove-trivial-equivalences top-clause
                                       nil
                                       t
                                       (access rewrite-constant rcnst
                                               :current-enabled-structure)
                                       wrld state nil nil nil)
          (declare (ignore pts))
          (let ((local-rcnst (change rewrite-constant rcnst
                                     :top-clause top-clause
                                     :current-clause current-clause))
                (current-clause-pts (enumerate-elements current-clause 0)))
            (mv-let
             (contradictionp type-alist fc-pair-lst)
             (forward-chain current-clause
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

               (mv 'hit
                   nil
                   (cons-tag-trees remove-trivial-equivalences-ttree
                                   fc-pair-lst)))
              (t

; We next construct the initial simplify-clause-pot-lst.
; The construction might prove current-clause, in which case the
; contradictionp answer is non-nil.

               (mv-let
                (contradictionp simplify-clause-pot-lst)
                (pstk
                 (setup-simplify-clause-pot-lst current-clause
                                                (pts-to-ttree-lst 
                                                 current-clause-pts)
                                                fc-pair-lst
                                                type-alist
                                                local-rcnst wrld state))
                (cond
                 (contradictionp

; A non-nil contradictionp is a poly meaning linear proved current-clause
; (modulo the assumptions in the tag tree of the poly).

                  (mv 'hit
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
                        wrld state ttree nil nil))
                      (declare (ignore pts hitp))
                      (mv 'hit
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

                     (mv-let
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
                                      state)
                      (declare (ignore ecnt))
                      (cond
                       ((null flg)
                        #-acl2-loop-only (dmr-flush t)
                        (mv-let
                         (pos unhidden-lit old-cl-id)
                         (unhidden-lit-info hist top-clause 0 wrld)
                         (cond (pos (let ((tail (nthcdr (1+ pos) top-clause)))
                                      (mv 'hit-rewrite
                                          (list (append (take pos top-clause)
                                                        (cons unhidden-lit
                                                              tail)))
                                          (add-to-tag-tree
                                           'hyp-phrase
                                           (tilde-@-hyp-phrase (len tail)
                                                               top-clause)
                                           (add-to-tag-tree
                                            'clause-id old-cl-id
                                            (push-lemma (fn-rune-nume 'hide nil
                                                                      nil wrld)
                                                        nil))))))
                               (t (mv nil ans ttree)))))
                       (t
                        #-acl2-loop-only (dmr-flush t)
                        (mv 'hit-rewrite ans ttree))))))))))))))))

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
  ((rewrite-constant induction-hyp-terms . induction-concl-terms)
   (tag-tree . hint-settings)
   (pool . gag-state)
   user-supplied-term displayed-goal orig-hints . otf-flg)
  t)

; The orig-hints setting is the list of clause-ids and hint-settings
; supplied to prove.  The hint-settings is the particular hint
; settings for the current clause.  The only reason we have the
; orig-hints field is so that we can compute the hints appropriate for
; the top-level goal if we have to abandon the initial work and revert
; to the user-supplied term.

(defrec gag-info

; This record corresponds to a key checkpoint, but not necessarily the active
; checkpoint.  Suppose for example we see a goal that is hit by an elim before
; any other checkpoint.  Then we push an instance of this record on the
; appropriate stack.  When a goal is pushed for induction and this record is
; for the active checkpoint, then we add the clause-id and pool-lst for that
; goal.

  (clause-id ; could be nil
   clause    ; nil iff clause-id is nil
   .         ; list of pairs (clause-id . pool-lst); see above
   pushed
   )
  t)

(defrec gag-state
  ((top-stack . sub-stack)  ; each a list of gag-info records
   (active-cl-id            ; for active key checkpoint if any, else nil
    . active-printed-p)     ; true when active key checkpoint has been printed
   forcep                   ; true after next forcing round has been announced
   . abort-stack)           ; the top-stack when aborting
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
        :orig-hints nil
        :pool nil
        :gag-state *initial-gag-state*
        :user-supplied-term *t*
        :displayed-goal nil
        :otf-flg nil))

(defun filter-disabled-expand-terms (terms ens wrld)

; We build expand hint strucures, throwing certain terms out of terms.
; Variables and constants are kept (but they should never be there).  Lambda
; applications are kept.  Function symbol applications are kept provided the
; symbol has a non-nil, enabled def-body.  There is no point in keeping on
; :expand-lst a term whose function symbol has no def-body, because it
; there that we go when we decide to force an expansion (from other than
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
           (let ((def-body (def-body (ffn-symb (car terms)) wrld)))
             (cond
              ((and def-body
                    (enabled-numep (access def-body def-body :nume)
                                   ens))
               (cons (make expand-hint
                           :pattern (car terms)
                           :alist :none
                           :rune (access def-body def-body :rune)
                           :equiv 'equal
                           :hyp (access def-body def-body :hyp)
                           :lhs (cons-term (ffn-symb (car terms))
                                           (access def-body def-body
                                                   :formals))
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

(defabbrev append? (x y)
  (cond ((null y) x)
        (t (append x y))))

(defun simplify-clause (cl hist pspv wrld state)

; Warning: Keep this in sync with function simplify-clause-rcnst defined in
; books/misc/computed-hint-rewrite.lisp.

; This is the first "clause processor" of the waterfall.  Its input and
; output spec is consistent with that of all such processors.  See the
; waterfall for a general discussion.

; Cl is a clause with history hist.  We can obtain a rewrite-constant
; from the prove spec var pspv.  We assume nothing about the
; rewrite-constant except that it has the user's hint settings in it
; and that the pt is nil.  We install our top-clause and
; current-clause when necessary.

; We return 4 values.  The first is a signal that in general is 'miss,
; 'abort, 'error, or a "hit".  In this case, it is always either 'miss
; or one of 'hit, 'hit-rewrite, or 'hit-rewrite2 (as described further
; below).  When the signal is 'miss, the other 3 values are
; irrelevant.  When the signal is 'hit, the second result is the list
; of new clauses, the third is a ttree that will become that component
; of the history-entry for this simplification, and the fourth is the
; unmodified pspv.  (We return the fourth thing to adhere to the
; convention used by all clause processors in the waterfall (q.v.).)

; If the first result is a "hit" then the conjunction of the new
; clauses returned implies cl.  Equivalently, under the assumption
; that cl is false, cl is equivalent to the conjunction of the new
; clauses.

; On Tail Biting by Simplify-clause:

; Tail biting can occur at the simplify-clause level, i.e., we can
; return a set of clauses that is a generalization of the clause cl,
; e.g., a set whose conjunction is false even though cl is not.  This
; is because of the way we manage the simplify-clause-pot-lst and
; pts.  We build a single pot-lst and use parent trees to
; render inactive those polys that we wish to avoid.  To arrange to
; bite our own tail, put two slightly different versions of the same
; inequality literal into cl.  The poly arising from the second can be
; used to rewrite the first and the poly arising from first can be used
; to rewrite the second.  If the first rewrites to false immediately our
; use of parent trees (as arranged by passing local-rcnst to the recursive
; call of rewrite-clause in rewrite-clause) will wisely prevent the use of
; its poly while rewriting the second.  But if the first rewrites to some
; non-linear term (which will be rewritten to false later) then we'll
; permit ourselves to use the first's poly while working on the second
; and we could bite our tail.

; This would not happen if we produced a new linear pot-lst for each
; literal -- a pot-lst in which the literal to be rewritten was not
; assumed false.  Early experiments with that approach led us to
; conclude it was too expensive.

; If the specification of rewrite is correct, then tail biting cannot
; happen except via the involvement of linear arithmetic.  To see this,
; consider the assumptions governing the rewriting of each literal in the
; clause and ask whether the literal being rewritten in in rewrite-clause
; is assumed false via any of those assumptions.  There are five sources
; of assumptions in the specification of rewrite: (a) the type-alist
; (which is constructed so as to avoid that literal), (b) the assumptions
; in ancestors (which is initially empty), (c) the assumptions in the
; pot-lst (which we are excepting), and (d) 'assumptions in ttree
; (which we are excepting).  Thus, the only place that assumption might
; be found is simplify-clause-pot-lst.  If linear is eliminated, the only
; assumptions left are free of the literal being worked on.

; This is really an interface function between the rewriter and the rest of
; the prover.  It has three jobs.

; The first is to convert from the world of pspv to the world of
; rcnst.  That is, from the package of spec vars passed around in the
; waterfall to the package of constants known to the rewriter.

; The second job of this function is to control the expansion of the
; induction-hyp-terms and induction-concl terms (preventing the
; expansion of the former and forcing the expansion of the latter) by
; possibly adding them to terms-to-be-ignored-by-rewrite and
; expand-lst, respectively.  This is done as part of the conversion
; from pspv (where induction hyps and concl are found) to rcnst (where
; terms-to-be-ignored-by-rewrite and expand-lst are found).  They are
; so controlled as long as we are in the first simplification stages
; after induction.  As soon as the clause has gone through the
; rewriter with some change, with input free of induction-concl-terms,
; we stop interfering.  The real work horse of clause level
; simplification is simplify-clause1.

; The third job is to convert the simplify-clause1 answers into the
; kind required by a clause processor in the waterfall.  The work
; horse doesn't return an pspv and we do.

 (prog2$
  (initialize-brr-stack state)
  (cond ((assoc-eq 'settled-down-clause hist)

; The clause has settled down under rewriting with the
; induction-hyp-terms initially ignored and the induction-concl-terms
; forcibly expanded.  In general, we now want to stop treating those
; terms specially and continue simplifying.  However, there is a
; special case that will save a little time.  Suppose that the clause
; just settled down -- i.e., the most recent hist entry is the one we
; just found.  And suppose that none of the specially treated terms
; occurs in the clause we're to simplify.  Then we needn't simplify it
; again.

         (cond ((and (eq 'settled-down-clause
                         (access history-entry (car hist) :processor))
                     (not (some-element-dumb-occur-lst
                           (access prove-spec-var
                                   pspv
                                   :induction-hyp-terms)
                           cl)))

; Since we know the induction-concl-terms couldn't occur in the clause
; -- they would have been expanded -- we are done.  (Or at least: if
; they do occur in the clause, then still, removing them from the
; expand-lst should not help the rewriter!)  This test should speed up
; base cases and preinduction simplification at least.

                (mv 'miss nil nil nil))
               (t

; We now cease interfering and let the heuristics do their job.

                (mv-let (changedp clauses ttree)
                        (simplify-clause1
                         cl hist
                         (change rewrite-constant
                                 (access prove-spec-var pspv
                                         :rewrite-constant)
                                 :force-info
                                 (if (ffnnamep-lst 'if cl)
                                     'weak
                                   t))
                         wrld
                         state)
                        (cond (changedp

; Note: It is possible that our input, cl, is a member-equal of our
; output, clauses!  Such simplifications are said to be "specious."
; But we do not bother to detect that here because we want to report
; the specious simplification as though everything were ok and then
; pretend nothing happened.  This gives the user some indication of
; where the loop is.  In the old days, we just signalled a 'miss if
; (member-equal cl clauses) and that caused a lot of confusion among
; experienced users, who saw simplifiable clauses being passed on to
; elim, etc.  See :DOC specious-simplification.

                               (mv 'hit clauses ttree pspv))
                              (t (mv 'miss nil nil nil)))))))
        (t

; The clause has not settled down yet.  So we arrange to ignore the
; induction-hyp-terms when appropriate, and to expand the
; induction-concl-terms without question.  The local-rcnst created
; below is not passed out of this function.

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

; We have previously passed through the rewriter, and either a
; predecessor goal or this one is free of induction-concl-terms.  In
; that case we stop meddling with the rewriter by inhibiting rewriting
; of induction-hyp-terms and forcing expansion of
; induction-concl-terms.  Before Version_2.8 we waited until
; 'settled-down-clause before ceasing our meddling.  However, Dave
; Greve and Matt Wilding reported an example in which that heuristic
; slowed down the prover substantially by needlessly delaying the
; rewriting of induction-hyp-terms.  Notice that this heuristic nicely
; matches the induction heuristics: both consider only the goal, not
; the result of rewriting it.  (We however ignore rewriting by
; preprocess-clause for the present purpose: we want to wait for a
; full-blown rewrite before allowing rewriting of
; induction-hyp-terms.)

; Initially we attempted to fix the slowdown mentioned above (the one
; reported by Greve and Wilding) by eliminating completely the special
; treatment of induction-hyp-terms.  However, lemma
; psuedo-termp-binary-op_tree in books/meta/pseudo-termp-lemmas.lisp
; showed the folly of this attempt.  The relevant goal was as follows.

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

; In this case induction-hyp-terms contained the single term
; (binary-op_tree binary-op-name constant-name fix-name (cdr l)).
; Without special treatment of induction-hyp-terms, the above
; binary-op_tree term was rewritten, and hence so was the pseudo-termp
; hypothesis.  The result seemed to give permission to the next
; hypothesis, (pseudo-term-listp l), to be rewritten much more
; agressively than it was formerly, which bogged down the rewriter
; (perhaps even in an infinite loop).

; A later attempt used the simple algorithm that we stop meddling once
; we have made a pass through the rewriter, even if there are still
; induction-concl-terms around.  Lemma flip-eq-subst-commute in
; books/workshops/1999/ivy/ivy-v2/ivy-sources/flip.lisp showed the
; problem with that approach.  Subgoal *1/2' below was produced by
; preprocess-clause.  It produces goal Subgoal *1/2.16, which has a
; new occurrence in the conclusion of the induction-concl-term
; (SUBST-FREE F X TM):

#|
 Subgoal *1/2'
 (IMPLIES (AND (NOT (WFNOT F))
               (CONSP F)
               (CONSP (CDR F))
               (CONSP (CDDR F))
               (NOT (CDDDR F))
               (OR (EQUAL (CAR F) 'AND)
                   (EQUAL (CAR F) 'OR)
                   (EQUAL (CAR F) 'IMP)
                   (EQUAL (CAR F) 'IFF))
               (EQUAL (SUBST-FREE (FLIP-EQ (CADR F) (CDR POS))
                                  X TM)
                      (FLIP-EQ (SUBST-FREE (CADR F) X TM)
                               (CDR POS)))
               (EQUAL (SUBST-FREE (FLIP-EQ (CADDR F) (CDR POS))
                                  X TM)
                      (FLIP-EQ (SUBST-FREE (CADDR F) X TM)
                               (CDR POS))))
          (EQUAL (SUBST-FREE (FLIP-EQ F POS) X TM)
                 (FLIP-EQ (SUBST-FREE F X TM) POS))).

 This simplifies, using the :definitions FLIP-EQ, LEN, LIST2P, LIST3P,
 SUBST-FREE, TRUE-LISTP, WFBINARY, WFEQ and WFNOT, the :executable-
 counterparts of BINARY-+, EQUAL, LEN and TRUE-LISTP, primitive type
 reasoning and the :rewrite rules CAR-CONS and CDR-CONS, to the following
 16 conjectures.

 Subgoal *1/2.16
 (IMPLIES (AND (CONSP F)
               (CONSP (CDR F))
               (CONSP (CDDR F))
               (NOT (CDDDR F))
               (EQUAL (CAR F) 'AND)
               (EQUAL (SUBST-FREE (FLIP-EQ (CADR F) (CDR POS))
                                  X TM)
                      (FLIP-EQ (SUBST-FREE (CADR F) X TM)
                               (CDR POS)))
               (EQUAL (SUBST-FREE (FLIP-EQ (CADDR F) (CDR POS))
                                  X TM)
                      (FLIP-EQ (SUBST-FREE (CADDR F) X TM)
                               (CDR POS)))
               (NOT (CONSP POS)))
          (EQUAL (SUBST-FREE F X TM)
                 (LIST 'AND
                       (SUBST-FREE (CADR F) X TM)
                       (SUBST-FREE (CADDR F) X TM))))
|#

; If we stop meddling after Subgoal *1/2', then hypothesis rewriting
; in Subgoal *1/2.16 is so severe that we are subject to
; case-split-limitations and never reach the conclusion!  If memory
; serves, an attempt to turn off case-split-limitations just led the
; prover off the deep end.

                        (change rewrite-constant
                                rcnst
                                :force-info new-force-info

; We also tried a modification in which we use the same :expand-lst as
; below, thus continuing to meddle with induction-concl-terms even
; after we are done meddling with induction-hyp-terms.  However, that
; caused problems with, for example, the proof of exponents-add-1 in
; books/arithmetic-2/pass1/expt-helper.lisp.  Apparently the forced
; expansion of (EXPT R J) looped with rule exponents-add-2 (rewriting
; r^(i+j)).  At any rate, it seems reasonable enough to keep
; suppression of induction-hyp-terms rewriting in sync with forced
; expansion of induction-concl-terms.

; And we tried one more idea: removing the test on whether the clause had been
; rewritten.  We got one failure, on collect-times-3b in v2-8 in
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
           (mv-let (hitp clauses ttree)
                   (simplify-clause1 cl hist local-rcnst wrld state)
                   (cond
                    (hitp (mv (if hit-rewrite2 'hit-rewrite2 hitp)
                              clauses ttree pspv))
                    (t (mv 'miss nil nil nil)))))))))

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

(defun insert-pair-by-cdr (car-val cdr-val alist)

; A car-cdr-sorted alist is an alist whose keys are symbols and whose
; values are alists sorted by cdr, where each value is a cons of
; symbols.  Such alists are the type returned by
; extract-and-classify-lemmas.

  (cond ((null alist)
         (list (cons car-val cdr-val)))
        ((eq cdr-val (cdar alist))
         (cond
          ((eq car-val (caar alist))
           alist)
          ((symbol-< car-val (caar alist))
           (cons (cons car-val cdr-val)
                 alist))
          (t
           (cons (car alist)
                 (cons (cons car-val cdr-val)
                       (cdr alist))))))
        ((symbol-< cdr-val (cdar alist))
         (cons (cons car-val cdr-val) alist))
        (t
         (cons (car alist)
               (insert-pair-by-cdr car-val cdr-val (cdr alist))))))

(defun extend-car-cdr-sorted-alist (key car-val cdr-val alist)

  (cond ((null alist)
         (list (cons key (list (cons car-val cdr-val)))))
        ((eq key (caar alist))
         (cons (cons key (insert-pair-by-cdr
                          car-val cdr-val (cdr (car alist))))
               (cdr alist)))
        ((symbol-< key (caar alist))
         (cons (cons key (list (cons car-val cdr-val)))
               alist))
        (t (cons (car alist)
                 (extend-car-cdr-sorted-alist
                  key car-val cdr-val (cdr alist))))))

(defun extract-and-classify-lemmas (ttree ignore-lst forced-runes alist)

; We essentially partition the set of runes tagged as 'lemmas in ttree
; into partitions based on the type (i.e., the keyword token) for each
; rune.  In addition, we indicate whether the rune is a member of
; forced-runes.  In our partitioning we actually throw away the runes and
; just report the corresponding base symbols.

; In particular, scan ttree for all the 'lemma tags and return an
; alist associating each type of rune used in the ttree with a list of
; pairs.  Each pair is of the form (flg . name), where flg is t or nil
; and name is the base symbol of a rune of the given type used in the
; ttree.  There is a pair for every rune in the ttree, except those
; whose base symbols are in ignore-lst; those runes we ignore.  If flg
; is t, the corresponding rune is a member of forced-runes.

; An example alist returned is
; '((:DEFINITION (NIL . APP) (T . REV))
;   (:REWRITE (NIL . LEMMA1) (T . LEMMA2) (NIL . LEMMA3))
;   (:TYPE-PRESCRIPTION (T . FN1) (T . FN2) (NIL . FN3)))
; indicating that three :REWRITE runes were used, with base symbols
; LEMMA1, LEMMA2 (which was forced), and LEMMA3, etc. 

; The alist is sorted by car.  Each value is itself an alist that is
; sorted by cdr.

  (cond ((null ttree) alist)
        ((symbolp (caar ttree))
         (cond
          ((eq (caar ttree) 'lemma)
           (extract-and-classify-lemmas
            (cdr ttree) ignore-lst forced-runes
            (let ((rune (cdar ttree)))
              (cond
               ((member-eq (base-symbol rune) ignore-lst)
                alist)
               (t
                (extend-car-cdr-sorted-alist
                 (car rune)
                 (cond ((member-equal rune forced-runes) t)
                       (t nil))
                 (base-symbol rune)
                 alist))))))
          (t (extract-and-classify-lemmas (cdr ttree)
                                          ignore-lst forced-runes alist))))
        (t (extract-and-classify-lemmas
            (cdr ttree) ignore-lst forced-runes
            (extract-and-classify-lemmas (car ttree)
                                         ignore-lst forced-runes alist)))))

(deflabel Simple
  :doc
  ":Doc-Section Miscellaneous

  ~c[:]~ilc[definition] and ~c[:]~ilc[rewrite] rules used in preprocessing~/
  ~bv[]
  Example of simple rewrite rule:
  (equal (car (cons x y)) x)

  Examples of simple definition:
  (defun file-clock-p (x) (integerp x))
  (defun naturalp (x)
    (and (integerp x) (>= x 0)))
  ~ev[]~/

  The theorem prover output sometimes refers to ``simple'' definitions
  and rewrite rules.  These rules can be used by the preprocessor,
  which is one of the theorem prover's ``processes'' understood by the
  ~c[:do-not] hint; ~pl[hints].

  The preprocessor expands certain definitions and uses certain
  rewrite rules that it considers to be ``fast''.  There are two ways
  to qualify as fast.  One is to be an ``abbreviation'', where a
  rewrite rule with no hypotheses or loop stopper is an
  ``abbreviation'' if the right side contains no more variable
  occurrences than the left side, and the right side does not call the
  functions ~ilc[if], ~ilc[not] or ~ilc[implies].  Definitions and rewrite rules can
  both be abbreviations; the criterion for definitions is similar,
  except that the definition must not be recursive.  The other way to
  qualify applies only to a non-recursive definition, and applies when
  its body is a disjunction or conjunction, according to a perhaps
  subtle criterion that is intended to avoid case splits.")

(defun tilde-*-conjunction-of-possibly-forced-names-phrase1 (lst)
  (cond
   ((null lst) nil)
   (t
    (cons (msg (if (caar lst)
                   "~x0 (forced)"
                   "~x0")
               (cdar lst))
          (tilde-*-conjunction-of-possibly-forced-names-phrase1 (cdr lst))))))

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

(defconst *fake-rune-alist*

; We use this constant for dealing with fake runes in tag trees.  We ignore
; *fake-rune-for-anonymous-enabled-rule*, because push-lemma is careful not to
; put it into any tag trees.

  (list (cons (car *fake-rune-for-linear*)
              "linear arithmetic")
        (cons (car *fake-rune-for-type-set*)
              "primitive type reasoning")
        (cons (car *fake-rune-for-nu-rewriter*)
              "the nu-rewriter")))

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

(mutual-recursion

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

(defun all-runes-in-ttree (ttree ans)

; Ttree is any ttree produced by this system.  We sweep it collecting into ans
; every rune in it.  

  (cond
   ((null ttree) ans)
   ((symbolp (caar ttree))
    (all-runes-in-ttree
     (cdr ttree)
     (let ((val (cdar ttree)))

; Val is the value of the tag.  Below we enumerate all possible tags.  For each
; we document the shape of val and then process it for runes. 

       (case
        (caar ttree)
        (lemma                        ;;; Shape:  rune
         (add-to-set-equal val ans))
        (:by                          ;;; Shape: (lmi-lst thm-cl-set constraint-cl k)
         ;;(all-runes-in-lmi-lst (car val) wrld ans)

; As of this writing, there aren't any runes in an lmi list that are
; being treated as runes.  Imagine proving a lemma that is then
; supplied in a :use hint.  It shouldn't matter, from the point of
; view of tracking RUNES, whether that lemma created a rewrite rule that
; is currently disabled or whether that lemma has :rule-classes nil.

         ans)
        (:bye                         ;;; Shape: (name . cl), where name is a
                                      ;;; "new" name, not the name of something
                                      ;;; used.
         ans)
        (:or                          ;;; Shape (parent-cl-id
                                      ;;;        nil-or-branch-number
                                      ;;;        ((user-hint1 . hint-settings1)
                                      ;;;         ...))
                                      ;;; See comment about the :by case above.
         ans)
        (:use                         ;;; Shape: ((lmi-lst (hyp1 ...) cl k) . n)
         ;;(all-runes-in-lmi-lst (car (car val)) wrld ans)

; See comment for the :by case above.

         ans)
        (:cases                       ;;; Shape: ((term1 ... termn) . clauses)
         ans)
        (preprocess-ttree             ;;; Shape: ttree
         (all-runes-in-ttree val ans))
        (assumption                   ;;; Shape: term
         ans)
        (pt                           ;;; Shape: parent tree - just numbers
         ans)
        (fc-derivation                ;;; Shape: fc-derivation record
         (add-to-set-equal (access fc-derivation val :rune)
                           (all-runes-in-ttree (access fc-derivation val :ttree)
                                               ans)))
        (find-equational-poly         ;;; Shape: (poly1 . poly2)
         (all-runes-in-ttree (access poly (car val) :ttree)
                             (all-runes-in-ttree (access poly (cdr val) :ttree)
                                                 ans)))
        (variables                    ;;; Shape: var-lst
         ans)
        (elim-sequence                ;;; Shape: ((rune rhs lhs alist 
                                    ;;;          restricted-vars
                                    ;;;          var-to-runes-alist
                                    ;;;          ttree) ...)
         (all-runes-in-elim-sequence val ans))
        ((literal                     ;;; Shape: term
          hyp-phrase                  ;;;        tilde-@ phrase
          equiv                       ;;;        equiv relation
          bullet                      ;;;        term
          target                      ;;;        term
          cross-fert-flg              ;;;        boolean flg
          delete-lit-flg              ;;;        boolean flg
          clause-id                   ;;;        clause-id
          binding-lst)                ;;;        alist binding vars to terms
         ans)
        ((terms                       ;;; Shape: list of terms
          restricted-vars)            ;;;        list of vars
         ans)
        (var-to-runes-alist           ;;; Shape: (...(var . (rune1 ...))...)
         (all-runes-in-var-to-runes-alist val ans))
        (ts-ttree                     ;;; Shape: ttree
         (all-runes-in-ttree val ans))
        ((irrelevant-lits             ;;; Shape: clause
          clause)                     ;;;        clause
         ans)
        (hidden-clause                ;;; Shape: t
         ans)
        (abort-cause                  ;;; Shape: symbol
         ans)
        (bddnote                      ;;; Shape: bddnote

; A bddnote has a ttree in it.  However, whenever a bddnote is put into a given
; ttree, the ttree from that bddnote is also added to the same given ttree.
; So, we don't really think of a bddnote as containing a "ttree" per se, but
; rather, a sort of data structure that is isomorphic to a ttree.

         ans)
        (case-limit                   ;;; Shape: t
         ans)
        (sr-limit                     ;;; Shape: t
         ans)
        (:clause-processor            ;;; Shape: (clause-processor-hint
         ans)                         ;;;         . clauses)
        (otherwise (er hard 'all-runes-in-ttree
                       "This function must know every possible tag so that it ~
                        can recover the runes used in a ttree.  The unknown ~
                        tag ~x0, whose value is ~x1, has just been encountered."
                       (caar ttree)
                       (cdar ttree)))))))
   (t (all-runes-in-ttree (cdr ttree)
                          (all-runes-in-ttree (car ttree) ans)))))
)

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
               (tilde-*-conjunction-of-possibly-forced-names-phrase (cdar alist)))

; Note: Names is a tilde-* object that will print a conjoined list of names
; (possibly followed by parenthetical "forced" remarks).  We must determine
; whether there is more than one name in the list.  The names printe are just
; those in (cdar alist), which we know is a non-empty true list of pairs.
; Below we set pluralp to t if two or more names will be printed and to nil if
; exactly one name will be printed.  

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

(defun recover-forced-runes (ttree ans)

; Every assumption in ttree has exactly one assumnote.  Let the
; ":rune" of the assumption be the :rune field of the car of its
; assumnotes.

; We scan the tag tree ttree for all occurrences of the 'assumption
; tag and collect into ans the :rune of each assumption, when the
; :rune is a rune.  We ignore the symbolp :runes because we will be
; searching the resulting list for genuine runes and thus need not
; clutter it with symbols.  

  (cond
   ((null ttree) ans)
   ((symbolp (caar ttree))
    (cond
     ((and (eq (caar ttree) 'assumption)
           (not (symbolp
                 (access assumnote
                         (car (access assumption (cdar ttree) :assumnotes))
                         :rune))))
      (recover-forced-runes
       (cdr ttree)
       (add-to-set-equal
        (access assumnote
                (car (access assumption (cdar ttree) :assumnotes))
                :rune)
        ans)))
     (t (recover-forced-runes (cdr ttree) ans))))
   (t (recover-forced-runes
       (car ttree)
       (recover-forced-runes (cdr ttree) ans)))))

(defun tilde-*-raw-simp-phrase (ttree punct phrase)

; See tilde-*-simp-phrase.  But here, we print as specified by value :raw for
; state global 'raw-proof-format.  We supply the concluding punctuation msg,
; punct.

  (let ((forced-runes (recover-forced-runes ttree nil)))
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
                                    (#\, ",")
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

  (let ((forced-runes (recover-forced-runes ttree nil)))
    (mv-let (message-lst char-alist)
            (tilde-*-simp-phrase1
             (extract-and-classify-lemmas ttree nil forced-runes nil)
             nil)
            (list* "trivial ob~-ser~-va~-tions"
                   "~@*"
                   "~@* and "
                   "~@*, "
                   message-lst
                   char-alist))))

; CLAUSE IDENTIFICATION

; Before we can write the function that prints a description of
; simplify-clause's output, we must be able to identify clauses.  This raises
; some issues that are more understandable later, namely, the notion of the
; pool.  See Section PUSH-CLAUSE and The Pool.

; Associated with every clause in the waterfall is a unique object
; called the clause identifier or clause-id.  These are printed out
; at the user in a certain form, e.g.,

; [3]Subgoal *2.1/5.7.9.11'''

; but the internal form of these ids is:

(defrec clause-id ((forcing-round . pool-lst) case-lst . primes) t)

; where forcing-round is a natural number, pool-lst and case-lst are generally
; true-lists of non-zero naturals (though elements of case-lst can be of the
; form Dk in the case of a dijunctive split) and primes is a natural.  The
; pool-lst is indeed a pool-lst.  (See the function pool-lst.) The case-lst is
; structurally analogous.

; A useful constant, the first clause-id:

(defconst *initial-clause-id*
  (make clause-id
        :forcing-round 0
        :pool-lst nil
        :case-lst nil
        :primes 0))

; Note: If this changes, inspect every use of it.  As of this writing there is
; one place where we avoid a make clause-id and use *initial-clause-id* instead
; because we know the forcing-round is 0 and pool-lst and case-lst fields are
; both nil and the primes field is 0.

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
; signallying that we want a pool name to use within a clause id -- even though
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

; Because of the way :DO-NOT-INDUCT name hints are implemented, we need to be
; able to produce a literal atom of the form |name clause-id| where clause-id
; is what tilde-@-clause-id-phrase will print on id.  Therefore, we now
; virtually repeat the definition of tilde-@-clause-id-phrase, except this time
; building a string.  We could use this to print all clause ids.  But that is
; slow because it involves consing up strings.  So we suffer the inconvenience
; of duplication.  If tilde-@-clause-id-phrase is changed, be sure to change
; the functions below.

(defun string-for-tilde-@-clause-id-phrase/periods (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond
   ((null lst) nil)
   ((null (cdr lst)) (explode-atom (car lst) 10))
   (t (append (explode-atom (car lst) 10)
              (cons #\.
                    (string-for-tilde-@-clause-id-phrase/periods
                     (cdr lst)))))))

(defun string-for-tilde-@-clause-id-phrase/primes (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cond ((= n 0) nil)
        ((= n 1) '(#\'))
        ((= n 2) '(#\' #\'))
        ((= n 3) '(#\' #\' #\'))
        (t (cons #\' (append (explode-atom n 10) '(#\'))))))

(defun string-for-tilde-@-clause-id-phrase (id)
  (coerce
   (append
    (if (= (access clause-id id :forcing-round) 0)
        nil
        `(#\[ ,@(explode-atom (access clause-id id :forcing-round) 10) #\]))
    (cond ((null (access clause-id id :pool-lst))
           (cond ((null (access clause-id id :case-lst))
                  (append '(#\G #\o #\a #\l)
                          (string-for-tilde-@-clause-id-phrase/primes
                           (access clause-id id :primes))))
                 (t (append '(#\S #\u #\b #\g #\o #\a #\l #\Space)
                            (string-for-tilde-@-clause-id-phrase/periods
                             (access clause-id id :case-lst))
                            (string-for-tilde-@-clause-id-phrase/primes
                             (access clause-id id :primes))))))
          (t (append
              '(#\S #\u #\b #\g #\o #\a #\l #\Space #\*)
              (string-for-tilde-@-clause-id-phrase/periods
               (access clause-id id :pool-lst))
              (cons #\/
                    (append (string-for-tilde-@-clause-id-phrase/periods
                             (access clause-id id :case-lst))
                            (string-for-tilde-@-clause-id-phrase/primes
                             (access clause-id id :primes))))))))
   'string))

(defrec bddnote
  (cl-id goal-term mx-id err-string fmt-alist cst term bdd-call-stack ttree)
  nil)

(defun tilde-@-bddnote-phrase (x)

; Bddnote is either a tagged bddnote pair or nil.  This function returns a ~@
; phrase to be used just after "But simplification" or "This simplifies".

  (cond ((null x) "")
        (t (msg " with BDDs (~x0 nodes)"
                (access bddnote (cdr x) :mx-id)))))

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
           (list (cons #\0 (if (tagged-object 'assumption ttree) 1 0))
                 (cons #\1 (if raw-proof-format
                               (tilde-*-raw-simp-phrase ttree #\, "")
                             (tilde-*-simp-phrase ttree)))
                 (cons #\p (if raw-proof-format "" ", "))
                 (cons #\3 (tilde-@-clause-id-phrase cl-id))
                 (cons #\b (tilde-@-bddnote-phrase
                            (tagged-object 'bddnote ttree)))
                 (cons #\c (tilde-@-case-split-limitations-phrase
                            (tagged-object 'sr-limit ttree)
                            (tagged-object 'case-limit ttree)
                            "  ")))
           (proofs-co state)
           state
           (term-evisc-tuple nil state)))
     ((null clauses)
      (cond
       (raw-proof-format
        (fms "But ~#0~[~/forced ~]simplification~@b reduces this to T, using ~
              ~*1~|"
             (list (cons #\0 (if (tagged-object 'assumption ttree) 1 0))
                   (cons #\1 (tilde-*-raw-simp-phrase
                              ttree
                              #\.
                              (tilde-@-case-split-limitations-phrase
                               (tagged-object 'sr-limit ttree)
                               (tagged-object 'case-limit ttree)
                               "")))
                   (cons #\b (tilde-@-bddnote-phrase
                              (tagged-object 'bddnote ttree))))
             (proofs-co state)
             state
             (term-evisc-tuple nil state)))
       (t
        (fms "But ~#0~[~/forced ~]simplification~@b reduces this to T, using ~
              ~*1.~@c~|"
             (list (cons #\0 (if (tagged-object 'assumption ttree) 1 0))
                   (cons #\1 (tilde-*-simp-phrase ttree))
                   (cons #\b (tilde-@-bddnote-phrase
                              (tagged-object 'bddnote ttree)))
                   (cons #\c (tilde-@-case-split-limitations-phrase
                              (tagged-object 'sr-limit ttree)
                              (tagged-object 'case-limit ttree)
                              "  ")))
             (proofs-co state)
             state
             (term-evisc-tuple nil state)))))
     (t
      (let ((hyp-phrase-pair (tagged-object 'hyp-phrase ttree)))
        (cond (hyp-phrase-pair
               (fms "We remove HIDE from ~@0, which was used heuristically to ~
                     transform ~@1 by substituting into the rest of that ~
                     goal.  This produces~|"
                    (list (cons #\0 (cdr hyp-phrase-pair))
                          (cons #\1 (tilde-@-clause-id-phrase
                                     (cdr (tagged-object 'clause-id ttree)))))
                    (proofs-co state)
                    state
                    (term-evisc-tuple nil state)))
              (raw-proof-format
               (fms "This ~#0~[~/forcibly ~]simplifies~@b, using ~*1~
                     to~#2~[~/ the following ~n3 conjectures.~@c~]~|"
                    (list (cons #\0 (if (tagged-object 'assumption ttree) 1 0))
                          (cons #\1 (tilde-*-raw-simp-phrase ttree #\, ""))
                          (cons #\2 clauses)
                          (cons #\3 (length clauses))
                          (cons #\b (tilde-@-bddnote-phrase
                                     (tagged-object 'bddnote ttree)))
                          (cons #\c (tilde-@-case-split-limitations-phrase
                                     (tagged-object 'sr-limit ttree)
                                     (tagged-object 'case-limit ttree)
                                     "  ")))
                    (proofs-co state)
                    state
                    (term-evisc-tuple nil state)))
              (t
               (fms "This ~#0~[~/forcibly ~]simplifies~@b, using ~*1, ~
                     to~#2~[~/ the following ~n3 conjectures.~@c~]~|"
                    (list (cons #\0 (if (tagged-object 'assumption ttree) 1 0))
                          (cons #\1 (tilde-*-simp-phrase ttree))
                          (cons #\2 clauses)
                          (cons #\3 (length clauses))
                          (cons #\b (tilde-@-bddnote-phrase
                                     (tagged-object 'bddnote ttree)))
                          (cons #\c (tilde-@-case-split-limitations-phrase
                                     (tagged-object 'sr-limit ttree)
                                     (tagged-object 'case-limit ttree)
                                     "  ")))
                    (proofs-co state)
                    state
                    (term-evisc-tuple nil state)))))))))

(deflabel specious-simplification
  :doc
  ":Doc-Section Miscellaneous

  nonproductive proof steps~/

  Occasionally the ACL2 theorem prover reports that the current goal
  simplifies to itself or to a set including itself.  Such
  simplifications are said to be ``specious'' and are ignored in the
  sense that the theorem prover acts as though no simplification were
  possible and tries the next available proof technique.  Specious
  simplifications are almost always caused by forcing.~/

  The simplification of a formula proceeds primarily by the local
  application of ~c[:]~ilc[rewrite], ~c[:]~ilc[type-prescription], and other rules to its
  various subterms.  If no rewrite rules apply, the formula cannot be
  simplified and is passed to the next ACL2 proof technique, which is
  generally the elimination of destructors.  The experienced ACL2 user
  pays special attention to such ``maximally simplified'' formulas;
  the presence of unexpected terms in them indicates the need for
  additional rules or the presence of some conflict that prevents
  existing rules from working harmoniously together.

  However, consider the following interesting possibility: local
  rewrite rules apply but, when applied, reproduce the goal as one of
  its own subgoals.  How can rewrite rules apply and reproduce the
  goal?  Of course, one way is for one rule application to undo the
  effect of another, as when commutativity is applied twice in
  succession to the same term.  Another kind of example is when two rules
  conflict and undermine each other.  For example, under suitable
  hypotheses, ~c[(length x)] might be rewritten to ~c[(+ 1 (length (cdr x)))]
  by the ~c[:]~ilc[definition] of ~ilc[length] and then a ~c[:]~ilc[rewrite] rule might be used
  to ``fold'' that back to ~c[(length x)].  Generally speaking the
  presence of such ``looping'' rewrite rules causes ACL2's simplifier
  either to stop gracefully because of heuristics such as that
  described in the documentation for ~ilc[loop-stopper] or to cause a
  stack overflow because of indefinite recursion.

  A more insidious kind of loop can be imagined: two rewrites in
  different parts of the formula undo each other's effects ``at a
  distance,'' that is, without ever being applied to one another's
  output.  For example, perhaps the first hypothesis of the formula is
  simplified to the second, but then the second is simplified to the
  first, so that the end result is a formula propositionally
  equivalent to the original one but with the two hypotheses commuted.
  This is thought to be impossible unless forcing or case-splitting
  occurs, but if those features are exploited (~pl[force] and
  ~pl[case-split]) it can be made to happen relatively easily.

  Here is a simple example.  Declare ~c[foo] to be a function of one
  argument returning one result:
  ~bv[]
  (defstub p1 (x) t)
  ~ev[]
  Prove the following silly rule:
  ~bv[]
  (defthm bad
    (implies (case-split (p1 x))
             (p1 x)))
  ~ev[]
  Now suppose we try the following.
  ~bv[]
  (thm (p1 x))
  ~ev[]
  The ~il[rewrite] rule ~c[bad] will rewrite ~c[(p1 x)] to ~c[t], but it will
  be unable to prove the hypothesis ~c[(case-split (p1 x))].  As a result, the
  prover will spawn a new goal, to prove ~c[(p1 x)].  However, since this new
  goal is the same as the original goal, ACL2 will recognize the simplification
  as ~em[specious] and consider the attempted simplification to have failed.

  In other words, despite the rewriting, no progress was made!  In more common
  cases, the original goal may simplify to a set of subgoals, one of which
  includes the original goal.

  If ACL2 were to adopt the new set of subgoals, it would loop
  indefinitely.  Therefore, it checks whether the input goal is a
  member of the output subgoals.  If so, it announces that the
  simplification is ``specious'' and pretends that no simplification
  occurred.

  ``Maximally simplified'' formulas that produce specious
  simplifications are maximally simplified in a very technical sense:
  were ACL2 to apply every applicable rule to them, no progress would
  be made.  Since ACL2 can only apply every applicable rule, it cannot
  make further progress with the formula.  But the informed user can
  perhaps identify some rule that should not be applied and make it
  inapplicable by disabling it, allowing the simplifier to apply all
  the others and thus make progress.

  When specious simplifications are a problem it might be helpful to
  ~il[disable] all forcing (including ~il[case-split]s) and resubmit
  the formula to observe whether forcing is involved in the loop or
  not.  ~l[force].  The commands
  ~bv[]
  ACL2 !>:disable-forcing
  and
  ACL2 !>:enable-forcing
  ~ev[]
  ~il[disable] and ~il[enable] the pragmatic effects of both ~c[force]
  and ~c[case-split].  If the loop is broken when forcing is
  ~il[disable]d, then it is very likely some ~il[force]d hypothesis of
  some rule is ``undoing'' a prior simplification.  The most common
  cause of this is when we ~il[force] a hypothesis that is actually
  false but whose falsity is somehow temporarily hidden (more below).
  To find the offending rule, compare the specious simplification with
  its non-specious counterpart and look for rules that were speciously
  applied that are not applied in the non-specious case.  Most likely
  you will find at least one such rule and it will have a ~ilc[force]d
  hypothesis.  By disabling that rule, at least for the subgoal in
  question, you may allow the simplifier to make progress on the
  subgoal.")

(defun settled-down-clause-msg1 (signal clauses ttree pspv state)

; The arguments to this function are the standard ones for an output
; function in the waterfall.  See the discussion of the waterfall.

  (declare (ignore signal clauses ttree pspv))
  state)
