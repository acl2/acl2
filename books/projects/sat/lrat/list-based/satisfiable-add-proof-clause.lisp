; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book,
; namely, that an addition (non-deletion) proof step preserves consistency: if
; the formula F is satisfiable and a proof clause C is verified again the
; formula, then the union F U {C} is satisfiable.  Here is a sketch of the
; proof.

#||

Notation.  Below, "unit-propagation" refers to any unit propagation,
even if it is partial (that is, with respect to a sequence of
clauses).  We denote this operation by U(F,A), where F is a formula
and A is an assignment.  If A is empty we may write U(F).  We say that
U(F,A) = t if the indicated unit-propagation produces a contradiction,
that is, an assignment that falsifies some clause in F.  For C a
clause, let N(C) be the assignment consisting of the negations of the
literals from C.  We write "A |= P" to indicate that P, which is a
formula or a clause, is true under assignment A.  We write A \ {L} to
denote (remove-literal L A).

Lemma (truth-monotone).  For a clause or formula P and assignments A1
and A2 with A1 \subset A2, if A1 |= P then A2 |= P.

Proof sketch.  First prove this by induction on \subset for P a
clause.  Then prove this for formulas by induction on F. -|

Lemma (unit-propagation-identity).  Suppose that F is a formula and
that assignment A |= F.  Then U(F,A) = A (hence is not t).

Proof sketch.  This is an easy induction on U.  In the base case we
have a clause in F that is false under A, so it cannot be that A |=
F.  The induction step is clear by truth-monotone. -|

Lemma (unit-propagation-t-monotone).  For a formula F and assignments
A1 and A2 with A1 \subset A2, if U(F,A1) = t then U(F,A2) = t.

Proof sketch: By induction using a merge of the induction schemes for
(unit-propagation F indices A1) and (unit-propagation F indices A2). -|

Lemma (unit-propagation-monotonicity).  For a formula F and
assignments A1 and A2 with A1 \subset A2, if U(F,A2) is not t, then
U(F,A1) is an assignment and U(F,A1) \subset U(F,A2).

Lemma (unit-propagation-correct).  Suppose that F is a formula, C is a
clause, and assignment A |= F.  Also suppose that U(F,N(C)) = t.  Then
A |= C.

Proof sketch.  Suppose (for a contradiction) otherwise; thus, the
assumptions hold but A is disjoint from C.  Let B = A U N(C).  Then B
is an assignment, and by truth-monotone, B |= F.  Since U(F,N(C)) = t
then by unit-propagation-t-monotone, U(F,B) = t.  We are done by the
lemma, unit-propagation-identity. -|

Finally, we outline the proof of the main result,
satisfiable-add-proof-clause.  Assume that we have a formula F and a
clause C that is verified for addition to F.  In our code we also have
a formula F' obtained by "shrinking" F.  The following lemmas show
that this isn't a problem, at least in principle; but we will try to
reference either F' or F below, as appropriate, in order to guide us
in development of a mechanically-checkable proof.

Lemma (satisfiable-maybe-shrink-formula).  F' is satisfiable if and
only if F is satisfiable.  [We can surely also prove, if necessary,
that F' and F are true under the same assignments.]

Lemma (unit-propagation-maybe-shrink-formula).  For all A and F,
U(F,A) = U(F',A). -|

There are two cases, according to the definition of verify-clause,
hence two main sub-lemmas.  First, the easier one:

Case 1: U(F,N(C)) = t (Lemma satisfiable-add-proof-clause-rup).

Proof sketch.  By unit-propagation-correct, any assignment A
satisfying F also satisfies C; thus A |= F' U {C} by a slight
variation of satisfiable-maybe-shrink-formula. -|

Case 2: U(F,N(C)) is not t and C is {L} U C' (Lemma
satisfiable-add-proof-clause-drat).  We also assume that (*) F' U {C}
is not satisfiable, since otherwise we are done.

Proof sketch.  Let A |= F.  Thus A |= F'.

  Claim 1 (Lemma satisfiable-add-proof-clause-drat-1): N(C) \subset A.

Proof sketch for Claim 1.  Otherwise, taking P in N(C) \ A, we can
extend A by -P to get an assignment A' extending A; then A' |= F' by
truth-monotone, and A' |= C by choice of P, so A' |= F' U {C},
contradicting (*).

Let B = A \ {-L} U {L}.  We will prove:

  Claim 2 (Lemma satisfiable-add-proof-clause-drat-2): Let D \in F;
  then B |= D.

Assume Claim 2 for the moment.  It clearly implies that B |= F; thus
B|= F'.  Also B |= C because L is in C.  This contradicts (*), proving
Case 2, Lemma satisfiable-add-proof-clause-drat.

So it remains to prove Claim 2.  First here are some useful lemmas.

Lemma (truth-remove-irrelevant-lit-1).  For assignment A and clause C,
if A |= C and L is not in C then A \ {L} |= C.

Proof sketch: Easy induction. -|

Lemma (truth-remove-irrelevant-lit-2).  For A and B as above and clause
C0 that does not contain -L or L, if A |= C0 then B |= C0.

Proof sketch: Easy induction. -|

Lemma (truth-remove-irrelevant-lit-3).  For assignment A and clause C,
if A |= C \ {L} then A |= C.

Proof sketch: Easy induction. -|

Lemma (subsetp-preserves-assignment).  If A is an assignment, B has
unique literals, and B \subset A, then B is an assignment. -|

Now to prove Claim 2, let D \in F.  Then since A |= F, A |= D.

Case 2.1: -L is not in D.  Then A \ {-L} |= D by Lemma
truth-remove-irrelevant-lit-1, so by truth-monotone, B |= D and we are
done.

Now let D' = D \ {-L]; thus D = {-L} U D'.

Case 2.2: -L is in D and A |= D'.  Then by
truth-remove-irrelevant-lit-2, B |= D'; then B |= D by
truth-remove-irrelevant-lit-3, and we are done.

Case 2.3: -L is in D and A does not satisfy D'.

Let RAT-A = A U N(D') and RAT-NC = U(F,N(C)) U N(D').  Technically:
RAT-A  = rat-assignment(A,-L,D) and
RAT-NC = rat-assignment(U(F,N(C)),-L,D).

Lemma (clause-or-assignment-p-rat-assignment).  Suppose that A is an
assignment and C is a clause.  Then if rat-assignment(A,lit,C) is not t,
it is an assignment.

Lemma (rat-assignment-not-t).  Suppose that A is an assignment, C is a
clause, and rat-assignment(A,lit,C) = t.  Then A |= remove-lit(lit,C).

Claim 2.3.1.  RAT-A is an assignment, by Lemmas
clause-or-assignment-p-rat-assignment.

CLaim 2.3.2.  U(F,A) = A since A |= F, by unit-propagation-identity.

Claim 2.3.3.  U(F,N(C)) \subset A.

Proof sketch.  Note that since U(F,A) = A by Claim 2.3.2; so U(F,A) is
an assignment.  Therefore since by Claim 1, N(C) \subset A, we have
U(F,N(C)) \subset U(F,A) by unit-propagation-monotonicity.  We are
done by again using U(F,A) = A.

Lemma (rat-assignment-monotone).  If A1 \ subset A2 and
rat-assignment(A2,-L,D) is not t, then rat-assignment(A1,-L,D) \subset
rat-assignment(A2,-L,D).

Claim 2.3.4.  RAT-NC is an assignment and \subset RAT-A, by Claims
2.3.1 and 2.3.3 and rat-assignment-monotone.

Claim 2.3.5.  Now U(F',RAT-NC) = t by the RAT check for D.  Hence by
lemma unit-propagation-maybe-shrink-formula, U(F,RAT-NC) = t.

Claim 2.3.6.  U(F,RAT-A) = t, by Claims 2.3.1, 2.3.4, and 2.3.5,
together with unit-propagation-t-monotone.

Claim 2.3.7.  A |= N(RAT-A).

Proof sketch.  This is clear from Claim 2.3.6 and our assumption that
A |= F, by unit-propagation-correct and an obvious lemma
(negate-clause-or-assignment-self-inverts) that implies N(N(RAT-A)) =
RAT-A by Claim 2.3.1.

Lemma (negate-rat-assignment-key).  Let RAT-A = rat-assignment(A,x,D)
where A is an assignment, D is a clause, and x is a literal in D.
Suppose A |= N(RAT-A).  Then A |= remove-literal(x,D).

Proof sketch: easy induction on rat-assignment(A,x,D), where for the
base case we need it to be false that A |= N(A).  For that we prove by
induction that if B \subset A then evaluate-clause(N(B),A) = nil, and
then appeal to reflexivity of \subset.

Claim 2.3.8.  A |= D', by Claim 2.3.7 and Lemma
negate-rat-assignment-key.

Claim 2.3.9.  Hence B |= D' by truth-remove-irrelevant-lit-2.

So B |= D by truth-remove-irrelevant-lit-3. -|

||#

(in-package "LRAT")

(include-book "lrat-checker")

(local
 (encapsulate
   ()

   (local (include-book "satisfiable-add-proof-clause-rup"))
   (local (include-book "satisfiable-add-proof-clause-drat"))

   (set-enforce-redundancy t)

   (defthm satisfiable-add-proof-clause-rup
     (mv-let (ncls ndel new-formula)
       (verify-clause formula entry ncls ndel)
       (declare (ignore ncls ndel))
       (implies (and (proof-entry-p entry)
                     (formula-p formula)
                     (satisfiable formula)
                     (equal (unit-propagation formula
                                              (access add-step entry :rup-indices)
                                              (negate-clause-or-assignment
                                               (access add-step entry :clause)))
                            t))
                (satisfiable (add-proof-clause
                              (access add-step entry :index)
                              (access add-step entry :clause)
                              new-formula))))
     :rule-classes nil)

   (defthm satisfiable-add-proof-clause-drat
     (mv-let (ncls ndel new-formula)
       (verify-clause formula entry ncls ndel)
       (declare (ignore ndel))
       (implies (and ncls
                     (proof-entry-p entry)
                     (not (proof-entry-deletion-p entry))
                     (formula-p formula)
                     (satisfiable formula)
                     (not (equal (unit-propagation formula
                                                   (access add-step entry
                                                           :rup-indices)
                                                   (negate-clause-or-assignment
                                                    (access add-step entry
                                                            :clause)))
                                 t))
                     (consp (access add-step entry :clause)))
                (satisfiable (add-proof-clause
                              (access add-step entry :index)
                              (access add-step entry :clause)
                              new-formula))))
     :rule-classes nil)))

(defthm satisfiable-add-proof-clause
  (mv-let (ncls ndel new-formula)
    (verify-clause formula entry ncls ndel)
    (declare (ignore ndel))
    (implies (and ncls ; success
                  (proof-entry-p entry)
                  (not (proof-entry-deletion-p entry))
                  (formula-p formula)
                  (satisfiable formula))
             (satisfiable (add-proof-clause
                           (access add-step entry :index)
                           (access add-step entry :clause)
                           new-formula))))
  :hints (("Goal"
           :use (satisfiable-add-proof-clause-rup
                 satisfiable-add-proof-clause-drat)
           :in-theory (union-theories '(verify-clause)
                                      (theory 'minimal-theory)))))
