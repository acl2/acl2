; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; Note from J Moore:

; AI found a bug that it alleged occurred in the source code function
; arg1-almost-subsumes-arg2.  That function takes two clauses and quickly
; determines if the propositional resolvent of the two propositionally subsumes
; the second clause -- except it is allowed to fail (to say the resolvent does
; not subsume the second clause when in fact it does).  The agent suggested a
; fix that required computing the resolvent and testing subsumption.  That was
; slower and broke some proofs in the regression.  But
; arg1-almost-subsumes-arg2 exploits the fact that the initial prefixes of the
; two clauses are almost always the same (because they usually come from
; adjacent branches of an IF-expression).  Furthermore, the fast algorithm used
; was known to be correct if (it is verified in the book
; system/toy-arg1-almost-subsumes-arg2.lisp) provided the the first clause is
; not a tautology, and does not contain doubly negated or duplicate literals.
; Our diagnosis of the problem was not that arg1-almost-subsumes-arg2 needed to
; be fixed but that its input was bad: we forgot the precondition on the first
; clause when we wrote the function that called it.  Therefore, the bug was
; fixed by eliminating tautologies and cleaning up double negations and
; duplicate literals -- which in fact renders the set of clauses being analyzed
; more manageable.  See the comment above clean-clause-set in the source code,
; and the use of that function in clausify.

; ISSUE B2 (arg1-almost-subsumes-arg2 replacement resolution unsound when arg1 is a tautology;
;           if-interp emits tautology clause for pushed (not (not a))).
; Example B2-a: :by hint.
; EXPECT-AFTER-FIX: THM2 proves, BAD2 fails.

(in-package "ACL2") ; Added by Matt Kaufmann to make a certifiable book

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(defthm thm2 (and (if a (not (not a)) t) (if b t (if a (car (cons a c)) t))) :rule-classes nil)

(must-fail ; This must-fail wrapper was added by Matt Kaufmann
(defthm bad2 (or b (car (cons a c))) :hints (("Goal" :by thm2)) :rule-classes nil)
)

(must-fail ; This must-fail wrapper was added by Matt Kaufmann
(defthm contradiction2 nil
  :hints (("Goal" :use ((:instance bad2 (a nil) (b nil) (c nil))))) :rule-classes nil)
)
