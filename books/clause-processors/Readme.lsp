((:FILES
"
.:
Makefile
Readme.lsp
autohide.acl2
autohide.lisp
basic-examples.acl2
basic-examples.lisp
bv-add-common.lisp
bv-add-tests.lisp
bv-add.lisp
decomp-hint.lisp
equality.acl2
equality.lisp
ev-theoremp.lisp
generalize.acl2
generalize.lisp
join-thms.lisp
meta-extract-simple-test.lisp
meta-extract-user.lisp
multi-env-trick.lisp
null-fail-hints.lisp
replace-defined-consts.acl2
replace-defined-consts.lisp
replace-impl.lisp
term-patterns.lisp
unify-subst.lisp
use-by-hint.lisp
")
 (:TITLE    "Clause processor examples")
 (:AUTHOR/S 
  "Jared Davis"
  "Matt Kaufmann"
  "Erik Reeber"
  "Sol Swords"
  )
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "clause processors"
   )
 (:ABSTRACT "This directory contains books that illustrates the use
of clause processors.  Also see :DOC clause-processors and the following
paper:

     M. Kaufmann, J S. Moore, S. Ray, and E. Reeber, \"Integrating
     External Deduction Tools with ACL2.\"  Proceedings of the 6th
     International Workshop on the Implementation of Logics (IWIL 2006)
     (C. Benzmueller, B. Fischer, and G. Sutcliffe, editors), CEUR
     Workshop Proceedings Vol. 212, Phnom Penh, Cambodia, pp. 7-26,
     November 2006, http://ceur-ws.org/Vol-212/.

Book autohide.lisp introduces a verified clause processor (and a default
hint for using it) that instructs ACL2 to automatically wrap any calls
of certain functions in HIDE.

Book basic-examples.lisp contains many examples of correct and incorrect
definitions and uses of trivial trusted and verified clause processors.

Books bv-add*.lisp illustrate the use of clause processors to implement a
decision procedure for bit vectors.

Book decomp-hint.lisp introduces computed hints useful for proving local
properties of a cons tree by systematically structurally decomposing it.

Book equality.lisp illustrates the use of clause processors to deal with
equality reasoning.

Book ev-theoremp.lisp supports reasoning about evaluators and falsifiers.
A falsifier is a Skolem function that produces a variable assignment to 
falsify a term's evaluation, if there is such an assignment.  Therefore,
if a term's evaluation under its falsification is true, then it is a
theorem, i.e. true under all assignments.

Book generalize.lisp provides a generalization clause processor.

Book join-thms.lisp automates the introduction of certain theorems about
evaluators that are useful for verifying clause processors.

Book meta-extract-simple-test.lisp is a simple example, based on more complex
examples in meta-extract-user.lisp, that illustrates meta-extract hypotheses
in :meta rules.

Book meta-extract-user.lisp defines theorems and tools to enable the user to
more easily take advantage of the meta-extract hypotheses feature for :meta
rules.

Book multi-env-trick.lisp automates a trick for introducing clause
processors that allows each generated clause to be evaluated under multiple
binding alists in the correctness proof.

Book null-fail-hints.lisp introduces keyword hints :null, which does
nothing, and :fail, which causes the proof to fail.  These are probably not
as good as :no-op and :error, which are built into ACL2.

Book replace-defined-consts.lisp introduces a computed hint that replaces
defined constants (see tools/defined-const.lisp) with their definitions.

Book replace-impl.lisp introduces a clause processor that replaces a hyp
with something implied by that hyp.

Book term-patterns.lisp introduces a table and algorithm for syntactically
recognizing categories of terms that may be extended or changed by the user.

Book use-by-hint introduces a computed hint to apply a particular :by hint
as signalled by a logically meaningless hyp placed in the clause, so that a
clause processor can produce clauses that are copies of statements of
existing theorems.

Book unify-subst introduces functions for term unification and substitution,
and proves theorems about them that may be useful in defining clause
processors."))
