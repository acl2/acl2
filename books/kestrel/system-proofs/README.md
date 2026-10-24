This directory contains proofs, largely AI-generated, that are
intended to establish the correctness of parts of the ACL2 system.
(Yes, proving these facts using ACL2 is logically circular, but the
point is to try to increase assurance and eliminate bugs.)

Warning: The contents of this directory have not been carefully
reviewed.

Note to the ACL2 implementors: If changes to the ACL2 sources cause
these proofs to break, feel free to comment things out and/or add
skip-proofs.  But please notify Eric Smith or someone else at Kestrel,
so we can fix them.  If ACL2 source code changes cause any of these
theorems to cease to be true, that is interesting and should probably
be investigated (keeping in mind though that most of this material is
unvetted).

## Correctness proofs about ACL2 system functions

The books in this directory (other than those in `irrelevance/` and
`generalize/`, which prove the soundness of irrelevance elimination and of the
clause built by generalization: see `irrelevance/README.md` and
`generalize/README.md`) prove that functions in the ACL2 sources that
transform or match terms do what they are supposed to do, stated in terms of
evaluators.  The sources are not changed.  Most functions proved about are
already in `:logic` mode with their guards verified (they appear in
`*system-verify-guards-alist*`); the others (`sublis-expr`, `cnf-dnf` and
related functions, `all-picks`, `make-stack-from-alist`, `lambda-nest-hidep`,
`lambda-nest-unhide`, `add-literal` and the other clause-set functions,
`subsumes` and the other subsumption functions, `add-literal-smart` and the
other functions that drop literals and tests contradicted by an equality with
a constant, the clause-set functions for clauses tagged with `extra-info`,
`built-in-clausep1` and `built-in-clausep2`, `simplify-tests-and-calls`, and
`clean-up-loop$-recursion-induction-machine` and the functions it calls) are
put into `:logic` mode in these books with `verify-termination`.  Nor are any
libraries changed: lemmas about general-purpose functions (`termp`,
`arglistp`, `free-vars-in-term`, `collect-by-position`, etc.) that the proofs
need are in `helpers.lisp`, from which they could be moved to libraries such
as `kestrel/terms-light` and `kestrel/lists-light`.
`cterm-ev-helpers.lisp` contains lemmas about the `cterm-ev` evaluator, and
`cons-term-helpers.lisp` contains lemmas about `cons-term`, which may evaluate
a call of a primitive on constant arguments.  Counterexamples and examples
are in separate books, such as `subsumes-tests.lisp` for `subsumes.lisp`,
which `top.lisp` does not include.

Each result is stated using an evaluator that knows just the functions the
code depends on, so it can be functionally instantiated for any evaluator that
knows at least those functions:

- `empty-eval` (knows no functions): code that builds terms with `fcons-term`,
  and `make-stack-from-alist`.
- `if-eval` (`if`): `termify-clause-set`.
- `cons-nest-eval` (`cons`): `unmake-true-list-cons-nest`.
- `equality-eval` (`if`, `equal`, `eql`, `eq`, `not`): `flatten-ands-in-lit`,
  `dumb-negate-lit`.
- `implicate-eval` (the `equality-eval` functions plus `implies`): `implicate`.
- `type-set-inverter-eval` (the recognizers and other functions used in ACL2's
  built-in type-set-inverter rules): `type-set-quote`.
- `cterm-ev`, from `clause-processors/sublis-var-meaning.lisp`: code that
  builds terms with `cons-term`, which may evaluate any of about 30
  primitives on constant arguments.
- `one-way-unify-eval` (`binary-+`, `binary-*`, `unary--`, `unary-/`,
  `intern-in-package-of-symbol`, `coerce`, `cons`, `equal`): `one-way-unify`.
- `remove-guard-holders-eval` (the `cterm-ev` primitives plus `return-last`,
  `mv-list`, `the-check`, `cons-with-hint`, `to-df`, `from-df`, `df0`, `df1`,
  and `do$`): `remove-guard-holders1`.
- `cnf-dnf-eval` (`if`, `not`): `cnf-dnf` and the tau functions that use it.
- `hide-eval` (`hide`): `lambda-nest-unhide` and the terms that `rewrite`
  builds for `hide` terms.
- `hide-cterm-eval` (the `cterm-ev` primitives plus `hide`): the connection
  between those terms and `sublis-var`.
- `clause-set-eval` (`if`, `not`, `equal`, `iff`, `hard-error`, `integerp`,
  `rationalp`): `add-literal` and the functions that combine clauses and sets
  of clauses.
- `subsumes-eval` (the `one-way-unify-eval` functions plus `if`, `not`, and
  `extra-info`): `subsumes` and the functions built on it, including
  `built-in-clausep1` and `built-in-clausep2`.
- `bic-eval` (the `subsumes-eval` functions plus those in the initial built-in
  clauses, such as `o<` and `acl2-count`): the initial built-in clauses.
- `smart-eval` (the `clause-set-eval` functions plus `eq`, `eql`, and `=`):
  `add-literal-smart`, `add-test-smart`, and the related functions.
- `extra-info-eval` (the `clause-set-eval` functions plus `extra-info`): the
  clause-set functions for clauses tagged with `extra-info`.
- `tests-eval` (the `remove-guard-holders-eval` and `smart-eval` functions):
  `simplify-tests-and-calls`.
- `cleanup-eval` (`if`, `not`, `equal`, `iff`):
  `clean-up-loop$-recursion-induction-machine` and the functions it calls.

`all-picks` is not about terms; its theorem says it agrees with Nqthm's
definition.

The books certify with ACL2 built from the current testing-kestrel sources,
which include Matt's fix to the `TO-DF` case of `remove-guard-holders1` (see
"Other findings").

## Results

| Function (source file) | Main theorem | Hypotheses |
|---|---|---|
| `subst-var` (translate.lisp) | `subst-var-correct`: value is that of `form` with `old` bound to the value of `new` | `old` is not `nil`; `form` is a pseudo-term |
| `subst-var` | `subst-var-correct-when-equal-values` | `new` and `old` have the same value |
| `subst-each-for-var` (translate.lisp) | `subst-each-for-var-correct`: the `n`th result is `term` with `old` bound to the value of the `n`th member of `new-lst` | as for `subst-var-correct` |
| `subst-expr1`, `subst-expr` (rewrite.lisp) | `subst-expr1-correct`, `subst-expr-correct` | `new` and `old` have the same value; for `subst-expr`, `old` is not a quoted constant (from the guard) |
| `subcor-var` (basis-b.lisp) | `subcor-var-correct`: value is that of `form` with `vars` bound to the values of `terms` | `nil` is not a free variable of `form`; `form` is a pseudo-term |
| `fsubcor-var` (other-events.lisp) | `fsubcor-var-correct`: as for `subcor-var` | as for `subcor-var` |
| `remove-lambdas` (defuns.lisp) | `remove-lambdas-correct`, `remove-lambdas-correct-when-termp` | lambdas are closed and there are no `nil` variables -- true of every `termp` |
| `expand-all-lambdas` (translate.lisp) | `expand-all-lambdas-correct`, `expand-all-lambdas-correct-when-termp` | same as for `remove-lambdas` |
| `flatten-ands-in-lit`, `dumb-negate-lit` (translate.lisp, basis-b.lisp) | `equality-eval-of-conjoin-of-flatten-ands-in-lit`, `equality-eval-of-dumb-negate-lit` | the term is a pseudo-term |
| `make-lambda-application` (translate.lisp) | `make-lambda-application-correct`: value is that of `body` with `formals` bound to the values of `actuals` | `body` is a pseudo-term without `nil` as a free variable; nothing about `formals` or `actuals` |
| `one-way-unify` (translate.lisp) | `one-way-unify-correct`: on success, `pat` evaluated under the substitution equals `term` | `pat` and `term` are `termp`s in a world where `equal`, `cons`, and `intern-in-package-of-symbol` have arity 2 |
| `one-way-unify-restrictions` (rewrite.lisp) | `one-way-unify-restrictions-correct`: as for `one-way-unify` | as for `one-way-unify`, plus `alistp-listp` of the restrictions (from the guard) |
| `implicate` (tau.lisp) | `implicate-correct`: true iff `t1` implies `t2` | `t1` and `t2` are pseudo-terms |
| `termify-clause-set` (induct.lisp) | `termify-clause-set-correct`: true iff `conjoin-clauses` is true | the clause list is a true list (from the guard) |
| `unmake-true-list-cons-nest` (translate.lisp) | `unmake-true-list-cons-nest-correct`: the list of terms evaluates to the value of the cons nest | the result is not `:fail` |
| `type-set-quote` (type-set-b.lisp) | `type-set-quote-correct`: for every rule in `*initial-type-set-inverter-rules*`, the object satisfies the rule's terms iff its type-set is a subset of the rule's type-set | the object is not a "bad atom" (bad atoms can't be quoted constants); ACL2 without non-standard analysis |
| `genvar` (basis-b.lisp) | `legal-variablep-of-genvar`, `not-member-equal-of-genvar`: the result is a legal variable not in `avoid-lst` | the guard |
| `remove-guard-holders1`, `remove-guard-holders-weak` (translate.lisp) | `remove-guard-holders1-correct`, `remove-guard-holders1-lst-correct`, `remove-guard-holders-weak-correct` | the term is a `termp` in a world where `return-last`, `mv-list`, `the-check`, `cons-with-hint`, `to-df`, and `from-df` have their usual arities |
| `sublis-expr` (other-processes.lisp) | `sublis-expr-correct`: value is unchanged when each term in the domain of the alist has the value of the corresponding term in its range; `sublis-expr-of-pairlis$-generalizes`: replacing terms with new variables, then binding the variables to the values of the terms, gives the original value (which is why generalization is sound) | `term` is a pseudo-term; for the second, the variables are distinct, not `nil`, and occur neither in `term` nor in the terms |
| `cnf-dnf` (tau.lisp) | **not correct** for `not`: `cnf-dnf-incorrect-for-not`; a copy with a one-line fix is correct: `cnf-dnf-fixed-correct` (the result, read as a CNF or DNF, is equivalent to the term or its negation) | none |
| `split-on-conjoined-disjunctions`, `split-on-conjoined-disjunctions-in-hyps-of-pairs` (tau.lisp) | `split-on-conjoined-disjunctions-correct`, `split-on-conjoined-disjunctions-in-hyps-of-pairs-correct`: the pairs made for tau rules are true if the original pairs are | `cnf-dnf` is correct on the hypotheses (true after the fix) |
| `all-picks` (induct.lisp) | `all-picks-correct`: with `rflg` = `nil` it returns exactly what Nqthm's `all-picks` returned, as its comments ask to be shown (and with `rflg` = `t`, the reverse) | the pockets are true lists |
| `make-stack-from-alist` (rewrite.lisp) | `make-stack-from-alist-correct`: evaluating `term` in an alist that binds just the formals of the stack's single frame to the values of its actuals gives the value of `term`/`alist` (that is, of `term` with the variables of `alist` bound to the values of the terms they are bound to); so does the lambda application that `make-lambda-application` makes from the frame (`make-lambda-application-of-make-stack-from-alist-correct`) | `alist` is not `nil`; `term` is a pseudo-term without `nil` as a free variable |
| `lambda-nest-unhide` (rewrite.lisp) | `lambda-nest-unhide-correct`: removing the `hide` from a nest of lambdas whose innermost body is a call of `hide` (`lambda-nest-hidep`) does not change its value | lambdas are closed and there are no `nil` variables -- true of every `termp` |
| `add-literal` (simplify.lisp) | `add-literal-correct`: the result, as a disjunction, is the disjunction of the literal and the clause | the literal is a pseudo-term |
| `add-each-literal`, `disjoin-clauses` (simplify.lisp) | `add-each-literal-correct`, `disjoin-clauses-correct`: the meaning is unchanged, or is the disjunction of the two clauses | the literals added are pseudo-terms |
| `conjoin-clause-to-clause-set` (simplify.lisp) | `conjoin-clause-to-clause-set-correct`: the result, as a conjunction of clauses, is the conjunction of the clause and the set | none |
| `add-each-literal-lst`, `conjoin-clause-sets`, `disjoin-clause-segment-to-clause-set`, `split-on-assumptions` (simplify.lisp) | `add-each-literal-lst-correct`, `conjoin-clause-sets-correct`, `disjoin-clause-segment-to-clause-set-correct`, `split-on-assumptions-correct` | the clauses are pseudo-term lists; for `conjoin-clause-sets`, the first set is a true list |
| `subsumes` (simplify.lisp) | `subsumes-correct`: if it returns `t` and `cl1` is valid (true under all alists), then `cl2` is true; `subsumes!-rec-correct-with-substitution`: `cl1`, instantiated by the substitution found, implies `cl2` | the clauses are `termp`s in a world where `equal`, `cons`, and `intern-in-package-of-symbol` have arity 2 (for `one-way-unify1`); the limit is a natural number or `nil` |
| `some-member-subsumes` (simplify.lisp) | `some-member-subsumes-correct`: if it returns `t`, the clause is true if the members of the set are valid | as for `subsumes` |
| `clause-set-subsumes` (prove.lisp) | **not correct with a limit**: `clause-set-subsumes-can-give-up-and-return-t`; correct without one (as for `:by` hints): `clause-set-subsumes-correct-when-no-limit`; a copy with a one-line fix is correct: `clause-set-subsumes-fixed-correct` | as for `subsumes` |
| `built-in-clausep1`, `built-in-clausep2` (simplify.lisp) | `built-in-clausep1-correct`, `built-in-clausep2-correct`: if they return a rune, the clause is true, provided the stored built-in clauses are valid; `built-in-clausep2-of-initial-built-in-clauses-correct`: for the initial built-in clauses, which are proved valid (`bic-eval-valid-built-in-clause-listp-of-initial-built-in-clauses`) | as for `subsumes`, with the stored clauses `termp`s; for the initial built-in clauses, the functions in them have their usual arities; ACL2 without non-standard analysis |
| `add-literal-smart`, `simplify-clause-for-term-equal-const` (history-management.lisp) | `add-literal-smart-correct`: the result, as a disjunction, is the disjunction of the literal and the clause (although, when `lit` is a negated equality, it drops the literals that are false wherever `lit` is); `simplify-clause-for-term-equal-const-correct`: dropping the literals that equate `var` with a constant other than `const` does not change the clause where `var` has the value of `const` | the literal and the clause are pseudo-terms |
| `add-literals`, `add-segments-to-clause` (history-management.lisp) | `add-literals-correct`: the disjunction of the two clauses; `add-segments-to-clause-correct`: the conjunction of the disjunctions of the clause with each segment | the literals added are pseudo-terms; the segments are pseudo-term lists (so `segments` is a true list) |
| `simplify-tests`, `add-test-smart` (induct.lisp) | `simplify-tests-correct`: dropping the negated tests that equate `var` with a constant other than `const` does not change the conjunction of the tests where `var` has the value of `const`; `add-test-smart-correct`: the result, as a conjunction, is the conjunction of the test and the tests | the tests are pseudo-terms |
| `simplify-tests-and-calls` (induct.lisp) | `simplify-tests-and-calls-correct`: the simplified tests of a case of an induction machine are true exactly when the original tests are, and the simplified calls have the values of the original calls | the tests and calls are `termp`s in a world where the functions treated specially by `remove-guard-holders1` have their usual arities |
| `clean-up-nots`, `clean-up-conjunction` (defuns.lisp) | `clean-up-nots-correct`: the result is true exactly when the term is (though its value may differ: `clean-up-nots-does-not-preserve-value`); `clean-up-conjunction-contradiction-correct`: it returns `:contradiction` only for tests that cannot all be true; `clean-up-conjunction-correct`: otherwise, the result, as a conjunction, is true exactly when the tests are | none |
| `clean-up-loop$-recursion-induction-machine` (defuns.lisp) | `applicable-calls-of-clean-up-loop$-recursion-induction-machine`: under any assignment, the cleaned-up machine has exactly the cases of the original machine whose tests are true, in the same order and with the same calls | none (not even that the tests are terms) |
| `conjoin-clause-to-clause-set-extra-info`, `conjoin-clause-sets-extra-info`, `conjoin-clause-sets+` (history-management.lisp) | `conjoin-clause-to-clause-set-extra-info-correct`, `conjoin-clause-sets-extra-info-correct`, `conjoin-clause-sets+-correct`: the result, as a conjunction of clauses, is the conjunction of the clause (or first set) and the set; the `extra-info` tags are false literals, so they do not change the meaning of a clause | none; for the functions on two sets, the first set is a true list |
| the two `hide` cases of `rewrite` (rewrite.lisp) | `rewrite-hide-case-correct`, `rewrite-lambda-nest-hide-case-correct`: the term built for `term` under `alist` (for `(hide x)`, and for "lambda-hide commuting") has the value of `term`/`alist`; `rewrite-hide-case-correct-sublis-var`, `rewrite-lambda-nest-hide-case-correct-sublis-var`: that is, the value of `(sublis-var alist term)` | `term` is a pseudo-term without `nil` variables (and, for lambda-hide commuting, with closed lambdas); for the `sublis-var` versions, `alist` does not bind `nil` |

## Other properties

Besides preserving meaning, the functions that build terms preserve the usual
well-formedness properties of terms, and several of them provably do what
they are for.  The theorems are in the same books (for `remove-guard-holders1`,
in `remove-guard-holders1-properties.lisp`); their hypotheses are mostly the
corresponding properties of the inputs.

Well-formedness of the result:

| Function | `termp` | `no-nils-in-termp` | `lambdas-closed-in-termp` | `no-duplicate-lambda-formals-in-termp` | Free variables of the result |
|---|---|---|---|---|---|
| `subst-var`, `subst-each-for-var` | yes | yes | yes | yes | at most those of `new` and those of `form` other than `old` |
| `subst-expr1`, `subst-expr` | yes | yes | yes | yes | at most those of `new` and `term` |
| `subcor-var`, `fsubcor-var` | yes | yes | yes | yes | at most those of `terms` and those of `form` other than `vars` |
| `remove-lambdas` | yes | yes | yes (trivially: no lambdas) | yes (trivially) | |
| `expand-all-lambdas` | yes | yes | yes (trivially) | yes (trivially) | |
| `make-lambda-application` | yes | yes | yes | yes | at most those of `actuals` and those of `body` other than `formals` |
| `dumb-negate-lit`, `flatten-ands-in-lit` | yes | (no: see below) | yes | yes | |
| `implicate` | yes | | yes | yes | |
| `termify-clause-set`, `unmake-true-list-cons-nest` | yes | | | | |
| `remove-guard-holders1`, `remove-guard-holders-weak` | yes | yes | yes | yes | at most those of the input |
| `sublis-expr` | yes | yes | yes | yes | at most those of `term` and of the terms in the range of the alist |
| `one-way-unify` (the terms in the substitution) | yes | yes | yes | yes | |
| `lambda-nest-unhide` | yes | yes (for a `termp`) | yes | yes | at most those of the input (for a `termp`) |
| `add-literal`, `add-each-literal`, `disjoin-clauses` | yes (for `term-listp`) | | | | |
| `conjoin-clause-to-clause-set`, `conjoin-clause-sets`, `disjoin-clause-segment-to-clause-set`, `split-on-assumptions` | yes (for `term-list-listp`) | | | | |
| `add-literal-smart`, `add-literals`, `simplify-clause-for-term-equal-const`, `simplify-tests`, `add-test-smart` | yes (for `term-listp`) | | | | |
| `add-segments-to-clause`, `conjoin-clause-to-clause-set-extra-info`, `conjoin-clause-sets-extra-info`, `conjoin-clause-sets+` | yes (for `term-list-listp`) | | | | |
| `simplify-tests-and-calls` (the tests and the calls) | yes (for `term-listp`) | | | | |
| `clean-up-nots`, `clean-up-conjunction` | yes (for `termp`, `term-listp`) | | | | |
| `clean-up-loop$-recursion-induction-machine` (the tests and the calls) | yes (for `term-listp`) | | | | |
| `make-lambda-application` applied to the frame from `make-stack-from-alist` (the `hide` case of `rewrite`) | yes | yes | yes | yes | at most those of `term` not bound by `alist` and those of the terms it binds them to |

The `termp` results need the usual arities of the functions the code
introduces (for example, `cons` for `remove-guard-holders1`, which turns
`cons-with-hint` into `cons`).  For the terms built in the `hide` cases of
`rewrite` (which are proved to be `termp`s), `alist` must bind distinct
variables to terms, as substitutions in the rewriter do.

What the functions are for:

- `subst-var`: `old` is not a free variable of the result, unless it is one of
  `new` (`not-member-equal-of-free-vars-in-term-of-subst-var`).
- `subst-expr1`: when `new` is a variable that does not occur in `old`, `old`
  does not occur in the result (`not-occur-of-subst-expr1`), provided the term
  contains no call that `cons-term` would evaluate (see below).
- `remove-lambdas`, `expand-all-lambdas`: the result contains no lambdas
  (`lambda-free-termp-of-remove-lambdas`,
  `lambda-free-termp-of-expand-all-lambdas`); also, the CHANGEDP flag of
  `remove-lambdas1` is accurate.
- `make-lambda-application`: it returns `body` when no lambda is needed, and
  otherwise a lambda application whose body is `body` and whose formals are
  exactly the variables of `body` (none unused, and the lambda is closed),
  distinct if the `formals` are
  (`make-lambda-application-when-lambda-needed`).
- `make-stack-from-alist`: as its comment requires, the frame binds every
  variable of `term`
  (`subsetp-equal-of-free-vars-in-term-and-car-of-car-of-make-stack-from-alist`),
  so `term` can be the body of a closed lambda whose formals are those of the
  frame; the formals are distinct if the variables bound by `alist` are, and
  there are as many actuals as formals.
- `add-literal`: it returns the clause, the true clause, or the clause with the
  literal added at the front or end (`add-literal-cases`);
  `conjoin-clause-to-clause-set` returns the set or the set with the clause
  added (`conjoin-clause-to-clause-set-cases`).
- `simplify-clause-for-term-equal-const`, `simplify-tests`: they drop exactly
  the literals (for `simplify-tests`, the negated tests) that equate `var`
  with a constant other than `const`
  (`member-equal-of-simplify-clause-for-term-equal-const`,
  `member-equal-of-simplify-tests`), and their `changedp` results say
  whether they dropped any (`simplify-clause-for-term-equal-const-1-changedp`,
  `simplify-tests-changedp`).  `add-literal-smart` returns the true clause or
  a subset of the clause with the literal added (`add-literal-smart-cases`),
  and `add-test-smart` returns the test followed by a subset of the tests
  (`add-test-smart-cases`).  `term-equated-to-constant-in-termlist` finds the
  first test that equates a term with a constant
  (`term-equated-to-constant-in-termlist-becomes-term-equated-to-constant`),
  and `simplify-tests` never drops that test.
- `conjoin-clause-to-clause-set-extra-info`: as its comments describe, when
  the clause differs from a member of the set only in its `extra-info` tags,
  it replaces the first such member with the clause made of the member's
  tags, then the tags of the clause that the member lacks, then the rest of
  the clause; otherwise it adds the clause at the front
  (`conjoin-clause-to-clause-set-extra-info-merges-tags`).  As its comment
  says, `set-difference-equal-changedp` computes `set-difference-equal`, and
  its flag says whether the lists intersect.
- `clean-up-conjunction`: as its comment says, it eliminates duplicates and
  double negations: it returns `:contradiction` exactly when some cleaned-up
  test has its complement (modulo commuting `equal` or `iff`) among the
  earlier ones (`clean-up-conjunction-contradiction-iff`), and otherwise the
  tests with `clean-up-nots` applied, in order, keeping only the first
  occurrence of each (`clean-up-conjunction-when-not-contradiction`,
  `no-duplicatesp-equal-of-clean-up-conjunction`,
  `member-equal-of-clean-up-conjunction`).
- `subsumes`: the substitution found extends the input alist
  (`subsumes!-rec-alist-extends-alist`), and the count-limited search
  succeeds only if the unlimited one does (`subsumes!-rec-when-subsumes`).
- `flatten-ands-in-lit`: no member of the result is `'t` or a conjunction (a
  call of `if` with `'nil` as its second or third argument).
- `one-way-unify`: the substitution binds only variables of the pattern
  (`subsetp-equal-of-strip-cars-of-mv-nth-1-of-one-way-unify`), and, as its
  comments say, `one-way-unify1` is a "No-Change Loser": on failure it returns
  its input alist (`mv-nth-1-of-one-way-unify1-when-fails`), while
  `one-way-unify1-lst` is not one.
- `remove-guard-holders1`: the result contains no calls of `return-last`,
  `mv-list`, `the-check`, `cons-with-hint`, `from-df`, `df0`, or `df1`, except
  inside calls of `hide`
  (`guard-holder-free-termp-of-mv-nth-1-of-remove-guard-holders1`), and the
  CHANGEDP flag is accurate (`remove-guard-holders1-changedp-contract`), both
  provided every call of `to-df` has one argument, as in any `termp`
  (`unary-to-df-callsp`; see "Other findings").

## Preconditions the proofs revealed

Several of these functions are correct only under conditions stronger than
their guards.  None of these is a bug, since ACL2 applies the functions only to
translated terms, but the `-tests.lisp` books contain small counterexample
theorems showing that the conditions cannot be dropped:

- `remove-lambdas`, `expand-all-lambdas`: a lambda whose body has a free
  variable, or a lambda that binds the "variable" `nil`, can be beta-reduced
  into a term with a different value.
- `one-way-unify`: a pattern containing a variable named `t` "matches"
  constants it does not match (`(binary-+ '1 t)` matches `'7` with no
  bindings), because `one-way-unify1-quotep-subproblems` uses `t` as a flag
  value; a pattern variable named `nil` gets bound but always evaluates to
  `nil`; and a call of `cons` with one argument matches any cons constant
  whose car matches.  (The `equal` arity hypothesis may not be necessary, but
  the proof uses it.)
- `remove-guard-holders1`: a call of `the-check` with two arguments is replaced
  by its last argument, but it evaluates to its (missing) third argument.
- `termify-clause-set`: it tests for the end of the clause list with `null`,
  while `conjoin-clauses` uses `endp`, so for the non-list `a` it returns
  `'nil` though `conjoin-clauses` returns `'t`.

The proofs of the other properties revealed a few more such conditions, also
shown by counterexample theorems:

- `subst-expr1`: a subterm that `cons-term` evaluates is not replaced, so
  `(subst-expr1 'v '(f '3) '(f (binary-+ '1 '2)))` is `'(f '3)`, which still
  contains `old` (the input is not in the normal form that `cons-term`
  produces).
- `dumb-negate-lit`: `(dumb-negate-lit '(not))` is `nil`, so `no-nils-in-termp`
  is preserved only for well-formed terms (which `termp` ensures).
- `make-lambda-application`: with duplicate formals, as in
  `(make-lambda-application '(x x) '(f x) '(a b))`, the lambda it makes has
  duplicate formals (so the result is not a `termp`).
- `remove-lambdas`, `expand-all-lambdas`: `no-nils-in-termp` is preserved only
  when lambda applications have as many arguments as formals (which
  `pseudo-termp` ensures).
- `add-literal`: the literal must be a pseudo-term: it treats the malformed
  constant `(quote nil nil)`, whose value is `nil`, as a true literal and
  returns the true clause (`add-literal-needs-pseudo-termp`).
- `conjoin-clause-sets` and the functions it calls, and
  `conjoin-clause-sets-extra-info`, test for the end of the first set with
  `null`, so for a set that is not a true list they conjoin a final empty
  (false) clause (`conjoin-clause-sets-extra-info-needs-true-listp`).
- `add-literal-smart`, `add-test-smart`: the clause and the tests must be
  pseudo-terms (not just the literal or test added), because the constants
  are compared syntactically: adding `(not (equal x '1))` to a clause
  containing the malformed literal `(equal x (quote 1 2))`, whose value is
  that of `(equal x '1)`, drops that literal, so a true clause becomes one
  that is false when `x` is 1 (`add-literal-smart-needs-pseudo-term-listp`);
  similarly, adding the test `(equal x '1)` to the test
  `(not (equal x (quote 1 2)))` drops it, so contradictory tests become tests
  that are true when `x` is 1 (`add-test-smart-needs-pseudo-term-listp`).
- `lambda-nest-unhide`: the lambdas must be closed: in
  `((lambda (x) (hide y)) a)`, `y` always evaluates to `nil`, but once the
  `hide` is removed, `y` is bound from the outside
  (`lambda-nest-unhide-needs-closed-lambdas`).  And when the `hide` has no
  argument, `nil` becomes a free variable of the result
  (`lambda-nest-unhide-when-hide-has-no-argument`), so the `no-nils-in-termp`
  and free-variable results assume a `termp` (with `hide` of arity 1).  (The
  value is still preserved in that case.)

`remove-lambdas`, `one-way-unify`, `remove-guard-holders1`, and
`termify-clause-set` are soundness-critical: the left-hand side of every
`:rewrite` rule is the result of `remove-lambdas` (see
`interpret-term-as-rewrite-rule1`); `one-way-unify` decides when the rewriter,
type-set, and other parts of the prover can use a rule; as its source comments
say, `remove-guard-holders-weak` (which calls `remove-guard-holders1`) is used
to compute induction and termination machines and constraints, so it must
return a term provably equal to its input; the guard and termination
conjectures for definitions are proved in the form produced by
`termify-clause-set`; the terms built in the `hide` cases of `rewrite`
(using `make-stack-from-alist`, `lambda-nest-unhide`, and
`make-lambda-application`) replace subterms of goals; the simplifier builds
clauses with `add-literal` and the other clause-set functions; the guard proof
obligations are built with `add-literal-smart`, `add-literals`, and
`add-segments-to-clause`, and the guard and termination proof obligations are
combined with `conjoin-clause-sets+` (which uses the `extra-info` functions
for `:guard-debug` and `:measure-debug`), so these must not weaken the
obligations; termination and induction machines are built with
`add-test-smart`, and induction machines are simplified with
`simplify-tests-and-calls`; and a goal subsumed by a theorem (for a `:by`
hint, a built-in clause, an `:equivalence` rule, or a goal in the induction
pool) is considered proved.

## Other findings

**A soundness bug in `clause-set-subsumes-1` (prove.lisp).**  It checks that
every clause of one set is subsumed by some clause of another, returning `'?`
if the subsumption check gave up on some clause because it reached its limit
on calls of `one-way-unify1`.  But it passes the result for the latest clause
as its accumulator, so a `'?` for one clause is forgotten when a later clause
gives `t`, and the result is `t`
(`clause-set-subsumes-can-give-up-and-return-t`).  The check for
`:equivalence` rules uses a limit and trusts `t`, so this allows a proof of
`nil`:

```lisp
(defun my-le (x y) (<= (nfix x) (nfix y)))   ; not symmetric
(defthm my-le-is-an-equivalence
  (and (booleanp (my-le x y))
       (my-le x x)
       ;; trivially true, but the check for symmetry gives up on its clause:
       (implies (and (not p1) (not p2) (not p3) (not p4) (not p5)
                     (not p6) (not p7) (not p8) (not p9) (not p10)
                     (not p11) (not p12) (not p13) (not p14) (not p15)
                     (not p16) (not p17) (not p18) (not p19) (not p20)
                     (not p21) (not p22))
                (equal q q))
       (implies (and (my-le x y) (my-le y z)) (my-le x z)))
  :rule-classes :equivalence)
(defthm bad (implies (my-le a b) (my-le b a)) :rule-classes nil)
(thm nil :hints (("Goal" :use (:instance bad (a 0) (b 1)))))
```

The pool subsumption check (`some-pool-member-subsumes`) also uses a limit and
trusts `t`.  The fix is to keep the `'?` (`subsumes.lisp` proves a fixed copy
correct); a separate patch makes that change in the sources, with a release
note and a test book.

**A soundness bug in `cnf-dnf` (tau.lisp).**  In the `not` case, `cnf-dnf`
calls itself on the argument with `cnfp` negated, so the result for the
argument is read in the wrong normal form:
`(cnf-dnf t '(not (if a a b)) nil)` is `(((not a)) ((not b)))`, which as a DNF
means `(or (not a) (not b))` rather than `(not (or a b))`.  Since
`split-on-conjoined-disjunctions` uses `cnf-dnf` to split the hypotheses of tau
rules, a hypothesis `(not (or p q))` is split into two rules with hypotheses
`(not p)` and `(not q)`, each stronger than the theorem.  This allows a proof
of `nil`:

```lisp
(tau-status :system t)
(defthm not-int-or-string
  (implies (not (or (integerp x) (stringp x)))
           (not (natp x)))
  :rule-classes :tau-system)
(defthm bad (implies (natp x) (stringp x))
  :hints (("Goal" :in-theory (disable natp)))
  :rule-classes nil)
(thm nil :hints (("Goal" :use (:instance bad (x 3)))))
```

This appears to be a regression from the recent change that introduced
`cnfp1` in the `if` case (an ACL2 built from sources before that change does
not prove `bad`).  The fix is to pass `cnfp` unchanged in the `not` case;
`cnf-dnf.lisp` proves that the fixed function is correct.

**`clean-up-loop$-recursion-induction-machine` is not called.**  Its comment
says it is for the induction machines of loop$ recursive functions, but
`induction-machines` never builds such machines (see Note 1 there), and
nothing in the sources or the books calls it.  So its correctness, proved in
`clean-up-conjunction.lisp`, does not currently matter for soundness.

**`subst-expr` in practice.**  The terms that reach `subst-expr` are usually
already in the normal form that `cons-term` produces (the prover normalizes
clauses, even inside `hide`, and `remove-guard-holders` normalizes rule
conclusions except inside `hide`), so the subtlety described above seldom
matters.  It can show up for a `:type-prescription` rule whose `:typed-term`
is a call of `hide`: `subst-expr-tests.lisp` contains an event that is
rejected for this reason (inside `must-fail`) and is accepted if written
slightly differently.

The comments in `genvar` say that it generates a variable "in the same package
as pkg-witness", but the result can be a symbol imported into that package:
`(genvar 'foo "LIST" nil nil)` is `COMMON-LISP::LIST` (see
`genvar-tests.lisp`).  It is still a legal variable that is not in the avoid
list, which is what matters.

The comments in `remove-guard-holders1` say that "if changedp is nil, then
changedp0 is nil and new-term is identical to term".  This used to fail because
the `TO-DF` case returned the `changedp` flag for the argument of `TO-DF`,
ignoring `changedp0`: `(remove-guard-holders1 nil '(return-last 'progn (bar)
(to-df x)) nil)` returned `(mv nil '(to-df x))`, so that
`(remove-guard-holders-weak '(foo (return-last 'progn (bar) (to-df x))) nil)`
left the `return-last` in place (only a missed simplification, since the
result was still equal to the input).  Matt has fixed this: the `TO-DF` case
now returns `(or changedp0 changedp1)` (and the lambda case also checks
`changedp0`).  The books now prove the contract, and that no guard holders
remain, whenever every call of `TO-DF` has one argument;
`remove-guard-holders1-tests.lisp` checks the two examples above against the
fixed behavior.  The one-argument condition is needed:
`(remove-guard-holders1 nil '(to-df x y) nil)` returns `(mv nil '(to-df x))`
(`remove-guard-holders1-changedp-needs-unary-to-df`), which doesn't matter
for translated terms.
