# Soundness of the clause built by generalization

ACL2's generalization process, source function `generalize-clause`, calls
`generalize1` to build its result clause:

```lisp
(sublis-expr-lst (pairlis$ terms vars)
                 (disjoin-clauses tr-seg (disjoin-clauses gr-seg cl)))
```

Here `terms` are the terms being generalized and `vars` are the new
variables.  `tr-seg` is computed by `type-restriction-segment` using
`type-set`, and contains the negations of facts about the types of the terms.
`gr-seg` is computed by `generalize-rule-segment`, and contains the negations
of instances of `:generalize` rules.

`generalize-clause` itself cannot be put into `:logic` mode with
`verify-termination`, because `type-restriction-segment` and
`generate-variable-lst` call `type-set`, whose supporters (264 functions)
include linear arithmetic and `clausify`.  So these books verify the part
that builds the result clause: `sublis-expr`, `disjoin-clauses` (with
`add-literal`), and `generalize-rule-segment` (with `apply-generalize-rule`,
`subterm-one-way-unify`, `one-way-unify`, and `sublis-var`).

The main theorem, in `generalize-proofs.lisp`, is:

```lisp
(defthm generalize-ev-when-generalize1-clause
  (implies (and (generalize-ev (disjoin (sublis-expr-lst
                                         (pairlis$ terms vars)
                                         (disjoin-clauses
                                          tr-seg
                                          (disjoin-clauses
                                           (mv-nth 0 (generalize-rule-segment terms vars ens wrld))
                                           cl))))
                               (generalization-alist terms vars a))
                ;; The type restrictions are true.  TR-SEG holds their
                ;; negations, as clause literals (hypotheses of the
                ;; generalized clause), so they are true when all of these
                ;; literals are false:
                (all-eval-to-false-with-generalize-ev tr-seg a)
                ;; The :generalize rules are theorems:
                (generalize-rules-okp (global-val 'generalize-rules wrld))
                ;; The new variables are fresh:
                (generalization-vars-okp vars terms)
                (not (intersectp-equal vars (free-vars-in-terms cl)))
                (not (intersectp-equal vars (free-vars-in-terms terms)))
                (not (intersectp-equal vars (free-vars-in-terms tr-seg)))
                (pseudo-term-listp cl)
                (pseudo-term-listp terms)
                (pseudo-term-listp tr-seg))
           (generalize-ev (disjoin cl) a))
  :rule-classes nil)
```

That is, if the generalized clause is true when the new variables are bound
to the values of the terms (`generalization-alist`), then the original clause
is true.  This is the clause-processor form of soundness in which the result
is evaluated under a different alist.

The hypotheses state what the rest of the prover must guarantee:

- The type restrictions in `tr-seg` are true.  This is the soundness of
  `type-set` and of how `type-restriction-segment` turns its results into
  literals (with `convert-type-set-to-term` and `clausify`), which is not
  covered here.
- The formula of each `:generalize` rule in the world is a theorem (see
  `generalize-rules-okp`).  This holds for a valid world.
- The new variables are distinct non-`nil` symbols, one per term, that do not
  occur in the clause, the terms, or the type restrictions.  `generalize-clause`
  chooses them with `generate-variable-lst` to avoid the variables of the
  clause.  The variables of `gr-seg` need not be avoided separately: we prove
  that they are among the variables of the terms.

As a sanity check, `generalize-clause-processor.lisp` uses the main theorem
to verify a clause processor that generalizes terms given in the hint, and
uses it in a proof.

## The books

- `generalize-logic.lisp`: Puts the functions listed above into `:logic`
  mode with `verify-termination` (measures proved, no `skip-proofs`).  Guards
  are not verified.
- `generalize-ev.lisp`: The evaluator, and the meanings of `sublis-var` and
  `cons-term` (by functional instantiation of
  `clause-processors/sublis-var-meaning`).
- `disjoin-clauses-proofs.lisp`: `add-literal` and `disjoin-clauses` are
  sound, including their tautology and redundancy checks.
- `sublis-expr-proofs.lisp`: Replacing the terms by the variables preserves
  meaning.
- `one-way-unify-proofs.lisp`: The bindings computed by `one-way-unify1` are
  pseudo-terms that mention only variables of the term.
- `generalize-rule-proofs.lisp`: The literals returned by
  `generalize-rule-segment` are false and mention only variables of the terms.
- `generalize-proofs.lisp`: The main theorem.
- `generalize-clause-processor.lisp`: The clause processor and an example.
- `helpers.lisp`: General lemmas, used locally.

These books need no changes to the ACL2 sources.
