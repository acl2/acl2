# Soundness of irrelevance elimination

The books in this directory prove the soundness of ACL2's irrelevance
elimination process, source function `eliminate-irrelevance-clause`, stated
using `irrelevance-ev`, an evaluator (made with `defevaluator+`) that knows
`if` and `not`.

The main theorem, in `irrelevance-proofs.lisp`, is:

```lisp
(defthm irrelevance-ev-when-eliminate-irrelevance-clause
  (implies (and (equal (mv-nth 0 (eliminate-irrelevance-clause cl hist pspv wrld state))
                       'hit)
                (irrelevance-ev (conjoin-clauses
                                 (mv-nth 1 (eliminate-irrelevance-clause cl hist pspv wrld state)))
                                a))
           (irrelevance-ev (disjoin cl) a)))
```

That is, if the process applies and the clause it returns is true, then so is
the clause it was given.  The proof is easy, because the clause returned is a
subset of the clause given, so it does not depend on how the irrelevant
literals are chosen.  Most of the work is putting the code into `:logic` mode.

As a sanity check, `irrelevance-clause-processor.lisp` uses the main theorem
to verify a clause processor that calls `eliminate-irrelevance-clause`, and
uses that clause processor in a proof by induction.

## The books

- `irrelevance-logic.lisp`: Puts `eliminate-irrelevance-clause` and its 43
  `:program` mode subroutines into `:logic` mode with `verify-termination`
  (measures proved, no `skip-proofs`).  Guards are not verified.  Most of
  these functions are the induction-candidate merging code (such as
  `merge-candidates` and `flush-candidates`) that `m&m-apply` dispatches to,
  since irrelevance elimination partitions the literals of a clause using
  `m&m`.  The interesting measures are those of the `pigeon-holep` clique
  and of `m&m1`.
- `irrelevance-proofs.lisp`: The evaluator and the main theorem.
- `irrelevance-clause-processor.lisp`: The clause processor and examples.

These books need no changes to the ACL2 sources.
