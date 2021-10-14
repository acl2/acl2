This directory formalizes the idea of a finite field consisting of the
integers modulo some prime p.

The main books provided are:

prime-fields.lisp: Definitions and rules about individual functions.

prime-fields-rules.lisp: Basic rules about prime-fields.

equal-of-add-cancel.lisp: Non-bind-free rules to cancel common addends
  in equalities.

equal-of-add-move-negs.lisp: Non-bind-free rules to to move
  negations to the other sides of equalities.

equal-of-add-rules.lisp: Gather non-bind-free rules about equalities
  of additions.

equal-of-add-cancel-bind-free.lisp: Bind-free rules to cancel addends
  in equalities.

equal-of-add-move-negs-bind-free.lisp: Bind-free rules to move
  negations to the other sides of equalities.

bind-free-rules.lisp: Gather all bind-free rules.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

Additional books include:

bind-free-common.lisp: Supporting utilities for bind-free rules.

bind-free-tests.lisp: Tests of bind-free rules.

doc.lisp: Xdoc documenation.

portcullis.lisp: Used to define the PFIELD package.

prime-fields-alt.lisp: Alternate formulation that uses a constrained
  function for the prime (not used much yet).

support.lisp: A few rules used internally by the library

top.lisp: Gather a maximal set of (compatible) books.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

Guidance:

To get just the definitions, include prime-fields.lisp.

For normal reasoning, include prime-fields-rules.lisp.

To deal with normalizing an equality of sums, you have a choice.  Either include:

  equal-of-add-cancel-bind-free.lisp
  and
  equal-of-add-move-negs-bind-free.lisp

or include:

  equal-of-add-cancel.lisp
  and
  equal-of-add-move-negs.lisp

WARNING: Including both will likely lead to loops!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

Normal forms:

We leave SUB enabled, to expose an ADD of a NEG.

We prefer (neg x) to (mul -1 x).
