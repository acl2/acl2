ARM32 model test harness
for running the ARM32 model on concrete test vectors

Copyright (C) 2026 Kestrel Institute

License: A 3-clause BSD license. See the file books/3BSD-mod.txt.

Author: Eric McCarthy (mccarthy@kestrel.edu)

---

This directory contains a harness for running the ARM32 model in
books/kestrel/arm on concrete test vectors.  A test vector gives the state
before one instruction and the expected state after it.

Contents (alphabetical order):

* acl2-customization.lsp: Sets up the ARM package for interactive sessions
  started in this directory.

* harness.lisp: Loads a vector into the state, executes one instruction, and
  checks the result.  run-vectors runs every vector under two fillings that
  differ in every bit, which tells real mismatches from fields that depend on
  UNKNOWN values, and returns both kinds.  Its last section turns those
  results into one record per vector for report.lisp, with what only this
  model knows: the decoder's name for the instruction, and which of the
  model's error values decide a vector's outcome.  summarize-vectors runs
  vectors and summarizes the results.

* read-vectors.lisp: Reads a file of test vectors, one S-expression each, and
  reports the position and id of the first malformed one.

* report.lisp: Summarizes the records of a run without knowing anything
  about ARM32: gives each vector an outcome class (pass, mismatch, waived,
  UNKNOWN-dependent, coverage gap, unsupported, unpredictable, skipped),
  applies waivers, tallies the classes per instruction, and prints, writes,
  merges, and checks summaries.  Waivers must give a reason from a fixed list
  and a citation.  Another model's harness could use it unchanged.

* smoke.lisp: Hand-computed vectors, checked when the book is certified: the
  smoke tests proper, vectors whose results include UNKNOWN values, and one
  vector for each outcome class decided by the model's errors.

* unknown-values.lisp: Makes instructions with UNKNOWN results executable,
  by attaching an executable function to the model's unknown-bits.  It
  returns a marker value XORed with a "filling" stored in the state.

* vectors.lisp: The format of test vectors, and the recognizers that check
  it.  They reject unknown and repeated keys, so a misspelled key is caught
  instead of silently dropping its check.

---

To run the smoke tests, certify smoke.lisp.  Certification fails if any check
fails.  Either way, it prints a summary of each set of vectors, which cert.pl
writes to smoke.cert.out among the other output; for example:

```
  % grep 'smoke.*vectors' smoke.cert.out
  smoke: 12 vectors, 12 pass, 0 mismatch
  smoke UNKNOWN: 2 vectors, 0 mismatch, 2 UNKNOWN-dependent
  smoke classes: 5 vectors, 1 pass, 0 mismatch, 1 waived, 1 coverage gap, 1 unsupported, 1 unpredictable
```

Interactively, after including smoke.lisp,
`(run-vectors *smoke-vectors*)` returns (mv nil nil) when every vector passes,
and `(print-summary (summarize-vectors "smoke" *smoke-vectors* nil nil) 10 nil)`
prints the summary.
