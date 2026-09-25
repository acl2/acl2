ARM32 model test harness
for running the ARM32 model on concrete test vectors

Copyright (C) 2026 Kestrel Institute

License: A 3-clause BSD license. See the file books/3BSD-mod.txt.

Author: Eric McCarthy (mccarthy@kestrel.edu)

---

This directory contains a harness for running the ARM32 model in
books/kestrel/arm on concrete test vectors.  A test vector gives the state
before one instruction and the expected state after it.

Contents:

* acl2-customization.lsp: Sets up the ARM package for interactive sessions
  started in this directory.

* vectors.lisp: The format of test vectors, and the recognizers that check
  it.  They reject unknown and repeated keys, so a misspelled key is caught
  instead of silently dropping its check.

* unknown-values.lisp: Makes instructions with UNKNOWN results executable,
  by attaching an executable function to the model's unknown-bits.  It
  returns a marker value XORed with a "filling" stored in the state.

* harness.lisp: Loads a vector into the state, executes one instruction, and
  checks the result.  The entry point, run-vectors, runs every vector under
  two fillings that differ in every bit, which tells real mismatches from
  fields that depend on UNKNOWN values, and returns both kinds.

* smoke.lisp: Hand-computed vectors, checked when the book is certified.

To run the smoke tests, certify smoke.lisp.  Interactively, after including
smoke.lisp, (run-vectors *smoke-vectors*) returns (mv nil nil) when every
vector passes.
