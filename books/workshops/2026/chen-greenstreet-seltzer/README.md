Smtlink 3
====================

*Smtlink 3* is a framework for translating ACL2 proof goals to SMT-LIB for external proof. It uses the ACL2 rewriter for verified type inference and term rewriting.

### Requirements

* Z3

The default Smtlink configuration defaults to using whichever z3 binary exists in your path. If you have z3 in a location outside your path, copy *smtlink3-config* to your home directory and modify *smt-cmd* to point to a z3 executable.

### Build Smtlink

The Makefile in this ACL2 2026 Workshop subdirectory has two targets:
The *top* target builds the Smtlink 3 books.
The *example* target runs the proofs from the paper.
