Smtlink 3
====================

*Smtlink 3* is a framework for translating ACL2 proof goals to SMT-LIB for external proof. It uses the ACL2 rewriter for verified type inference and term rewriting.

### Requirements

* Z3

The default Smtlink configuration defaults to using whichever z3 binary exists in your path. Note that previous versions of Smtlink used Python to interact with Z3, so if you have an old *smtlink-config* file in your home directory, you should delete it, move it out of the way, or change *smt-cmd* to point to a Z3 executable.

### Build Smtlink

The Makefile in this ACL2 2026 Workshop subdirectory has two targets:
The *top* target builds the Smtlink 3 books.
The *example* target runs the proofs from the paper.
