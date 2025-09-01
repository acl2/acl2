The Axe Toolkit
===============================

This directory contains Kestrel's open-source Axe toolkit.

Tools of interest may include rewriter-basic.lisp and prover-basic.lisp.

The [jvm/](jvm) directory contains Axe lifters for JVM bytecode programs.

The [x86/](x86) directory contains Axe lifters for x86 binary programs.

The [risc-v/](risc-v) directory contains Axe lifters for RISC-V binary programs.

The [r1cs/](r1cs) directory contains Axe lifters for Rank-1 Constraint Systems.

For more information, see the [Axe Webpage][Axe] and the [Axe
Docmentation][Axe-doc].  Much more documenation is available in the
source files themselves.

[Axe]: https://kestrel.edu/research/axe/

[Axe-doc]: https://acl2.org/doc/?topic=ACL2____AXE

# Setup: Installing the STP solver.

The STP SMT solver is needed for most uses of Axe.  See the [STP doc topic][STP-doc] for
information about installing it.

[STP-doc]: https://acl2.org/doc/?topic=ACL2____STP