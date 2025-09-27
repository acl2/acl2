The Axe Toolkit
===============================

This directory contains Kestrel's open-source Axe toolkit.

General purpose Axe tools are in this axe/ directory.  Tools of
interest may include rewriter-basic, prover-basic,
def-simplified-basic, and unroll-spec-basic.  See
[top.lisp/](top.lisp) for more information about the files in this
directory.

The [jvm/](jvm) subdirectory contains Axe tools for JVM bytecode programs.

The [x86/](x86) subdirectory contains Axe tools for x86 binary programs.

The [risc-v/](risc-v) subdirectory contains Axe tools for RISC-V binary programs.

The [r1cs/](r1cs) subdirectory contains Axe tools for Rank-1 Constraint Systems.

See also the examples in:

[jvm/examples/](jvm/examples)

[x86/examples/](x86/examples)

[risc-v/examples/](risc-v/examples)

For more information, see the [Axe Webpage][Axe] and the [Axe
Documentation][Axe-doc].  Much more documenation is available as
comments in the source files themselves.

[Axe]: https://kestrel.edu/research/axe/

[Axe-doc]: https://acl2.org/doc/?topic=ACL2____AXE

# Setup: Installing the STP solver.

The STP SMT solver is needed for most uses of Axe.  See the [STP doc topic][STP-doc] for
information about installing it.

[STP-doc]: https://acl2.org/doc/?topic=ACL2____STP