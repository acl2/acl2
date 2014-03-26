include ../Makefile-generic

BOOKS = $(patsubst %.lisp, %, $(wildcard *.lisp)) benchmarks

clean: clean-benchmarks

clean-benchmarks:
	rm -f benchmarks.lisp

benchmarks.lisp: cbf.cert

# Below is the result of running 'make dependencies' after executing
# "make ACL2_PCERT=".  If we run 'make dependencies' before creating
# benchmarks.lisp, we get some unfortunate error output.  So, we avoid
# using the usual -include of Makefile-deps.

alu-proofs.cert: alu-proofs.lisp
alu-proofs.cert: alu.cert

alu.cert: alu.lisp
alu.cert: bdd-primitives.cert

bdd-primitives.cert: bdd-primitives.lisp

benchmarks.cert: benchmarks.lisp
benchmarks.cert: bool-ops.cert
benchmarks.cert: benchmarks.acl2
benchmarks.cert: cbf.cert

bool-ops.cert: bool-ops.lisp

cbf.cert: cbf.lisp
cbf.cert: bool-ops.cert

hamming.cert: hamming.lisp
hamming.cert: bdd-primitives.cert

pg-theory.cert: pg-theory.lisp
pg-theory.cert: bdd-primitives.cert

# DEPENDENCIES FOR PROVISIONAL CERTIFICATION ONLY:
ifneq ($(ACL2_PCERT),)

# Dependencies for .pcert files:

alu-proofs.pcert: alu-proofs.acl2x

alu.pcert: alu.acl2x

bdd-primitives.pcert: bdd-primitives.acl2x

benchmarks.pcert: benchmarks.acl2x
benchmarks.pcert: benchmarks.acl2

bool-ops.pcert: bool-ops.acl2x

cbf.pcert: cbf.acl2x

hamming.pcert: hamming.acl2x

pg-theory.pcert: pg-theory.acl2x

benchmarks.pcert: benchmarks.acl2x
benchmarks.pcert: benchmarks.acl2

# Dependencies for .acl2x files (similar to those for .cert files):

alu-proofs.acl2x: alu-proofs.lisp
alu-proofs.acl2x: alu.acl2x

alu.acl2x: alu.lisp
alu.acl2x: bdd-primitives.acl2x

bdd-primitives.acl2x: bdd-primitives.lisp

benchmarks.acl2x: benchmarks.lisp
benchmarks.acl2x: bool-ops.acl2x
benchmarks.acl2x: benchmarks.acl2
benchmarks.acl2x: cbf.acl2x

bool-ops.acl2x: bool-ops.lisp

cbf.acl2x: cbf.lisp
cbf.acl2x: bool-ops.acl2x

hamming.acl2x: hamming.lisp
hamming.acl2x: bdd-primitives.acl2x

pg-theory.acl2x: pg-theory.lisp
pg-theory.acl2x: bdd-primitives.acl2x

benchmarks.acl2x: benchmarks.lisp
benchmarks.acl2x: bool-ops.acl2x
benchmarks.acl2x: benchmarks.acl2
benchmarks.acl2x: cbf.acl2x

# Dependencies for converting .pcert to .cert files:

alu-proofs.cert: alu-proofs.pcert
alu.cert: alu.pcert
bdd-primitives.cert: bdd-primitives.pcert
benchmarks.cert: benchmarks.pcert
bool-ops.cert: bool-ops.pcert
cbf.cert: cbf.pcert
hamming.cert: hamming.pcert
pg-theory.cert: pg-theory.pcert
benchmarks.cert: benchmarks.pcert

endif
