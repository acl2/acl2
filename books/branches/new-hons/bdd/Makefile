include ../Makefile-generic

BOOKS = $(patsubst %.lisp, %, $(wildcard *.lisp)) benchmarks

clean: clean-benchmarks

clean-benchmarks:
	rm -f benchmarks.lisp

benchmarks.lisp: cbf.cert

# Below is the result of running 'make Makefile-deps', except for one
# addition, a noted.  We get a warning, however, if we run that make
# command; so instead we include the dependencies below.

alu-proofs.cert: alu-proofs.lisp
alu-proofs.cert: alu.cert

alu.cert: alu.lisp
alu.cert: bdd-primitives.cert

bdd-primitives.cert: bdd-primitives.lisp

bool-ops.cert: bool-ops.lisp

cbf.cert: cbf.lisp
cbf.cert: bool-ops.cert

hamming.cert: hamming.lisp
hamming.cert: bdd-primitives.cert

pg-theory.cert: pg-theory.lisp
pg-theory.cert: bdd-primitives.cert

benchmarks.cert: benchmarks.lisp
benchmarks.cert: benchmarks.acl2
benchmarks.cert: cbf.cert
# Added manually:
benchmarks.cert: bool-ops.cert
