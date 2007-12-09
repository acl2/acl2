include ../Makefile-generic

BOOKS = $(patsubst %.lisp, %, $(wildcard *.lisp)) benchmarks

clean: clean-benchmarks

clean-benchmarks:
	rm -f benchmarks.lisp

benchmarks.lisp: cbf.cert

# Other dependencies:

alu-proofs.cert: alu-proofs.lisp
alu-proofs.cert: alu.cert

alu.cert: alu.lisp
alu.cert: bdd-primitives.cert

bdd-primitives.cert: bdd-primitives.lisp

benchmarks.cert: benchmarks.lisp
benchmarks.cert: bool-ops.cert
benchmarks.cert: benchmarks.acl2
benchmarks.acl2: cbf.cert

bool-ops.cert: bool-ops.lisp

cbf.cert: cbf.lisp
cbf.cert: bool-ops.cert

hamming.cert: hamming.lisp
hamming.cert: bdd-primitives.cert

pg-theory.cert: pg-theory.lisp
pg-theory.cert: bdd-primitives.cert
