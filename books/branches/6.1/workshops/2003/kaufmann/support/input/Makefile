include ../../../../../Makefile-generic

# Avoid provisional certification since we are not using Makefile-deps
# (because there are generated .lisp files):
override ACL2_PCERT =

BOOKS = defs-in inputs lemmas-in defs-out defs-eq lemmas-out 

FAILED = 0

all: check.txt

# Compare generated .lisp files against expected files, in ../output/ directory.
check.txt: defs-eq.cert defs-out.cert lemmas-in.cert defs-in.cert inputs.cert lemmas-out.cert 
	@diff defs-out.lisp ../output/defs-out.lisp || (echo "defs-out.lisp failed" ; $(MAKE) -s --no-print-directory FAILED)
	@diff defs-eq.lisp ../output/defs-eq.lisp || (echo "defs-eq.lisp failed" ; $(MAKE) -s --no-print-directory FAILED)
	@diff lemmas-out.lisp ../output/lemmas-out.lisp || (echo "lemmas-out.lisp failed" ; $(MAKE) -s --no-print-directory FAILED)
	touch check.txt

# Dependencies:

# Created manually:

defs-eq.lisp lemmas-out.lisp: defs-out.lisp

defs-out.lisp: defs-in.cert lemmas-in.lisp ../../../../../misc/simplify-defuns.cert
	$(ACL2) < defs-out.cmds > defs-out.lisp.out

clean: clean-more

clean-more:
	rm -f defs-out.lisp defs-eq.lisp lemmas-out.lisp check.txt

# Created with make dependencies after a successful run:

defs-in.cert: defs-in.lisp
defs-in.cert: defs-in.acl2
defs-in.cert: inputs.cert

inputs.cert: inputs.lisp

lemmas-in.cert: lemmas-in.lisp
lemmas-in.cert: defs-in.cert

defs-out.cert: defs-out.lisp
defs-out.cert: defs-out.acl2
defs-out.cert: inputs.cert

defs-eq.cert: defs-eq.lisp
defs-eq.cert: defs-eq.acl2
defs-eq.cert: defs-in.cert
defs-eq.cert: defs-out.cert

lemmas-out.cert: lemmas-out.lisp
lemmas-out.cert: defs-out.cert
lemmas-out.cert: lemmas-in.cert
lemmas-out.cert: defs-eq.cert
