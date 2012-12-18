
# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
#ACL2_SYSTEM_BOOKS = /projects/hvg/reeber-local/v2-9-4-linux/books
ACL2_SYSTEM_BOOKS ?= $(shell cd ../../../.. ; pwd)

# Avoid provisional certification since the presence of "Fake
# dependency added to avoid parallel execution" below makes us
# nervious about adding parallelism with provisional certification.
override ACL2_PCERT =

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 ?= ${ACL2_SYSTEM_BOOKS}/../saved_acl2

BOOKS = test-help sudoku benchmark test-incremental tutorial

clean: sat-clean

# Pasted in from "make dependencies":
sat-clean: 
	rm -f *.cert *~ *.sexpr *.d *.sot
	rm -f -r sat-temp-files

.PHONY: sat-clean

test-help.cert: test-help.lisp
test-help.cert: ../clause-processors/sat-clause-processor.cert
test-help.cert: test-help.acl2

benchmark.cert: benchmark.lisp
benchmark.cert: test-help.cert

# Fake dependency added to avoid parallel execution
test-incremental.cert: benchmark.cert
test-incremental.cert: test-incremental.lisp
test-incremental.cert: test-help.cert

# Fake dependency added to avoid parallel execution
sudoku.cert: test-incremental.cert
sudoku.cert: sudoku.lisp
sudoku.cert: test-help.cert

tutorial.cert: tutorial.lisp
tutorial.cert: sudoku.cert

