
ACL2_SYSTEM_BOOKS = ../../..

DIRS = sat clause-processors sat-tests bv-smt-solver 

include ${ACL2_SYSTEM_BOOKS}/Makefile-psubdirs

.PHONY: $(DIRS)

clause-processors: sat
sat-tests: clause-processors
bv-smt-solver: clause-processors

