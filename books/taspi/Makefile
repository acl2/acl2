# Avoid provisional certification with `make' until we start using Makefile-deps.
override ACL2_PCERT =

export ACL2_SYSTEM_BOOKS ?= $(shell (cd .. ; pwd))

DIRS = code database single-input sets-input \
	tree-distance tree-score tree-generation \
	proofs 
#read-write : nothing to be certified (raw-mode support)
include $(ACL2_SYSTEM_BOOKS)/Makefile-subdirs
