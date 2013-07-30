# Note that ACL2 and ACL2_SYSTEM_BOOKS should be defined, e.g.:
# bash
# ACL2_DIR=/Users/kaufmann/acl2/v6-2/acl2-sources
# export ACL2=${ACL2_DIR}/saved_acl2
# export ACL2_SYSTEM_BOOKS=${ACL2_DIR}/books

# Example, when running from this directory:
# make ACL2=acl2ch ACL2_SYSTEM_BOOKS=/projects/acl2/devel/books

# WARNING: Do not run with -j (unless it's -j 1)!  Otherwise you may
# get errors.

ACL2_DIR ?= $(shell cd ../../.. ; pwd)
export ACL2 ?= $(ACL2_DIR)/saved_acl2
export ACL2_SYSTEM_BOOKS ?= $(ACL2_DIR)/books

DIRS = translator examples/thacker
include $(ACL2_SYSTEM_BOOKS)/Makefile-subdirs
