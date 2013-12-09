# Note that ACL2 and ACL2_SYSTEM_BOOKS should be defined, e.g.:
# bash
# ACL2_DIR=/Users/kaufmann/acl2/v6-2/acl2-sources
# export ACL2=${ACL2_DIR}/saved_acl2
# export ACL2_SYSTEM_BOOKS=${ACL2_DIR}/books

# Example, when running from this directory:
# make ACL2=acl2ch ACL2_SYSTEM_BOOKS=/projects/acl2/devel/books

# WARNING: Do not run with -j (unless it's -j 1)!  Otherwise you may
# get errors.

ACL2_DIR ?= $(shell cd ../../../.. ; pwd)
export ACL2 ?= $(ACL2_DIR)/saved_acl2
export ACL2_SYSTEM_BOOKS ?= $(ACL2_DIR)/books

# There were issues with examples/thacker when testing in late
# September 2013 on Windows, so for now we remove that directory.  If
# you want it included at your local installation, simply uncomment
# the next line and comment out the one immediately below it.
# DIRS = translator examples/thacker
DIRS = translator
include $(ACL2_SYSTEM_BOOKS)/Makefile-subdirs
