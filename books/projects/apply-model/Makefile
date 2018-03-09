# Target "all" is the top target of Makefile-generic, and target "top"
# is the top target of Makefile-psubdirs.  We must make "all" before
# "top", and then we want to make "top".  So we include
# Makefile-psubdirs first so that "top" is the top-level target, but
# we make "top" depend on "all" so that "all" is built before "top".

top: all

DIRS = ex1 ex2

ACL2 ?= ../../../saved_acl2

ACL2_SYSTEM_BOOKS ?= ../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-psubdirs
include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

-include Makefile-deps
