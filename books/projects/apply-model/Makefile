# Target "all" is the top target of Makefile-generic, and target "top"
# is the top target of Makefile-psubdirs.  We must make "all" before
# "top".

top ex1 ex2: all
DIRS = ex1 ex2

ACL2 ?= ../../../saved_acl2

ACL2_SYSTEM_BOOKS ?= ../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
include $(ACL2_SYSTEM_BOOKS)/Makefile-psubdirs

-include Makefile-deps
