# Target "all" is the top target of Makefile-generic, and target "top"
# is the top target of Makefile-psubdirs.  We must make "all" before
# "top".

# Matt K. comment: However, I have seen ex1 and ex2 made before all
# completed!  This happened when attempting an "everything" regression
# after books/tools/flag.lisp had changed.  The log showed that the
# "make" command for this top-level directory was issued before
# entering ex1 and ex2, but that certification began in those
# directories before this top directory's "all" target completed.
# It's a mystery to me.  Perhaps it's a bug in GNU Make 3.80.  At any
# rate, I'll move the following line below the includes.
# top ex1 ex2: all

DIRS = ex1 ex2

ACL2 ?= ../../../saved_acl2

ACL2_SYSTEM_BOOKS ?= ../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
include $(ACL2_SYSTEM_BOOKS)/Makefile-psubdirs

# See comments above for why the following line is down here.
top ex1 ex2: all

-include Makefile-deps
