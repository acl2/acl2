# WARNING: Do not run with -j (unless it's -j 1)!  Otherwise you may
# get errors.

# We compute the variable ACL2_DIR if it is not already defined.
# Using only pwd on Windows, Harsh Raju Chamarthi reported a failure.
# It turned out that the cbd seemed was set to a path of the form
# "C:/msys/home/...", but an include-book command failed with
# corresponding pathname "/home/...".  So we make an attempt to
# include the leading "C:/msys" for msys/mingw, and for cygwin we try
# to get a suitable value using cygpath.

ifneq ($(findstring MINGW, $(shell uname)),)
ACL2_DIR ?= $(shell cd ../../../.. ; pwd -W)
else
ifneq ($(findstring CYGWIN, $(shell uname)),)
ACL2_DIR ?= $(shell cd ../../../.. ; cygpath -m `pwd`)
else
ACL2_DIR ?= $(shell cd ../../../.. ; pwd)
endif
endif

# $(warning ACL2_DIR is $(ACL2_DIR))

export ACL2 ?= $(ACL2_DIR)/saved_acl2
export ACL2_SYSTEM_BOOKS ?= $(ACL2_DIR)/books

DIRS = translator examples/thacker
include $(ACL2_SYSTEM_BOOKS)/Makefile-subdirs

# For target.cert:

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
top: target.cert
