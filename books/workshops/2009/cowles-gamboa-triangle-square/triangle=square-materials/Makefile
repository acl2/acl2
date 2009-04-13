# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS ?= ../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# From make dependencies:

log2.cert: log2.lisp
# log2.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/top.cert

tri-sq.cert: tri-sq.lisp
tri-sq.cert: log2.cert
# tri-sq.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/top.cert
