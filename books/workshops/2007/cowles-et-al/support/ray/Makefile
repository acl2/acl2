# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS ?= ../../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# From make dependencies:

reflexive-macros.cert: reflexive-macros.lisp
reflexive-macros.cert: reflexive.cert

reflexive.cert: reflexive.lisp
# reflexive.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
