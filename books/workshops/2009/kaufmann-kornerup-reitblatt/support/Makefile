# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS ?= ../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# From make dependencies:

gauss-fns.cert: gauss-fns.lisp
gauss-fns.cert: gauss-fns.acl2
gauss-fns.cert: preliminaries.cert

gauss-work.cert: gauss-work.lisp
gauss-work.cert: generic-loop-inv.cert
gauss-work.cert: gauss-work.acl2
gauss-work.cert: gauss-fns.cert

gauss.cert: gauss.lisp
gauss.cert: gauss-fns.cert
gauss.cert: gauss-work.cert

generic-loop-inv.cert: generic-loop-inv.lisp
# generic-loop-inv.cert: $(ACL2_SYSTEM_BOOKS)/defexec/other-apps/records/records.cert

preliminaries.cert: preliminaries.lisp
# preliminaries.cert: $(ACL2_SYSTEM_BOOKS)/defexec/other-apps/records/records.cert
preliminaries.cert: preliminaries.acl2
# preliminaries.cert: $(ACL2_SYSTEM_BOOKS)/defexec/other-apps/records/records.cert
