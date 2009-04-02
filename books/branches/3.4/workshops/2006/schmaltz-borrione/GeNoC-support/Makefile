# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS = ../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# Pasted in from "make dependencies":

GeNoC-interfaces.cert: GeNoC-interfaces.lisp

GeNoC.cert: GeNoC.lisp
GeNoC.cert: GeNoC-scheduling.cert
GeNoC.cert: GeNoC-routing.cert
GeNoC.cert: GeNoC-interfaces.cert

GeNoC-misc.cert: GeNoC-misc.lisp
GeNoC-misc.cert: GeNoC-types.cert

GeNoC-nodeset.cert: GeNoC-nodeset.lisp

GeNoC-routing.cert: GeNoC-routing.lisp
GeNoC-routing.cert: GeNoC-nodeset.cert
GeNoC-routing.cert: GeNoC-misc.cert

GeNoC-scheduling.cert: GeNoC-scheduling.lisp
GeNoC-scheduling.cert: GeNoC-nodeset.cert
GeNoC-scheduling.cert: GeNoC-misc.cert

GeNoC-types.cert: GeNoC-types.lisp
# GeNoC-types.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defuns.cert
# GeNoC-types.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defthms.cert
# GeNoC-types.cert: $(ACL2_SYSTEM_BOOKS)/textbook/chap11/qsort.cert
