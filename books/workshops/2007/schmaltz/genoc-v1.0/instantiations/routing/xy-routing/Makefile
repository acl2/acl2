# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS = ../../../../../../../../books

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# Pasted in from "make dependencies":

xy-routing.cert: xy-routing.lisp
xy-routing.cert: ../../../generic-modules/GeNoC-routing.cert
xy-routing.cert: ../../nodeset/2D-mesh-nodeset.cert
# xy-routing.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
# xy-routing.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert
