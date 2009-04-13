
# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS = ../../../../../../..
ACL2 ?= ../../../../../../../../saved_acl2

#include ${ACL2_SYSTEM_BOOKS}/Makefile-subdirs
include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
#ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

circuit.cert: circuit.lisp
circuit.cert: ../../../generic-modules/GeNoC-scheduling.cert
circuit.cert: intersect.cert
circuit.cert: ../../ntkstate/simple/simple.cert
circuit.cert: ../../synchronization/circuit-global/circuit.cert
circuit.cert: ../../genoc/simple-ct-global/trlst-equal.cert

intersect.cert: intersect.lisp
# intersect.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defuns.cert
# intersect.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defthms.cert