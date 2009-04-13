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

sets.cert: sets.lisp

simple.cert: simple.lisp
simple.cert: ../../routing/XY/XYRouting.cert
simple.cert: ../../departure/simple/simple-R4D.cert
simple.cert: trlst-equal.cert
simple.cert: ../../scheduling/circuit-switching-global/circuit.cert
simple.cert: ../../simulation/simple/simple.cert
simple.cert: ../../interfaces/dummy-interfaces/interfaces-computes.cert
simple.cert: ../../../generic-modules/GeNoC.cert
simple.cert: sets.cert

trlst-equal.cert: trlst-equal.lisp
trlst-equal.cert: ../../../generic-modules/GeNoC-misc.cert
