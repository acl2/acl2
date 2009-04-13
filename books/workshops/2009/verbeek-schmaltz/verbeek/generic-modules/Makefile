
# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.

ACL2_SYSTEM_BOOKS = ../../../../..
ACL2 ?= ../../../../../../saved_acl2

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic
include ${ACL2_SYSTEM_BOOKS}/Makefile-subdirs

interfaces-computes.cert: interfaces-computes.lisp
interfaces-computes.cert: GeNoC-misc.cert
interfaces-computes.cert: GeNoC-interfaces.cert

GeNoC-departure.cert: GeNoC-departure.lisp
GeNoC-departure.cert: GeNoC-nodeset.cert
GeNoC-departure.cert: GeNoC-misc.cert
GeNoC-departure.cert: GeNoC-ntkstate.cert

GeNoC-interfaces.cert: GeNoC-interfaces.lisp
GeNoC-interfaces.cert: $(ACL2_SYSTEM_BOOKS)/make-event/defspec.cert

GeNoC-misc.cert: GeNoC-misc.lisp
GeNoC-misc.cert: GeNoC-types.cert
GeNoC-misc.cert: $(ACL2_SYSTEM_BOOKS)/make-event/defspec.cert

GeNoC-nodeset.cert: GeNoC-nodeset.lisp
GeNoC-nodeset.cert: $(ACL2_SYSTEM_BOOKS)/make-event/defspec.cert

GeNoC-ntkstate.cert: GeNoC-ntkstate.lisp
GeNoC-ntkstate.cert: GeNoC-nodeset.cert
GeNoC-ntkstate.cert: GeNoC-misc.cert
GeNoC-ntkstate.cert: GeNoC-types.cert
GeNoC-ntkstate.cert: $(ACL2_SYSTEM_BOOKS)/make-event/defspec.cert

GeNoC-priority.cert: GeNoC-priority.lisp
GeNoC-priority.cert: own-perm.cert
GeNoC-priority.cert: GeNoC-types.cert
GeNoC-priority.cert: GeNoC-misc.cert

GeNoC-routing.cert: GeNoC-routing.lisp
GeNoC-routing.cert: GeNoC-nodeset.cert
GeNoC-routing.cert: GeNoC-misc.cert

GeNoC-scheduling.cert: GeNoC-nodeset.cert
GeNoC-scheduling.cert: GeNoC-misc.cert
GeNoC-scheduling.cert: GeNoC-ntkstate.cert

GeNoC-simulation.cert: GeNoC-simulation.lisp
GeNoC-simulation.cert: $(ACL2_SYSTEM_BOOKS)/make-event/defspec.cert

GeNoC-synchronization.cert: GeNoC-synchronization.lisp
GeNoC-synchronization.cert: GeNoC-misc.cert

GeNoC-types.cert: GeNoC-types.lisp
GeNoC-types.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defuns.cert
GeNoC-types.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defthms.cert
GeNoC-types.cert: $(ACL2_SYSTEM_BOOKS)/textbook/chap11/qsort.cert

GeNoC.cert: GeNoC.lisp
GeNoC.cert: interfaces-computes.cert
GeNoC.cert: GeNoC-scheduling.cert
GeNoC.cert: GeNoC-routing.cert
GeNoC.cert: GeNoC-departure.cert
GeNoC.cert: GeNoC-simulation.cert

own-perm.cert: own-perm.lisp
