include ../../../../Makefile-generic

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
