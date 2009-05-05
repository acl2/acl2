# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS ?= ../../../../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# Pasted in from "make dependencies":

getting_rid_of_mod.cert: getting_rid_of_mod.lisp
getting_rid_of_mod.cert: routing_defuns.cert

mod_lemmas.cert: mod_lemmas.lisp
# mod_lemmas.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
# mod_lemmas.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert

routing_defuns.cert: routing_defuns.lisp
routing_defuns.cert: mod_lemmas.cert

routing_local_lemmas.cert: routing_local_lemmas.lisp
routing_local_lemmas.cert: getting_rid_of_mod.cert
routing_local_lemmas.cert: ../../nodeset/octagon-nodeset.cert
# routing_local_lemmas.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defuns.cert
# routing_local_lemmas.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defthms.cert

routing_main.cert: routing_main.lisp
routing_main.cert: routing_local_lemmas.cert
routing_main.cert: ../../../generic-modules/GeNoC-routing.cert
