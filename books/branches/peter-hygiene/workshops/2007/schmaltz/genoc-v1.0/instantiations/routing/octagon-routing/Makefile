include ../../../../../../../Makefile-generic

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
