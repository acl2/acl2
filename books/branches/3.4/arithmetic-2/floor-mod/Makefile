include ../../Makefile-generic
ACL2 = ../../../saved_acl2

# Dependencies:

# From make -s dependencies:

floor-mod-helper.cert: floor-mod-helper.lisp
floor-mod-helper.cert: ../meta/top.cert
floor-mod-helper.cert: ../../ihs/quotient-remainder-lemmas.cert

floor-mod.cert: floor-mod.lisp
floor-mod.cert: floor-mod-helper.cert

