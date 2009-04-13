
# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.

ACL2_SYSTEM_BOOKS = ../../../../..
ACL2 ?= ../../../../../../saved_acl2
include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

network.cert: network.lisp
network.cert: types.cert

departure.cert: departure.lisp
departure.cert: network.cert

datalink.cert: datalink.lisp
datalink.cert: types.cert

routecontrol.cert: routecontrol.lisp
routecontrol.cert: types.cert

flowcontrol.cert: flowcontrol.lisp
flowcontrol.cert: types.cert

router.cert: router.lisp
router.cert: datalink.cert
router.cert: routecontrol.cert
router.cert: flowcontrol.cert

GeNoC.cert: GeNoC.lisp
GeNoC.cert: network.cert
GeNoC.cert: departure.cert
GeNoC.cert: router.cert

types.cert: types.lisp