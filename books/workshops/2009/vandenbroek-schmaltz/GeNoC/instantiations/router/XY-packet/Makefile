
# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.

ACL2_SYSTEM_BOOKS = ../../../../../../..
ACL2 ?= ../../../../../../../../saved_acl2
include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

router.cert: router.lisp
router.cert: ../../../generic-modules/router.cert
router.cert: ../../datalink/simple/datalink.cert
router.cert: ../../routecontrol/xy/routecontrol.cert
router.cert: ../../flowcontrol/packet/flowcontrol.cert
