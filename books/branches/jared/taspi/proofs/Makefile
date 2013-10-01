include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
BOOKS = sets omerge-good-order fringes-taspi

sets.cert: sets.lisp
sets.cert: sets.acl2

omerge-good-order.cert: omerge-good-order.lisp
omerge-good-order.cert: omerge-good-order.acl2
omerge-good-order.acl2: sets.cert

fringes-taspi.cert: fringes-taspi.lisp
fringes-taspi.cert: fringes-taspi.acl2
fringes-taspi.acl2: omerge-good-order.cert
