# The following variable should represent the ACL2 source directory.  It and
# ACL2 are the only variables in this Makefile that may need to be edited.
ACL2_SYSTEM_BOOKS ?= ../../../../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
ACL2 ?= $(ACL2_SYSTEM_BOOKS)/../saved_acl2

BOOKS = list-top mv-nth lists list-exports

list-top.cert: list-top.lisp
list-top.cert: list-top.acl2
list-top.acl2: lists.cert
list-top.acl2: list-exports.cert
list-top.acl2: mv-nth.cert

mv-nth.cert: mv-nth.lisp
mv-nth.cert: cert.acl2

lists.cert: lists.lisp
# lists.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
lists.cert: cert.acl2

list-exports.cert: list-exports.lisp
list-exports.cert: cert.acl2
