# The following variable should represent the ACL2 source directory.
# It is the only variable in this Makefile that may need to be edited.
ACL2_SRC = ../../../../..

include $(ACL2_SRC)/books/Makefile-generic
ACL2 = $(ACL2_SRC)/saved_acl2

defcoerce.cert: defcoerce.lisp
defcoerce.cert: generic.cert
# defcoerce.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert

defpun-exec.cert: defpun-exec.lisp
# defpun-exec.cert: defpun.cert # from a multi-line comment
# defpun-exec.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert

generic.cert: generic.lisp
# generic.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert
