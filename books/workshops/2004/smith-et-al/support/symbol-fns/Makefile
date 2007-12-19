# The following variable should represent the ACL2 source directory.  It and
# ACL2 are the only variables in this Makefile that may need to be edited.
ACL2_SYSTEM_BOOKS ?= ../../../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
ACL2 ?= $(ACL2_SYSTEM_BOOKS)/../saved_acl2

BOOKS = symbol-fns symbol-fns-exports

# Dependencies:

symbol-fns.cert: symbol-fns.lisp
symbol-fns.cert: symbol-fns.acl2
symbol-fns.acl2: symbol-fns-exports.cert

symbol-fns-exports.cert: symbol-fns-exports.lisp
symbol-fns-exports.cert: symbol-fns-exports.acl2
