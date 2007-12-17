# The following variable should represent the ACL2 source directory.  It is the
# only variable in this Makefile that may need to be edited.
ACL2_SRC = ../../../../../..

include $(ACL2_SRC)/books/Makefile-generic
ACL2 = $(ACL2_SRC)/saved_acl2

BOOKS = symbol-fns symbol-fns-exports

# Dependencies:

symbol-fns.cert: symbol-fns.lisp
symbol-fns.cert: symbol-fns.acl2
symbol-fns.acl2: symbol-fns-exports.cert

symbol-fns-exports.cert: symbol-fns-exports.lisp
symbol-fns-exports.cert: symbol-fns-exports.acl2
