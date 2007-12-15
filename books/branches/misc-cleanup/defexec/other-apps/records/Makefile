include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2

# Dependencies:

inline.cert: inline.lisp

records.cert: records.lisp
# records.cert: $(ACL2_SYSTEM_BOOKS)/misc/total-order.cert

recordsim.cert: recordsim.lisp
recordsim.cert: records.cert
recordsim.cert: inline.cert
