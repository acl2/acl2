# The following variable should represent the ACL2 source directory.
# It is the only variable in this Makefile that may need to be edited.
ACL2_SRC = ../../..

ACL2_SYSTEM_BOOKS = $(ACL2_SRC)/books
include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
ACL2 = $(ACL2_SRC)/saved_acl2

# This makefile certifies the m5 model, including a recursive factorial
# method. This is unchanged (well almost) from J's standard Makefile.

demo.cert: demo.lisp
demo.cert: utilities.cert
demo.cert: demo.acl2
demo.acl2: utilities.cert

m5.cert: m5.lisp
m5.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert
m5.cert: m5.acl2

utilities.cert: utilities.lisp
utilities.cert: m5.cert
utilities.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
utilities.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
utilities.cert: utilities.acl2
utilities.acl2: m5.cert
