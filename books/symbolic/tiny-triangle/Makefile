# The following variable should represent the ACL2 source directory.
# It is the only variable in this Makefile that may need to be edited.
ACL2_SRC = ../../..

ACL2_SYSTEM_BOOKS ?= $(ACL2_SRC)/books
include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
ACL2 ?= $(ACL2_SRC)/saved_acl2

tiny-triangle-correct.cert: tiny-triangle-correct.lisp
tiny-triangle-correct.cert: ../tiny-fib/tiny-rewrites.cert
tiny-triangle-correct.cert: triangle-def.cert
tiny-triangle-correct.cert: ../generic/defsimulate.cert
tiny-triangle-correct.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/ordinals.cert

triangle-def.cert: triangle-def.lisp
triangle-def.cert: ../tiny-fib/tiny.cert
