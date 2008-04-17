# The following variable should represent the ACL2 source directory.
# It is the only variable in this Makefile that may need to be edited

ACL2_SYSTEM_BOOKS ?= ../..
ACL2_SRC = ../../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
ACL2 = $(ACL2_SRC)/saved_acl2


defstobj+.cert: defstobj+.lisp
defstobj+.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert

fib-def.cert: fib-def.lisp
fib-def.cert: tiny.cert

tiny-rewrites.cert: tiny-rewrites.lisp
tiny-rewrites.cert: tiny.cert
tiny-rewrites.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert

tiny.cert: tiny.lisp
tiny.cert: defstobj+.cert
tiny.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
tiny.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defthms.cert
tiny.cert: $(ACL2_SYSTEM_BOOKS)/ihs/logops-lemmas.cert
tiny.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
