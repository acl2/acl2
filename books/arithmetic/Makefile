include ../Makefile-generic
-include Makefile-deps

# Unfortunately, we cannot certify top-with-meta until we have completed
# certification in the meta/ directory.  So we set BOOKS so that
# top-with-meta.cert is not made by default.  The ":=" makes the assignment
# non-recursive.

BOOKS := $(filter-out top-with-meta,$(BOOKS))

# Extra deps for top-with-meta because of circularity with meta directory.
# Messy messy.

top-with-meta.cert: top-with-meta.lisp
top-with-meta.cert: top.cert
top-with-meta.cert: ../meta/meta.cert
# DEPENDENCIES FOR PROVISIONAL CERTIFICATION ONLY:
ifneq ($(ACL2_PCERT),)
top-with-meta.pcert: top-with-meta.acl2x
top-with-meta.acl2x: top-with-meta.lisp
top-with-meta.acl2x: top.acl2x
top-with-meta.acl2x: ../meta/meta.acl2x
top-with-meta.cert: top-with-meta.pcert
endif

