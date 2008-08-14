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
