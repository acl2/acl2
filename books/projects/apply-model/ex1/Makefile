SHELL ?= $(shell which bash)

ACL2 ?= ../../../../saved_acl2

ACL2_SYSTEM_BOOKS ?= ../../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

clean: clean-more

.PHONY: clean-more
clean-more:
	rm -f evaluation-apply.lisp evaluation-user-defs.lisp Makefile-deps

REBUILD_MAKEFILE_DEPS := $(shell \
  rm -f Makefile-deps Makefile-deps.out && \
  (diff ../apply.lisp evaluation-apply.lisp 2>&1 > /dev/null || \
   cp -pf ../apply.lisp evaluation-apply.lisp) && \
  (diff user-defs.lisp evaluation-user-defs.lisp 2>&1 > /dev/null || \
   cp -pf user-defs.lisp evaluation-user-defs.lisp) && \
  $(ACL2_SYSTEM_BOOKS)/build/cert.pl --include-excludes -s Makefile-deps *.lisp)

include Makefile-deps
