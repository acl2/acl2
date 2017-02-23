SHELL ?= $(shell which bash)

ACL2 ?= ../../../../saved_acl2

ACL2_SYSTEM_BOOKS ?= ../../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

clean: clean-more

clean-more:
	rm -f evaluation-apply.lisp evaluation-user-defs.lisp Makefile-deps

ifndef NO_RESCAN

REBUILD_MAKEFILE_DEPS := $(shell \
  rm -f Makefile-deps Makefile-deps.out && \
  (diff apply.lisp Makefile 2>&1 > /dev/null || \
   cp -pf ../apply.lisp evaluation-apply.lisp) && \
  (diff user-defs.lisp evaluation-user-defs.lisp 2>&1 > /dev/null || \
   cp -pf user-defs.lisp evaluation-user-defs.lisp) && \
  $(ACL2_SYSTEM_BOOKS)/build/cert.pl *.lisp -s Makefile-deps)

endif # ifndef NO_RESCAN

-include Makefile-deps
