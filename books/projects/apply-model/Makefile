# Target "all" is the top target of Makefile-generic.  We avoid
# including Makefile-subdirs or Makefile-psubdirs because we want to
# be sure to control the order: first this directory, then
# subdirectories.

ACL2 ?= ../../../saved_acl2
ACL2_SYSTEM_BOOKS ?= ../..

.PHONY: top all-subdirs ex1 ex2 clean-subdirs

top: all
	$(MAKE) all-subdirs

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
-include Makefile-deps

all-subdirs: ex1 ex2

ex1:
	cd ex1 ; $(MAKE)

ex2:
	cd ex2 ; $(MAKE)

clean: clean-subdirs

clean-subdirs:
	cd ex1 ; $(MAKE) clean
	cd ex2 ; $(MAKE) clean
