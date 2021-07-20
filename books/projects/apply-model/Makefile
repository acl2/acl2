# Target "all" is the top target of Makefile-generic.  We avoid
# including Makefile-subdirs or Makefile-psubdirs because we want to
# be sure to control the order: first this directory, then
# subdirectories.

# At one time we had something like this:

# top: all
# 	$(MAKE) all-subdirs
# all-subdirs: ex1 ex2

# However, I (Matt K.) started seeing surprising (to me) dependency
# errors, perhaps due to some change in GNU Make around version 4.1.
# So now I take care to ensure that all books in the current directory
# are certified before certification is attempted in the
# subdirectories and, moreover, those subdirectories are done
# sequentially (to avoid the parallel recertification of
# e.g. apply-prim.lisp in the present directory on behalf of ex1/ and
# ex2/).

ACL2 ?= ../../../saved_acl2
ACL2_SYSTEM_BOOKS ?= ../..

.PHONY: top ex1 ex2 clean-subdirs clean-Makefile-tmp

top: Makefile-tmp
	@$(MAKE) -s -f Makefile-tmp all ACL2_BOOKS_MAKEFILE=Makefile-tmp
	@$(MAKE) -s ex1
	@$(MAKE) -s ex2

Makefile-tmp : Makefile Makefile-deps
	@echo "Making $(PWD)/Makefile-tmp"
	@cat Makefile Makefile-deps > Makefile-tmp

apply-prim.cert : $(ACL2_SYSTEM_BOOKS)/build/first-order-like-terms-and-out-arities.certdep

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

ex1:
	@cd ex1 ; $(MAKE) -s

ex2:
	@cd ex2 ; $(MAKE) -s

clean: clean-subdirs clean-Makefile-tmp

clean-Makefile-tmp:
	@rm -f Makefile-tmp

clean-subdirs:
	@cd ex1 ; $(MAKE) -s clean > /dev/null
	@cd ex2 ; $(MAKE) -s clean > /dev/null
