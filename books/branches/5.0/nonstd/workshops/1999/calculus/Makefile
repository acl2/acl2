DIRS = book solutions
include ../../../Makefile-subdirs

# If ACL2(r) has been built then we can certify the case study input script as
# well, not only the solutions.
all-plus: all
	(cd book ; $(MAKE) ; cd ..)

clean: clean-book-dir

clean-book-dir:
	(cd book ; \
	$(MAKE) clean ; \
	cd ..)
