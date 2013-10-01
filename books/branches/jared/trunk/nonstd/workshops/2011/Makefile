# This is the workshops/2011/ Makefile under books/nonstd.

DIRS = reid-gamboa-differentiator/support
include ../../Makefile-subdirs

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
