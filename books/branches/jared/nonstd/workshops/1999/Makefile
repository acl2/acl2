# This is the workshops/1999/ Makefile under books/nonstd.

DIRS = analysis calculus
include ../../Makefile-subdirs

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
