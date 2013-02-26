
DIRS = 1999 2011
include ../Makefile-subdirs

tar:
	@for dir in $(DIRS) ; \
	do \
	(cd $$dir ; \
	$(MAKE) tar ; \
	cd ..) ; \
	done
