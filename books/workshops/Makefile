
DIRS = 1999 2000 2002 2003 2004 2006 2007 2009 2011
include ../Makefile-psubdirs

# Because 2003/greve-wilding_mbe/support/fpst.cert
# depends on ../../../1999/graph/linear-find-path.cert, we add:
2003: 1999

tar:
	@for dir in $(DIRS) ; \
	do \
	(cd $$dir ; \
	$(MAKE) tar ; \
	cd ..) ; \
	done
