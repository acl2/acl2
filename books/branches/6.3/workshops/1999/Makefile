# Here are the directories containing books to be certified.  Note that
# analysis is deliberately omitted because it is to be done with ACL2(r) only;
# see ../nonstd/case-studies/.  (However, calculus is included because its
# exercises are certifiable with standard ACL2.)
DIRS = calculus compiler de-hdl embedded graph knuth-91 mu-calculus multiplier \
	pipeline simulator ste vhdl ivy
include ../../Makefile-psubdirs

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
