# Makefile for certifying workshop/2007 books.

##############################

# Supporting materials for books already distributed:

# None at this point.

##############################

# Supporting materials not yet certifiable:

# None at this point.

##############################

# Supporting materials that are not meant for ACL2 processing.

# gordon/support/

##############################

# There are no supporting materials for the following contributions.

# Carl Eastlund, Matthias Felleisen, Dale Vaillancourt
#   ACL2 for Freshmen: First Experiences

# Gabriel Infante-Lopez
#   Building Lemmas Using Examples

##############################

DIRS =  cowles-et-al/support \
	dillinger-et-al/code \
	erickson/bprove \
	rubio/support \
	rimlinger/support \
	schmaltz/genoc-v1.0

include ../../Makefile-psubdirs

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
