#|-*-Makefile-*-=============================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#| util                                                                      |#
#|===========================================================================|#

# RAMS Makefile
# Use "make help" for more information


# Enter the path to the make directory, e.g., MAKEDIR = ../make

RAMS_MAKEDIR ?= ../make
MAKEDIR ?= $(RAMS_MAKEDIR)


# Enter the external libraries depended upon, e.g., LIBS = :bags :lists, or 
# leave this blank if there are no external dependencies.

# DAG : we should probably combine these two directories

LIBS = :symbol-fns


# Enter the names of the books to certify, e.g., BOOKS = book1 book2

BOOKS = mv-nth iff syntaxp ith fixequiv ifixequiv nfixequiv table \
        good-rewrite-order rewrite-equiv clause-processor defsubtype deffix \
        defdoc defbinding ordinal-order \
        rule-sets-documentation rule-sets  rule-sets-support \
        defun-support defun debug skip-rewrite pseudo-translate \
	in-conclusion implies extra-info extra-info-test ifdef \
        recursion-support

# At this point, we turn over control to RAMS and
# it handles everything else.

include $(MAKEDIR)/Makefile.top
