#|-*-Makefile-*-=============================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#| lists                                                                     |#
#|===========================================================================|#

# RAMS Makefile
# Use "make help" for more information


# Enter the path to the make directory, e.g., MAKEDIR = ../make

RAMS_MAKEDIR ?= ../make
MAKEDIR ?= $(RAMS_MAKEDIR)


# Enter the external libraries depended upon, e.g., LIBS = :bags :lists, or 
# leave this blank if there are no external dependencies.

LIBS = :adviser :nary :util


# Enter the names of the books to certify, e.g., BOOKS = book1 book2

BOOKS = acl2-count basic memberp \
        repeat map-cons \
        nth-and-update-nth \
	list-top update-nth-array mixed \
	nth-meta nth-meta2 find-index \
	subsetp remove set remove-induction disjoint \
	listset-induction \
	mv-nth

# Note: mv-nth had been deprecated, but we include it above because it supports
# lcf/single.lisp.

# DEPRICATED = mv-nth

LDFILES = list-defpkg.lsp list-exports.lsp

# At this point, we turn over control to RAMS and
# it handles everything else.

include $(MAKEDIR)/Makefile.top
