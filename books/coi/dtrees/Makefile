#|-*-Makefile-*-=============================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#| dtrees                                                                    |#
#|===========================================================================|#

# RAMS Makefile
# Use "make help" for more information


# Enter the path to the make directory, e.g., MAKEDIR = ../make

RAMS_MAKEDIR ?= ../make
MAKEDIR ?= $(RAMS_MAKEDIR)


# Enter the external libraries depended upon, e.g., LIBS = :bags :lists, or 
# leave this blank if there are no external dependencies.

LIBS = :paths :osets :lists :bags :adviser :maps :util


# Enter the names of the books to certify, e.g., BOOKS = book1 book2

BOOKS = base deps equiv raw child set erase leafp royalp top

LDFILES = dtree-defpkg.lsp

# At this point, we turn over control to RAMS and
# it handles everything else.

include $(MAKEDIR)/Makefile.top
