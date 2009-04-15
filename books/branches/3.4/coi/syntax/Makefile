#|-*-Makefile-*-=============================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#| syntax                                                                    |#
#|===========================================================================|#

# RAMS Makefile
# Use "make help" for more information


# Enter the path to the make directory, e.g., MAKEDIR = ../make

RAMS_MAKEDIR ?= ../make
MAKEDIR ?= $(RAMS_MAKEDIR)


# Enter the external libraries depended upon, e.g., LIBS = :bags :lists, or 
# leave this blank if there are no external dependencies.

LIBS = :util :symbol-fns

# Enter the names of the books to certify, e.g., BOOKS = book1 book2

BOOKS = syn-pkg auxilary syntax-extensions defevaluator defbinding syntax quine

LDFILES = syn-defpkg.lsp

# At this point, we turn over control to RAMS and
# it handles everything else.

include $(MAKEDIR)/Makefile.top
