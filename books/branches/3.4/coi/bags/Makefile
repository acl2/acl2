#|-*-Makefile-*-=============================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#| bags                                                                      |#
#|===========================================================================|#
# RAMS Makefile
# Use "make help" for more information

# Enter the path to the make directory, e.g., MAKEDIR = ../make

RAMS_MAKEDIR ?= ../make
MAKEDIR ?= $(RAMS_MAKEDIR)

# Enter the external libraries depended upon, e.g., LIBS = :bags :lists, or
# leave this blank if there are no external dependencies.

LIBS = :util :lists :syntax :adviser

# Enter the names of the books to certify, e.g., BOOKS = book1 book2

BOOKS = basic pick-a-point bind-free-rules cons eric-meta \
        meta neq top two-level two-level-meta extras

## Perhaps LDFILES should be added to the all: target in Makefile.deps

LDFILES = bag-defpkg.lsp bag-exports.lsp

# At this point, we turn over control to RAMS and
# it handles everything else.

include $(MAKEDIR)/Makefile.top
