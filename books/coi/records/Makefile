#|-*-Makefile-*-=============================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#| records                                                                   |#
#|===========================================================================|#

# RAMS Makefile
# Use "make help" for more information

# Enter the path to the make directory, e.g., MAKEDIR = ../make

RAMS_MAKEDIR ?= ../make
MAKEDIR ?= $(RAMS_MAKEDIR)

# Enter the external libraries depended upon, e.g., LIBS = :bags :lists, or
# leave this blank if there are no external dependencies.

LIBS = :records :symbol-fns :lists :syntax :bags :alists :osets :util

# Enter the names of the books to certify, e.g., BOOKS = book1 book2

BOOKS = fixedpoint record-exports defrecord records domain set-domain defarray defrecord-fast mem-domain memory

LDFILES = record-exports.lsp rec-defpkg.lsp

# At this point, we turn over control to RAMS and
# it handles everything else.

include $(MAKEDIR)/Makefile.top
