#|-*-Makefile-*-=============================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#| gacc                                                                      |#
#|===========================================================================|#

# RAMS Makefile
# Use "make help" for more information

# Enter the path to the make directory, e.g., MAKEDIR = ../make

RAMS_MAKEDIR ?= ../make
MAKEDIR ?= $(RAMS_MAKEDIR)

# Enter the external libraries depended upon, e.g., LIBS = :bags :lists, or
# leave this blank if there are no external dependencies.

LIBS = :super-ihs :lists :bags :records :defstructure :paths :osets :util

# Enter the names of the books to certify, e.g., BOOKS = book1 book2

BOOKS = gacc-pkg gacc-exports abstract-gacc addr-range bits mem-fast mem \
list-ops-common list-ops-fast wrap ram3 ram2b ram2  list-ops ram0 block \
ram gacc gacc2 gax finite gacc3 top fr-path-connection tr-path-connection

LDFILES = gacc-defpkg.lsp gacc-exports.lisp

# At this point, we turn over control to RAMS and
# it handles everything else.

include $(MAKEDIR)/Makefile.top
