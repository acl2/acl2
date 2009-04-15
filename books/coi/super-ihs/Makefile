#|-*-Makefile-*-=============================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#| super-ihs                                                                 |#
#|===========================================================================|#

# RAMS Makefile
# Use "make help" for more information

# Enter the path to the make directory, e.g., MAKEDIR = ../make

RAMS_MAKEDIR ?= ../make
MAKEDIR ?= $(RAMS_MAKEDIR)

# Enter the external libraries depended upon, e.g., LIBS = :bags :lists, or
# leave this blank if there are no external dependencies.

LIBS = :util

# Enter the names of the books to certify, e.g., BOOKS = book1 book2

BOOKS = from-rtl arithmetic evenp bit-functions logcar loghead ash	\
basics c-functions logpair byte-p logapp loglist logical-logops			\
bit-twiddling-logops hacks eric lshu super-ihs iter-sqrt logtail		\
unsigned-byte-p logbitp logext logcons logcdr min-max logbit meta inductions	\
fast carry logior-logapp-crock signed-byte-p-overflow plus-logapp-suck

# symbols (see symbols.lsp)

# At this point, we turn over control to RAMS and
# it handles everything else.

include $(MAKEDIR)/Makefile.top
