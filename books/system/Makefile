system-top: top all
all: top

DIRS = pcert links unicode
include ../Makefile-generic
include ../Makefile-subdirs

-include Makefile-deps

BOOKS := convert-normalized-term-to-pairs extend-pathname f-put-global gather-dcls \
		 hl-addr-combine meta-extract pseudo-good-worldp pseudo-termp-lemmas \
		 subcor-var sublis-var subst-expr subst-var too-many-ifs top \
         verified-termination-and-guards worldp-check update-state
# Add the following to the line above if you wish to build the wrapper
# book "io" with the GNU Make system.  Note that cert.pl will build
# the wrapper if needed.  We omit the building of this book from the
# GNU Make system, because (1) we ascertain that this wrapper is only
# needed by people that use cert.pl to build books (i.e., Centaur),
# and (2) the wrapper introduces a circular dependency, which the GNU
# Make system does not handle gracefully.
#		 io
