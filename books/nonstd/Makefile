# -*- mode: makefile -*-

#; Support for Community Books to Go with ACL2 Version 6.2
#; Copyright (C) 2013, Regents of the University of Texas

#; This program is free software; you can redistribute it and/or
#; modify it under the terms of Version 2 of the GNU General Public
#; License as published by the Free Software Foundation.

#; This program is distributed in the hope that it will be useful,
#; but WITHOUT ANY WARRANTY; without even the implied warranty of
#; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#; GNU General Public License for more details.

#; You should have received a copy of the GNU General Public License
#; along with this program; if not, write to the Free Software
#; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

#; Written by:  Matt Kaufmann               and J Strother Moore
#; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
#; Department of Computer Sciences
#; University of Texas at Austin
#; Austin, TX 78712-1188 U.S.A.

# Here is a summary of variables in this file that might be edited as
# the regression evolves.  All directory names have a trailing slash
# (/).  In brief, it would be good to extend the regression by adding
# to FULLDIRS and also eliminating values from BADDIRS and
# EXCLUDED_PREFIXES.

# FULLDIRS
#   Directories that are self-contained, in the sense that links to
#   standard books are not to be added
#   [NOTE: xdoc/ is in this list, but is a sort of short-circuit that
#    is a gutted version of the standard xdoc/; see
#    nonstd/xdoc/top.lisp.]
# BADDIRS
#   Directories for which no files or subdirectories are to
#   participate in the regression
# EXCLUDED_PREFIXES (note: used by ../Makefile)
#   Extension of BADDIRS by .cert filenames for books that are not
#   already excluded by BADDIRS but are not to be certified
# EXTRA_TARGETS and also see "Additional dependencies and actions:
#   Miscellaneous custom stuff

SHELL := $(shell which bash)

# All directories:
ALLDIRS := $(patsubst ./%,%/,$(shell find . -type d | fgrep -v .svn))

# Directories that have their own contents and do not get links to
# standard books. (Note that xdoc/ is a special case; see
# xdoc/top.lisp.)
FULLDIRS := nsa/ fft/ xdoc/

# Initialize BADDIRS as the right sort of variable:
BADDIRS := $(BADDIRS)

# We exclude std/ because its books includes books from directories
# not yet brought into nonstd/.  Perhaps that won't be difficult,
# but it's for another day.
BADDIRS += std/

# We exclude workshops/2011/ because (at least)
# workshops/2011/reid-gamboa-differentiator/support/inverse-square
# includes nsa/inverse-square, which is excluded below because it
# doesn't certify as of this writing.
BADDIRS += workshops/2011/

# Directories that need links:
LINKDIRS := $(filter-out $(FULLDIRS) $(addsuffix %, $(BADDIRS)),$(ALLDIRS))

EXCLUDED_PREFIXES += $(BADDIRS)

# These no longer certify; Ruben might be working on them.
EXCLUDED_PREFIXES += nsa/inverse-square.cert \
		     nsa/inverse-derivatives.cert \

# The book nsa/inverse-trig no longer certifies; Ruben might be
# working on it.  We also exclude nsa/complex-polar, since it includes
# inverse-trig, and nsa/ln, since it includes complex-polar, and
# nsa/raise, since it includes ln
EXCLUDED_PREFIXES += nsa/inverse-trig.cert \
		     nsa/complex-polar.cert \
		     nsa/ln.cert \
		     nsa/raise.cert

# We run links, even before including ../Makefile, so that
# Makefiles are present.  Use clean-links explicitly to remove links.
# Note that at the end of the following command, we remove any
# symbolic links that should not have been put there.

SAVED_DIR := $(shell pwd)
STD_DIR := $(shell cd .. ; pwd)

$(info Making links to ../*.pl files...)
LINKS0 := $(shell for file in $(wildcard ../*.pl) ; \
	do \
	if [ ! -e $${file\#../} ] ; then ln -s $$file . ; fi ; \
	done)

$(info Making links in subdirectories: $(LINKDIRS))
LINKS := $(shell \
	(cd $(SAVED_DIR) ;\
	for book_dir in $(LINKDIRS) ; \
	do \
	if [ -d $(STD_DIR)/$$book_dir ] ; then \
	$(SAVED_DIR)/link-up.sh $$book_dir $(STD_DIR) ; \
	fi ; \
	done ; \
	if [ -h workshops/1999/calculus/book/tree.lisp ] ; then \
	rm workshops/1999/calculus/book/tree.lisp ; \
	fi) >& links.log)

# Some directories may have books that would require books in
# directories not yet included under nonstd.  It might be good to
# include those others, but in the meantime we simply exclude the
# problematic books.

$(info Removing unwanted links...)
BAD_LINKS :=

# Include-book forms in tools/lint.lisp for books not included in nonstd:
# (include-book "cutil/da-base" :dir :system)
# (include-book "str/cat" :dir :system)
# (include-book "defsort/duplicated-members" :dir :system)
# (include-book "clause-processors/unify-subst" :dir :system)
BAD_LINKS += tools/lint.*

# The book std/top includes lots of stuff under std/ that is not yet in
# the books directory nonstd/std/.
BAD_LINKS += std/top.*

# The book misc/symbol-btree includes std/lists/take and
# std/lists/nthcdr.  And misc/symbol-btree, in turn, supports
# misc/rtl-untranslate and misc/untranslate-patterns.
BAD_LINKS += misc/symbol-btree.* \
	     misc/rtl-untranslate.* \
	     misc/untranslate-patterns.*

ifneq ($(BAD_LINKS), )
REMOVE_LINKS := $(shell rm -f $(BAD_LINKS))
endif # ifneq ($(BAD_LINKS), )

# Note that the following assumes that we execute make in this directory.
# Also note that the parent directory provides some directory dependencies
# that may need to be re-thought for the nonstd/ case at some point; but as
# long as things are working, we leave well enough alone.
include ../Makefile

.PHONY: $(EXTRA_TARGETS)
EXTRA_TARGETS := workshops/1999/calculus/book/tree/proof-outline

all: $(EXTRA_TARGETS)

# Warning: targets like all-fasl have not been updated to work for
# nonstd.

moreclean: clean-links

clean: clean-more-nonstd

clean-more-nonstd:
	rm -f workshops/1999/calculus/book/tree.lisp

clean-links:
	@echo 'Cleaning links *.pl:'
	@(for file in $(wildcard *.pl) ; do \
	 if [ -L $$file ] ; then rm -f $$file ; fi ; done) >& /dev/null
	@echo "Cleaning links from directories:"
	@for book_dir in $(LINKDIRS) ; \
	do \
	if [ -d $$book_dir ] ; then \
	cd $$book_dir ; \
	echo "Cleaning links from $$book_dir" ; \
	for file in `\ls` ; \
	do \
	if [ -h $$file ] ; then \
	rm -f $$file ; \
	fi ; \
	done ; \
	cd - > /dev/null ; \
	fi ; \
	done

# Additional dependencies and actions:

arithmetic/top.cert: arithmetic/realp.cert arithmetic/real-listp.cert

workshops/1999/calculus/book/proof-outline.cert: workshops/1999/calculus/book/tree.cert

workshops/1999/calculus/book/tree.cert: workshops/1999/calculus/book/tree.lisp
	cd workshops/1999/calculus/book/ ; \
	$(MAKE) tree.cert

workshops/1999/calculus/book/tree.lisp:
	cd workshops/1999/calculus/book ; $(MAKE) -f Makefile-essence tree.lisp

workshops/1999/calculus/book/tree/proof-outline: \
	workshops/1999/calculus/book/tree.cert \
	workshops/1999/calculus/book/proof-outline.cert
	cd workshops/1999/calculus/book/ ; $(MAKE) proof-outline
