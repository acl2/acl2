# -*- mode: makefile -*-

# ACL2 Community Books Makefile
# Copyright (C) 2013 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.  This program is distributed in the hope that it will be useful but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.  You should have received a copy of the GNU General Public
# License along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

##############################
### Section: Credits and History
##############################

# For many years, the ACL2 books were built using the "Makefile-generic"
# system.  This make system was written by
#
#      Matt Kaufmann <kaufmann@cs.utexas.edu> and
#      J Strother Moore <moore@cs.utexas.edu>
#
# and was actually an adaptation of Makefiles used by Bishop Brock for his IHS
# and data-structures libraries.
#
# In 2008, Sol Swords <sswords@centtech.com> developed cert.pl, a perl-based
# alternative to ACL2's make system.  This build system was largely compatible
# with the previous Makefile-generic system, but featured enhanced,
# cross-directory dependency tracking.  Centaur Technology used cert.pl for
# many years, both internally and for their publicly released "centaur/"
# community books.
#
# In 2013, Jared Davis <jared@centtech.com> developed an initial version of
# this current Makefile, which is substantially based on cert.pl, and made
# minor adjustments to several Community Books to ensure that they could all be
# certified with the new system.
#
# Subsequently, significant contributions to this Makefile have been made by
# many people, notably:
#
#   - Matt Kaufmann <kaufmann@cs.utexas.edu> has extended the Makefile in
#     support of certifying ACL2(r) books, multi-lisp compilation, provisional
#     certification, chk-include-book-worlds target, among numerous other
#     improvements and contributions such as testing the Makefile on many
#     systems and further tweaking some Community Books.
#
#   - Sol Swords <sswords@cs.utexas.edu> has provided significant support for
#     cert.pl, notably extending it to operate on Windows, and adding features
#     such as automatically tracking books that rely on ACL2(h).
#
#   - David Rager <ragerdl@cs.utexas.edu> provided significant early beta
#     testing and worked to ensure the Makefile works with ACL2(p) and in
#     different configurations of ACL2_CUSTOMIZATION; he has also provided
#     useful make targets.
#
#   - Jared Davis <jared@centtech.com> has made other miscellaneous
#     improvements, e.g., a more comprehensive implementation of book cleaning.

##############################
### Section: Documentation
##############################

# Basic usage:
#    make -j <jobs> [<target>]
#
# Where:
#    - <jobs> is how many books you want to certify in parallel,
#        typically the number of cores on your machine
#    - <target> is optional and defaults to "all" when omitted,
#        or names the target you want to build (see below).

# Major top-level targets:
#   - `all' is the default
#   - `everything' includes everything in `all' and also some slow books
#   - `lite' is most of `all', but with a few things excluded

# Jared Davis has summarized the improvements over the earlier
# Makefile as follows.

#  - It simplifies the build system, doing away with hundreds of Makefiles in
#    individual directories, and replacing them with this single file.  This is
#    possible because I've gone through and fixed up many books so that they
#    follow certain conventions, explained below.
#
#  - It increases (significantly) opportunities for parallelism, by doing away
#    with directory-level dependencies.  Essentially, any books that do not
#    have an include-book dependency can be built in parallel.  At the same
#    time, this means that books can be reorganized based on their logical
#    content, without regards to directory build order.
#
#  - It generally increases build-system automation.  We use "find" commands to
#    find Lisp files instead of maintaining (by hand) lists of directories.  We
#    also do not need to manually keep track of dependencies between
#    directories, etc.
#
# This Makefile starts by automatically scanning for books and their
# dependencies.  This scanning can be slightly expensive, especially on slow
# NFS systems.  When you know that you haven't added or changed any books, you
# might prefer to avoid rescanning by adding NO_RESCAN=1 to the command line.
#
# In order to make the book- and dependency-scanning simple and reliable, books
# are expected to follow certain conventions.  These conventions are generally
# very similar to the previous behavior of cert.pl and Makefile-generic.
#
#   - We scan for lines like (include-book "foo") and (ld "foo.lisp"); for
#     dependency scanning to work, these commands must be on a single line and
#     can't be wrapped up in macros.  Occasionally it is useful to fool the
#     dependency scanner, e.g., in a multi-line comments you might do:
#
#        #| Here's an example of how to use this stuff:
#
#           (include-book ;; newline to fool dependency scanner
#             "foo")
#
#           (demo-of-how-to-use-foo)
#        |#
#
#   - Additional dependencies (e.g., on raw-lisp files or other kinds of data
#     files) can be added using depends-on comments, e.g.,
#
#        ; (depends-on "foo-raw.lsp")
#
#   - Certifiable books should be named foo.lisp
#   - Non-certifiable Lisp files should be named foo.lsp
#   - The instructions for certifying foo.lisp are found in:
#       foo.acl2, if it exists, or else
#       cert.acl2, if it exists, or else
#       default to simply (certify-book "foo" ? t)
#     These instructions specify argument to certify-book, for example:
#       ; cert-flags: ? t :ttags :all
#   - Books that depend on ACL2(h), such as centaur/tutorial/alu16-book.lisp,
#     contain this line (or, a cert_param directive can be in the
#     .acl2 file that is consulted, as discussed above):
#       ; cert_param: (hons-only)
#   - Two-pass certification is handled as follows, for example in
#     books/make-event/stobj-test.acl2 (as indicated above, this can
#     also go into the book instead of the relevant .acl2 file):
#       ; cert_param: (acl2x)
#   - It's not clear that provisional certification is fully
#     supported.  For now, we implement it for two specific
#     directories; search below for "provisional certification" to see
#     how that's done.
#   - The "user" target allows one to restrict to specific
#     directories.  Search for "user" below to see an example.
#
# CHANGE/BOZO: In this Makefile (as in cert.pl), any certify-book lines given
# in the .acl2 file are ignored.  Instead, we generate the certify-book command
# to use by looking for comments like:
#
#         ; cert-flags: ? t :ttags :all
#
# These comments can be put in the individual foo.acl2 or (for directory-level
# defaults) in cert.acl2.  The default cert-flags are "? t".  Using special
# comments instead of certify-book forms means that the certification flags
# can't be hidden inside macros, possibly easing the job of an "evaluator."
#
# BOZO (from Jared) I have gone through the ACL2 regression suite and replaced
# certify-book lines throughout .acl2 files with cert-flags comments.  However,
# for now I've left the certify-book commands intact, for compatiblity with
# Makefile-generic.  Eventually, we should not have both things in .acl2 files.
# Before we can do that, we'll need to change Makefile-generic to look for
# cert-flags instead of certify-book commands.  Alternately, maybe the scheme
# should be something like: if you give a certify-book command, we use it;
# otherwise we generate one using the cert-flags.


# STATUS / TODO LIST / MISSING FEATURES / BOZOS:
#
#  [DONE] Requires perl on the client machine (I think we've agreed this is
#         okay)
#
#  [DONE] Two-pass certification seems to work, using the cert.pl directive
#         cert_param(acl2x).  See for instance
#         books/make-event/stobj-test.acl2.
#
#  [DONE] How should cleaning work?
#
#    Using a find command has the advantage that it will get rid of old files
#    even after the .lisp files have been deleted.  It has the disadvantage
#    that it seems tricky to properly delete .h and .c files using a find
#    command.  An alternative would be to use CERT_PL_CERTS to generate a huge
#    list of files to remove.  This will require using xargs, etc., which is
#    gross, but so does the find command.  Blah.
#
#    We now implement the CERT_PL_CERTS-based approach, but using clean.pl,
#    which nicely deals with the whole too-many-arguments issue.  It seems to
#    perform well.  I think this is probably as good as we can do.

##############################
### Section: Preliminaries
##############################

ifneq ($(ACL2_JOBS), )
$(error Error: variable ACL2_JOBS is obsolete (use -j instead); see :DOC book-makefiles)
endif # ifneq ($(ACL2_JOBS), )

ACL2 ?= acl2

SHELL := $(shell which bash)
STARTJOB ?= $(SHELL)

.SUFFIXES:
.SUFFIXES: .cert .lisp

# Keep this .PHONY target here, even though the main target
# definitions come much later in the file, because we start defining
# the "all" target (at least) well before then.  Also, keep "all:"
# here so that "all" is the top target.
.PHONY: all lite everything
all:

##############################
### Section: Create auxiliary files (Makefile-xxx) and initial OK_CERTS
##############################

# It seems that info is defined starting in GNU make version 3.81.
# But version 3.80 seems to tolerate calls of info, simply ignoring
# them.  We could use a variable, as follows, so that you can set
# INFO=warning on the command line if you want to see the messages
# even with GNU make version 3.80.  But maybe this is too ugly, so we
# just leave the idea as a comment.
## INFO := info
### Example: Prints something like "Makefile:227: just a test" when
### invoked with INFO=warning; otherwise, same as $(info just a test).
## $(eval $$($(INFO) just a test))

ifndef NO_RESCAN

# In the following, we exclude centaur/quicklisp explicitly rather
# than using the usual cert_pl_exclude file, because centaur/quicklisp
# uses cert.pl to certify books.  We exclude centaur/quicklisp
# explicitly since when we do want to make it, it will use cert.pl and
# hence we can't put a cert_pl_exclude file in that directory.  Some
# others we exclude because there are subdirectories and it's simply
# easiest to stop at the root.
$(info Scanning for books...)
REBUILD_MAKEFILE_BOOKS := $(shell \
  rm -f Makefile-books; \
  time find . -name "*.lisp" \
    | egrep -v '^(\./)?(interface|nonstd|centaur/quicklisp|clause-processors/SULFA|workshops/2003/kaufmann/support)' \
  > Makefile-books; \
  ls -l Makefile-books)
#$(info $(REBUILD_MAKEFILE_BOOKS))

$(info Scanning for dependencies...)
REBUILD_MAKEFILE_DEPS := $(shell \
  rm -f Makefile-deps Makefile-deps.out; \
  time (./cert.pl \
          --quiet \
          --static-makefile Makefile-deps \
          --cache Makefile-cache \
          --acl2-books `pwd` \
          --targets Makefile-books \
          1>&2) ;\
  echo 'MFDEPS_DEBUG := $$(shell echo Reading book deps ' \
       'Makefile-deps created on' `date` '1>&2)' \
    >> Makefile-deps; \
  ls -l Makefile-deps)
#$(info $(REBUILD_MAKEFILE_DEPS))
$(info Done scanning.)

endif # ifndef NO_RESCAN

include Makefile-deps

$(info Determining ACL2 features (for ACL2 = $(ACL2)))
ACL2_FEATURES := $(shell \
  rm -f Makefile-features ; \
  ACL2_CUSTOMIZATION=NONE $(STARTJOB) -c \
     "$(ACL2) < cert_features.lsp &> Makefile-features.out" ;\
  ls -l Makefile-features)

# Only conditionally include Makefile-features, so that make clean works even
# if ACL2 isn't built.
-include Makefile-features
$(info ACL2_HAS_HONS     := $(ACL2_HAS_HONS))
$(info ACL2_HAS_PARALLEL := $(ACL2_HAS_PARALLEL))
$(info ACL2_HAS_REALS    := $(ACL2_HAS_REALS))
$(info ACL2_COMP_EXT     := $(ACL2_COMP_EXT))
$(info ACL2_HOST_LISP    := $(ACL2_HOST_LISP))
$(info Done with features.)

OK_CERTS := $(CERT_PL_CERTS)

ifeq ($(ACL2_HAS_HONS), )

# $(info Excluding books that depend on ACL2(h))
OK_CERTS := $(filter-out $(CERT_PL_HONS_ONLY), $(OK_CERTS))

endif # ifeq ($(ACL2_HAS_HONS), )

# SLOW_BOOKS are books that are too slow to include as part of an
# ordinary regression.  There are currently comments in some of the
# corresponding Makefiles that explain something about these books.

SLOW_BOOKS := \
  coi/termination/assuming/complex.cert \
  models/jvm/m5/apprentice.cert \
  parallel/proofs/ideal-speedup.cert \
  workshops/2009/sumners/support/examples.cert \
  workshops/2011/krug-et-al/support/MinVisor/va-to-pa-thm.cert \
  workshops/2011/krug-et-al/support/MinVisor/setup-nested-page-tables.cert

OK_CERTS := $(filter-out $(SLOW_BOOKS), $(OK_CERTS))

##############################
### Section: Cleaning
##############################

# We delegate most of the cleaning process to clean.pl, a simple perl script
# that lets us take care not to delete certain kinds of files.  The clean.pl
# script will remove things like .cert and .fasl files.

CLEAN_FILES_EXPLICIT := \
   xdoc-impl/bookdoc.dat \
   Makefile-comp \
   Makefile-comp-pre \
   Makefile-deps \
   Makefile-books \
   Makefile-features \
   Makefile-cache \
   serialize/test.sao \
   bdd/benchmarks.lisp \
   nonstd/workshops/1999/calculus/book/tree.lisp

MORECLEAN_FILES_EXPLICIT := \
   xdoc-impl/manual \
   centaur/manual

.PHONY: clean_books clean

clean_books:
	@echo "Using clean.pl to remove certificates, etc."
	./clean.pl

# We test that directory centaur/quicklisp exists because it probably
# doesn't for nonstd/, and we include this makefile from that
# directory.
clean: clean_books
	@echo "Removing extra, explicitly temporary files."
	rm -rf $(CLEAN_FILES_EXPLICIT)
	for dir in centaur/quicklisp $(dir $(ACL2_CUSTOM_TARGETS)) ; \
	do \
	if [ -d $$dir ] ; then \
	(cd $$dir ; $(MAKE) clean) ; \
	fi ; \
	done

moreclean: clean
	@echo "Removing even more generated files (documentation, etc)."
	rm -rf $(MORECLEAN_FILES_EXPLICIT)

##############################
### Section: Miscellaneous custom support
##############################

# Next, we deal with books that need special handling.

# xdoc-impl is tricky because we have to generate bookdoc.dat.

xdoc-impl/bookdoc.dat: \
  xdoc-impl/acl2-customization.lsp \
  xdoc-impl/bookdoc.lsp \
  xdoc/package.lsp \
  $(wildcard xdoc/*.lisp) \
  $(wildcard xdoc-impl/*.lisp) \
  xdoc-impl/extra-packages.cert
	@echo "Making xdoc-impl/bookdoc.dat"
	@cd xdoc-impl; \
          $(STARTJOB) -c "$(ACL2) < bookdoc.lsp &> bookdoc.out"
	@ls -l xdoc-impl/bookdoc.dat

# We assume that ACL2_HAS_REALS indicates a regression being done in
# nonstd/.
ifndef ACL2_HAS_REALS

# The following dependency is to be ignored in ACL2(r), where the
# relevant include-book in arithmetic-3/extra/ext.lisp is guarded by
# #-:non-standard-analysis.
arithmetic-3/extra/ext.cert: rtl/rel8/arithmetic/top.cert

endif # ifndef ACL2_HAS_REALS

# BOZO.   make-event/local-elided stuff is tricky because it thinks it can tell whether
# local-elided.lisp was provisionally certified or not, which doesn't
# necessarily make any sense... this is the easiest way to fix it so that it
# works with provisional certification:

make-event/local-elided-include.pcert1: make-event/local-elided.cert

make-event/macros-include.pcert1: make-event/macros.cert

make-event/local-requires-skip-check-include.pcert1: \
  make-event/local-requires-skip-check.cert

# Deal with generated file bdd/benchmarks.lisp.

OK_CERTS += bdd/benchmarks.cert

bdd/benchmarks.cert: bdd/benchmarks.lisp

bdd/benchmarks.lisp: bdd/cbf.cert bdd/create-benchmarks.lsp
	cd bdd ; (echo '(ld "create-benchmarks.lsp")' | $(ACL2))

# Use custom Makefiles:

# There are several directories that we can't easily work directly
# into our general framework because they each have a custom Makefile.
# We handle those next.  For example, two directories test provisional
# certification: system/pcert, which was constructed explicitly to
# test provisional certification; and workshops/2011/verbeek-schmaltz,
# which is slow without provisional certification but is reasonably
# fast using provisional certification.

# Our perhaps gross hack is to use the old ACL2 Makefile-generic
# system to invoke the custom makefiles, for example as follows for
# verbeek-schmaltz.

#   - we tell cert.pl not to look at verbeek-schmaltz/sources, via a
#     cert_pl_exclude file;
#   - we add a verbeek-schmaltz/deps.lisp file with the prerequisites that
#     we need before going into the verbeek-schmaltz directory;
#   - we use an arbitrary top-level target to certify the actual
#     verbeek-schmaltz books after certifying the deps, which need not
#     be in any sense "the top-level book" for the directory -- but if
#     not, then if a book B in any other directory comes to depend on
#     a book other than the target that we picked, we will need to
#     make it depend on that target.

# In order to create a deps file, we connect to the directory (e.g., 
# cd clause-processors/SULFA), and then use shell commands:
#   fgrep ':dir :system' `find . -name "*.lisp"`
#   fgrep ':dir :system' `find . -name "*.acl2"`

# We skip those that do not have counterparts under nonstd/ when
# ACL2_HAS_REALS indicates a regression being done by ACL2(r) in
# nonstd/.  Also, for simplicity, we only handle ACL2_COMP for
# system/pcert/, and we do that in the section below, "Support for
# ACL2_COMP".

ifndef ACL2_COMP

ifndef ACL2_HAS_REALS

# Warning!  For each file below, the directory should either have a
# cert_pl_exclude file or else be explicitly excluded in the egrep
# command that is used to define REBUILD_MAKEFILE_BOOKS, above.
# Otherwise we might make the same file twice, would could cause
# conflicts if -j is other than 1.
ACL2_CUSTOM_TARGETS := \
  clause-processors/SULFA/target.cert \
  fix-cert/fix-cert.cert \
  workshops/1999/multiplier/proof.cert \
  workshops/2003/greve-wilding-vanfleet/support/firewallworks.cert \
  workshops/2003/kaufmann/support/input/defs-in.cert \
  workshops/2004/sumners-ray/support/success.txt \
  workshops/2011/verbeek-schmaltz/sources/correctness2.cert

# We only make the books under SULFA if a documented test for an
# installed SAT solver succeeds.
clause-processors/SULFA/target.cert: \
  clause-processors/deps-SULFA.cert
	@if [ -f ${PWD}/../aux/minisat2/${HOSTTYPE}/minisat/core/minisat ] ; \
	then \
	(cd $(@D) ; $(MAKE)) ; \
	else \
	echo "*NOTE*: Skipping SULFA subdirectory (no SAT solver installed; see SULFA/README)." ; \
	fi

# The following has no dependencies, so doesn't need a "deps" file.
fix-cert/fix-cert.cert:
	cd $(@D) ; $(MAKE)

workshops/1999/multiplier/proof.cert: \
  workshops/1999/deps-multiplier.cert
	cd $(@D) ; $(MAKE)

workshops/2003/greve-wilding-vanfleet/support/firewallworks.cert: \
  workshops/2003/greve-wilding-vanfleet/deps.cert
	cd $(@D) ; $(MAKE)

# Note that we change to the parent directory in order to pick up all
# of support/.
workshops/2003/kaufmann/support/input/defs-in.cert: \
  workshops/2003/kaufmann/deps.cert
	cd $(@D)/.. ; $(MAKE)

# The following has no dependencies, so doesn't need a "deps" file.
workshops/2004/sumners-ray/support/success.txt:
	cd $(@D) ; $(MAKE)

workshops/2011/verbeek-schmaltz/sources/correctness2.cert: \
  workshops/2011/verbeek-schmaltz/deps.cert
	cd $(@D) ; $(MAKE)

endif # ifndef ACL2_HAS_REALS

ACL2_CUSTOM_TARGETS += system/pcert/sub.cert

system/pcert/sub.cert: \
  system/deps-pcert.cert
	cd $(@D) ; $(MAKE)

endif # ifndef ACL2_COMP

# We avoid += because we want the custom targets to start first, in
# order to maximize parallelism.  If they go at the end, maybe we'll
# have an expensive sequential tail in the regression.
OK_CERTS := $(ACL2_CUSTOM_TARGETS) $(OK_CERTS)

##############################
### Section: Support for ACL2_COMP
##############################

ifdef ACL2_COMP

# Multi-lisp compilation stuff for developers.

# NOTE: This build might fail for compiled files that involve
# include-raw, that have readtime conditionals, that can cause stack
# overflows when loading uncompiled code, etc.  We don't consider it
# critical, however, that every compiled file get built.  See "Define
# books to be skipped for multi-lisp compilation", above, for the
# compiled files we do not attempt to build.

# Typical making of compiled files in books/ could be done as follows.
# First, in ACL2 sources directory:
#   make -j 4 regression-fresh ACL2_SAVE_EXPANSION=t ACL2=acl2-ccl
# Then, in books/ directory (where ACL2_SAVE_EXPANSION=t is optional,
# but a good idea in case some .cert file is unexpectedly remade):
#   make -j 4 -k ACL2_COMP=t ACL2_SAVE_EXPANSION=t ACL2=acl2-sbcl

# Typical making of compiled files in books/nonstd/ could be done as follows.
# First, in ACL2 sources directory:
#   make -j 4 regression-nonstd-fresh ACL2_SAVE_EXPANSION=t ACL2=acl2r-ccl
# Then, in books/nonstd/ directory (where ACL2_SAVE_EXPANSION=t is optional,
# but a good idea in case some .cert file is unexpectedly remade):
#   make -j 4 -k ACL2_COMP=t ACL2_SAVE_EXPANSION=t ACL2=acl2r-sbcl

# Note: these targets won't work unless you've already done a build
# using a "compatible" ACL2 (both ACL2, both ACL2(hp), etc.) after
# first setting ACL2_SAVE_EXPANSION=t, and then you define ACL2_COMP
# (e.g., ACL2_COMP=1) with a subsequent call of make.

# We skip multi-lisp compilation for the centaur books, because these
# may be more likely to have code conditional on the combination of
# both features :CCL and :HONS.  That can affect checksums, thus
# making it appear that a book certified in CCL is not certified in
# another Lisp.  We also skip multi-lisp compilation for books that
# depend on centaur/ books when we see a multi-lisp compilation
# failure for books in their directories.  (Thus, even though
# security/des/ depends on GL and hence centaur/, we don't exclude
# its books.)
$(info For building compiled (.$(ACL2_COMP_EXT)) files, excluding centaur books)
OK_CERTS := $(filter-out centaur/%, \
              $(filter-out models/y86/%, \
                $(OK_CERTS)))

ifndef NO_RESCAN

$(info Scanning for "make comp" dependencies...)
# Below, we use a different --var-prefix from the default used for the
# cert.pl call above, since we don't want to redefine the CERT_PL_xxx
# variables.  But note that we don't use the ACL2_COMP_xxx variables.
REBUILD_MAKEFILE_COMP := $(shell \
  rm -f Makefile-comp Makefile-comp.out; \
  time ((./cert.pl \
          --quiet \
          --static-makefile Makefile-comp-pre \
          --cache Makefile-cache \
          --acl2-books `pwd` \
          --targets Makefile-books \
          --no-boilerplate \
          --var-prefix ACL2_COMP) \
          1>&2) ;\
          (cat Makefile-comp-pre | sed "s/[.]cert/.$(ACL2_COMP_EXT)/g" > \
           Makefile-comp) 1>&2 ;\
  echo 'MFDEPS_DEBUG := $$(shell echo Reading book comp ' \
       'Makefile-comp created on' `date` '1>&2)' \
    >> Makefile-comp; \
  ls -l Makefile-comp)
$(info Done scanning.)

endif # ifndef NO_RESCAN

include Makefile-comp

# Define books to be skipped for multi-lisp compilation.

OK_CERTS := $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(OK_CERTS))

# Start a sequence of assignments to BOOKS_SKIP_COMP:
BOOKS_SKIP_COMP :=

# Unusual directory:
BOOKS_SKIP_COMP += $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(wildcard fix-cert/*.cert))

# Contains Lisp-specific readtime conditionals:
BOOKS_SKIP_COMP += hacking/evalable-ld-printing.$(ACL2_COMP_EXT)

# dft-ex.acl2 specifies no compilation; getprop.lisp can give stack
# overflow in during the load of the expansion file -- perhaps not
# surprising, given that (comp t) occurs in the .lisp file:
BOOKS_SKIP_COMP += misc/dft-ex.$(ACL2_COMP_EXT) misc/getprop.$(ACL2_COMP_EXT)

# aof.acl2 specifies no compilation; knuth-arch.lisp depends on aof:
BOOKS_SKIP_COMP += workshops/1999/knuth-91/aof.$(ACL2_COMP_EXT) \
                   workshops/1999/knuth-91/knuth-arch.$(ACL2_COMP_EXT)

# The .acl2 files specify no compilation:
BOOKS_SKIP_COMP += $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(wildcard workshops/2002/cowles-flat/support/*.cert))

# The .acl2 files specify no compilation:
BOOKS_SKIP_COMP += $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(wildcard workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly/*.cert))

# Some .acl2 files specify no compilation, including ed3.acl2, and
# many books depend on ed3:
BOOKS_SKIP_COMP += $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(wildcard workshops/2006/cowles-gamboa-euclid/Euclid/*.cert))

# The .acl2 files specify no compilation:
BOOKS_SKIP_COMP += workshops/2006/kaufmann-moore/support/rhs1-iff.$(ACL2_COMP_EXT) \
		   workshops/2006/kaufmann-moore/support/rhs1.$(ACL2_COMP_EXT) \
		   workshops/2006/kaufmann-moore/support/rhs2.$(ACL2_COMP_EXT) \
		   workshops/2006/kaufmann-moore/support/warnings.$(ACL2_COMP_EXT)

# There seems to be a problem with files that use include-raw.  We
# skip those.
# Has (include-raw "timer.lsp"):
BOOKS_SKIP_COMP += memoize/top.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += $(patsubst %-raw.lsp, %.$(ACL2_COMP_EXT), $(shell find . -name '*-raw.lsp' -print))

# Has readtime conditionals #+ccl and #-ccl ("not supported for this
# host Lisp").
BOOKS_SKIP_COMP += centaur/bridge/top.$(ACL2_COMP_EXT)

# CLISP says: "Lisp stack overflow":
BOOKS_SKIP_COMP += workshops/2006/rager/support/ptest-mergesort.$(ACL2_COMP_EXT)

# In Makefile-comp, bdd/benchmarks.$(ACL2_COMP_EXT) may depend on
# bdd/benchmarks.lisp, but we don't want to make either, so we do this
# explicitly:
BOOKS_SKIP_COMP += bdd/benchmarks.$(ACL2_COMP_EXT)

OK_CERTS := $(filter-out $(BOOKS_SKIP_COMP), $(OK_CERTS))

# Avoid trying to make compiled files; target %.$(ACL2_COMP_EXT) still
# "executes", but only once, and doesn't cause other compiled files to
# be out of date.
.INTERMEDIATE: $(BOOKS_SKIP_COMP)

# Note that because of the .INTERMEDIATE target above, then for the
# next targets, "Skipping" will only be printed for skipped targets
# that are dependencies of not-skipped targets.  Apologies for the
# very long line.  With it broken into lines using `\', a syntax error
# was reported on Linux using make version 3.80.  Sigh.
%.$(ACL2_COMP_EXT): %.cert
	@if [ "$(findstring $@, $(BOOKS_SKIP_COMP))" != "" ] ; then \
	echo "Skipping $$PWD/$@" ; \
	else \
	echo "Making $$PWD/$@" ; \
	(echo '(ld `((include-book "$(patsubst %.$(ACL2_COMP_EXT),%,$(@))" :load-compiled-file :comp :ttags :all))) (acl2::value :q) (acl2::exit-lisp)' | $(ACL2) >& $@.out) ; (ls -al $@ || (echo "**COMPILATION FAILED** for `pwd`/$@" ; exit 1)) ; fi

# Finally, we handle system/pcert/, which is a special case and thus
# would otherwise be ignored because of its cert_pl_exclude file.  We
# use -j 1 because the old Makefile-generic, included by the
# directory's Makefile, doesn't establish dependencies between the
# compiled files, and this can cause an error when attempting to load
# another book's partially-built compiled file.  Note that this rule
# overrides the pattern rule just above (a feature of GNU make).
system/pcert/sub.$(ACL2_COMP_EXT): \
  system/deps-pcert.$(ACL2_COMP_EXT)
	@echo "Making $@"
	@cd system/pcert/ ; \
	$(MAKE) -j 1 $(ACL2_COMP_EXT) ACL2_PCERT= >& make-$(ACL2_COMP_EXT).out ; \
	(cd ../.. ; ls -al $(@D)/*.$(ACL2_COMP_EXT)) ; \
	if [ `ls -1 *.$(ACL2_COMP_EXT) | wc -l` != `ls -1 *.cert | wc -l` ] ; then \
	echo "**COMPILATION FAILED** for $(@D);" ; \
	echo "  search for '**' in `pwd`/make-$(ACL2_COMP_EXT).out to see failures." ; \
	exit 1 ; \
	fi

OK_CERTS += system/pcert/sub.$(ACL2_COMP_EXT)

endif # ifdef ACL2_COMP

##############################
### Section: Define targets
##############################

# Keep this section at the end, so that all variable definitions have
# been completed (in particular, for OK_CERTS).

# First, we let the user filter the books by specifying the roots of
# the forest of books to be certified.  Our implementation reduces
# $(OK_CERTS), which normally is probably closed under dependencies.
# But for most purposes it is probably not important that $(OK_CERTS)
# be closed under dependencies.
#
# Example (just remove "# " at the beginning of each line):
#
# make -k -j 4 NO_RESCAN=1 ACL2=acl2h \
# ACL2_BOOK_CERTS=" \
# workshops/2006/cowles-gamboa-euclid/Euclid/ed6a.cert \
# workshops/2006/cowles-gamboa-euclid/Euclid/ed4bb.cert \
# " 
#
# If variable ACL2_BOOK_DIRS is set, then ACL2_BOOK_CERTS is extended
# accordingly.  Note that the pathnames in ACL2_BOOK_DIRS should be
# relative to the top-level books directory, not absolute pathnames.

# So  that ACL2_BOOK_CERTS is not recursive:
ACL2_BOOK_CERTS := $(ACL2_BOOK_CERTS)
ifneq ($(ACL2_BOOK_DIRS), )
$(info ACL2_BOOK_DIRS = $(ACL2_BOOK_DIRS))
ACL2_BOOK_DIRS_PATTERNS := $(addsuffix /%, $(ACL2_BOOK_DIRS))
ACL2_BOOK_CERTS += $(ACL2_BOOK_CERTS) \
                   $(filter $(ACL2_BOOK_DIRS_PATTERNS), $(OK_CERTS))
endif # ifneq ($(ACL2_BOOK_DIRS), )

ifneq ($(ACL2_BOOK_CERTS), )
$(info ACL2_BOOK_CERTS = $(ACL2_BOOK_CERTS))
OK_CERTS := $(ACL2_BOOK_CERTS)
else

# Normal case, where neither ACL2_BOOK_DIRS nor ACL2_BOOK_CERTS is
# defined:

# We prefer not to certify books under the directories filtered out
# just below, for the following reasons.
# - rtl/rel7/: This directory isn't used anywhere else and it doesn't
#   add much from a regression perspective, given the other rtl/
#   subdirectories that are included in the regression.

# However, we want cert.pl to scan within any such directory, to
# support the "everything" target, so we avoid putting cert_pl_exclude
# files in such a directory or excluding them from the egrep command
# that is used to define REBUILD_MAKEFILE_BOOKS, above.  Instead, we
# exclude them from the "all" and "lite" targets now.

OK_CERTS_EXCLUSIONS := $(filter rtl/rel7/%, $(OK_CERTS))

ifneq ($(ACL2_HAS_HONS), )
ifeq ($(filter CCL ALLEGRO SBCL, $(ACL2_HOST_LISP)), )

# We exclude models/y86/ for ACL2(h) except for CCL, which has
# significant optimizations for ACL2(h), and except for other Lisps
# that we have observed to perform acceptably on certifying these
# books.  In an ANSI GCL ACL2(h) regression, certification runs were
# still proceeding after more than 10 hours for each of four books
# under models/y86/ (y86-basic/common/x86-state,
# y86-two-level/common/x86-state,
# y86-two-level-abs/common/x86-state-concrete, and
# y86-basic/py86/popcount), probably because of the demands of
# def-gl-thm.  Moreover, LispWorks has too small a value for
# array-dimension-limit to support these certifications.

OK_CERTS_EXCLUSIONS += $(filter models/y86/%, $(OK_CERTS))
endif # ifeq ($(ACL2_HOST_LISP), GCL)
endif # ifneq ($(ACL2_HAS_HONS), )

OK_CERTS := $(filter-out $(OK_CERTS_EXCLUSIONS), $(OK_CERTS))

endif # ifneq ($(ACL2_BOOK_CERTS), )

# Avoid realpath below (isn't implemented in make 3.80).
ifeq ($(shell ls workshops 2> /dev/null), )
OK_CERTS := $(filter-out workshops/%, $(OK_CERTS))
endif # ifeq ($(realpath workshops), )

lite: $(OK_CERTS)
all: lite
# OK_CERTS_EXCLUSIONS is undefined if ACL2_BOOK_CERTS is defined, but
# that's not a problem; after all, in that case OK_CERTS wasn't
# filtered by OK_CERTS_EXCLUSIONS.
everything: all $(OK_CERTS_EXCLUSIONS)

# The critical path report will work only if you have set up certificate timing
# BEFORE you build the books.  See ./critpath.pl --help for details.

# BOZO I probably broke this, we shouldn't use --targets, we should use ok_certs...
critpath.txt: $(OK_CERTS)
	echo "Building critpath.txt..."
	time ./critpath.pl -m 2 --targets Makefile-books > critpath.txt


# The following are handy targets for building subsets of the books,
# and they show how others are easy to add.  It's OK for the community
# to make updates to this set of targets through addition, deletion,
# or modification.  (But it's probably best to leave the "all", "lite"
# and "everything" targets unchanged unless there is a strong reason
# to change those.)

.PHONY: centaur coi workshops \
        workshop1999 workshop2000 workshop2001 workshop2002 \
        workshop2003 workshop2004 workshop2006 workshop2007 \
        workshop2009 workshop2011

centaur: $(filter centaur/%, $(OK_CERTS))

coi: $(filter coi/%, $(OK_CERTS))

workshops: $(filter workshops/%, $(OK_CERTS))
workshop1999: $(filter workshops/1999/%, $(OK_CERTS))
workshop2000: $(filter workshops/2000/%, $(OK_CERTS))
workshop2001: $(filter workshops/2001/%, $(OK_CERTS))
workshop2002: $(filter workshops/2002/%, $(OK_CERTS))
workshop2003: $(filter workshops/2003/%, $(OK_CERTS))
workshop2004: $(filter workshops/2004/%, $(OK_CERTS))
workshop2006: $(filter workshops/2006/%, $(OK_CERTS))
workshop2007: $(filter workshops/2007/%, $(OK_CERTS))
workshop2009: $(filter workshops/2009/%, $(OK_CERTS))
workshop2011: $(filter workshops/2011/%, $(OK_CERTS))
workshop2013: $(filter workshops/2013/%, $(OK_CERTS))


# We define a set of books that support rapid prototyping and
# reasoning about such prototypes in ACL2.  We consider these books to
# constitute a "standard" approach to using ACL2 to model real
# problems.  The below target includes many more books than just those
# that make up this approach, but we leave it for now, because our
# main motivation in having such a target is to provide a quick target
# that certifies at least the books that consititute this approach.
# Regardless, this target should always include the "std" directory.

.PHONY: std

std: $(filter std/% cutil/%, $(OK_CERTS))

# We provide a basic target to show maintainers how they can filter
# out particular directories from the build.
.PHONY: basic

basic: $(filter-out centaur/%, \
         $(filter-out coi/%, \
           $(filter-out workshops/%, $(OK_CERTS))))

short-test: $(filter cowles/% arithmetic/% meta/% xdoc/% ordinals/% \
                     data-structures/% bdd/%, \
                     $(OK_CERTS))

# Warning: ACL2's GNUmakefile uses the following target to implement
# its own target certify-books, which some might use to build all
# "appropriate" books when installing ACL2.
.PHONY: certify-books
certify-books: $(filter-out workshops/%, $(OK_CERTS))

# The following dummy target does nothing, e.g., so that you can test
# the dependency scanning stuff without actually building anything.
.PHONY: dummy
dummy:
	@echo "Making dummy -- nothing to do."

# We now provide a way (adapted from the old Makefile-generic) for
# developers to be able to check well-formedness of the ACL2 world
# after including each book.  Note that the two problematic
# directories for world-checking, hacking/ and
# workshops/2007/dillinger-et-al/code/ override the
# chk-include-book-worlds target by setting environment variable
# ACL2_SKIP_CHK_INCLUDE_BOOK_WORLDS in order to skip this check.  The
# problem seems likely to be that in many of the books in these two
# directories, the first bad triple is a GLOBAL-VALUE for either the
# unknown property EXTEND-PROGN! or RETRACT-PROGN!, or else is an
# unbinding of the PREDEFINED property for PROGN! (indicating a use of
# :REDEF); presumably these books mess with raw mode.

BOOKS_BKCHK_OUT := $(patsubst %.cert,%.bkchk.out,$(OK_CERTS))
BOOKS_BKCHK_OUT := $(filter-out hacking/%, $(BOOKS_BKCHK_OUT))
BOOKS_BKCHK_OUT := $(filter-out workshops/2007/dillinger-et-al/code/%, $(BOOKS_BKCHK_OUT))

.PHONY: chk-include-book-worlds
chk-include-book-worlds: $(BOOKS_BKCHK_OUT)

%.bkchk.out: %.cert
	@echo "Including $(@D)/$* on `date`"
	@echo '(acl2::value :q)' > $(@D)/workxxx.bkchk.$(*F)
	@echo '(in-package "ACL2")' >> $(@D)/workxxx.bkchk.$(*F)
	@echo '(acl2::lp)' >> $(@D)/workxxx.bkchk.$(*F)
	@echo '(acl2::in-package "ACL2")' >> $(@D)/workxxx.bkchk.$(*F)
	@echo '(include-book "$*")' >> $(@D)/workxxx.bkchk.$(*F)
	@echo '(include-book "system/pseudo-good-worldp" :dir :system)' >> $(@D)/workxxx.bkchk.$(*F)
	@echo "Checking world created by including `pwd`/$* on `date`"
	@echo '(chk-pseudo-good-worldp "$*")' >> $(@D)/workxxx.bkchk.$(*F)
	@($(ACL2) < $(@D)/workxxx.bkchk.$(*F) 2>&1) > $*.bkchk.out
	@(fgrep 'Pseudo-good-worldp check for including "$*" passed.' $@) || \
            (echo '** Pseudo-good-worldp check FAILED for including $*;' "see `pwd`/$@" '**' ;\
             exit 1)
	@rm -f $(@D)/workxxx.bkchk.$(*F)

##############################
### Section: Some notes
##############################

# Comparable runs using this Makefile vs. the older Makefile.legacy
# can be done from the ACL2 sources directory as follows.

# ; uses Makefile
# (time nice make -j 8 regression ACL2=acl2ch)

# ; uses Makefile.legacy
# (time nice make ACL2_JOBS=8 regression-legacy-hons ACL2=acl2ch)

# The resulting of .cert files can be obtained by running the command

#   find . -name '*.cert' -print | sort

# in the directory of this Makefile immediately after each run.
# Here is what can be expected to find (based on having done this
# experiment on 5/10/2013).

# There were two .cert files from the legacy run that were not from
# the new run, as follows, and both are 0-length files that were
# written by their directories' Makefiles in order to avoid
# certification of these slow books.  That avoidance is handled
# differently by the new books/Makefile, without creating a .cert
# file.

# coi/termination/assuming/complex.cert
# models/jvm/m5/apprentice.cert

# There were six .cert files in the new run that were not in the
# legacy run.  The first two are explicitly avoided by the legacy run
# because they would introduce circular directory dependencies.

# str/base64.cert (certification took about 10 seconds)
# system/io.cert (certification took under 1 second)

# The other four have only the form (in-package "ACL2"), the rest
# being comments to assist the dependency scanner.

# workshops/1999/deps-multiplier.cert
# workshops/2003/greve-wilding-vanfleet/deps.cert
# workshops/2003/kaufmann/deps.cert
# workshops/2011/verbeek-schmaltz/deps.cert
