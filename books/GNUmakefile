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
#
# For authorship information, see "Credits and History" below.


# Note: to use this Makefile, you will need to have already built a copy of
# ACL2.  To get ACL2, see: http://www.cs.utexas.edu/users/moore/acl2/
#
#
# Usage:  make [-j <jobs>] [<targets>] [ACL2=<cmd>] [options]
#
#   -j <jobs>     How many books you want to certify in parallel; typically the
#                 number of cores on your machine.
#
#   <targets>     Collections of books (or particular books) that you want to
#                 certify.  Default: "basic"
#
#   ACL2=<cmd>    The command to use to run ACL2.  Default: "acl2"
#
# Targets:
#
#   basic         The default.  This is a lightweight selection of books for
#                 reasoning about arithmetic, lists, sets, strings, io, etc.,
#                 and other miscellaneous tools and macros.  Many users may
#                 find "basic" to be a convenient starting place.
#
#   all           Certifies most books that are not horribly slow, including,
#                 for instance, most of workshops, projects, the centaur
#                 books, y86 and jvm models, etc.  Usually, committers to
#                 acl2-books should run "make all" first.
#
#   everything    A very full build, including very slow books.  Most users
#                 will not want to use this target.  It is useful for, e.g.,
#                 regression testing before releases.  Note that
#                 EXCLUDED_PREFIXES may not work with the `everything' target.
#
#   <dirname>     There are targets for many top-level directories, e.g., you
#                 may run "make coi" to build everything in coi/ directory,
#                 "make rtl" to build the books within rtl/, and so on.
#
#   <file-name>   You can ask to certify particular files, for instance,
#                 "make arithmetic-5/top.cert"
#
#   manual        Builds centaur/doc.cert, which produces the combined ACL2
#                 books+system manual in centaur/manual/index.html.  Note:
#                 this target requires ACL2(h) and USE_QUICKLISP=1.
#
#   special       Includes all the books, allowing arbitrary code before and
#                 after an include-book, and writing the log for each book
#                 <bk>.lisp to the file <bk>.special.out.
#
# Basic Options:
#
#   USE_QUICKLISP=1
#                 Experimental; needed for certain books.  Quicklisp is a
#                 packaging system for Common Lisp libraries, sort of like CPAN
#                 for Perl or RubyGems for Ruby.  May not work with some Lisps.
#
# Advanced Options:
#
#   STARTJOB=<command>
#                 The shell to use for running jobs.  Default: "bash"
#
#   NO_RESCAN=1   Assume dependency information is up to date.  This may save
#                 a few seconds on subsequent builds, especially on slow NFS
#                 systems.  May cause trouble if dependencies have changed.
#
#   ACL2_COMP=1   Causes multi-lisp compilation; not needed for most users.
#
#   EXCLUDED_PREFIXES=<strings>
#                 Do not certify books that start with these prefixes.  For
#                 instance, EXCLUDED_PREFIXES="projects workshops coi" would
#                 avoid building the books in these directories.
#
#   ACL2_BOOK_CERTS=<cert-file-names>
#   ACL2_BOOK_DIRS=<dir-names>
#                 Add particular files or directories as additional targets
#                 to certify, when using certain Makefile targets.
#
#   [For target "special":]
#   ACL2_SPECIAL_PRE=<pre-file-name>
#   ACL2_SPECIAL_POST=<post-file-name>
#                 Specify the files of forms to execute in the ACL2 loop
#                 immediately before (<pre-file-name>) and immediately after
#                 (<post-file-name>) including a book.
#
# Of course, the usual GNU make options are also available.  In particular, -k
# is useful for causing make to keep going when an error is encountered (but
# return a non-zero error status at the end).



##############################
### Section: Preliminaries
##############################

# For cygwin, we need to do something special to get a Unix-like
# pathname.
ifneq (,$(findstring CYGWIN, $(shell uname)))
export ACL2_SYSTEM_BOOKS := $(shell cygpath -m $(CURDIR))
else
export ACL2_SYSTEM_BOOKS := $(CURDIR)
endif

$(info ACL2_SYSTEM_BOOKS is $(ACL2_SYSTEM_BOOKS))
ifneq ($(ACL2_JOBS), )
${error Error: variable ACL2_JOBS is obsolete -- use -j instead -- see :DOC book-makefiles }
endif # ifneq ($(ACL2_JOBS), )

ACL2 ?= acl2
BUILD_DIR := $(ACL2_SYSTEM_BOOKS)/build

# Here is an undocumented way to specify a different shell, e.g., sh.
# There are no guarantees that another shell will work, however!
ifdef ACL2_SHELL_OVERRIDE
SHELL := $(ACL2_SHELL_OVERRIDE)
else
SHELL := $(shell which bash)
endif # ifdef ACL2_SHELL_OVERRIDE

STARTJOB ?= $(SHELL)

.SUFFIXES:
.SUFFIXES: .cert .lisp

.PHONY: basic all

# Keep this before any other target so that basic will be the default target
basic:


QUICKLISP_DIR=centaur/quicklisp

ifneq ($(USE_QUICKLISP), )

$(QUICKLISP_DIR)/quicklisp.lisp:
	@echo "Downloading Quicklisp"
	@cd $(QUICKLISP_DIR); curl -O http://beta.quicklisp.org/quicklisp.lisp
	@ls -l $(QUICKLISP_DIR)/quicklisp.lisp

$(QUICKLISP_DIR)/setup.lisp: $(QUICKLISP_DIR)/quicklisp.lisp \
                             $(QUICKLISP_DIR)/install.lsp
	@echo "Setting up Quicklisp"
	@cd $(QUICKLISP_DIR); $(STARTJOB) -c "$(ACL2) < install.lsp &> install.out"
	@ls -l $(QUICKLISP_DIR)/setup.lisp

$(QUICKLISP_DIR)/top.cert: $(QUICKLISP_DIR)/setup.lisp \
                           $(QUICKLISP_DIR)/cert.acl2 \
                           tools/include-raw.cert

all: $(QUICKLISP_DIR)/top.cert

endif # USE_QUICKLISP

# [Jared]: I moved these out of the USE_QUICKLISP section so that "make clean"
# will always remove the quicklisp files if you have ever built with
# USE_QUICKLISP before.  The goal is to ensure that stale quicklisp files
# aren't left around after a "make clean" by accident.

.PHONY: quicklisp_clean

# We check for QUICKLISP_DIR since this Makefile is included by
# nonstd/Makefile, and there is no nonstd/$(QUICKLISP_DIR) directory.
quicklisp_clean:
	@if [ -d $(QUICKLISP_DIR) ] ; then \
	  echo "Removing downloaded quicklisp files (if any)" ; \
	  cd $(QUICKLISP_DIR); rm -rf setup.lisp quicklisp.lisp asdf.lisp \
          cache dists local-projects tmp install.out quicklisp Makefile-tmp ; \
	fi

clean: quicklisp_clean


# Ensure that the following variable is simply expanded.
ACL2_CUSTOM_TARGETS :=

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

# We skip the scan for excluded prefixes.  This change was implemented
# by Matt Kaufmann on 9/25/2013 as part of the process of fixing
# ACL2(r) regressions.  (Note that nonstd/Makefile includes this
# Makefile.)
ifneq ($(EXCLUDED_PREFIXES), )
space =  # just a space
EGREP_EXTRA_EXCLUDE_STRING = |$(subst $(space) $(space),|,$(strip $(EXCLUDED_PREFIXES)))
endif # ifneq ($(EXCLUDED_PREFIXES), )

# We exclude centaur/quicklisp explicitly, instead of using a cert_pl_exclude
# file, because when people actually install Quicklisp packages, it ends up
# having subdirectories that we don't know about ahead of time.  We exclude
# some other directories because there are subdirectories and it's just easiest
# to stop at the root.

# We also exclude centaur/satlink/solvers because it depends on all kinds of
# extra SAT solvers.
$(info Scanning for books...)
REBUILD_MAKEFILE_BOOKS := $(shell \
  rm -f $(BUILD_DIR)/Makefile-books; \
  time find . -name "*.lisp" \
    | egrep -v '^(\./)?(interface|nonstd|centaur/quicklisp|centaur/satlink/solvers|projects/milawa/ACL2|clause-processors/SULFA|workshops/2003/kaufmann/support|models/y86/$(EGREP_EXTRA_EXCLUDE_STRING))' \
    | fgrep -v '.\#' \
  > $(BUILD_DIR)/Makefile-books; \
  ls -l $(BUILD_DIR)/Makefile-books)
#$(info $(REBUILD_MAKEFILE_BOOKS))

$(info Scanning for dependencies...)
REBUILD_MAKEFILE_DEPS := $(shell \
  rm -f $(BUILD_DIR)/Makefile-deps $(BUILD_DIR)/Makefile-deps.out; \
  time ($(BUILD_DIR)/cert.pl \
          --quiet \
          --static-makefile $(BUILD_DIR)/Makefile-deps \
          --cache $(BUILD_DIR)/Makefile-cache \
          --acl2-books `pwd` \
          --targets $(BUILD_DIR)/Makefile-books \
          1>&2) ;\
  echo 'MFDEPS_DEBUG := $$(shell echo Reading book deps ' \
       'Makefile-deps created on' `date` '1>&2)' \
    >> $(BUILD_DIR)/Makefile-deps; \
  ls -l $(BUILD_DIR)/Makefile-deps)
#$(info $(REBUILD_MAKEFILE_DEPS))
$(info Done scanning.)

endif # ifndef NO_RESCAN

include $(BUILD_DIR)/Makefile-deps

$(info Determining ACL2 features (for ACL2 = $(ACL2)))
ACL2_FEATURES := $(shell \
  rm -f $(BUILD_DIR)/Makefile-features ; \
  cd $(BUILD_DIR); ACL2_CUSTOMIZATION=NONE $(STARTJOB) -c \
     "$(ACL2) < cert_features.lsp &> Makefile-features.out" ;\
  ls -l $(BUILD_DIR)/Makefile-features)

$(info Determining whether Glucose is installed)
# If glucose doesn't exist, then the error message saying it can't be
# found is redirected to /dev/null, resulting in an empty value for
# GLUCOSE_EXISTS
GLUCOSE_EXISTS := $(shell glucose --version 2>/dev/null)
ifdef GLUCOSE_EXISTS
  OS_HAS_GLUCOSE := 1
endif # ifdef GLUCOSE_EXISTS

# Only conditionally include Makefile-features, so that make clean works even
# if ACL2 isn't built.
-include $(BUILD_DIR)/Makefile-features
$(info ACL2_HAS_HONS     := $(ACL2_HAS_HONS))
$(info ACL2_HAS_PARALLEL := $(ACL2_HAS_PARALLEL))
$(info ACL2_HAS_REALS    := $(ACL2_HAS_REALS))
$(info ACL2_COMP_EXT     := $(ACL2_COMP_EXT))
$(info ACL2_HOST_LISP    := $(ACL2_HOST_LISP))
$(info OS_HAS_GLUCOSE    := $(OS_HAS_GLUCOSE))
$(info USE_QUICKLISP     := $(USE_QUICKLISP))
$(info Done with features.)

# Cause error for illegal certification attempts:

ifeq ($(ACL2_HAS_HONS), )

$(CERT_PL_HONS_ONLY):
	$(MAKE) no_hons_error NO_RESCAN=1 CERT_PL_HONS_ONLY_BOOK=$@

.PHONY: no_hons_error
no_hons_error:
	@echo "Error! Target $(CERT_PL_HONS_ONLY_BOOK) requires hons."
	@exit 1

endif

# End of "Cause error for illegal certification attempts".

OK_CERTS := $(CERT_PL_CERTS)

ifeq ($(ACL2_HAS_HONS), )

# We use "{...}" delimeters to avoid errors in version 3.80 of make.
${info Excluding books that need ACL2(h) [...]}
OK_CERTS := $(filter-out $(CERT_PL_HONS_ONLY), $(OK_CERTS))

endif # ifeq ($(ACL2_HAS_HONS), )

ifeq ($(OS_HAS_GLUCOSE), )

$(info Excluding books that need Glucose: [$(CERT_PL_USES_GLUCOSE)])
OK_CERTS := $(filter-out $(CERT_PL_USES_GLUCOSE), $(OK_CERTS))

endif # ifeq ($(OS_HAS_GLUCOSE), )

ifeq ($(USE_QUICKLISP), )
$(info Excluding books that depend on Quicklisp: [$(CERT_PL_USES_QUICKLISP)])
OK_CERTS := $(filter-out $(CERT_PL_USES_QUICKLISP), $(OK_CERTS))
endif

# SLOW_BOOKS is a list of books that are too slow to include as part
# of an ordinary regression.  There are currently comments in some of
# the corresponding Makefiles that explain something about these
# books.  WARNING: It is probably a bad idea to include targets here
# that are in ACL2_CUSTOM_TARGETS: SLOW_BOOKS is removed from OK_CERTS
# just below, but later, ACL2_CUSTOM_TARGETS adds its targets to
# OK_CERTS.

# Before defining SLOW_BOOKS, we define ADDED_BOOKS to be the books
# that we want to add back in when using target "everything" instead
# of the default target, "all".

ADDED_BOOKS := \
  coi/termination/assuming/complex.cert \
  models/jvm/m5/apprentice.cert \
  system/parallel/proofs/ideal-speedup.cert \
  workshops/2009/sumners/support/examples.cert \
  workshops/2011/krug-et-al/support/MinVisor/va-to-pa-thm.cert \
  workshops/2011/krug-et-al/support/MinVisor/setup-nested-page-tables.cert

# The following has taken only a couple of minutes on a decent Linux
# system in 2013.  However, ACL2 built on GCL 2.6.8 and Mac OS 10.6
# cannot complete the certification without running exhausting STRING
# storage, probably because it contains a large stobj.  So we certify
# it only in "everything" regressions.

ADDED_BOOKS += workshops/2013/hardin-hardin/support/APSP.cert

ifneq ($(ACL2_HAS_HONS), )
ADDED_BOOKS += milawa-test-basic
endif

# Now SLOW_BOOKS is defined as the list above, except that below, we
# also include in SLOW_BOOKS some books that are too slow for both an
# ordinary regression (target "all") and an "everything" regression.
# Then we remove SLOW_BOOKS from regressions, restoring its subset,
# ADDED_BOOKS, for the "everything" target.

SLOW_BOOKS := $(ADDED_BOOKS)

# Note that models/y86/ is already excluded in the setting of
# REBUILD_MAKEFILE_BOOKS above, but these books are built if
# models/y86-target.cert is included.  File models/y86-target.lisp is
# already labeled as hons-only, but even with ACL2(h) we want to
# exclude some host Lisps.  Certainly CCL can handle these books,
# since it has significant optimizations for ACL2(h).  But in one ANSI
# GCL ACL2(h) regression, certification runs were still proceeding
# after more than 10 hours for each of four books under models/y86/
# (y86-basic/common/x86-state, y86-two-level/common/x86-state,
# y86-two-level-abs/common/x86-state-concrete, and
# y86-basic/py86/popcount), probably because of the demands of
# def-gl-thm.  Moreover, LispWorks has too small a value for
# array-dimension-limit to support these certifications.

ifeq ($(filter CCL ALLEGRO SBCL, $(ACL2_HOST_LISP)), )
# When the Lisp is not one of those mentioned on the line above, we
# skip the models/y86/ books.
  SLOW_BOOKS += models/y86-target.cert
endif

OK_CERTS := $(filter-out $(SLOW_BOOKS), $(OK_CERTS))

##############################
### Section: Cleaning
##############################

# We delegate most of the cleaning process to clean.pl, a simple perl script
# that lets us take care not to delete certain kinds of files.  The clean.pl
# script will remove things like .cert and .fasl files.

CLEAN_FILES_EXPLICIT := \
   $(BUILD_DIR)/Makefile-comp \
   $(BUILD_DIR)/Makefile-comp-pre \
   $(BUILD_DIR)/Makefile-deps \
   $(BUILD_DIR)/Makefile-books \
   $(BUILD_DIR)/Makefile-features \
   $(BUILD_DIR)/Makefile-cache \
   serialize/test.sao \
   bdd/benchmarks.lisp \
   nonstd/workshops/1999/calculus/book/tree.lisp

MORECLEAN_FILES_EXPLICIT := \
   centaur/manual \
   system/doc/manual

.PHONY: clean_books clean

clean_books:
	@echo "Using clean.pl to remove certificates, etc."
	$(BUILD_DIR)/clean.pl

# We test that directory centaur/quicklisp exists because it probably
# doesn't for nonstd/, and we include this makefile from that
# directory.  Also, we clean models/y86 explicitly, since
# models/Makefile (from custom target models/y86-target.cert) doesn't
# exist.
clean: clean_books
	@echo "Removing extra, explicitly temporary files."
	rm -rf $(CLEAN_FILES_EXPLICIT)
	for dir in $(dir $(ACL2_CUSTOM_TARGETS)) models/y86 ; \
	do \
	if [ -f $$dir/Makefile ] ; then \
	(cd $$dir ; $(MAKE) clean) ; \
	fi ; \
	done

moreclean: clean
	@echo "Removing even more generated files (documentation, etc)."
	rm -rf $(MORECLEAN_FILES_EXPLICIT)

##############################
### Section: Miscellaneous custom support
##############################

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
	cd bdd ; $(STARTJOB) -c "(echo '(ld \"create-benchmarks.lsp\")' | $(ACL2))"

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

ifeq ($(ACL2_HAS_REALS), )

# Warning!  For each file below, the directory should either have a
# cert_pl_exclude file or else be explicitly excluded in the egrep
# command that is used to define REBUILD_MAKEFILE_BOOKS, above.
# Otherwise we might make the same file twice, would could cause
# conflicts if -j is other than 1.  Also: Do not include any targets,
# such as models/y86-target.cert, that we don't always want built with
# "all".

ACL2_CUSTOM_TARGETS := \
  clause-processors/SULFA/target.cert \
  fix-cert/fix-cert.cert \
  projects/translators/l3-to-acl2/target.cert \
  workshops/1999/multiplier/proof.cert \
  workshops/2003/greve-wilding-vanfleet/support/firewallworks.cert \
  workshops/2003/kaufmann/support/input/defs-in.cert \
  workshops/2004/sumners-ray/support/success.txt \
  workshops/2011/verbeek-schmaltz/sources/correctness2.cert

# Warning!  For each target below, if there is a cert_pl_exclude file
# in the directory or it is exluded explicitly by
# REBUILD_MAKEFILE_BOOKS, and a "deps" file is used, then that "deps"
# file should be placed in a different directory (that is not
# excluded).  For example, projects/translators/l3-to-acl2/target.cert
# below depends on projects/translators/l3-to-acl2-deps.cert, for
# which dependencies will be generated since there is no
# cert_pl_exclude file in projects/translators/ (even though there is
# a cert_pl_exclude in projects/translators/l3-to-acl2/).

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
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

# The following need not be made a custom target, since it's not in an
# excluded directory.  Note that we use -j 1 because of the
# potentially large memory requirements.
ifneq ($(ACL2_HAS_HONS), )
models/y86-target.cert:
	cd $(@D)/y86 ; $(STARTJOB) -c "$(MAKE) -j 1"
endif

projects/translators/l3-to-acl2/target.cert: \
  projects/translators/l3-to-acl2-deps.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE) -j 1"

workshops/1999/multiplier/proof.cert: \
  workshops/1999/deps-multiplier.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

workshops/2003/greve-wilding-vanfleet/support/firewallworks.cert: \
  workshops/2003/greve-wilding-vanfleet/deps.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

# Note that we change to the parent directory in order to pick up all
# of support/.
workshops/2003/kaufmann/support/input/defs-in.cert: \
  workshops/2003/kaufmann/deps.cert
	cd $(@D)/.. ; $(STARTJOB) -c "$(MAKE)"

# The following has no dependencies, so doesn't need a "deps" file.
workshops/2004/sumners-ray/support/success.txt:
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

workshops/2011/verbeek-schmaltz/sources/correctness2.cert: \
  workshops/2011/verbeek-schmaltz/deps.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

endif # ifeq ($(ACL2_HAS_REALS), )

ACL2_CUSTOM_TARGETS += system/pcert/sub.cert

system/pcert/sub.cert: \
  system/deps-pcert.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

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
# projects/security/des/ depends on GL and hence centaur/, we don't exclude
# its books.)
$(info For building compiled (.$(ACL2_COMP_EXT)) files, excluding centaur books)
OK_CERTS := $(filter-out centaur/%, \
              $(filter-out models/y86%, \
                $(OK_CERTS)))

ifndef NO_RESCAN

$(info Scanning for "make comp" dependencies...)
# Below, we use a different --var-prefix from the default used for the
# cert.pl call above, since we don't want to redefine the CERT_PL_xxx
# variables.  But note that we don't use the ACL2_COMP_xxx variables.
REBUILD_MAKEFILE_COMP := $(shell \
  rm -f $(BUILD_DIR)/Makefile-comp $(BUILD_DIR)/Makefile-comp.out; \
  time (($(BUILD_DIR)/cert.pl \
          --quiet \
          --static-makefile $(BUILD_DIR)/Makefile-comp-pre \
          --cache $(BUILD_DIR)/Makefile-cache \
          --acl2-books `pwd` \
          --targets $(BUILD_DIR)/Makefile-books \
          --no-boilerplate \
          --var-prefix ACL2_COMP) \
          1>&2) ;\
          (cat $(BUILD_DIR)/Makefile-comp-pre | sed "s/[.]cert/.$(ACL2_COMP_EXT)/g" > \
           $(BUILD_DIR)/Makefile-comp) 1>&2 ;\
  echo 'MFDEPS_DEBUG := $$(shell echo Reading book comp ' \
       'Makefile-comp created on' `date` '1>&2)' \
    >> $(BUILD_DIR)/Makefile-comp; \
  ls -l $(BUILD_DIR)/Makefile-comp)
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

# The .acl2 file specifies no compilation:
BOOKS_SKIP_COMP += ccg/ccg.$(ACL2_COMP_EXT)

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
### Section: Exclude EXCLUDED_PREFIXES
##############################

# It might no longer be necessary to filter out EXCLUDED_PREFIXES from
# OK_CERTS, now that EGREP_EXTRA_EXCLUDE_STRING contributes to the
# exclusion process, but we go ahead and do so here, for robustness.

OK_CERTS := $(filter-out $(addsuffix %, $(EXCLUDED_PREFIXES)), $(OK_CERTS))

##############################
### Section: Define targets
##############################

# Keep this section at the end, so that all variable definitions have
# been completed (in particular, for OK_CERTS).

# Warning: ACL2's GNUmakefile uses the "all" target of this Makefile
# to implement its target, "regression".  So please be careful about
# making major changes to "all" in this Makefile.

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

# So that ACL2_BOOK_CERTS is not recursive (but don't set it to the
# empty string, since it might be set on the command line!).
ACL2_BOOK_CERTS := $(ACL2_BOOK_CERTS)
ifneq ($(ACL2_BOOK_DIRS), )
$(info ACL2_BOOK_DIRS = $(ACL2_BOOK_DIRS))
ACL2_BOOK_DIRS_PATTERNS := $(addsuffix /%, $(ACL2_BOOK_DIRS))
ACL2_BOOK_CERTS += $(filter $(ACL2_BOOK_DIRS_PATTERNS), $(OK_CERTS))
endif # ifneq ($(ACL2_BOOK_DIRS), )

ifneq ($(ACL2_BOOK_CERTS), )
$(info ACL2_BOOK_CERTS = $(ACL2_BOOK_CERTS))
OK_CERTS := $(ACL2_BOOK_CERTS)

endif # ifneq ($(ACL2_BOOK_CERTS), )

# Avoid realpath below (isn't implemented in make 3.80).
ifeq ($(shell ls workshops 2> /dev/null), )
OK_CERTS := $(filter-out workshops/%, $(OK_CERTS))
endif # ifeq ($(realpath workshops), )

all: $(OK_CERTS)

# It was tempting to handle the `everything' target as follows:
#  everything: USE_QUICKLISP = 1
#  everything: all $(ADDED_BOOKS)
# But that didn't work, presumably because the value of OK_CERTS was
# on a first pass through the Makefile without USE_QUICKLISP being
# set.
.PHONY: everything
everything:
	$(MAKE) all $(ADDED_BOOKS) USE_QUICKLISP=1

# The critical path report will work only if you have set up certificate timing
# BEFORE you build the books.  See ./critpath.pl --help for details.

# BOZO I probably broke this, we shouldn't use --targets, we should use ok_certs...
critpath.txt: $(OK_CERTS)
	echo "Building critpath.txt..."
	time $(BUILD_DIR)/critpath.pl -m 2 --targets Makefile-books > critpath.txt


# Targets for building whole directories of books.

# basic is the default set of books to build:
.PHONY: basic
basic: arithmetic arithmetic-2 arithmetic-3 arithmetic-5 ihs std str xdoc tools misc data-structures


.PHONY: add-ons
add-ons: $(filter add-ons/%, $(OK_CERTS))

.PHONY: arithmetic
arithmetic: $(filter arithmetic/%, $(OK_CERTS))

.PHONY: arithmetic-2
arithmetic-2: $(filter arithmetic-2/%, $(OK_CERTS))

.PHONY: arithmetic-3
arithmetic-3: $(filter arithmetic-3/%, $(OK_CERTS))

.PHONY: arithmetic-5
arithmetic-5: $(filter arithmetic-5/%, $(OK_CERTS))

.PHONY: bdd
bdd: $(filter bdd/%, $(OK_CERTS))

.PHONY: ccg
ccg: $(filter ccg/%, $(OK_CERTS))

.PHONY: centaur
centaur: $(filter centaur/%, $(OK_CERTS))

.PHONY: cgen
cgen: $(filter cgen/%, $(OK_CERTS))

.PHONY: clause-processors
clause-processors: $(filter clause-processors/%, $(OK_CERTS))

.PHONY: coi
coi: $(filter coi/%, $(OK_CERTS))

.PHONY: cowles
cowles: $(filter cowles/%, $(OK_CERTS))

.PHONY: data-structures
data-structures: $(filter-out data-structures/memories/%, $(filter data-structures/%, $(OK_CERTS)))

.PHONY: defsort
defsort: $(filter defsort/%, $(OK_CERTS))

.PHONY: finite-set-theory
finite-set-theory: $(filter finite-set-theory/%, $(OK_CERTS))

.PHONY: hacking
hacking: $(filter hacking/%, $(OK_CERTS))

.PHONY: hints
hints: $(filter hints/%, $(OK_CERTS))

.PHONY: ihs
ihs: $(filter ihs/%, $(OK_CERTS))

.PHONY: make-event
make-event: $(filter make-event/%, $(OK_CERTS))

.PHONY: memoize
memoize: $(filter memoize/%, $(OK_CERTS))

.PHONY: meta
meta: $(filter meta/%, $(OK_CERTS))

.PHONY: misc
misc: $(filter-out misc/misc2/%, $(filter misc/%, $(OK_CERTS)))

.PHONY: models
models: $(filter models/%, $(OK_CERTS))

.PHONY: ordinals
ordinals: $(filter ordinals/%, $(OK_CERTS))

.PHONY: oslib
oslib: $(filter oslib/%, $(OK_CERTS))

.PHONY: parsers
parsers: $(filter parsers/%, $(OK_CERTS))

.PHONY: powerlists
powerlists: $(filter powerlists/%, $(OK_CERTS))

# projects are dealt with individually below

.PHONY: proofstyles
proofstyles: $(filter proofstyles/%, $(OK_CERTS))

.PHONY: regex
regex: $(filter regex/%, $(OK_CERTS))

.PHONY: rtl
rtl: $(filter rtl/%, $(OK_CERTS))

.PHONY: serialize
serialize: $(filter serialize/%, $(OK_CERTS))

.PHONY: sorting
sorting: $(filter sorting/%, $(OK_CERTS))

.PHONY: std
std: $(filter std/%, $(OK_CERTS))

.PHONY: str
str: $(filter str/%, $(OK_CERTS))

.PHONY: system
system: $(filter system/%, $(OK_CERTS))

.PHONY: tau
tau: $(filter tau/%, $(OK_CERTS))

.PHONY: textbook
textbook: $(filter textbook/%, $(OK_CERTS))

.PHONY: tools
tools: $(filter tools/%, $(OK_CERTS))

.PHONY: unicode
unicode: $(filter unicode/%, $(OK_CERTS))

.PHONY: xdoc
xdoc: $(filter xdoc/%, $(OK_CERTS))


.PHONY: workshops \
        workshop1999 workshop2000 workshop2001 workshop2002 \
        workshop2003 workshop2004 workshop2006 workshop2007 \
        workshop2009 workshop2011 workshop2013

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



# Projects targets:

.PHONY: paco
paco: $(filter projects/paco/%, $(OK_CERTS))

.PHONY: taspi
taspi: $(filter projects/taspi/%, $(OK_CERTS))

.PHONY: jfkr
jfkr: $(filter projects/security/jfkr/%, $(OK_CERTS))

.PHONY: des
des: $(filter projects/security/des/%, $(OK_CERTS))

.PHONY: sha-2
sha-2: $(filter projects/security/sha-2/%, $(OK_CERTS))

.PHONY: security
security: jfkr des sha-2

.PHONY: wp-gen
wp-gen: $(filter projects/wp-gen/%, $(OK_CERTS))

.PHONY: concurrent-programs
concurrent-programs: $(filter projects/concurrent-programs/%, $(OK_CERTS))

.PHONY: equational
equational: $(filter projects/equational/%, $(OK_CERTS))

.PHONY: leftist-trees
leftist-trees: $(filter projects/leftist-trees/%, $(OK_CERTS))

.PHONY: legacy-defrstobj
legacy-defrstobj: $(filter projects/legacy-defrstobj/%, $(OK_CERTS))

# Dependencies based on running the following in the milawa/ACL2 directory:
#   grep "include-book" `find . -name "*.lisp"` | grep :dir
# We want to make sure these are certified before trying to build Milawa,
# so that we don't have to integrate its Make system into this Makefile
MILAWA_DEPS := misc/untranslate-patterns.cert \
               misc/hons-help2.cert \
               misc/definline.cert \
               str/top.cert \
               arithmetic-3/floor-mod/floor-mod.cert \
               tools/include-raw.cert \
               centaur/misc/seed-random.cert \
               ihs/logops-lemmas.cert

.PHONY: milawa-test-basic

milawa-test-basic: $(MILAWA_DEPS)
	cd projects/milawa/ACL2; $(MAKE) ACL2=$(ACL2) acl2-images/utilities-symmetry

.PHONY: milawa-test-extended
milawa-test-extended: milawa-test-basic
	cd projects/milawa/ACL2; $(MAKE) ACL2=$(ACL2) all

.PHONY: milawa-clean
# The -d test below avoids problems with nonstd/Makefile, which
# includes the present Makefile.
milawa-clean:
	if [ -d projects/milawa/ACL2 ] ; then \
	cd projects/milawa/ACL2; $(MAKE) clean ; \
	fi

clean: milawa-clean

# Warning: ACL2's GNUmakefile uses the following "certify-books"
# target to implement its own target, "certify-books", which some
# might use to build all "appropriate" books when installing ACL2.  So
# please be careful about making major changes to "certify-books" in
# this Makefile.
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
# :REDEF); presumably these books mess with raw mode.  Since we have
# had such problems with ccg/ccg.lisp (presumably because it includes
# hacking/hacker), we exclude that book too.

BOOKS_BKCHK_OUT := $(patsubst %.cert,%.bkchk.out,$(OK_CERTS))
BOOKS_BKCHK_OUT := $(filter-out hacking/%, $(BOOKS_BKCHK_OUT))
BOOKS_BKCHK_OUT := $(filter-out workshops/2007/dillinger-et-al/code/%, $(BOOKS_BKCHK_OUT))
BOOKS_BKCHK_OUT := $(filter-out ccg/ccg.bkchk.out, $(BOOKS_BKCHK_OUT))

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

# Next, we implement the target "special", which generalize the
# approach for bkchk (above) to allow arbitrary code before and after
# an include-book.

BOOKS_SPECIAL_OUT := $(patsubst %.cert,%.special.out,$(OK_CERTS))
BOOKS_SPECIAL_OUT := $(filter-out hacking/%, $(BOOKS_SPECIAL_OUT))
BOOKS_SPECIAL_OUT := $(filter-out workshops/2007/dillinger-et-al/code/%, $(BOOKS_SPECIAL_OUT))

.PHONY: special
special: $(BOOKS_SPECIAL_OUT)

%.special.out: %.cert
	@echo "Including $* on `date`"
	@echo '(acl2::value :q)' > $(@D)/workxxx.special.$(*F)
	@echo '(in-package "ACL2")' >> $(@D)/workxxx.special.$(*F)
	@echo '(acl2::lp)' >> $(@D)/workxxx.special.$(*F)
	@echo '(acl2::in-package "ACL2")' >> $(@D)/workxxx.special.$(*F)
	@cat $(ACL2_SPECIAL_PRE) >> $(@D)/workxxx.special.$(*F)
	@echo '(include-book "$*")' >> $(@D)/workxxx.special.$(*F)
	@cat $(ACL2_SPECIAL_POST) >> $(@D)/workxxx.special.$(*F)
	@($(ACL2) < $(@D)/workxxx.special.$(*F) 2>&1) > $*.special.out
	@rm -f $(@D)/workxxx.special.$(*F)

##############################
### Section: Building the XDOC combined manual
##############################

# See :DOC xdoc for more information.

# The xdoc combined manual is built in directory centaur/manual/, top
# page index.html, as a byproduct of building centaur/doc.cert with
# ACL2(h).  The following target builds the combined manual, but you
# may wish to issue the command below directly, so that the -j option
# is passed to the call of make.  Don't forget to include ACL2=acl2h,
# where acl2h is your ACL2(h) executable.

# This has been tested using CCL on Linux, but may work for other
# OS/Lisp combinations.  Note that ACL2(h) is required for that build
# of the xdoc manual, because it is required for some of the books
# included in centaur/doc.lisp.

manual:
	$(MAKE) USE_QUICKLISP=1 centaur/doc.cert

# In order to read the acl2+books combined manual in the Emacs-based
# ACL2-Doc browser (see :DOC acl2-doc), the file
# system/doc/rendered-doc-combined.lsp is required.  That requires (or
# causes) centaur/doc.cert to be built, as above, which can be
# time-consuming.  We expect to include
# system/doc/rendered-doc-combined.lsp with releases and also,
# perhaps, with occasional updates on the ACL2 website.  To build this
# text-based file after building centaur/doc.cert as above, issue the
# following command in this directory, where acl2h is an ACL2(h)
# executable.

#   make system/doc/render-doc-combined.cert ACL2=acl2h

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

# VL Toolkit

centaur/vl/bin/vl: centaur/vl/kit/top.cert
	@echo "Making VL Verilog Toolkit executable"
	@cd centaur/vl/kit; \
         ACL2_CUSTOMIZATION=NONE $(STARTJOB) -c "$(ACL2) < save.lsp &> save.out"
	@ls -la centaur/vl/bin/vl

.PHONY: vl
vl: centaur/vl/bin/vl

.PHONY: clean_vl
clean_vl:
	@echo "Cleaning centaur/vl/bin directory"
	@rm -f centaur/vl/bin/*

clean: clean_vl




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
#
# Jared Davis has summarized the improvements over the earlier Makefile as
# follows.
#
#  - It simplifies the build system, doing away with hundreds of Makefiles in
#    individual directories, and replacing them with this single file.  This is
#    possible because I've gone through and fixed up many books so that they
#    follow certain conventions, explained below.
#
#  - It increases (significantly) opportunities for book-level parallelism, by
#    doing away with directory-level dependencies.  Essentially, any books that
#    do not have an include-book dependency can be built in parallel.  At the
#    same time, this means that books can be reorganized based on their logical
#    content, without regards to directory build order.
#
#  - It generally increases build-system automation.  We use "find" commands to
#    find Lisp files instead of maintaining (by hand) lists of directories.  We
#    also do not need to manually keep track of dependencies between
#    directories, etc.





# BOZO --- the comments below should eventually be integrated into the XDOC
# documentatio about cert.pl.

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
#     These instructions specify arguments to certify-book, for example:
#       ; cert-flags: ? t :ttags :all
#   - In the following cases, books may be skipped in which case,
#     recursively, so are books that include such books, books that
#     include those parent books, and so on.  In each case, the
#     indicated line may be placed either in the .lisp file or in the
#     .acl2 file that is consulted, as discussed above.
#       - Books that depend on ACL2(h), such as
#         centaur/tutorial/alu16-book.lisp, contain this line:
#           ; cert_param: (hons-only)
#       - Books that require glucose (a SAT solver) contain this line:
#           ; cert_param: (uses-glucose)
#       - Books that require quicklisp contain this line:
#           ; cert_param: (uses-quicklisp)
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
