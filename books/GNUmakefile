# ACL2 Community Books Makefile
# Copyright (C) 2013 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# License: (An MIT/X11-style license)
#
#   Permission is hereby granted, free of charge, to any person obtaining a
#   copy of this software and associated documentation files (the "Software"),
#   to deal in the Software without restriction, including without limitation
#   the rights to use, copy, modify, merge, publish, distribute, sublicense,
#   and/or sell copies of the Software, and to permit persons to whom the
#   Software is furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in
#   all copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#   DEALINGS IN THE SOFTWARE.
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
#   regression    Certifies most books that are not horribly slow, including,
#                 for instance, most of workshops, projects, the centaur
#                 books, the jvm models, etc.  Usually, committers to
#                 acl2-books should run "make regression" first.
#
#   regression-everything
#                 A very full build, including very slow books.  Most users
#                 will not want to use this target.  It is useful for, e.g.,
#                 regression testing before releases.  Note that
#                 EXCLUDED_PREFIXES may not work with the
#                 `regression-everything' target.
#
#   all           alias for regression-everything
#
#   <dirname>     There are targets for many top-level directories, e.g., you
#                 may run "make coi" to build everything in coi/ directory,
#                 "make rtl" to build the books within rtl/, and so on.
#
#   <file-name>   You can ask to certify particular files, for instance,
#                 "make arithmetic-5/top.cert"
#
#   manual        Builds doc/top.cert, which produces the combined ACL2
#                 books+system manual in doc/manual/index.html.  Note:
#                 this target requires USE_QUICKLISP=1.
#
#   special       Includes all the books, allowing arbitrary code before and
#                 after an include-book, and writing the log for each book
#                 <bk>.lisp to the file <bk>.special.out.
#
#   TAGS          Makes a tag database for emacs including all the book sources.
#
# Basic Options:
#
#   USE_QUICKLISP=1
#                 Needed for certain books.  Quicklisp is a packaging
#                 system for Common Lisp libraries, sort of like CPAN
#                 for Perl or RubyGems for Ruby.  May not work with
#                 some Lisps (but seems to work with all ACL2 host
#                 Lisps except GCL).  This might still work if the
#                 system books directory is relocated after
#                 certification.  But if, after the move, you want to
#                 certify books that depend on quicklisp, you should
#                 probably run "make quicklisp_clean" first.
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

# GNU Make exports exported variables to the shell inside recipes, but
# not inside $(shell ...).  To work around this, we'll add every
# variable we export to a list and manually provide the environment we
# want when we need it.
EXPORTED_VARS :=


# For cygwin, we need to do something special to get a Unix-like
# pathname.
ifneq (,$(findstring CYGWIN, $(shell uname)))
export ACL2_SYSTEM_BOOKS := $(shell cygpath -m $(CURDIR))
EXPORTED_VARS += ACL2_SYSTEM_BOOKS
else
export ACL2_SYSTEM_BOOKS := $(CURDIR)
EXPORTED_VARS += ACL2_SYSTEM_BOOKS
endif

$(info ACL2_SYSTEM_BOOKS is $(ACL2_SYSTEM_BOOKS))
ifneq ($(ACL2_JOBS), )
${error Error: variable ACL2_JOBS is obsolete -- use -j instead -- see :DOC book-makefiles }
endif # ifneq ($(ACL2_JOBS), )

# The build of saved_acl2 may succeed even if the directory name has
# spaces, but book certification will almost surely fail, so we
# disallow such a build.  Comment out the three lines below if you
# want to take your chances nonetheless!
ifneq (,$(word 2, $(ACL2_SYSTEM_BOOKS)))
$(error Illegal ACL2 books directory (contains a space): $(ACL2_SYSTEM_BOOKS)/)
endif

BUILD_DIR := $(ACL2_SYSTEM_BOOKS)/build

# Here is an undocumented way to specify a different shell, e.g., sh.
# There are no guarantees that another shell will work, however!
ifdef ACL2_SHELL_OVERRIDE
SHELL := $(ACL2_SHELL_OVERRIDE)
else
SHELL := $(shell which bash)
endif # ifdef ACL2_SHELL_OVERRIDE

STARTJOB ?= $(SHELL)
export STARTJOB

# We avoid ?= below because we want to be sure that the check below is
# done only after ACL2 has been assigned, and because we want to treat
# an empty $(ACL2) the same as an undefined ACL2.
ifeq ($(ACL2),)
ACL2 := acl2
endif # ifeq ($(ACL2),)
export ACL2

.SUFFIXES:
.SUFFIXES: .cert .lisp

.PHONY: default basic regression

# Keep this before any other target so that default will be the default target
default: basic

basic:

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

RUN_ACL2_FEATURES := $(shell cd $(BUILD_DIR); ACL2=$(ACL2) STARTJOB=$(STARTJOB) ./features.sh > features.out)
# Only conditionally include Makefile-features, so that make clean works even
# if ACL2 isn't built.
-include $(BUILD_DIR)/Makefile-features

$(info ACL2_HAS_HONS      := $(ACL2_HAS_HONS))
$(info ACL2_HAS_ANSI      := $(ACL2_HAS_ANSI))
$(info ACL2_HAS_PARALLEL  := $(ACL2_HAS_PARALLEL))
$(info ACL2_HAS_REALS     := $(ACL2_HAS_REALS))
$(info ACL2_COMP_EXT      := $(ACL2_COMP_EXT))
$(info ACL2_HOST_LISP     := $(ACL2_HOST_LISP))
$(info OS_HAS_ABC         := $(OS_HAS_ABC))
$(info OS_HAS_GLUCOSE     := $(OS_HAS_GLUCOSE))
$(info OS_HAS_IPASIR      := $(OS_HAS_IPASIR))
$(info OS_HAS_SMTLINK     := $(OS_HAS_SMTLINK))
$(info OS_HAS_STP         := $(OS_HAS_STP))
$(info USE_QUICKLISP      := $(USE_QUICKLISP))
$(info ACL2_USELESS_RUNES := $(ACL2_USELESS_RUNES))
$(info Done with features.)

ifdef ACL2_FEATURES_DETECTED
# This sanity check tries to make sure that the copy of ACL2 you are using
# thinks that this is the right books directory.  We can only do this check if
# we have successfully included Makefile-features, which may not be the case if
# we're doing something like a make clean in an already-clean directory, or if
# ACL2 isn't successfully found in the path and Makefile-features doesn't
# exist.
SANITY_CHECK_ACTUAL_DIR   := $(shell pwd -P)
SANITY_CHECK_EXPECTED_DIR := $(shell cd $(ACL2_THINKS_BOOK_DIR_IS); pwd -P)
ifneq ($(SANITY_CHECK_ACTUAL_DIR), $(SANITY_CHECK_EXPECTED_DIR))
$(info Books Sanity Check Failed)
$(info - Using ACL2 from                 $(ACL2))
$(info - ACL2 thinks system books are in $(ACL2_THINKS_BOOK_DIR_IS))
$(info - This resolves to                $(SANITY_CHECK_EXPECTED_DIR))
$(info - But we are currently in         $(SANITY_CHECK_ACTUAL_DIR))
$(error Books Sanity Check Failed)
endif

endif # ACL2_FEATURES_DETECTED

ifndef NO_RESCAN

# We skip the scan for excluded prefixes.  This change was implemented
# by Matt Kaufmann on 9/25/2013 as part of the process of fixing
# ACL2(r) regressions.  (Note that nonstd/Makefile includes this
# Makefile.)
ifneq ($(EXCLUDED_PREFIXES), )
space =  # just a space
EGREP_EXTRA_EXCLUDE_STRING = |$(subst $(space) $(space),|,$(strip $(EXCLUDED_PREFIXES)))
endif # ifneq ($(EXCLUDED_PREFIXES), )

# We exclude some directories because there are subdirectories and
# it's just easiest to stop at the root.  We also exclude
# centaur/satlink/solvers because it depends on all kinds of extra SAT
# solvers.  We exclude projects/milawa/ACL2 because of the large
# amount of disk space otherwise consumed.
$(info Scanning for books...)
REBUILD_MAKEFILE_BOOKS := $(shell \
  rm -f $(BUILD_DIR)/Makefile-books; \
  time find . -name "*.lisp" \
    | egrep -v '^(\./)?(interface|centaur/satlink/solvers|projects/milawa/ACL2|clause-processors/SULFA|workshops/2003/kaufmann/support/input|workshops/2003/kaufmann/support/rtl|build/test-ifdef-define$(EGREP_EXTRA_EXCLUDE_STRING))' \
    | fgrep -v '.\#' \
  > $(BUILD_DIR)/Makefile-books; \
  ls -l $(BUILD_DIR)/Makefile-books)
#$(info $(REBUILD_MAKEFILE_BOOKS))

ifdef ACL2_PCERT
	PCERT_OPT := "--pcert-all"
else
	PCERT_OPT :=
endif

$(info Scanning for dependencies...)
REBUILD_MAKEFILE_DEPS := $(shell \
  rm -f $(BUILD_DIR)/Makefile-deps $(BUILD_DIR)/Makefile-deps.out; \
    time ($(EXPORT_SHELL_ENV) \
          $(BUILD_DIR)/cert.pl \
          --quiet \
          --print-relocs \
          $(PCERT_OPT) \
          --static-makefile $(BUILD_DIR)/Makefile-deps \
          --cache $(BUILD_DIR)/Makefile-cache \
          --acl2-books `pwd` \
          --targets $(BUILD_DIR)/Makefile-books \
          --write-sources $(BUILD_DIR)/Makefile-sources \
          --write-certs $(BUILD_DIR)/Makefile-certs \
          1>&2) ;\
  echo 'MFDEPS_DEBUG := $$(shell echo Reading book deps ' \
       'Makefile-deps created on' `date` '1>&2)' \
    >> $(BUILD_DIR)/Makefile-deps; \
  ls -l $(BUILD_DIR)/Makefile-deps)
#$(info $(REBUILD_MAKEFILE_DEPS))
$(info Done scanning.)

endif # ifndef NO_RESCAN

include $(BUILD_DIR)/Makefile-deps


# Cause error for illegal certification attempts:

ifeq ($(ACL2_HAS_HONS), )

$(CERT_PL_HONS_ONLY):
	$(MAKE) no_hons_error NO_RESCAN=1 CERT_PL_HONS_ONLY_BOOK=$@

.PHONY: no_hons_error
no_hons_error:
	@echo "Error! Target $(CERT_PL_HONS_ONLY_BOOK) requires hons."
	@exit 1

endif # ifeq ($(ACL2_HAS_HONS), )

ifeq ($(ACL2_HAS_ANSI), )

# We are presumably running GCL/CLtL1.  There is no need to cause an
# error in the ansi-only case, because the code above will already
# handle that.
$(filter-out $(CERT_PL_HONS_ONLY), $(CERT_PL_ANSI_ONLY)):
	$(MAKE) no_ansi_error NO_RESCAN=1 CERT_PL_ANSI_ONLY_BOOK=$@

.PHONY: no_ansi_error
no_ansi_error:
	@echo "Error! Target $(CERT_PL_ANSI_ONLY_BOOK) requires ANSI Common Lisp."
	@exit 1

endif # ifeq ($(ACL2_HAS_ANSI), )

# End of "Cause error for illegal certification attempts".

OK_CERTS := $(CERT_PL_CERTS)

ifeq ($(ACL2_HAS_HONS), )

# We use "{...}" delimiters to avoid errors in version 3.80 of make.
${info Excluding books that need ACL2(h) [...]}
OK_CERTS := $(filter-out $(CERT_PL_HONS_ONLY), $(OK_CERTS))

endif # ifeq ($(ACL2_HAS_HONS), )


ifneq (CCL, $(ACL2_HOST_LISP))
${info Excluding books that are CCL-only: [$(CERT_PL_CCL_ONLY)]}
OK_CERTS := $(filter-out $(CERT_PL_CCL_ONLY), $(OK_CERTS))
endif

ifeq (ALLEGRO, $(ACL2_HOST_LISP))
${info Excluding non-Allegro books: [$(CERT_PL_NON_ALLEGRO)]}
OK_CERTS := $(filter-out $(CERT_PL_NON_ALLEGRO), $(OK_CERTS))
endif

ifeq (LISPWORKS, $(ACL2_HOST_LISP))
${info Excluding non-Lispworks books: [$(CERT_PL_NON_LISPWORKS)]}
OK_CERTS := $(filter-out $(CERT_PL_NON_LISPWORKS), $(OK_CERTS))
endif

ifeq (SBCL, $(ACL2_HOST_LISP))
${info Excluding non-SBCL books: [$(CERT_PL_NON_SBCL)]}
OK_CERTS := $(filter-out $(CERT_PL_NON_SBCL), $(OK_CERTS))
endif

ifeq (CMU, $(ACL2_HOST_LISP))
${info Excluding non-CMUCL books: [$(CERT_PL_NON_CMUCL)]}
OK_CERTS := $(filter-out $(CERT_PL_NON_CMUCL), $(OK_CERTS))
endif

ifeq (GCL, $(ACL2_HOST_LISP))
${info Excluding non-GCL books: [$(CERT_PL_NON_GCL)]}
OK_CERTS := $(filter-out $(CERT_PL_NON_GCL), $(OK_CERTS))
endif

ifeq ($(ACL2_HAS_ANSI), )

# We use "{...}" delimiters to avoid errors in version 3.80 of make.
${info Excluding books that need ANSI Common Lisp [...]}
OK_CERTS := $(filter-out $(CERT_PL_ANSI_ONLY), $(OK_CERTS))

endif # ifeq ($(ACL2_HAS_ANSI), )

ifeq ($(OS_HAS_ABC), )
$(info Excluding books that need ABC: [$(CERT_PL_USES_ABC)])
OK_CERTS := $(filter-out $(CERT_PL_USES_ABC), $(OK_CERTS))
endif

ifeq ($(OS_HAS_GLUCOSE), )
$(info Excluding books that need Glucose: [$(CERT_PL_USES_GLUCOSE)])
OK_CERTS := $(filter-out $(CERT_PL_USES_GLUCOSE), $(OK_CERTS))
endif

ifeq ($(OS_HAS_IPASIR), )
$(info Excluding books that need Ipasir: [$(CERT_PL_USES_IPASIR)])
OK_CERTS := $(filter-out $(CERT_PL_USES_IPASIR), $(OK_CERTS))
endif

ifeq ($(OS_HAS_SMTLINK), )
$(info Excluding books that need SMTLINK: [$(CERT_PL_USES_SMTLINK)])
OK_CERTS := $(filter-out $(CERT_PL_USES_SMTLINK), $(OK_CERTS))
endif

ifeq ($(OS_HAS_STP), )
$(info Excluding books that need STP: [$(CERT_PL_USES_STP)])
OK_CERTS := $(filter-out $(CERT_PL_USES_STP), $(OK_CERTS))
endif


ifeq ($(ACL2_HAS_REALS), )

$(info Excluding ACL2(r)-only books: [$(CERT_PL_USES_ACL2R)])
OK_CERTS := $(filter-out $(CERT_PL_USES_ACL2R), $(OK_CERTS))

endif # ifeq ($(ACL2_HAS_REALS), )


ifneq ($(ACL2_HAS_REALS), )

$(info Excluding non-ACL2(r) books: [$(CERT_PL_NON_ACL2R)])
OK_CERTS := $(filter-out $(CERT_PL_NON_ACL2R), $(OK_CERTS))

regression: nonstd/workshops/1999/calculus/book/proof-outline.cert
regression: nonstd/workshops/1999/calculus/book/tree.cert
regression: nonstd/workshops/1999/calculus/book/tree/proof-outline

# Some additional special instructions for generated ACL2(r)-only books.
nonstd/workshops/1999/calculus/book/proof-outline.cert: nonstd/workshops/1999/calculus/book/tree.cert

nonstd/workshops/1999/calculus/book/tree.cert: nonstd/workshops/1999/calculus/book/tree.lisp
	cd nonstd/workshops/1999/calculus/book/ ; \
	   $(STARTJOB) -c "$(MAKE) tree.cert"
	ls -l nonstd/workshops/1999/calculus/book/tree.cert

nonstd/workshops/1999/calculus/book/tree.lisp:
	cd nonstd/workshops/1999/calculus/book ; \
	   $(STARTJOB) -c "$(MAKE) -f Makefile-essence tree.lisp"
	ls -l nonstd/workshops/1999/calculus/book/tree.lisp

nonstd/workshops/1999/calculus/book/tree/proof-outline: \
	nonstd/workshops/1999/calculus/book/tree.cert \
	nonstd/workshops/1999/calculus/book/proof-outline.cert
	cd nonstd/workshops/1999/calculus/book/ ; \
           $(STARTJOB) -c "$(MAKE) proof-outline"


endif # ifneq ($(ACL2_HAS_REALS), )



# Set up REALLY_USE_QUICKLISP to be 1 if we really want to use Quicklisp or 0
# otherwise.  REALLY_USE_QUICKLISP is almost the same as USE_QUICKLISP.
# However, Quicklisp doesn't work on GCL, so if we're running on GCL, then
# ignore what the user said and don't try to build the Quicklisp books.
#
# I would much prefer to just reassign USE_QUICKLISP to 0 when we don't want
# it, but I can't get that to work in Make for whatever reason.
# (Note: Things have changed since the comment just above was written,
# so someone might want to try to simplify.)

ifeq ($(USE_QUICKLISP), 1)
  ifeq ($(ACL2_HOST_LISP), GCL)
    $(info Note: Ignoring USE_QUICKLISP=1 since Quicklisp does not work on GCL!)
    REALLY_USE_QUICKLISP := 0
  else
    REALLY_USE_QUICKLISP := 1
  endif
else
  REALLY_USE_QUICKLISP := 0
endif

QUICKLISP_DIR := quicklisp

.PHONY: quicklisp

ifeq ($(REALLY_USE_QUICKLISP), 0)

quicklisp:
	@echo "Error: Can't build Quicklisp without USE_QUICKLISP=1."
	@false

manual:
	@echo "Error: Can't build the manual without USE_QUICKLISP=1."
	@false

else

ifneq ($(filter-out CCL SBCL, $(ACL2_HOST_LISP)),)
# As of this writing (late 2019), ACL2 built on Allegro CL, Lispworks,
# or (as is well known) GCL fails to certify all books necessary to
# build the manual, probably because of problems involving quicklisp.
# Ideally someone will fix those problems, but for now we will simply
# cause an immediate error on an attempt to build the manual with this
# target.
manual:
	@echo "Error: The manual may be built only using ACL2 built on CCL or SBCL,"
	@echo "       not $(ACL2_HOST_LISP)."
	@exit 1

else

quicklisp: $(QUICKLISP_DIR)/top.cert

manual: doc/top.cert system/doc/acl2-manual.cert

endif # ifneq ($(filter-out CCL SBCL, $(ACL2_HOST_LISP)),)
endif # REALLY_USE_QUICKLISP


# [Jared]: I moved these out of the REALLY_USE_QUICKLISP section so that "make
# clean" will always remove the quicklisp files if you have ever built with
# REALLY_USE_QUICKLISP before.  The goal is to ensure that stale quicklisp
# files aren't left around after a "make clean" by accident.

.PHONY: quicklisp_clean

quicklisp_clean:
	@echo "Cleaning up Quicklisp files"
	cd $(QUICKLISP_DIR); ./clean.sh

clean: quicklisp_clean

ifeq ($(REALLY_USE_QUICKLISP), 0)
$(info Excluding books that depend on Quicklisp: [$(CERT_PL_USES_QUICKLISP)])
OK_CERTS := $(filter-out $(CERT_PL_USES_QUICKLISP), $(OK_CERTS))
endif


# Books that currently don't certify (or don't certify on some
# systems), and that we want to work around for the moment:
BROKEN_BOOKS :=

# The models/y86 books are a special case.  We prefer to include them
# only with the "all" target, not the "regression" target, since they
# have large memory requirements -- and then, only for certain host
# Lisps.  Originally we handled them in a custom way, using old-style
# Makefiles based on Makefile-generic rather than cert.pl, but then we
# did not get the benefit of the cert.pl dependency analysis; for
# example, if arithmetic-5/top.cert was out of date then "make" would
# not rebuild the models/y86/ books as it should.  So we no longer
# exclude them in the "egrep -v" command above, instead allowing
# cert.pl to do its thing.

ifneq ($(ACL2_HAS_HONS), )
ifeq ($(filter CCL ALLEGRO SBCL, $(ACL2_HOST_LISP)), )

# When the Lisp is not one of those mentioned on the line above, we
# skip the models/y86/ books, even for the "all" target.  In
# particular, we exclude GCL: in one ANSI GCL ACL2(h) regression,
# certification runs were still proceeding after more than 10 hours
# for each of four books under models/y86/
# (y86-basic/common/x86-state, y86-two-level/common/x86-state,
# y86-two-level-abs/common/x86-state-concrete, and
# y86-basic/py86/popcount), probably because of the demands of
# def-gl-thm.  Moreover, LispWorks has too small a value for
# array-dimension-limit to support these certifications.

BROKEN_BOOKS += $(filter models/y86/%, $(OK_CERTS))
endif # ifneq ($(filter CCL ALLEGRO SBCL, $(ACL2_HOST_LISP)), )
endif # ifneq ($(ACL2_HAS_HONS), )

OK_CERTS := $(filter-out $(BROKEN_BOOKS), $(OK_CERTS))


# SLOW_BOOKS is a list of books that are too slow (or in any way
# undesirable) to include as part of an ordinary regression.  There
# are currently comments in some of the corresponding Makefiles that
# explain something about these books.  WARNING: It is probably a bad
# idea to include targets here that are in ACL2_CUSTOM_TARGETS:
# SLOW_BOOKS is removed from OK_CERTS just below, but later,
# ACL2_CUSTOM_TARGETS adds its targets to OK_CERTS.

SLOW_BOOKS := \
  books/misc/check-acl2-exports.cert \
  coi/defung/defung-stress-long.cert \
  models/jvm/m5/apprentice.cert \
  system/parallel/proofs/ideal-speedup.cert \
  workshops/2009/sumners/support/examples.cert \
  workshops/2011/krug-et-al/support/MinVisor/va-to-pa-thm.cert \
  workshops/2011/krug-et-al/support/MinVisor/setup-nested-page-tables.cert \
  workshops/2013/hardin-hardin/support/APSP.cert \
  doc/top-slow.cert

# The following could well be considered as slow books, too.
# doc/top.cert
# doc/top-fast.cert
# projects/include-doc.cert
# projects/doc.cert
# projects/top-doc.cert
# ALSO, directory projects/async/gcd/ (perhaps even projects/async/)
# AND   directory projects/arm/
# could be added as x86isa is below.

SLOW_BOOKS += $(filter projects/x86isa/%, $(OK_CERTS))

SLOW_BOOK_TARGETS :=

ifneq ($(ACL2_HAS_HONS), )
SLOW_BOOK_TARGETS += milawa-test-basic
endif

# Now SLOW_BOOKS is defined as the list above.
SLOW_BOOKS += $(SLOW_BOOK_TARGETS)

# We used to filter out the slow books here. As of mid-2020, we do it later, as
# part of the `regression` target
# OK_CERTS := $(filter-out $(SLOW_BOOKS), $(OK_CERTS))


##############################
### Section: Cleaning
##############################

# We delegate most of the cleaning process to clean.pl, a simple perl script
# that lets us take care not to delete certain kinds of files.  The clean.pl
# script will remove things like .cert and .fasl files.  A few files don't
# get explicitly cleaned.

CLEAN_FILES_EXPLICIT := \
   $(BUILD_DIR)/Makefile-comp \
   $(BUILD_DIR)/Makefile-comp-pre \
   $(BUILD_DIR)/Makefile-deps \
   $(BUILD_DIR)/Makefile-books \
   $(BUILD_DIR)/Makefile-features \
   $(BUILD_DIR)/Makefile-cache \
   serialize/test.sao \
   bdd/benchmarks.lisp \
   nonstd/workshops/1999/calculus/book/tree.lisp \
   centaur/getopt/demo2.core \
   centaur/getopt/demo2.gcl \
   centaur/getopt/demo2.lw \
   centaur/getopt/demo2.lx86cl64 \
   centaur/getopt/demo2.dx86cl64 \
   centaur/getopt/demo2.ccl \
   nonstd/workshops/1999/calculus/book/outline/ \
   projects/sat/lrat/incremental/lrat-check \
   projects/sat/lrat/incremental/lrat-check.* \
   projects/sat/lrat/cube/cube-check \
   projects/sat/lrat/cube/cube-check.* \
   projects/apply-model/ex1/evaluation-apply.lisp \
   projects/apply-model/ex1/evaluation-user-defs.lisp \
   projects/apply-model/ex2/evaluation-apply.lisp \
   projects/apply-model/ex2/evaluation-user-defs.lisp \
   projects/apply-model-2/ex1/evaluation-apply.lisp \
   projects/apply-model-2/ex1/evaluation-user-defs.lisp \
   projects/apply-model-2/ex2/evaluation-apply.lisp \
   projects/apply-model-2/ex2/evaluation-user-defs.lisp

MORECLEAN_FILES_EXPLICIT := \
   doc/manual \
   system/doc/manual \
   system/doc/manual-fast \
   doc/xdoc.sao

.PHONY: clean_books clean

clean_books:
	@echo "Using clean.pl to remove certificates, etc."
	$(BUILD_DIR)/clean.pl

# We test that directory quicklisp exists because it probably
# doesn't for nonstd/, and we include this makefile from that
# directory.

# 2017-12-16: Rager wonders if the above comment should be
# removed, as there's no test of the quicklisp directory
# immediately below.

clean: clean_books
	@echo "Removing extra, explicitly temporary files."
	rm -rf $(CLEAN_FILES_EXPLICIT)
	for dir in $(dir $(ACL2_CUSTOM_TARGETS)) ; \
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
# We handle those next

# Our perhaps gross hack is to use the old ACL2 Makefile-generic
# system to invoke the custom makefiles, for example as follows for
# workshops/2003/greve-wilding-vanfleet:

#   - we tell cert.pl not to look at greve-wilding-vanfleet/support, via a
#     cert_pl_exclude file;
#   - we add a greve-wilding-vanfleet/deps.lisp file with the
#     prerequisites that we need before going into the support
#     directory;
#   - we use an arbitrary top-level target to certify the actual books
#     after certifying the deps, which need not be in any sense "the
#     top-level book" for the directory -- but if not, then if a book
#     B in any other directory comes to depend on a book other than
#     the target that we picked, we will need to make it depend on
#     that target.

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
# conflicts if -j is other than 1.  Also: Do not include any targets
# that we don't always want built with "regression".

ACL2_CUSTOM_TARGETS := \
  system/toothbrush/success.txt \
  clause-processors/SULFA/target.cert \
  projects/translators/l3-to-acl2/target.cert \
  workshops/1999/multiplier/proof.cert \
  workshops/2003/greve-wilding-vanfleet/support/firewallworks.cert \
  workshops/2003/kaufmann/support/input/defs-in.cert \
  workshops/2003/kaufmann/support/rtl/package-defs.cert \
  workshops/2004/sumners-ray/support/success.txt

# Currently, apply-model and (probably) apply-model-2 don't work for
# ACL2(r).
ifeq ($(ACL2_HAS_REALS), )
ACL2_CUSTOM_TARGETS += projects/apply-model/phony
ACL2_CUSTOM_TARGETS += projects/apply-model-2/phony
endif

# Warning!  For each target below, if there is a cert_pl_exclude file
# in the directory or it is exluded explicitly by
# REBUILD_MAKEFILE_BOOKS, and a "deps" file is used, then that "deps"
# file should be placed in a different directory (that is not
# excluded).  For example, projects/translators/l3-to-acl2/target.cert
# below depends on projects/translators/l3-to-acl2-deps.cert, for
# which dependencies will be generated since there is no
# cert_pl_exclude file in projects/translators/ (even though there is
# a cert_pl_exclude in projects/translators/l3-to-acl2/).

# It is currently only recommended to test the toothbrush mechanism
# for Lisps that compile on-the-fly, namely CCL and SBCL, since that
# mechanism doesn't use (or depend on) compiled files in the main
# ACL2 directory.  We might revisit that decision if there is reason
# to do so.
ifeq ($(TB_LISP), )
.PHONY: system/toothbrush/success.txt
system/toothbrush/success.txt:
	@echo "Note: Skipping $@ for host Lisp $(ACL2_HOST_LISP)."
else
system/toothbrush/success.txt: system/toothbrush-deps.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"
endif # ifeq ($(TB_LISP), )

# We only make the books under SULFA if a documented test for an
# installed SAT solver succeeds.
clause-processors/SULFA/target.cert: \
  clause-processors/deps-SULFA.cert
	@if [ -f ${PWD}/../aux/minisat2/${HOSTTYPE}/minisat/core/minisat ] ; \
	then \
	(cd $(@D) ; $(MAKE)) ; \
	else \
	echo "NOTE: Skipping SULFA subdirectory (need SAT solver installed as per books/clause-processors/SULFA/README)." ; \
	fi

projects/translators/l3-to-acl2/target.cert: \
  projects/translators/l3-to-acl2-deps.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE) -j 1 clean"
	cd $(@D) ; $(STARTJOB) -c "$(MAKE) -j 1"

workshops/1999/multiplier/proof.cert: \
  workshops/1999/deps-multiplier.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

workshops/2003/greve-wilding-vanfleet/support/firewallworks.cert: \
  workshops/2003/greve-wilding-vanfleet/deps.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

workshops/2003/kaufmann/support/input/defs-in.cert: \
  workshops/2003/kaufmann/deps.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

workshops/2003/kaufmann/support/rtl/package-defs.cert: \
  workshops/2003/kaufmann/deps.cert \
  workshops/2003/kaufmann/support/tool/simplify-defuns.cert \
  workshops/2003/kaufmann/support/tool/wrapper.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

# The following has no dependencies, so doesn't need a "deps" file.
workshops/2004/sumners-ray/support/success.txt:
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

.PHONY: projects/apply-model/phony
projects/apply-model/phony: projects/apply-model-deps.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

.PHONY: projects/apply-model-2/phony
projects/apply-model-2/phony: projects/apply-model-2-deps.cert
	cd $(@D) ; $(STARTJOB) -c "$(MAKE)"

endif # ifeq ($(ACL2_HAS_REALS), )

endif # ifndef ACL2_COMP

# We avoid += because we want the custom targets to start first, in
# order to maximize parallelism.  If they go at the end, maybe we'll
# have an expensive sequential tail in the regression.
OK_CERTS := $(ACL2_CUSTOM_TARGETS) $(OK_CERTS)

##############################
### Section: Support for ACL2_COMP
##############################

# NOTE: Books that were certified with pcert are, in many (and
# probably all) cases, recertified when using ACL2_COMP to build only
# compiled files.  This is unfortunate but probably not very
# important.  However, the book projects/stateman/stateman22.lisp
# takes a long time to certify and depends on
# tau/bounders/elementary-bounders.cert, which used pcert.  So we
# exclude that book below.

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
# projects/security/des/ depends on GL and hence centaur/, we don't
# exclude its books.)  We might not need to skip the y86 books, but
# since some Lisps have trouble certifying those, we play it safe and
# skip them.  Books under build/test/ present a problem because of
# dollar signs ($) in filenames, which doesn't seem worth solving.
# -- Hmmm, this filtering doesn't actually eliminate all centaur
# books.  That's OK provided the resulting targets all build
# successfully.
$(info For building compiled (.$(ACL2_COMP_EXT)) files, excluding some books (e.g., some centaur books))
OK_CERTS := $(filter-out centaur/%, \
              $(filter-out models/y86%, \
                $(filter-out build/test%, \
                  $(OK_CERTS))))

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

include $(BUILD_DIR)/Makefile-comp

# Define books to be skipped for multi-lisp compilation.

OK_CERTS := $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(OK_CERTS))

# Start a sequence of assignments to BOOKS_SKIP_COMP:
BOOKS_SKIP_COMP :=

# See comment above about this book; in short, it would be recertified
# (often taking a long time) because of its dependence on a book that,
# in turn, is recertified because it was originally certified with
# pcert.
BOOKS_SKIP_COMP += projects/stateman/stateman22.$(ACL2_COMP_EXT)

# Contain Lisp-specific readtime conditionals:
BOOKS_SKIP_COMP += hacking/evalable-ld-printing.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += centaur/misc/memory-mgmt-logic.$(ACL2_COMP_EXT)

# The following depend on centaur/misc/memory-mgmt-logic, which will
# be uncertified in other lisps and hence we won't get the target
# compiled file.
# NOTE: The list below is incomplete.  In particular, failures can be
# expected for centaur/ubdds/lite and centaur/esim/defmodules.  If we
# add those, then we get more failures; six attempts didn't reach
# closure.
BOOKS_SKIP_COMP += centaur/misc/memory-mgmt.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += centaur/ubdds/core.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += centaur/ubdds/extra-operations.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += std/strings/pretty-tests.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += centaur/ubdds/subset.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += centaur/ubdds/param.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += centaur/ubdds/witness.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += centaur/vl2014/loader/top.$(ACL2_COMP_EXT)
# WARNING!  See note above about "is incomplete" before attempting to
# extend the list above.

# Some attempts fail presumably due to dollar signs in filenames:
BOOKS_SKIP_COMP += $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(wildcard build/test/*.cert))

# dft-ex.acl2 specifies no compilation; getprop.lisp can give stack
# overflow in during the load of the expansion file -- perhaps not
# surprising, given that (comp t) occurs in the .lisp file:
BOOKS_SKIP_COMP += misc/dft-ex.$(ACL2_COMP_EXT) misc/getprop.$(ACL2_COMP_EXT)

# aof.acl2 specifies no compilation; knuth-arch.lisp depends on aof:
BOOKS_SKIP_COMP += workshops/1999/knuth-91/aof.$(ACL2_COMP_EXT) \
                   workshops/1999/knuth-91/knuth-arch.$(ACL2_COMP_EXT)

# The .acl2 files specify no compilation:
BOOKS_SKIP_COMP += $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(wildcard workshops/2002/cowles-flat/support/*.cert))
BOOKS_SKIP_COMP += $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(wildcard workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly/*.cert))
BOOKS_SKIP_COMP += demos/meta-wf-guarantee-example.$(ACL2_COMP_EXT)

# The .acl2 file for ccg.lisp specifies no compilation, so we exclude
# that books and books that include it.
BOOKS_SKIP_COMP += acl2s/ccg/ccg.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += acl2s/doc.$(ACL2_COMP_EXT)

# Some .acl2 files specify no compilation, including ed3.acl2, and
# many books depend on ed3:
BOOKS_SKIP_COMP += $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(wildcard workshops/2006/cowles-gamboa-euclid/Euclid/*.cert))

# At one time we handled system/pcert/ (using -j 1), which was a
# special case that was ignored because of its cert_pl_exclude file.
# But the exclude is no longer there, and we got a **PCERT0->PCERT1
# CONVERSION FAILED** error for
# system/pcert/acl2x-pcert-test-2-include.lisp.  So we simply exclude
# that directory.
BOOKS_SKIP_COMP += $(patsubst %.cert, %.$(ACL2_COMP_EXT), $(wildcard system/pcert/*.cert))

# The use of provisional certification seems to cause regeneration of
# the @expansion.lsp file, which can be a problem because, for
# example, GCL seems to generate "LISP" as a package name, which
# confuses the serialize reader.
BOOKS_SKIP_COMP += make-event/local-elided.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += make-event/local-elided-include.$(ACL2_COMP_EXT)

# The .acl2 files specify no compilation:
BOOKS_SKIP_COMP += workshops/2006/kaufmann-moore/support/rhs1-iff.$(ACL2_COMP_EXT) \
		   workshops/2006/kaufmann-moore/support/rhs1.$(ACL2_COMP_EXT) \
		   workshops/2006/kaufmann-moore/support/rhs2.$(ACL2_COMP_EXT) \
		   workshops/2006/kaufmann-moore/support/warnings.$(ACL2_COMP_EXT)

# There seems to be a problem with files that use include-raw.  We
# skip those.
# Has (include-raw "timer.lsp"):
BOOKS_SKIP_COMP += centaur/memoize/top.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += $(patsubst %-raw.lsp, %.$(ACL2_COMP_EXT), $(shell find . -name '*-raw.lsp' -print))

# Has readtime conditionals #+ccl and #-ccl ("not supported for this
# host Lisp").
BOOKS_SKIP_COMP += centaur/bridge/top.$(ACL2_COMP_EXT)

# Has readtime conditionals #+cmucl and #-cmucl:
BOOKS_SKIP_COMP += std/io/read-string-tests.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += tools/oracle-time-tests.$(ACL2_COMP_EXT)

# CLISP says: "Lisp stack overflow":
BOOKS_SKIP_COMP += workshops/2006/rager/support/ptest-mergesort.$(ACL2_COMP_EXT)

# GCL says: "Condition in IF [or a callee]: INTERNAL-SIMPLE-ERROR:
# Invocation history stack overflow."  Other Lisps had trouble too.
BOOKS_SKIP_COMP += system/hons-check/memoize-tests.$(ACL2_COMP_EXT)

# In Makefile-comp, bdd/benchmarks.$(ACL2_COMP_EXT) may depend on
# bdd/benchmarks.lisp, but we don't want to make either, so we do this
# explicitly:
BOOKS_SKIP_COMP += bdd/benchmarks.$(ACL2_COMP_EXT)

# Seems to have been headed for a stack overflow due to (comp t) not
# being invoked when loading @expansion.lsp file.  Including parent
# book too (perhaps not necessary):
BOOKS_SKIP_COMP += system/optimize-check-aux.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += system/optimize-check.$(ACL2_COMP_EXT)

# The following is a problem for CMUCL (see comment in the .lisp
# file), so for simplicity (actually, uniformity), we skip compilation
# in all Lisps for this book.
BOOKS_SKIP_COMP += demos/modeling/nested-stobj-toy-isa.$(ACL2_COMP_EXT)

# This book has a make-event guarded by #+Clozure, which might explain
# why compilation failed failed for Allegro CL.
BOOKS_SKIP_COMP += tools/oracle-timelimit-tests.$(ACL2_COMP_EXT)

# The following book cannot be included without what appears to be
# some sort of infinite loop.  The ones below it depend on that book.
BOOKS_SKIP_COMP += hacking/evalable-ld-printing.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += acl2s/mode-acl2s-dependencies.$(ACL2_COMP_EXT)

# When certification with CCL generates file top@expansion.lsp, that
# expansion file unconditionally loads the CCL-only file
# bridge-raw.lsp.  We thus seem to need to disqualify both of the
# following books.
BOOKS_SKIP_COMP += centaur/bridge/top.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += doc/top.$(ACL2_COMP_EXT)

# Stack overflow in GCL, Allegro CL, and LispWorks:
BOOKS_SKIP_COMP += system/tests/apply-timings.$(ACL2_COMP_EXT)

# Errors (using LispWorks) involve quicklisp, so I won't bother to debug:
BOOKS_SKIP_COMP += oslib/tests/ls.$(ACL2_COMP_EXT)
BOOKS_SKIP_COMP += oslib/tests/mkdir.$(ACL2_COMP_EXT)

# Has readtime conditionals for different Lisps:
BOOKS_SKIP_COMP += system/tests/stobj-issues.$(ACL2_COMP_EXT)

# GCL couldn't handle this one (tested 4/10/2020), saying "[GC Hole
# overrun]" and then "Unrecoverable error: Segmentation violation.."
# It's not clear why, but it doesn't seem important to figure it out.
BOOKS_SKIP_COMP += workshops/2011/verbeek-schmaltz/sources/invariants2.$(ACL2_COMP_EXT)

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

# Warning: ACL2's GNUmakefile uses the "regression" target of this
# Makefile to implement its target, "regression".  So please be
# careful about making major changes to "regression" in this Makefile.

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

regression: $(filter-out $(SLOW_BOOKS), $(OK_CERTS))

# Starting 8/15/2014, regression-everything does not automatically set
# USE_QUICKLISP=1, even in the HONS case.  In particular, "make
# regression-everything" no longer makes doc/manual/; for that, specify
# USE_QUICKLISP=1.  Update as of 7/30/2020: I think USE_QUICKLISP=1 is now the
# default, so we should probably remove this comment and the couple sentences
# before it.
.PHONY: regression-everything

regression-everything: $(OK_CERTS)

.PHONY: all

all: regression-everything

# The critical path report will work only if you have set up certificate timing
# BEFORE you build the books.  See ./critpath.pl --help for details.

# BOZO I probably broke this, we shouldn't use --targets, we should use ok_certs...
critpath.txt: $(OK_CERTS)
	echo "Building critpath.txt..."
	time $(BUILD_DIR)/critpath.pl -m 2 --targets $(BUILD_DIR)/Makefile-books > critpath.txt


# Targets for building whole directories of books.

# basic is the default set of books to build:
.PHONY: basic
basic: arithmetic arithmetic-3 arithmetic-5 ihs std xdoc tools misc data-structures apply

.PHONY: acl2s
acl2s: $(filter acl2s/%, $(OK_CERTS))

.PHONY: add-ons
add-ons: $(filter add-ons/%, $(OK_CERTS))

.PHONY: apply
apply: projects/apply/top.cert

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

.PHONY: centaur
centaur: $(filter centaur/%, $(OK_CERTS))

.PHONY: clause-processors
clause-processors: $(filter clause-processors/%, $(OK_CERTS))

.PHONY: coi
coi: $(filter coi/%, $(OK_CERTS))

.PHONY: cowles
cowles: $(filter cowles/%, $(OK_CERTS))

.PHONY: data-structures
data-structures: $(filter-out data-structures/memories/%, $(filter data-structures/%, $(OK_CERTS)))

.PHONY: defexec
defexec: $(filter defexec/%, $(OK_CERTS))

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

.PHONY: kestrel
kestrel: $(filter kestrel/%, $(OK_CERTS))

.PHONY: make-event
make-event: $(filter make-event/%, $(OK_CERTS))

.PHONY: meta
meta: $(filter meta/%, $(OK_CERTS))

.PHONY: misc
misc: $(filter-out misc/misc2/%, $(filter misc/%, $(OK_CERTS)))

.PHONY: models
models: $(filter models/%, $(OK_CERTS))

.PHONY: nonstd
nonstd: $(filter nonstd/%, $(OK_CERTS))

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
xdoc: $(filter-out xdoc/tests/%, $(filter xdoc/%, $(OK_CERTS)))

.PHONY: smtlink
smtlink: $(filter workshops/2015/peng-greenstreet/%, $(OK_CERTS))


.PHONY: workshops \
        workshop1999 workshop2000 workshop2001 workshop2002 \
        workshop2003 workshop2004 workshop2006 workshop2007 \
        workshop2009 workshop2011 workshop2013 workshop2014 \
        workshop2015 workshop2017 workshop2018

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
workshop2014: $(filter workshops/2014/%, $(OK_CERTS))
workshop2015: $(filter workshops/2015/%, $(OK_CERTS))
workshop2017: $(filter workshops/2017/%, $(OK_CERTS))
workshop2018: $(filter workshops/2018/%, $(OK_CERTS))


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
               std/strings/top.cert \
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

# The following dummy target does nothing, e.g., so that you can test
# the dependency scanning stuff without actually building anything.
.PHONY: dummy
dummy:
	@echo "Making dummy -- nothing to do."

# We now provide a way (adapted from the old Makefile-generic) for
# developers to be able to check well-formedness of the ACL2 world
# after including each book.  Note that we skip two problematic
# directories for world-checking, hacking/ and
# workshops/2007/dillinger-et-al/code/.  The problem seems likely to
# be that in many of the books in these two directories, the first bad
# triple is a GLOBAL-VALUE for either the unknown property
# EXTEND-PROGN! or RETRACT-PROGN!, or else is an unbinding of the
# PREDEFINED property for PROGN! (indicating a use of :REDEF);
# presumably these books mess with raw mode.  Since we have had such
# problems with acl2s/ccg/ccg.lisp (presumably because it includes
# hacking/hacker), and acl2s/doc.lisp, we exclude all books under
# acl2s/ as well as doc/top.lisp and doc/top-fast.lisp.  Finally, we
# exclude books in books/build/test/, since some have caused problems;
# there's nothing of interest in those books from a world perspective,
# so it's not worth figuring out the problem.

BOOKS_BKCHK_OUT := $(patsubst %.cert,%.bkchk.out,$(OK_CERTS))
BOOKS_BKCHK_OUT := $(filter-out $(SLOW_BOOKS), $(BOOKS_BKCHK_OUT))
BOOKS_BKCHK_OUT := $(filter-out hacking/%, $(BOOKS_BKCHK_OUT))
BOOKS_BKCHK_OUT := $(filter-out workshops/2007/dillinger-et-al/code/%, $(BOOKS_BKCHK_OUT))
BOOKS_BKCHK_OUT := $(filter-out acl2s/%, $(BOOKS_BKCHK_OUT))
BOOKS_BKCHK_OUT := $(filter-out doc/top.bkchk.out, $(BOOKS_BKCHK_OUT))
BOOKS_BKCHK_OUT := $(filter-out doc/top-slow.bkchk.out, $(BOOKS_BKCHK_OUT))
BOOKS_BKCHK_OUT := $(filter-out build/test/%, $(BOOKS_BKCHK_OUT))
# Uses redefinition:
BOOKS_BKCHK_OUT := $(filter-out system/tests/cert-data/redef.bkchk.out, $(BOOKS_BKCHK_OUT))
# Includes the redef book just above:
BOOKS_BKCHK_OUT := $(filter-out system/tests/cert-data/top.bkchk.out, $(BOOKS_BKCHK_OUT))
# Name conflict for "INSTANCE" package between instance.lisp and
# (included in system/pseudo-good-worldp.lisp) system book
# std/portcullis.lisp:
BOOKS_BKCHK_OUT := $(filter-out workshops/2004/davis/support/%, $(BOOKS_BKCHK_OUT))

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

# There was one .cert file from the legacy run that was not from
# the new run, as follows, and it is 0-length file that was
# written by its directory's Makefile in order to avoid
# certification of this slow book.  That avoidance is handled
# differently by the new books/Makefile, without creating a .cert
# file.

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

.PHONY: vl vl2014 vl_linttest sv_failtest sv_cosims vlfull

vl2014: centaur/vl2014/bin/vl2014

vl: centaur/vl/bin/vl \
    centaur/sv/cosims/cosim-core

# We don't make the sv cosims as part of "vl", because it requires commercial
# Verilog simulators that many ACL2 users may not have.

vlfull: vl sv_cosims vl_linttest sv_failtest


centaur/vl2014/bin/vl2014: centaur/vl2014/kit/top.cert
	@echo "Making VL Verilog Toolkit, 2014 Edition"
	@cd centaur/vl2014/kit; ACL2_CUSTOMIZATION=NONE $(STARTJOB) -c "$(ACL2) < save.lsp &> save.out"
	@ls -la centaur/vl2014/bin/vl2014

centaur/vl/bin/vl: centaur/vl/kit/top.cert
	@echo "Making VL Verilog Toolkit"
	@cd centaur/vl/kit; ACL2_CUSTOMIZATION=NONE $(STARTJOB) -c "$(ACL2) < save.lsp &> save.out"
	@ls -la centaur/vl/bin/vl

centaur/sv/cosims/cosim-core: centaur/sv/cosims/cosims.cert centaur/sv/cosims/make-cosim.lsp
	@echo "Making SV Cosims Tester"
	@cd centaur/sv/cosims; $(MAKE) cosim-core
	@ls -la centaur/sv/cosims/cosim-core

vl_linttest : centaur/vl/bin/vl
	@echo "Making VL linttests"
	@cd centaur/vl/linttest; $(MAKE)

sv_failtest : centaur/sv/cosims/cosim-core
	@echo "Making SV failtests"
	@cd centaur/sv/failtest; $(MAKE) passing

sv_cosims : centaur/sv/cosims/cosim-core
	@echo "Making SV cosim tests"
	@echo "NOTE: This will fail unless you have commercial simulators ncverilog and vcs in your path!"
	@cd centaur/sv/cosims; $(MAKE) passing


.PHONY: clean_vl
clean_vl:
	@echo "Cleaning centaur/vl/bin directory"
	@rm -f centaur/vl/bin/*
	@echo "Cleaning centaur/vl2014/bin directory"
	@rm -f centaur/vl2014/bin/*

clean: clean_vl



# Getopt Demo

centaur/getopt/demo2: centaur/getopt/demo2.cert
	@echo "Making getopt demo executable"
	@cd centaur/getopt; \
	 ACL2_CUSTOMIZATION=NONE $(STARTJOB) -c "$(ACL2) < demo2-save.lsp &> demo2-save.out"
	@ls -l centaur/getopt/demo2

centaur/getopt/demo2-test.ok: centaur/getopt/demo2 \
                              centaur/getopt/demo2-test.pl
	@echo "Testing getopt demo executable"
	@cd centaur/getopt; \
         $(STARTJOB) -c "./demo2-test.pl &> demo2-test.out"
	@cd centaur/getopt; cp demo2-test.out demo2-test.ok
	@ls -l centaur/getopt/demo2-test.ok

regression: centaur/getopt/demo2-test.ok



##############################
### Section: Tags
##############################

# These regular expressions may include things more appropriate for
# raw Lisp.  May want to remove some of these or extend them to
# support new types of definitions.
ETAGS=etags --language=none \
  --regex='/ *set[ \t]?\([^ =]*\)[ \n]*=/\1/i' \
  --regex='/(set[^ \t]*[ \t]?\([^ ]*\)[ \t]*/\2/i' \
  --regex='/ *(memoize[ \t]+\([^ \t\)]*\)[ \t\)]/\1/i' \
  --regex='/ *(\(def[^t]\|deft[^h]\|defth[^m]\)[^ \t]*[ \t]?\([^ ]*\)[ \t]*/\2/i'

TAGS : $(CERT_PL_SOURCES)
	@echo "Making TAGS"
	@rm -f TAGS
	cat $(BUILD_DIR)/Makefile-sources | tr '\n' '\0' | xargs -0 -n 100 $(ETAGS) -a


##############################
### Section: Git Status
##############################
# This is helpful for checking whether you have any new source files
# that need to be added before your commit -- candidates are things
# that show up under "Untracked files".
git_status:
	git ls-files -c | egrep '\.lisp$$' > $(BUILD_DIR)/git_lisp_sources
	$(BUILD_DIR)/cert.pl --quiet --no-build \
                      --cache $(BUILD_DIR)/Makefile-cache \
                      --acl2-books `pwd` \
                      --write-sources $(BUILD_DIR)/git_source_deps \
                      --write-otherdeps $(BUILD_DIR)/git_other_deps \
                      --targets $(BUILD_DIR)/git_lisp_sources
	cat $(BUILD_DIR)/git_source_deps $(BUILD_DIR)/git_other_deps | tr '\n' '\0' | xargs -0 git status -u --


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
#
# In 2019/2020, David Rager <ragerdl@defthm.com>, with support from the
# community, changed the "all" target so that it really builds all of the
# (non-broken) books.  He also reworked the logic for the "slow book" mechanism,
# and created a target for contibutors to use when making pull requests/pushes
# to the ACL2 community github.




# BOZO --- the comments below should eventually be integrated into the XDOC
# documentation about cert.pl.

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
#   - See :DOC books-certification for documentation of the cert_param
#     comment, which can be used to restrict which books are to be
#     certified.
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
