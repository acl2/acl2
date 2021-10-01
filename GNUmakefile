# ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
# Copyright (C) 2021, Regents of the University of Texas

# This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
# (C) 1997 Computational Logic, Inc.  See the documentation topic NOTES-2-0.

# This program is free software; you can redistribute it and/or modify
# it under the terms of the LICENSE file distributed with ACL2.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# LICENSE for more details.

# Written by:  Matt Kaufmann                  and J Strother Moore
# email:       Kaufmann@cs.utexas.edu         and Moore@cs.utexas.edu
# Department of Computer Science
# University of Texas at Austin
# Austin, TX 78712 U.S.A.

#  Example invocations for users:

#   make             ; Same as make all
#   make all         ; Same as make large, but also makes TAGS-acl2-doc if
#                    ;   TAGS_ACL2_DOC is non-empty and not SKIP.  Most output
#                    ;   goes to file make.log (customizable with
#                    ;   ACL2_MAKE_LOG), including output from both large and
#                    ;   TAGS-acl2-doc.
#   make large       ; Build ${PREFIXsaved_acl2} from scratch.  Most output
#                    ;   goes to file make.log (customizable with
#                    ;   ACL2_MAKE_LOG).
#   make TAGS-acl2-doc ; Build tags-table for books (used by acl2-doc browser)
#   make clean       ; Remove all generated files in top-level directory and doc/
#   make clean-all   ; Same as above
#   make distclean   ; Same as above
#   make clean-lite  ; Same as clean-all, except do not delete *saved_acl2*
#                    ; or doc.lisp.backup
#   make update      ; Same as make large, except that if the desired
#                    ; executable is up-to-date with respect to the
#                    ; ACL2 sources, then do nothing.  See warning
#                    ; next to `update' target, below.
#   make LISP=cl PREFIX=allegro-
#   make TAGS        ; Create tags table, handy for viewing sources with emacs.
#   make TAGS!       ; Same as TAGS, except forces a rebuild of TAGS.
#   make regression
#                    ; Certify most community books.
#   make regression ACL2=xxx
#                    ; Same as make regression, but use xxx as ACL2, which
#                    ; should either be an absolute filename or a command on
#                    ; one's path.
#   make regression ACL2_CUSTOMIZATION=xxx
#                    ; Same as make regression, but use xxx as the
#                    ; ACL2 customization file (see :DOC acl2-customization).
#                    ; In particular, this is useful for certifying
#                    ; the books in the regression suite using
#                    ; waterfall parallelism (requires the
#                    ; experimental extension ACL2(p) of ACL2); see
#                    ; file acl2-customization-files/README.
#   make regression-everything
#                    ; Same as make regression-everything in books/Makefile;
#                    ; certifies more than the regression target.
#   make clean-books ; Remove certificate files, object files, log files,
#                    ; debris, ..., created by `make basic',
#                    ; `make regression', etc.

###############################################################################

#  NOTE:  Perhaps only implementors should read below.
#  Example invocations for implementors:

#   NOTE:  Make completely recompiles, initializes and saves.

#   make full      ; A complete recompilation whether needed or not.
#   make full init ; Completely recompile, initialize and save.
#   make full-meter init  ; Completely recompile with meters, init and save.
#   make init      ; Just build full-size ${PREFIXsaved_acl2}.
#   make check-sum ; Call only after ACL2 is completely compiled.
#   make full LISP=lucid PREFIX=lucid-  ; makes acl2 in Lucid
#   make full LISP=cl PREFIX=allegro- ; makes acl2 in allegro
#   make full LISP=lispworks PREFIX=lispworks- ; makes acl2 in lispworks
#   make copy-distribution DIR=/stage/ftp/pub/moore/acl2/v2-9/acl2-sources
#                  ; copies all of acl2 plus books, doc, etc., to the named
#                  ; directory, as for compiling on another architecture or
#                  ; moving to the ftp site.
#                  ; Precondition:
#                  ;     The named directory must not already exist; if it
#                  ;     does, a harmless error is caused.
#   make DOC       ; Build xdoc manual and rebuild source file doc.lisp
#   make clean-doc ; Remove files created by make DOC
#   make proofs    ; Assuming sources are compiled, initialize without skipping
#                  ; proofs during pass 2.  Does not save an image.  Uses same
#                  ; flags used to build full-size image.

#  Metering: If the currently compiled version is unmetered and you
#  wish it metered, the fastest thing to do is to (push :acl2-metering
#  *features*) and then yank in and recompile just those definitions
#  that mention acl2-metering.  However, if you would like to install
#  metering as part of a system-wide recompilation, use the full-meter
#  option below.  If you want to get rid of the metering in the
#  compiled code, do make full.

###############################################################################

# Avoid loading the ACL2 customization file.  This is already done by
# the books build system; however we need this for "make DOC" and
# perhaps other targets.
export ACL2_CUSTOMIZATION ?= NONE

# Log file for builds
export ACL2_MAKE_LOG ?= make.log

# Avoid escape characters in regression log:
export CERT_PL_NO_COLOR ?= t

# Always make it possible to gather timing statistics after a regression.
export TIME_CERT = yes

LISP = ccl
DIR = /tmp

# The following is intended to provide the current working directory
# on Cygwin/Windows.
ifneq (,$(findstring CYGWIN, $(shell uname)))
ACL2_WD := $(shell cygpath -m `pwd`)
else
ACL2_WD := $(shell pwd)
endif

# The build of saved_acl2 may succeed even if the directory name has
# spaces, but book certification will almost surely fail, so we
# disallow such a build.  Comment out the three lines below if you
# want to take your chances nonetheless!
ifneq (,$(word 2, $(ACL2_WD)))
$(error Illegal ACL2 build directory (contains a space): $(ACL2_WD)/)
endif

# The variable ACL2_REAL should be defined for the non-standard
# version and not for the standard version.  Non-standard ACL2 images
# will include the suffix "r", for example saved_acl2r rather than
# saved_acl2.  Variables ACL2_PAR, ACL2_DEVEL, and ACL2_WAG (for
# feature write-arithmetic-goals) are similar (with suffixes p, d, and
# w, resp., rather than r), but for versions that respectively are
# parallel or (for implementors only) have features :acl2-devel or
# :write-arithmetic-goals, for special builds pertaining to
# guard-verified functions or writing out arithmetic lemma data to
# ~/write-arithmetic-goals.lisp.

# DO NOT EDIT ACL2_SUFFIX!  Edit the above-mentioned four variables instead.

ACL2_SUFFIX :=
ifdef ACL2_PAR
	ACL2_SUFFIX := $(ACL2_SUFFIX)p
endif
ifdef ACL2_WAG
	ACL2_SUFFIX := $(ACL2_SUFFIX)w
endif
ifdef ACL2_DEVEL
	ACL2_SUFFIX := $(ACL2_SUFFIX)d
endif
ifdef ACL2_REAL
	ACL2_SUFFIX := $(ACL2_SUFFIX)r
endif

# The user may define PREFIX; otherwise it is implicitly the empty string.
PREFIX :=

PREFIXsaved_acl2 := ${PREFIX}saved_acl2${ACL2_SUFFIX}
PREFIXosaved_acl2 := ${PREFIX}osaved_acl2${ACL2_SUFFIX}

ACL2 ?= $(ACL2_WD)/${PREFIXsaved_acl2}

# One may define ACL2_SAFETY and/or (only useful for CCL) ACL2_STACK_ACCESS
# to provide a safety or :stack-access setting.  We recommend
# ACL2_SAFETY = 3
# for careful error checking.  This can cause significant slowdown and for
# some Lisp implementations, the regression might not even complete.  For
# CCL we have had success with safety 3.
# NOTE: The use of ACL2_STACK_ACCESS relies on recognition by CCL of the
# :stack-access keyword for optimize expressions, hence will only have
# effect for CCL versions starting with 16678.
ACL2_SAFETY =
ACL2_STACK_ACCESS =

# Set ACL2_COMPILER_DISABLED, say with ACL2_COMPILER_DISABLED=t, to
# build the image with (SET-COMPILER-ENABLED NIL STATE), thus
# disabling use of the compiler for certify-book and include-book; see
# :DOC compilation.  This is generally not necessary, but for the use
# of some books employing raw Lisp code it could, on rare occasion, be
# useful; and for SBCL and CCL (as of this writing, May 2010),
# reasonably harmless other than to lose a bit of speed when including
# books with many complex defun forms.
ACL2_COMPILER_DISABLED =

# See *acl2-egc-on* for an explanation of the following variable.
ACL2_EGC_ON =

# The following supplies a value for *acl2-exit-lisp-hook*, which
# should be a symbol in the "COMMON-LISP-USER" package.  For example,
# for CCL consider:
# make ACL2_EXIT_LISP_HOOK='acl2-exit-lisp-ccl-report'.
ACL2_EXIT_LISP_HOOK =

# The following is not advertised.  It allows more symbol allocation
# when ACL2 package is created; if specified, its value should be a
# number to supply for the :size argument of defpackage.  For example,
# 3000000 has been found a useful such value for a use of the HONS
# version of ACL2 built on CCL on a 64-bit machine.
ACL2_SIZE =

# The following causes the calls of make that use it to continue past
# errors.  Delete -k if you want to stop at first error and return
# non-zero exit status in that case; or, instead of editing the line
# below, supply ACL2_IGNORE='' on the make command line.  Formerly we
# used -i; if you prefer that, use ACL2_IGNORE=-i on the command line.
# Note however that the GNU make manual
# (http://www.gnu.org/software/make/manual/make.html, May 2013) says
# that -i is "obsolete".
ACL2_IGNORE ?= -k

# The order of the files below is unimportant.
# NOTE: We deliberately exclude doc.lisp, which does not contribute to
# proclaiming or TAGS.
sources := axioms.lisp memoize.lisp hons.lisp\
           boot-strap-pass-2-a.lisp boot-strap-pass-2-b.lisp\
           basis-a.lisp basis-b.lisp parallel.lisp translate.lisp\
           type-set-a.lisp linear-a.lisp\
           type-set-b.lisp linear-b.lisp\
           non-linear.lisp tau.lisp\
           rewrite.lisp simplify.lisp bdd.lisp\
           other-processes.lisp induct.lisp prove.lisp\
           proof-builder-a.lisp history-management.lisp defuns.lisp\
           defthm.lisp other-events.lisp ld.lisp proof-builder-b.lisp\
           proof-builder-pkg.lisp apply-raw.lisp interface-raw.lisp\
           serialize.lisp serialize-raw.lisp\
           defpkgs.lisp\
           apply-prim.lisp apply-constraints.lisp apply.lisp

sources := $(sources) hons-raw.lisp memoize-raw.lisp

ifdef ACL2_PAR
	sources := $(sources) multi-threading-raw.lisp parallel-raw.lisp futures-raw.lisp
endif
# No change to sources for ACL2_DEVEL or ACL2_WAG

sources_extra := GNUmakefile acl2-characters doc.lisp \
	         acl2.lisp acl2-check.lisp acl2-fns.lisp acl2-init.lisp \
	         akcl-acl2-trace.lisp allegro-acl2-trace.lisp openmcl-acl2-trace.lisp

ACL2_DEPS := $(sources) $(sources_extra)

# Top (default) target:
.PHONY: all
all: large
ifneq ($(TAGS_ACL2_DOC),)
ifneq ($(TAGS_ACL2_DOC),SKIP)
ifeq ($(ACL2_MAKE_LOG),NONE)
	@$(MAKE) TAGS-acl2-doc
else
	@echo -n Making TAGS-acl2-doc...
	@$(MAKE) TAGS-acl2-doc >> "$(ACL2_MAKE_LOG)" 2>&1 || (echo "\nERROR: See $(ACL2_MAKE_LOG)." ; exit 1)
	@echo " done."
endif
endif
endif

# The following target is intended only for when $(ACL2_MAKE_LOG) is
# not NONE.
.PHONY: set-up-log
set-up-log:
	@if [ -f "$(ACL2_MAKE_LOG)".bak ] ; then \
	rm -f "$(ACL2_MAKE_LOG)".bak ; \
	fi
	@if [ -f "$(ACL2_MAKE_LOG)" ] ; then \
	cp -p "$(ACL2_MAKE_LOG)" "$(ACL2_MAKE_LOG)".bak ; \
	fi
	@echo "Preparing to build ${PREFIXsaved_acl2} (log file $(ACL2_MAKE_LOG))."
	@if [ -f "$(ACL2_MAKE_LOG)" ] && [ "`(tail -1 "$(ACL2_MAKE_LOG)" 2>&1)`" = "Preparing to build ${PREFIXsaved_acl2} (log file $(ACL2_MAKE_LOG))." ]; then \
	echo "" ;\
	>&2 echo '** ABORTING: Shell output has been redirected to the file' $(ACL2_MAKE_LOG) . ;\
	>&2 echo '             But this is illegal, because this "make" invocation' ;\
	>&2 echo '             is already directing its output to that same file.' ;\
	>&2 echo '             To change where this "make" invocation directs its output,' ;\
	>&2 echo '             you may set "make" variable ACL2_MAKE_LOG to that desired' ;\
	>&2 echo '             filename, but you are advised to consider simply avoiding' ;\
	>&2 echo '             the redirection of shell output to $(ACL2_MAKE_LOG).' ;\
	exit 1 ;\
	fi

# Build tags table for acl2-doc, with ACL2 topics first.
TAGS-acl2-doc: $(ACL2_DEPS)
	rm -f TAGS-acl2-doc
	etags *.lisp -o TAGS-acl2-doc
	find books -name '*.lisp' -print | (time xargs etags -o TAGS-acl2-doc --append)

.PHONY: acl2r
acl2r:
	@rm -f acl2r.lisp
	@$(MAKE) --no-print-directory acl2r.lisp

acl2r.lisp:
# The various "startup" code below can be loaded as a first step in
# building ACL2.  The first is actually always done in modern ACL2 builds.
	@echo "" > $@
	@if [ "$(ACL2_COMPILER_DISABLED)" != "" ] ; then \
	echo '(DEFPARAMETER *ACL2-COMPILER-ENABLED* NIL)' >> $@ ;\
	fi
	@if [ "$(ACL2_EGC_ON)" != "" ] ; then \
	echo '(DEFPARAMETER *ACL2-EGC-ON* $(ACL2_EGC_ON))' >> $@ ;\
	fi
# The next startup is something for developers only.  It is useful
# from time to time to check the arrangement that certain source
# functions come up as guard-verified.  See :DOC
# verify-guards-for-system-functions.
	@if [ "$(ACL2_DEVEL)" != "" ] ; then \
	echo '(or (member :acl2-devel *features*) (push :acl2-devel *features*))' >> $@ ;\
	fi
# WARNING: The next two startups are for building ACL2(p) and ACL2(r),
# respectively.
	@if [ "$(ACL2_PAR)" != "" ] ; then \
	echo '(or (member :acl2-par *features*) (push :acl2-par *features*))' >> $@ ;\
	fi
	@if [ "$(ACL2_REAL)" != "" ] ; then \
	echo '(or (member :non-standard-analysis *features*) (push :non-standard-analysis *features*))' >> $@ ;\
	fi
# WARNING: The startups below should be used with care.  Don't use
# them unless you know what you are doing!  They are not officially
# supported.
	@if [ "$(ACL2_WAG)" != "" ] ; then \
	mv -f ~/write-arithmetic-goals.lisp.old ; \
	mv -f ~/write-arithmetic-goals.lisp ~/write-arithmetic-goals.lisp.old ; \
	echo '(or (member :write-arithmetic-goals *features*) (push :write-arithmetic-goals *features*))' >> $@ ;\
	fi
	@if [ "$(ACL2_SAFETY)" != "" ] ; then \
	echo "(defparameter *acl2-safety* $(ACL2_SAFETY))" >> $@ ;\
	fi
	@if [ "$(ACL2_STACK_ACCESS)" != "" ] ; then \
	echo "(defparameter *acl2-stack-access* $(ACL2_STACK_ACCESS))" >> $@ ;\
	fi
	@if [ "$(ACL2_SIZE)" != "" ] ; then \
	echo '(or (find-package "ACL2") (#+(and gcl (not ansi-cl)) defpackage:defpackage #-(and gcl (not ansi-cl)) defpackage "ACL2" (:size $(ACL2_SIZE)) (:use)))' >> $@ ;\
	fi
	@if [ "$(ACL2_EXIT_LISP_HOOK)" != "" ] ; then \
	echo '(DEFPARAMETER *ACL2-EXIT-LISP-HOOK* (QUOTE $(ACL2_EXIT_LISP_HOOK)))' >> $@ ;\
	fi
# WARNING: The startup below should be used with even more care than
# those warned about above, since it allows you to put anything you
# like into acl2r.lisp, whether reasonable or not!  Example:
#   make ACL2_STARTUP_EXTRA='(push :acl2-save-unnormalized-bodies *features*)'
	@if [ "$(ACL2_STARTUP_EXTRA)" != "" ] ; then \
	echo '$(ACL2_STARTUP_EXTRA)' >> $@ ;\
	fi

.PHONY: chmod_image
chmod_image:
	if [ -f ${PREFIXsaved_acl2} ]; then \
	chmod 775 ${PREFIXsaved_acl2} ;\
	fi

.PHONY: do_saved
# Note: We removed line "chmod g+s saved" before the second chmod below, as it
# was causing errors in at least one environment, and instead did final chmod
# to 666 instead of 664 in case files in saved/ wind up in an unexpected group.
do_saved:
	rm -fr saved
	mkdir saved
	chmod 775 saved
	cp *.lisp acl2-characters GNUmakefile saved/
	chmod 666 saved/*

# Keep the use of :COMPILED/:COMPILE-SKIPPED below in sync with ACL2
# source function note-compile-ok.
.PHONY: check_compile_ok
check_compile_ok:
	@if [ ! -f acl2-status.txt ] ; then \
	echo 'Compile FAILED: file acl2-status.txt is missing.' ; \
	exit 1 ; \
	fi
	@if [ `cat acl2-status.txt` != :COMPILED ] && [ `cat acl2-status.txt` != :COMPILE-SKIPPED ] ; then \
	echo 'Compile FAILED: acl2-status.txt should contain :COMPILED or (for some Lisps) :COMPILE-SKIPPED.' ; \
	exit 1 ; \
	fi

# Keep the use of :INITIALIZED below in sync with ACL2 source function
# initialize-acl2.
.PHONY: check_init_ok
check_init_ok:
	@if [ ! -f acl2-status.txt ] ; then \
	echo 'Initialization FAILED: file acl2-status.txt is missing.' ; \
	exit 1 ; \
	fi
	@if [ `cat acl2-status.txt` != :INITIALIZED ] ; then \
	echo 'Initialization FAILED: acl2-status.txt should contain :INITIALIZED.' ; \
	exit 1 ; \
	fi
	@echo "Initialization SUCCEEDED."

# The following target should only be used when the compiled files are
# ready to use and, if needed, so is acl2-proclaims.lisp.
.PHONY: compile-ok
compile-ok:
	date
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::note-compile-ok)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	rm -f workxxx

.PHONY: check-sum
check-sum:
	date
	rm -f workxxx
	echo '(load "init.lisp") (acl2)' > workxxx
	echo '(acl2::make-check-sum-file)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	rm -f workxxx

.PHONY: full
full: TAGS
	$(MAKE) compile
	rm -f acl2-proclaims.lisp
# The following two forms should do nothing, and quickly, if
# *do-proclaims* is nil.
	$(MAKE) acl2-proclaims.lisp
	$(MAKE) compile USE_ACL2_PROCLAIMS=t

.PHONY: compile
compile:
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::compile-acl2 $(USE_ACL2_PROCLAIMS))' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	@$(MAKE) check_compile_ok

.PHONY: copy-distribution
copy-distribution: acl2r.lisp
# WARNING: Execute this from an ACL2 source directory.
# You must manually rm -r ${DIR} before this or it will fail without doing
# any damage.
# Note that below, /projects/acl2/ is not used, because this directory must
# match what lisp returns from truename.
	rm -f workxxx
	rm -f workyyy
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::copy-distribution "workyyy" "${CURDIR}" "${DIR}")' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	chmod 777 workyyy
	./workyyy
	rm -f workxxx
	rm -f workyyy

# You can replace the block of code below if etags doesn't exist on your system, by
# removing "#" on the two lines just below and commenting out the block below
# them.  However, since Lisp function make-tags deals with this issue, such a
# change is probably not necessary.
#TAGS:
#	@echo 'Skipping building of a tags table.'

# We build acl2r.lisp so that we build ACL2(h) and not ACL2(c), for example.
TAGS:   $(ACL2_DEPS)
	$(MAKE) acl2r
	rm -f TAGS
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::make-tags)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	rm -f workxxx
	if [ -f TAGS ] ; then chmod 644 TAGS ; fi

# THE FOLLOWING TARGET IS DEPRECATED, since TAGS now depends on $(ACL2_DEPS).
# The following remakes TAGS even if TAGS is up to date.  This target can be
# useful when building a parallel version after a normal version, or
# vice-versa.
.PHONY: TAGS!
TAGS!:  acl2r
	rm -f TAGS
	$(MAKE) TAGS

.PHONY: move-to-old
move-to-old:
	if [ -f ${PREFIXsaved_acl2} ] && [ -f ${PREFIXsaved_acl2}.${LISPEXT} ]; then \
	echo "Moving " ${PREFIXsaved_acl2}.${LISPEXT} " to ${PREFIXosaved_acl2}.${LISPEXT}"; \
	mv -f ${PREFIXsaved_acl2}.${LISPEXT} ${PREFIXosaved_acl2}.${LISPEXT}; \
	cat ${PREFIXsaved_acl2} | sed -e 's/saved_acl2${ACL2_SUFFIX}.${LISPEXT}$$/osaved_acl2${ACL2_SUFFIX}.${LISPEXT}/' > ${PREFIXosaved_acl2} ;\
	chmod 775 ${PREFIXosaved_acl2} ;\
	rm -f ${PREFIXsaved_acl2} ; fi

.PHONY: move-new
move-new:
	if [ -f nsaved_acl2.${LISPEXT} ]; then \
	mv -f nsaved_acl2.${LISPEXT} ${PREFIXsaved_acl2}.${LISPEXT} ; fi

# See the Essay on Proclaiming in source file acl2-fns.lisp.
acl2-proclaims.lisp: ${sources}
	rm -f acl2-proclaims.lisp
	rm -f workxxx
	rm -f worklispext
	echo '(load "init.lisp")' > workxxx
	echo '(in-package "ACL2")' >> workxxx
	echo '(generate-acl2-proclaims)' >> workxxx
	echo '(exit-lisp)' >> workxxx
	${LISP} < workxxx
	[ -f acl2-proclaims.lisp ]

.PHONY: init
init: acl2-proclaims.lisp
# Note:  If you believe that compilation is up-to-date, do
# make compile-ok init
# rather than
# make init.
	rm -f workxxx
	rm -f worklispext
	echo -n "" >> ${PREFIXosaved_acl2}
	rm -f ${PREFIXosaved_acl2}
	echo '(load "init.lisp")' > workxxx
	echo '(in-package "ACL2")' >> workxxx
	echo '(save-acl2 (quote (initialize-acl2 (quote include-book))) "${PREFIXsaved_acl2}")' >> workxxx
	echo '(exit-lisp)' >> workxxx
	${LISP} < workxxx
	@$(MAKE) check_init_ok
# Move to old.
	if [ -f worklispext ]; then $(MAKE) move-to-old LISPEXT=`cat worklispext` ;\
	elif [ -f ${PREFIXsaved_acl2} ]; then \
	mv -f ${PREFIXsaved_acl2} ${PREFIXosaved_acl2} ;\
	else \
	touch ${PREFIXsaved_acl2} ;\
	mv -f ${PREFIXsaved_acl2} ${PREFIXosaved_acl2} ;\
	fi
# End of move to old.
# Move new into position.
	mv -f nsaved_acl2 ${PREFIXsaved_acl2}
#   For Allegro 5.0 and later and cmulisp, only:
	if [ -f worklispext ]; then $(MAKE) move-new LISPEXT=`cat worklispext` ; fi
# End of move new into position.
	rm -f worklispext
	rm -f workxxx
	$(MAKE) do_saved
	rm -f workxxx
	$(MAKE) chmod_image
	@echo "Successfully built $(ACL2_WD)/${PREFIXsaved_acl2}."

# The following "proofs" target assumes that files for the specified LISP have
# been compiled.  We use :load-acl2-proclaims nil so that we don't
# have to worry about perhaps having wiped out acl2-proclaims.lisp
# since the time we compiled for the given Lisp.
.PHONY: proofs
proofs: compile-ok
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::load-acl2 :load-acl2-proclaims nil)' >> workxxx
	echo '(acl2::initialize-acl2 nil)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	@$(MAKE) check_init_ok
	rm -f workxxx

.PHONY: DOC acl2-manual check-acl2-exports check-books

check-books:
	@if [ ! -d books ] ; then \
	echo "ERROR: The system books directory, books/, does not exist." ;\
	exit 1 ;\
	fi
	@echo ACL2_WD is $(ACL2_WD)
	@echo ACL2 is $(ACL2)
	@uname -a

# The next target, DOC, is the target that should generally be used
# for rebuilding the ACL2 User's Manual.
# WARNING: Sub-targets below have their own warnings!
# WARNING: This is unlikely to work with ACL2; use ACL2(h).
# WARNING: We suggest that you supply ACL2=, e.g., make DOC
# ACL2=/u/acl2/saved_acl2.  Otherwise parts of the build might use
# copies of ACL2 that surprise you.  (It seems awkward to pass
# ACL2 through recursive calls of make so we leave this to the
# user.)
# WARNING: even though this target may rebuild doc.lisp, that will not
# update the documentation for the :DOC command at the terminal, of
# course; for that, you'll need to rebuild ACL2.
DOC: acl2-manual STATS check-books
	cd books ; rm -f system/doc/render-doc.cert system/doc/rendered-doc.lsp
	rm -f doc/home-page.html
	$(MAKE) update-doc.lisp doc/home-page.html

check-acl2-exports: check-books
	cd books ; rm -f misc/check-acl2-exports.cert ; $(MAKE) ACL2=$(ACL2) misc/check-acl2-exports.cert

# We remove doc/HTML before rebuilding it, in order to make sure that
# it is up to date.  We could do that removal in doc/create-doc
# instead, but this way create-doc provides an interface that makes
# sense for most users, where the sources for the HTML/ files will not
# be changing.  Still, we expect that doc/HTML is the main way people
# will update the home page
# WARNING: This target might be up to date even if the manual is out
# of date with respect to books/system/doc/acl2-doc.lisp.  Consider
# using the DOC target instead.
doc/home-page.html: doc/home-page.lisp
	cd doc ; rm -rf HTML ; ./create-doc 2>&1 create-doc.out

# The following will implicitly use ACL2=acl2 unless ACL2 is set.
# Note that books/system/doc/acl2-manual.lisp ends in a call of
# xdoc::save that populates doc/manual/ (not under books/).
acl2-manual: check-books
	rm -rf doc/manual books/system/doc/acl2-manual.cert
	cd books ; $(MAKE) USE_QUICKLISP=1 system/doc/acl2-manual.cert
	rm -rf doc/manual/download/*

# WARNING: The dependency list just below isn't complete, since it
# doesn't consider what _those_ files depend on.
# WARNING: even though this target may rebuild doc.lisp, that will not
# update the documentation for the :DOC command at the terminal, of
# course; for that, you'll need to rebuild ACL2.
# NOTE: We copy books/system/doc/rendered-doc.lsp without -p so that
# doc.lisp will be newer than books/system/doc/acl2-doc.lisp, and
# hence doc.lisp won't later be rebuilt needlessly.
.PHONY: update-doc.lisp
update-doc.lisp: books/system/doc/acl2-doc.lisp books/system/doc/rendered-doc.lsp
	@diff doc.lisp books/system/doc/rendered-doc.lsp 2>&1 > /dev/null ; \
	  if [ $$? != 0 ] ; then \
	    mv -f doc.lisp doc.lisp.backup ; \
	    cp books/system/doc/rendered-doc.lsp doc.lisp ; \
	    echo "NOTE: doc.lisp has changed." ; \
	    echo "      If you use :DOC at the terminal, then" ; \
	    echo "      you might wish to rebuild your ACL2 executable." ; \
	  else \
	    echo "Note: doc.lisp is up-to-date." ; \
	  fi

# Note: The following target uses $(PREFIXsaved_acl2) -- but we don't
# care much about whether it's up-to-date in any sense, so we don't
# make the next target depend on $(PREFIXsaved_acl2).  This hasn't
# been super carefully thought out, so could change.
books/system/doc/rendered-doc.lsp: check-books
	rm -f books/system/doc/rendered-doc.lsp
	cd books ; $(MAKE) USE_QUICKLISP=1 system/doc/render-doc.cert ACL2=$(ACL2)

.PHONY: STATS

# See the Essay on Computing Code Size in the ACL2 source code.
STATS:
	@ACL2=$(ACL2) ;\
	export ACL2 ;\
	ACL2_SOURCES="$(sources)" ;\
	export ACL2_SOURCES ;\
	doc/create-acl2-code-size

.PHONY: clean-lite
clean-lite:
# Unlike clean-all, this does not remove executables or corresponding scripts
# (since there could be many executables that one prefers not to delete),
# except for *osaved_acl2* files.
	rm -f *.o *#* *.c *.h *.data gazonk.* workxxx* workyyy* *.lib \
	  *.fasl *.fas *.sparcf *.ufsl *.64ufasl *.ufasl *.dfsl *.dxl \
	  *.d64fsl *.dx64fsl *.lx64fsl \
	  *.lx32fsl *.x86f *.sse2f *.o *.fn \
	  TAGS TAGS-acl2-doc acl2-status.txt acl2r.lisp acl2-proclaims.lisp \
	  .acl2rc *osaved_acl2* *.log devel-check.out TMP*
	rm -rf saved
	rm -f doc/*.o doc/*#* doc/*.c doc/*.h doc/*.data doc/gazonk.* \
	   doc/workxxx doc/workyyy doc/*.lib \
	   doc/*.fasl doc/*.fas doc/*.sparcf doc/*.ufsl doc/*.64ufasl doc/*.ufasl doc/*.dfsl \
	   doc/*.dxl doc/*.d64fsl doc/*.dx64fsl doc/*.lx64fsl \
	   doc/*.lx32fsl doc/*.x86f doc/*.sse2f doc/*.o doc/*.fn \
	   doc/*.cert doc/*.port doc/*.out \
	   doc/*.log doc/TMP*
	rm -rf doc/TEX doc/HTML doc/EMACS

.PHONY: clean-all clean
clean clean-all: clean-lite
	rm -f *saved_acl2* doc.lisp.backup

# Inspired by https://www.gnu.org/prep/standards/html_node/Standard-Targets.html:
.PHONY: distclean
distclean: clean-all

# The .NOTPARALLEL target avoids our doing any build process in
# parallel.  Uses of makefiles in other directories, even if invoked
# from this makefile, can still take advantage of -j (as per the GNU
# make documentation).
.NOTPARALLEL:

# Warning: Be careful about adding quotes on "echo" commands below.
# Those don't seem to work well with the "-n" option in a Makefile on
# at least one Mac.
.PHONY: large
large: acl2r
ifeq ($(ACL2_MAKE_LOG),NONE)
	$(MAKE) full init
else
	@$(MAKE) --no-print-directory set-up-log
	@echo -n Compiling ...
	@echo "-*- Mode: auto-revert -*-" > "$(ACL2_MAKE_LOG)"
	@rm -f acl2-status.txt
	@$(MAKE) full >> "$(ACL2_MAKE_LOG)" 2>&1 || (echo "\nERROR: See $(ACL2_MAKE_LOG)." ; exit 1)
# The "incomplete" case below shouldn't happen (unless maybe upon aborting).
	@acl2_compile_status="`cat acl2-status.txt`" ;\
	if [ "$$acl2_compile_status" = :COMPILED ] ; then \
	echo " done." ;\
	elif [ "$$acl2_compile_status" = :COMPILE-SKIPPED ] ; then \
	echo " not performed for this host Lisp." ;\
	else \
	echo " incomplete." ;\
	exit 1 ;\
	fi
	@echo -n Bootstrapping, then saving executable \(may take a few minutes\) ...
	@$(MAKE) init >> "$(ACL2_MAKE_LOG)" 2>&1 || (echo "\n**ERROR**: See $(ACL2_MAKE_LOG)." ; exit 1)
	@echo " done."
	@echo "Successfully built $(ACL2_WD)/${PREFIXsaved_acl2}."
endif

# The following target should be used with care, since it fails to
# rebuild the desired executable when it already exists and is more
# recent than the sources.  For example, if you change Lisp
# implementations without changing PREFIX, perhaps even only changing
# the version of your Lisp, then use "make large", not "make update".
.PHONY: update
update: $(PREFIXsaved_acl2)

# Note: Below, the lines below "large" probably aren't needed, since
# these variables can only be set on the command line.  But we'll
# leave them in place for now.
$(PREFIXsaved_acl2): $(ACL2_DEPS)
	@$(MAKE) large \
	PREFIX=$(PREFIX) \
	LISP=$(LISP) \
	ACL2_SAFETY=$(ACL2_SAFETY) \
	ACL2_STACK_ACCESS=$(ACL2_STACK_ACCESS) \
	ACL2_COMPILER_DISABLED=$(ACL2_COMPILER_DISABLED) \
	ACL2_EGC_ON=$(ACL2_EGC_ON) \
	ACL2_EXIT_LISP_HOOK=$(ACL2_EXIT_LISP_HOOK) \
	ACL2_SIZE=$(ACL2_SIZE) \
	ACL2_IGNORE=$(ACL2_IGNORE) \
	TAGS_ACL2_DOC=$(TAGS_ACL2_DOC)

.PHONY: large-acl2r
large-acl2r:
	@$(MAKE) -s large ACL2_REAL=r

.PHONY: large-acl2d
large-acl2d:
	@$(MAKE) -s large ACL2_DEVEL=d

.PHONY: large-acl2p
large-acl2p:
	@$(MAKE) -s large ACL2_PAR=p

# Since ACL2_WAG is for implementors only, we don't bother making a
# target for it.  Instead one just uses ACL2_WAG=w on the "make"
# command line.

# NOTE:  None of the book certification targets use PREFIX.  They use
# "acl2" by default, but the ACL2 executable can be specified on the command
# line with ACL2=<some_acl2_executable>.
# Success can generally be determined by checking for the absence of ** in the
# log.

# Certify books that are not up-to-date, even those less likely to be
# included in other books.  Success can generally be determined by
# checking for the absence of ** in the log, or by looking at the Unix
# exit status.

.PHONY: regression
regression: check-books
	cd books ; $(MAKE) $(ACL2_IGNORE) regression ACL2=$(ACL2)

.PHONY: regression-everything
regression-everything: check-books
	cd books ; $(MAKE) $(ACL2_IGNORE) regression-everything ACL2=$(ACL2)

# Do regression tests from scratch.
# Success can generally be determined by checking for the absence of ** in the
# log.
.PHONY: regression-fresh
regression-fresh: clean-books
	$(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2) regression

.PHONY: regression-everything-fresh
regression-everything-fresh: clean-books
	$(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2) regression-everything

# The following allows for a relatively short test, in response to a request
# from GCL maintainer Camm Maguire.  The legacy name is
# certify-books-short; the preferred name now is basic.
.PHONY: basic certify-books-short
basic: check-books
	uname -a
	cd books ; $(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2) basic
certify-books-short: basic

# The following target assumes that we are using an image built with
# ACL2_DEVEL set, and then have certified the books mentioned in
# *system-verify-guards-alist*, currently system/top, for example as
# follows.  (This has taken about 2 minutes on a 2015 MacBook Pro.)
#   # Perhaps start with make clean-books.  Then, where the -j
#   # argument is optional:
#   cd books
#   ./build/cert.pl -j 8 --acl2 `pwd`/../saved_acl2d system/top.cert
.PHONY: devel-check
devel-check:
	@echo "(chk-new-verified-guards)" > workxxx.devel-check
	@$(ACL2) < workxxx.devel-check > devel-check.out
	@if [ "`fgrep CHK-NEW-VERIFIED-GUARDS-SUCCESS devel-check.out`" ] ; then \
		rm -f workxxx.devel-check devel-check.out ;\
		echo 'SUCCESS for chk-new-verified-guards' ;\
		break ;\
	else \
		echo '**FAILED** for chk-new-verified-guards;' ;\
		echo '           output log follows:' ;\
		cat devel-check.out ;\
		rm -f workxxx.devel-check ;\
		exit 1 ;\
	fi
	@echo "(check-system-events)" > workxxx.devel-check
	@$(ACL2) < workxxx.devel-check > devel-check.out
	@if [ "`fgrep CHECK-SYSTEM-EVENTS-SUCCESS devel-check.out`" ] ; \
		then \
		rm -f workxxx.devel-check devel-check.out ;\
		echo 'SUCCESS for check-system-events' ;\
	else \
		echo '**FAILED** for check-new-system-events;' ;\
		echo '           output log follows:' ;\
		cat devel-check.out ;\
		rm -f workxxx.devel-check ;\
		exit 1 ;\
	fi
	@echo 'SUCCESS for devel-check'

# Note that clean-doc does NOT delete source file doc.lisp,
# because it's important that there is always a doc.lisp present when
# building ACL2.  If we want to refresh doc.lisp, we can do so
# without running the clean-doc target.

.PHONY: clean-doc
clean-doc: check-books
	cd books/system/doc ; ../../build/clean.pl
	rm -rf doc/manual
	rm -f books/system/doc/rendered-doc.lsp

.PHONY: clean-books
clean-books: check-books
	cd books ; $(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2) moreclean

# This following should be executed inside the acl2-sources directory.
# You probably need to be the owner of all files in order for the chmod
# commands to work, but perhaps not.
# Keep tar in sync with tar-workshops.
.PHONY: tar
tar:
	rm -f acl2.tar.Z acl2.tar.gz acl2.tar
	rm -f SUM
# Historical comment (may be updated some day...):
# We want the extracted tar files to have permission for everyone to write,
# so that when they use -p with tar they get that permission.
# But we don't want the tar file itself to have that permission.  We may as
# well protect all the other files too from writing by CLI people other than
# those in the acl2 group, even though these files aren't the ones transferred
# to the ftp server.  Those come from the tar file, and we will extract them
# without the -p option so that the ftp files will not be world-writable.
	cd .. ; chmod -R g+r acl2-sources ; chmod -R o+r acl2-sources ; tar cvf /tmp/acl2.tar acl2-sources ; chmod -R o-w acl2-sources
	mv /tmp/acl2.tar .
	gzip acl2.tar
	md5sum acl2.tar.gz > acl2-tar-gz-md5sum

# Keep tar-workshops in sync with tar.
# This target should be executed in the acl2-sources directory.
.PHONY: tar-workshops
tar-workshops: check-books
	cd books ; rm -f workshops.tar.Z workshops.tar.gz workshops.tar workshops-tar-gz-md5sum
	cd books ; chmod -R g+r workshops ; chmod -R o+r workshops ; tar cvf /tmp/workshops.tar workshops ; chmod -R o-w workshops
	mv /tmp/workshops.tar books/
	cd books ; gzip workshops.tar
	cd books ; (md5sum workshops.tar.gz > workshops-tar-gz-md5sum)

.PHONY: mini-proveall
mini-proveall:
	@rm -rf mini-proveall.out
	@echo '(value :q) (lp) (mini-proveall)' | ./${PREFIXsaved_acl2} > mini-proveall.out
	@(grep '^ "Mini-proveall completed successfully."' mini-proveall.out > /dev/null) || \
	(echo 'Mini-proveall failed!' ; ls -l ./${PREFIXsaved_acl2}; cat mini-proveall.out ; exit 1)
	@echo 'Mini-proveall passed.'

# Target for making an Allegro CL application acl2.exe in a new "bin/" subdirectory.
# NOTE: An Allegro CL dynamic runtime license is needed in order for this to work.
# Also, a file our-develenv.cl is needed in this (the ACL2 sources) directory.  As
# explained in file build-allegro-exe.cl:
# [File our-develenv.cl] is obtained from a path such as
# <path-to-allegro>/AllegroCL-7.0/acl70/develenv.cl, then commenting out those
# not allowed in runtime images, as suggested in the above file.
ACL2_BIN_DIR = bin
.PHONY: allegro-app
allegro-app: our-develenv.cl
	@if [ -L ${PREFIXsaved_acl2} ]; then \
	echo "Note: removing link ${PREFIXsaved_acl2}"; \
	rm -f ${PREFIXsaved_acl2}; \
	elif [ -f ${PREFIXsaved_acl2} ]; then \
	echo "ERROR: Please move or remove ${PREFIXsaved_acl2} first."; \
	exit 1; \
	fi
	@if [ -d "${ACL2_BIN_DIR}" ]; then \
	echo "ERROR: Please remove the ${ACL2_BIN_DIR}/ subdirectory."; \
	exit 1; \
	fi
	$(MAKE) full
	rm -f workxxx
	echo '(generate-application "acl2.exe" "${ACL2_BIN_DIR}/" (quote ("build-allegro-exe.cl")) :runtime :dynamic :include-compiler t) (exit)' > workxxx
	${LISP} < workxxx
	rm -f workxxx
	@echo "Creating link from ${PREFIXsaved_acl2} to ${ACL2_BIN_DIR}/acl2.exe ."
	ln -s ${ACL2_BIN_DIR}/acl2.exe ${PREFIXsaved_acl2}

# Support for target allegro-app:
our-develenv.cl:
	@echo "ERROR:"
	@echo "  Please create file our-develenv.cl.  This may be obtained by"
	@echo "  copying a file <path-to-allegro>/AllegroCL-7.0/acl70/develenv.cl,"
	@echo "  and then commenting out those forms not allowed in runtime"
	@echo "  images, as suggested in the that file."
	exit 1

# Developer target only.  WARNING: Be sure to run "make regression"
# first!  We could add a dependency on regression, but maybe there
# will be some case in which we know part of the regression fails but
# we want to run this anyhow and it would get in the way to have a
# regression failure (though I don't know how that might happen).
.PHONY: chk-include-book-worlds
chk-include-book-worlds: check-books
	uname -a
	cd books ; $(MAKE) $(ACL2_IGNORE) chk-include-book-worlds ACL2=$(ACL2)
