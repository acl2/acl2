#  -*- Fundamental -*- 

# ACL2 Version 6.1 -- A Computational Logic for Applicative Common Lisp
# Copyright (C) 2013, Regents of the University of Texas

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
# Austin, TX 78701 U.S.A.

#  Example invocations for users:

#   make             ; Build saved_acl2 from scratch.  Same as make large.
#   make large       ; Build large-saved_acl2 from scratch.
#   make LISP=cl PREFIX=allegro-
#   make LISP=lisp PREFIX=lucid-
#   make LISP='gcl -eval "(defparameter user::*fast-acl2-gcl-build* t)"'
#                    ; Build in GCL, but with a shortcut that cuts the time by
#                    ; perhaps 2/3 at the cost losing perhaps 1% in run-time
#                    ; performance.
#   make LISP='gcl -eval "(push :acl2-mv-as-values *features*)"'
#                    ; Build in GCL, with mv and mv-let defined in terms of
#                    ; values and multiple-value-bind (respectively).
#   make LISP='acl -e "(push :acl2-mv-as-values *features*)"'
#                    ; As above, but for Allegro CL.
#   make LISP='openmcl -e "(push :acl2-mv-as-values *features*)"'
#                    ; As above, but for OpenMCL.
#   make LISP="lispworks -init /projects/acl2/devel/lispworks-init.lisp" PREFIX=lispworks-
#                    ; Same as make, except that image is named
#                    ; lispworks-saved_acl2 and the indicated init file is
#                    ;  loaded when lispworks is invoked during the build
#                    ; Note from Rich Cohen:
#                    ; The "-init -" tell Lispworks not to load the user's
#                    ; initialisation file.  By default Lispworks will load
#                    ; ~/.lispworks at start-up, regardless of the current
#                    ; working directory.  Further, when you attempt to save a
#                    ; core image, Lispworks notes that you previously loaded
#                    ; your personal initialisation file, and requires
#                    ; confirmation before saving the core image.
#   make TAGS        ; Create tags table, handy for viewing sources with emacs.
#   make TAGS!       ; Same as TAGS, except forces a rebuild of TAGS.
#   make certify-books
#                    ; Certify the community books that might reasonably
#                    ; be useful to include in proof developments.
#   make regression
#                    ; Certify all the distributed books and, if present, the
#                    ; workshops/ books as well.
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
#                    ; Same as make regression, except that target "everything"
#                    ; is used in community books file, Makefile.
#   make regression-legacy-fast [DEPRECATED as is books/regression-targets (legacy)]
#                    ; (WARNING: This target uses variable ACL2, with default value
#                    ;      "acl2", so it is probably a good idea to run after
#                    ;      explicitly setting ACL2=<path_to_ACL2>.
#                    ;      End of warning.)
#                    ; Certify a substantial portion of the books that
#                    ; would be certified by `make regression', but
#                    ; with better parallelism.  We have used this
#                    ; with option "-j 24" to obtain over a 12x
#                    ; speedup.  This target assumes that
#                    ; books/Makefile-fast is up-to-date; if you are
#                    ; using an "alpha" version, just follow
#                    ; instructions in books/regression-targets to
#                    ; update that file first and then update
#                    ; books/Makefile-fast as follows:
#                    ;   cd books/
#                    ;   ./cert.pl -s Makefile-fast --targets regression-targets -b .
#   make clean-books ; Remove certificate files, object files, log files,
#                    ; debris, ..., created by `make certify-books',
#                    ; `make regression', etc.

# Also included are various legacy versions of these targets, which
# correspond to targets through ACL2 Version 6.1.  For example, target
# regression-legacy in this file corresponds to target regression in
# older versions of htis file.

###############################################################################

#  NOTE:  Users need not read below this line.  Neither should installers of
#  ACL2 at sites other than CLI.  We have no reason to believe that the make
#  commands illustrated below will work at sites other than CLI.  Indeed, we
#  have reasons to believe they will not!  A typical problem is that we refer
#  to a file or directory that exists at CLI but that is not created when our
#  installation instructions are followed at other sites.

#  Example invocations for CLI implementors:

#   NOTE:  Make large completely recompiles, initializes and
#   saves.  Consider some of the "fast" and "very-fast" options below if only
#   part of the system needs to be rebuilt.

#   make very-fast init 
#                  ; Build the system, recompiling as little as possible
#                  ; (perhaps don't even recompile TMP1.lisp).

#   make fast init ; Compile as needed, initialize, build saved_acl2

#   make full      ; A complete recompilation whether needed or not.
#   make full init ; Completely recompile, initialize and save.
#   make full-meter init  ; Completely recompile with meters, init and save.
#   make init      ; Just build full-size saved_acl2.
#   make check-sum ; Call only after ACL2 is completely compiled.
#   make full LISP=lucid PREFIX=lucid-  ; makes acl2 in Lucid
#   make full LISP=cl PREFIX=allegro- ; makes acl2 in allegro
#                  ; Note:  Allegro is not always named cl at CLI.  See
#                  ; ~moore/allegro/runcl for some clues.
#   make full LISP=lispworks PREFIX=lispworks- ; makes acl2 in lispworks
#   make copy DIR=targetdir  ; copies all of acl2 to targetdir.  Don't use ~ notation.
#   make copy-distribution DIR=/projects/acl2/v2-9-aix
#   make copy-extra DIR=/projects/acl2/v2-9-aix
#                  ; for developers only: same as copy-distribution, but
#                  ; includes the files in all-files-extra.txt
#   make copy-distribution DIR=/stage/ftp/pub/moore/acl2/v2-9/acl2-sources
#                  ; copies all of acl2 plus books, doc, etc., to the named
#                  ; directory, as for compiling on another architecture or
#                  ; moving to the ftp site.
#                  ; Preconditions:
#                  ; (1) The named directory must not already exist; if it
#                  ;     does, a harmless error is caused.
#                  ; (2) acl2-book must be gzipped, i.e., if necessary first do
#                         gzip /projects/acl2/v2-9/doc/TEX/acl2-book.ps
#                         gzip /projects/acl2/v2-9/doc/TEX/acl2-book.dvi
#   make DOC       ; Build html and emacs info files
#   make clean-doc ; Remove files created by make DOC
#   make red       ; Just build full-size saved_acl2, but do so without pass 2
#   make proofs    ; Assuming sources are compiled, initialize without skipping
#                  ; proofs during pass 2.  Does not save an image.  Uses same
#                  ; flags used to build full-size image.

#  Metering:  If the currently compiled version is unmetered and you wish
#  it metered, the fastest thing to do is to (push :acl2-metering *features*)
#  and then yank in and recompile just those definitions that mention
#  acl2-metering.  However, if you would like to install metering as part
#  of a system-wide recompilation, you must use the full-meter option below,
#  rather than the fast-meter option.  If, while running a fully metered
#  system you wish to do what would otherwise be a make fast but you want
#  to preserve the metering, use the fast-meter option.  If you want to
#  get rid of the metering in the compiled code, do make full.

LISP = ccl
DIR = /tmp

# The variable NONSTD should be defined for the non-standard version and not
# for the standard version.  Non-standard ACL2 images will end in saved_acl2r
# rather than saved_acl2.  ACL2_HONS, ACL2_PAR, ACL2_DEVEL, and ACL2_WAG (for
# feature write-arithmetic-goals) are similar (with suffixes h,
# p, d, and w, resp., rather than r), but for the experimental hons and
# parallel versions and the feature that writes out arithmetic lemma data to
# ~/write-arithmetic-goals.lisp (surely only of interest to implementors!).

# DO NOT EDIT ACL2_SUFFIX!  Edit the above-mentioned three variables instead.

ACL2_SUFFIX :=
ifdef ACL2_HONS
	ACL2_SUFFIX := $(ACL2_SUFFIX)h
endif
ifdef ACL2_PAR
	ACL2_SUFFIX := $(ACL2_SUFFIX)p
endif
ifdef ACL2_WAG
	ACL2_SUFFIX := $(ACL2_SUFFIX)w
endif
ifdef ACL2_DEVEL
	ACL2_SUFFIX := $(ACL2_SUFFIX)d
endif
ifdef NONSTD
	ACL2_SUFFIX := $(ACL2_SUFFIX)r
endif

# The user may legally edit the following variable, or set it on the command
# line, only when :acl2-mv-as-values is pushed on to *features*.  In that case,
# this variable may be set to ":REUSE", as shown in the comment below.  That
# will cause the use of the existing acl2-proclaims.lisp, which will save one
# compile and one initialization.  BUT this should only be done if the
# acl2-proclaims.lisp that would otherwise be generated would be identical to
# the existing acl2-proclaims.lisp.
USE_ACL2_PROCLAIMS =
# USE_ACL2_PROCLAIMS = :REUSE

# The user may define PREFIX; otherwise it is implicitly the empty string.
PREFIX = 

PREFIXsaved_acl2 = ${PREFIX}saved_acl2${ACL2_SUFFIX}
PREFIXosaved_acl2 = ${PREFIX}osaved_acl2${ACL2_SUFFIX}

# One may define ACL2_SAFETY to provide a safety setting.  We recommend
# ACL2_SAFETY = 3
# for careful error checking.  This can cause significant slowdown and for
# some Lisp implementations, the regression might not even complete.  For
# CCL we have had success with safety 3.
ACL2_SAFETY =

# Set ACL2_COMPILER_DISABLED, say with ACL2_COMPILER_DISABLED=t, to
# build the image with (SET-COMPILER-ENABLED NIL STATE), thus
# disabling use of the compiler for certify-book and include-book; see
# :DOC compilation.  This is generally not necessary, but for the use
# of some books employing raw Lisp code it could, on rare occasion, be
# useful; and for SBCL and CCL (as of this writing, May 2010),
# reasonably harmless other than to lose a bit of speed when including
# books with many complex defun forms.
ACL2_COMPILER_DISABLED =

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

sources := axioms.lisp memoize.lisp hons.lisp boot-strap-pass-2.lisp\
           basis.lisp parallel.lisp translate.lisp\
           type-set-a.lisp linear-a.lisp\
           type-set-b.lisp linear-b.lisp\
           non-linear.lisp tau.lisp\
           rewrite.lisp simplify.lisp bdd.lisp\
           other-processes.lisp induct.lisp prove.lisp\
           proof-checker-a.lisp history-management.lisp defuns.lisp defthm.lisp\
           other-events.lisp ld.lisp proof-checker-b.lisp interface-raw.lisp\
           serialize.lisp serialize-raw.lisp\
           defpkgs.lisp

ifdef ACL2_HONS
	sources := $(sources) hons-raw.lisp memoize-raw.lisp
endif
ifdef ACL2_PAR
	sources := $(sources) multi-threading-raw.lisp parallel-raw.lisp futures-raw.lisp
endif
# No change to sources for ACL2_DEVEL or ACL2_WAG

# Top target:
all: large

.PHONY: acl2r
acl2r:
	rm -f acl2r.lisp
	$(MAKE) acl2r.lisp

acl2r.lisp:
# The following is important if we sometimes build for GCL on Linux and
# sometimes on Unix.
	rm -f acl2-fns.o
	echo "" > acl2r.lisp
	if [ "$(NONSTD)" != "" ] ; then \
	echo '(or (member :non-standard-analysis *features*) (push :non-standard-analysis *features*))' >> acl2r.lisp ;\
	fi
	if [ "$(ACL2_HONS)" != "" ] ; then \
	echo '(or (member :hons *features*) (push :hons *features*))' >> acl2r.lisp ;\
	fi
	if [ "$(ACL2_HONS)" = "h_hack" ] ; then \
	echo '(or (member :memoize-hack *features*) (push :memoize-hack *features*))' >> acl2r.lisp ;\
	fi
	if [ "$(ACL2_PAR)" != "" ] ; then \
	echo '(or (member :acl2-par *features*) (push :acl2-par *features*))' >> acl2r.lisp ;\
	fi
	if [ "$(ACL2_DEVEL)" != "" ] ; then \
	echo '(or (member :acl2-devel *features*) (push :acl2-devel *features*))' >> acl2r.lisp ;\
	fi
	if [ "$(ACL2_WAG)" != "" ] ; then \
	mv -f ~/write-arithmetic-goals.lisp.old ; \
	mv -f ~/write-arithmetic-goals.lisp ~/write-arithmetic-goals.lisp.old ; \
	echo '(or (member :write-arithmetic-goals *features*) (push :write-arithmetic-goals *features*))' >> acl2r.lisp ;\
	fi
	if [ "$(ACL2_SAFETY)" != "" ] ; then \
	echo "(defparameter *acl2-safety* $(ACL2_SAFETY))" >> acl2r.lisp ;\
	fi
	if [ "$(ACL2_SIZE)" != "" ] ; then \
	echo '(or (find-package "ACL2") (#+gcl defpackage:defpackage #-gcl defpackage "ACL2" (:size $(ACL2_SIZE)) (:use)))' >> acl2r.lisp ;\
	fi
	if [ "$(ACL2_COMPILER_DISABLED)" != "" ] ; then \
	echo '(DEFPARAMETER *ACL2-COMPILER-ENABLED* NIL)' >> acl2r.lisp ;\
	fi

.PHONY: chmod_image
chmod_image:
	if [ -f ${PREFIXsaved_acl2} ]; then \
	chmod 775 ${PREFIXsaved_acl2} ;\
	fi

.PHONY: do_saved
# Note: Removed line "chmod g+s saved" before the second chmod below, as it was
# causing errors in at least one environment, and instead did final chmod to
# 666 instead of 664 in case files in saved/ wind up in an unexpected group.
do_saved:
	rm -fr saved
	mkdir saved
	chmod 775 saved
	cp *.lisp saved
	chmod 666 saved/*.lisp

# Keep the use of :COMPILED below in sync with ACL2 source function
# note-compile-ok.
.PHONY: check_compile_ok
check_compile_ok:
	@if [ ! -f acl2-status.txt ] ; then \
	echo 'Compile FAILED: file acl2-status.txt is missing.' ; \
	exit 1 ; \
	fi
	@if [ `cat acl2-status.txt` != :COMPILED ] ; then \
	echo 'Compile FAILED: acl2-status.txt should contain :COMPILED.' ; \
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

.PHONY: fast
fast:
	date
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::quick-compile-acl2 nil)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	@$(MAKE) check_compile_ok
	rm -f workxxx

.PHONY: compile-ok
compile-ok:  
	date
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::note-compile-ok)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	rm -f workxxx

.PHONY: very-fast
very-fast:
	date
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::quick-compile-acl2 t)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	@$(MAKE) check_compile_ok
	rm -f workxxx

.PHONY: fast-meter
fast-meter:
	date
	rm -f workxxx
	echo '(load "init.lisp") (push :acl2-metering *features*)' > workxxx
	echo '(acl2::quick-compile-acl2 nil)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	@$(MAKE) check_compile_ok
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
full:   TAGS!
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::compile-acl2 $(USE_ACL2_PROCLAIMS))' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	@$(MAKE) check_compile_ok
	rm -f workxxx

.PHONY: full-meter
full-meter:
	date
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::make-tags)' >> workxxx
	echo '(push :acl2-metering *features*)' >> workxxx
	echo '(acl2::compile-acl2)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	@$(MAKE) check_compile_ok
	rm -f workxxx

.PHONY: copy
copy:
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::copy-acl2 "${DIR}")' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	rm -f workxxx

.PHONY: copy-distribution
copy-distribution:
# WARNING: Execute this from an ACL2 source directory.
# Keep this in sync with copy-books.
# You must manually rm -r ${DIR} before this or it will fail without doing
# any damage.
# Note that below, /projects/acl2/ is not used, because this directory must
# match what lisp returns from truename.
	rm -f workxxx
	rm -f workyyy
	rm -f acl2r.lisp
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::copy-distribution "workyyy" "${CURDIR}" "${DIR}")' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	chmod 777 workyyy
	./workyyy
	rm -f workxxx
	rm -f workyyy

.PHONY: copy-books
copy-books:
# WARNING: Execute this from an ACL2 source directory.
# See the comments for copy-distribution, and keep these in sync.  Use the same
# DIR for both.
	rm -f workxxx
	rm -f workyyy
	rm -f acl2r.lisp
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::copy-distribution "workyyy" "${CURDIR}" "${DIR}" "all-files-books.txt" t)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	chmod 777 workyyy
	./workyyy
	rm -f workxxx
	rm -f workyyy

.PHONY: copy-extra
copy-extra:
# Developer target only.
# See the comments for copy-distribution, and keep these in sync.  Use the same
# DIR for both.
	$(MAKE) copy-distribution DIR=$(DIR)
	rm -f workxxx
	rm -f workyyy
	rm -f acl2r.lisp
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::copy-distribution "workyyy" "${CURDIR}" "${DIR}" "all-files-extra.txt" t)' >> workxxx
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

TAGS:   acl2.lisp acl2-check.lisp acl2-fns.lisp acl2-init.lisp ${sources}
	rm -f TAGS
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::make-tags)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	rm -f workxxx
	if [ -f TAGS ] ; then chmod 644 TAGS ; fi

# The following remakes TAGS even if TAGS is up to date.  This target can be
# useful when building a hons or parallel version after a normal version, or
# vice-versa.
.PHONY: TAGS!
TAGS!:  acl2r TAGS

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

.PHONY: make-acl2-proclaims
make-acl2-proclaims:
	if [ "$(USE_ACL2_PROCLAIMS)" != ":REUSE" ]; then \
	rm -f acl2-proclaims.lisp; \
	$(MAKE) acl2-proclaims.lisp; \
	$(MAKE) full USE_ACL2_PROCLAIMS=t; \
	fi

.PHONY: init
init: make-acl2-proclaims
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
	echo '(save-acl2 (quote (initialize-acl2 (quote include-book) acl2::*acl2-pass-2-files*)) "${PREFIXsaved_acl2}")' >> workxxx
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

# The following "proofs" target assumes that files for the specified LISP have
# been compiled.
.PHONY: proofs
proofs: compile-ok
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::load-acl2)' >> workxxx
	echo '(acl2::initialize-acl2 nil acl2::*acl2-pass-2-files*)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	@$(MAKE) check_init_ok
	rm -f workxxx

.PHONY: DOC HTML EMACS_TEX EMACS_ONLY STATS

DOC: HTML EMACS_TEX STATS

# Use ACL2_DOC_UNDOCUMENTED_FILE if you want to support broken links
# (by having them point to a page acknowledging that the link is
# broken, rather than by having doc/create-acl2-html simply fail).
# Note that this only works for the HTML target, not for the EMACS_TEX
# or EMACS_ONLY targets.
HTML:
	@if [ "$(ACL2)" = "" ]; then \
	    ACL2="../../$(PREFIX)saved_acl2$(ACL2_SUFFIX)" ;\
	    export ACL2 ;\
	    doc/create-acl2-html ;\
	else \
	    ACL2=$(ACL2) ;\
	    export ACL2 ;\
	    doc/create-acl2-html ;\
	fi

# Note: doc/create-acl2-tex builds a ps file, so depends on texi2dvi
# and dvips.  These might not be present on some systems (but is
# present at UT CS and have been seen to be present on a Mac where
# Latex is installed).  Use EMACS_ONLY instead of EMACS_TEX if you
# want to avoid this issue.

# Note that doc/create-acl2-texinfo certifies doc/write-acl2-texinfo,
# but (for efficiency) doc/create-acl2-tex does not.
EMACS_TEX:
	@if [ "$(ACL2)" = "" ]; then \
	    ACL2="./$(PREFIX)saved_acl2$(ACL2_SUFFIX)" ;\
	    export ACL2 ;\
	    doc/create-acl2-texinfo ; doc/create-acl2-tex ;\
	else \
	    ACL2=$(ACL2) ;\
	    export ACL2 ;\
	    doc/create-acl2-texinfo ; doc/create-acl2-tex ;\
	fi

EMACS_ONLY:
	@if [ "$(ACL2)" = "" ]; then \
	    ACL2="./$(PREFIX)saved_acl2$(ACL2_SUFFIX)" ;\
	    export ACL2 ;\
	    doc/create-acl2-texinfo ;\
	else \
	    ACL2=$(ACL2) ;\
	    export ACL2 ;\
	    doc/create-acl2-texinfo ;\
	fi

# See the Essay on Computing Code Size in the ACL2 source code.
STATS:
	@if [ "$(ACL2)" = "" ]; then \
	    ACL2="../$(PREFIX)saved_acl2$(ACL2_SUFFIX)" ;\
	    export ACL2 ;\
	    ACL2_SOURCES="$(sources)" ;\
	    export ACL2_SOURCES ;\
	    doc/create-acl2-code-size ;\
	else \
	    ACL2=$(ACL2) ;\
	    export ACL2 ;\
	    ACL2_SOURCES="$(sources)" ;\
	    export ACL2_SOURCES ;\
	    doc/create-acl2-code-size ;\
	fi

.PHONY: clean
clean:
# Does not remove executable or corresponding scripts
# (since there could be many executables that one prefers not to delete),
# except for *osaved_acl2* files.
	rm -f *.o *#* *.c *.h *.data gazonk.* workxxx workyyy *.lib \
	  *.fasl *.fas *.sparcf *.ufsl *.64ufasl *.ufasl *.dfsl *.dxl \
	  *.d64fsl *.dx64fsl *.lx64fsl \
	  *.lx32fsl *.x86f *.o \
	  TAGS acl2-status.txt acl2r.lisp acl2-proclaims.lisp .acl2rc \
	  *osaved_acl2 *osaved_acl2.* \
	  *.log TMP*
	rm -rf saved
	rm -f doc/*.o doc/*#* doc/*.c doc/*.h doc/*.data doc/gazonk.* \
	   doc/workxxx doc/workyyy doc/*.lib \
	   doc/*.fasl doc/*.fas doc/*.sparcf doc/*.ufsl doc/*.64ufasl doc/*.ufasl doc/*.dfsl \
	   doc/*.d64fsl doc/*.dx64fsl doc/*.lx64fsl \
	   doc/*.lx32fsl doc/*.x86f doc/*.o \
	   doc/*.cert doc/*.out \
	   doc/*.log doc/TMP*
	rm -rf doc/TEX doc/HTML doc/EMACS

.PHONY: red
red:    compile-ok
	rm -f workxxx
	echo '(load "init.lisp")' > workxxx
	echo '(in-package "ACL2")' >> workxxx
	echo '(save-acl2 (quote (initialize-acl2 nil nil)))' >> workxxx
	echo '(exit-lisp)' >> workxxx
	${LISP} < workxxx
	@$(MAKE) check_init_ok
	echo -n "" >> red-${PREFIXsaved_acl2}
# Note:  This needs to be updated for Allegro 5.0 and cmulisp if we decide to
# use it.  See init.
	mv -f red-${PREFIXsaved_acl2} red-${PREFIXosaved_acl2}
	mv -f nsaved_acl2 red-${PREFIXsaved_acl2}
	rm -f workxxx
	$(MAKE) do_saved

# The .NOTPARALLEL target avoids our doing any build process in
# parallel.  Uses of makefiles in other directories, even if invoked
# from this makefile, can still take advantage of -j (as per the GNU
# make documentation).
.NOTPARALLEL:

.PHONY: large
large: acl2r full init

.PHONY: large-acl2r
large-acl2r:
	$(MAKE) large NONSTD=r

.PHONY: large-acl2h
large-acl2h:
	$(MAKE) large ACL2_HONS=h

.PHONY: large-acl2d
large-acl2d:
	$(MAKE) large ACL2_DEVEL=d

.PHONY: large-acl2p
large-acl2p:
	$(MAKE) large ACL2_PAR=p

# Since ACL2_WAG is for implementors only, we don't bother making a
# target for it.  Instead one just uses ACL2_WAG=w on the "make"
# command line.

# Note that move-large may not have the desired effect for Allegro/CMUCL/SBCL
# images, because "large-" will not have been written to the core file name in
# ${PREFIXsaved_acl2}.
.PHONY: move-large
move-large:
	mv ${PREFIXsaved_acl2} large-${PREFIXsaved_acl2}
	if [ -f worklispext ]; then \
	mv ${PREFIXsaved_acl2}.`cat worklispext ` large-${PREFIXsaved_acl2}.`cat worklispext` ;\
	fi

# Certify books that are not up-to-date, but only those that might reasonably
# be useful to include in proof developments.
# NOTE:  None of the book certification targets use PREFIX.  They use
# "acl2" by default, but the ACL2 executable can be specified on the command
# line with ACL2=<some_acl2_executable>.
# Success can generally be determined by checking for the absence of ** in the
# log.
.PHONY: certify-books
certify-books:
ifndef ACL2
	cd books ; $(MAKE) $(ACL2_IGNORE) certify-books ACL2=$(shell pwd)/saved_acl2
else
	cd books ; $(MAKE) $(ACL2_IGNORE) certify-books ACL2=$(ACL2)
endif

# Certify books that are not up-to-date, even those less likely to be included
# in other books.  This does *not* certify the nonstd/ books.  It would be
# awkward to arrange for that here, because the ACL2 images are different;
# they might not even have the same prefix.  See target regression-nonstd.
# Success can generally be determined by checking for the absence of ** in the
# log, or by looking at the Unix exit status.
.PHONY: regression
regression:
	uname -a
ifndef ACL2
	cd books ; $(MAKE) $(ACL2_IGNORE) ACL2=$(shell pwd)/saved_acl2
else
	cd books ; $(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2)
endif

.PHONY: regression-everything
regression-everything:
	uname -a
ifndef ACL2
	cd books ; $(MAKE) $(ACL2_IGNORE) everything ACL2=$(shell pwd)/saved_acl2
else
	cd books ; $(MAKE) $(ACL2_IGNORE) everything ACL2=$(ACL2)
endif

.PHONY: regression-nonstd
regression-nonstd:
	uname -a
ifndef ACL2
	cd books/nonstd ; \
	$(MAKE) $(ACL2_IGNORE) ACL2=$(shell pwd)/saved_acl2r
else
	cd books/nonstd ; \
	$(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2)
endif

# Certify main books from scratch.
.PHONY: certify-books-fresh
certify-books-fresh: clean-books
	$(MAKE) $(ACL2_IGNORE) certify-books

# Do regression tests from scratch.
# Success can generally be determined by checking for the absence of ** in the
# log.
.PHONY: regression-fresh
regression-fresh: clean-books
ifndef ACL2
	$(MAKE) $(ACL2_IGNORE) ACL2=$(shell pwd)/saved_acl2 regression
else
	$(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2) regression
endif

.PHONY: regression-everything-fresh
regression-everything-fresh: clean-books
ifndef ACL2
	$(MAKE) $(ACL2_IGNORE) ACL2=$(shell pwd)/saved_acl2 regression-everything
else
	$(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2) regression-everything
endif

.PHONY: regression-nonstd-fresh
regression-nonstd-fresh: clean-books-nonstd
ifndef ACL2
	$(MAKE) $(ACL2_IGNORE) ACL2=$(shell pwd)/saved_acl2r regression-nonstd
else
	$(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2) regression-nonstd
endif

# The following allows for a relatively short test, in response to a request
# from GCL maintainer Camm Maguire.
.PHONY: certify-books-short
certify-books-short:
	uname -a
ifndef ACL2
	cd books ; \
	$(MAKE) $(ACL2_IGNORE) ACL2=$(shell pwd)/saved_acl2 short-test
else
	cd books ; \
	$(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2) short-test
endif

# The following target assumes that we are using an image built with
# ACL2_DEVEL set.
.PHONY: devel-check
devel-check:
	@counter=0 ; \
	while [ t ] ;\
	do \
	echo "(chk-new-verified-guards $$counter) ..." ;\
	echo "(chk-new-verified-guards $$counter)" > workxxx.devel-check ;\
	$(ACL2) < workxxx.devel-check > devel-check.out ;\
	if [ "`fgrep CHK-NEW-VERIFIED-GUARDS-COMPLETE devel-check.out`" ] ; then \
		rm -f workxxx.devel-check devel-check.out ;\
		echo 'SUCCESS for devel-check' ;\
		exit 0 ;\
	fi ;\
	if [ "`fgrep CHK-NEW-VERIFIED-GUARDS-SUCCESS devel-check.out`" ] ; then \
		rm -f workxxx.devel-check devel-check.out ;\
		counter=`expr $$counter + 1` ;\
	else \
		echo '**FAILED** devel-check: output log follows:' ;\
		cat devel-check.out ;\
		rm -f workxxx.devel-check devel-check.out ;\
		exit 1 ;\
	fi \
	done

.PHONY: clean-doc
clean-doc:
	cd doc ; rm -f *.o *~* *#* TAGS *.c *.h *.data gazonk.* workxxx \
	  *.lbin *.sbin *.fasl *.wfasl *.fas *.lib *.sparcf *.ufsl *.64ufasl *.ufasl *.x86f *.dfsl *.fn *.cert
	rm -rf doc/EMACS
	rm -rf doc/EMACS-old/
	rm -rf doc/HTML
	rm -rf doc/HTML-old
	rm -rf doc/TEX

.PHONY: clean-books
clean-books:
ifndef ACL2
	cd books ; $(MAKE) $(ACL2_IGNORE) ACL2=$(shell pwd)/saved_acl2 moreclean
else
	cd books ; $(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2) moreclean
endif

.PHONY: clean-books-nonstd
clean-books-nonstd:
ifndef ACL2
	cd books/nonstd ; \
	$(MAKE) $(ACL2_IGNORE) ACL2=$(shell pwd)/saved_acl2 clean
else
	cd books/nonstd ; \
	$(MAKE) $(ACL2_IGNORE) ACL2=$(ACL2) clean
endif

# This following should be executed inside the acl2-sources directory.
# You probably need to be the owner of all files in order for the chmod
# commands to work, but perhaps not.
# Keep tar in sync with tar-workshops and tar-nonstd.
.PHONY: tar
tar:
	rm -f acl2.tar.Z acl2.tar.gz acl2.tar
	rm -f SUM
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

# Keep tar-workshops in sync with tar and tar-nonstd.
# This target should be executed in the acl2-sources directory.
.PHONY: tar-workshops
tar-workshops:
	cd books ; rm -f workshops.tar.Z workshops.tar.gz workshops.tar workshops-tar-gz-md5sum
	cd books ; chmod -R g+r workshops ; chmod -R o+r workshops ; tar cvf /tmp/workshops.tar workshops ; chmod -R o-w workshops
	mv /tmp/workshops.tar books/
	cd books ; gzip workshops.tar
	cd books ; (md5sum workshops.tar.gz > workshops-tar-gz-md5sum)

# Keep tar-nonstd in sync with tar and tar-workshops.
# This target should be executed in the acl2-sources directory.
.PHONY: tar-nonstd
tar-nonstd:
	cd books ; rm -f nonstd.tar.Z nonstd.tar.gz nonstd.tar nonstd-tar-gz-md5sum
	cd books ; chmod -R g+r nonstd ; chmod -R o+r nonstd ; tar cvf /tmp/nonstd.tar nonstd ; chmod -R o-w nonstd
	mv /tmp/nonstd.tar books/
	cd books ; gzip nonstd.tar
	cd books ; (md5sum nonstd.tar.gz > nonstd-tar-gz-md5sum)

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
chk-include-book-worlds:
	uname -a
ifndef ACL2
	cd books ; $(MAKE) $(ACL2_IGNORE) chk-include-book-worlds ACL2=$(shell pwd)/saved_acl2
else
	cd books ; $(MAKE) $(ACL2_IGNORE) chk-include-book-worlds ACL2=$(ACL2)
endif

##########
### Legacy targets
### (renamed using "-legacy" and deprecated after ACL2 Version 6.1):
##########

# Here we provide support for a convenient way to pass -j down to the
# community books Makefile, for both `make' and cert.pl.  It seems
# cleanest and perhaps critical that below, when we call in the books
# directory we do so with an explicit -j, rather than leaving this to
# the Makefile in the books/ directory.
export ACL2_HONS_OPT
ifdef ACL2_JOBS
# Note: Because of recursive call of make, ACL2_HONS_OPT could
# ultimately include many -j options.  This anomaly seems harmless, so
# we leave it for now but may revisit it later.
ACL2_HONS_OPT += -j$(ACL2_JOBS)
ACL2_JOBS_OPT := -j $(ACL2_JOBS)
endif

.PHONY: clean-books-legacy
clean-books-legacy:
	cd books ; $(MAKE) -f Makefile.legacy $(ACL2_IGNORE) clean

.PHONY: regression-legacy
regression-legacy:
	uname -a
	cd books ; $(MAKE) -f Makefile.legacy $(ACL2_IGNORE) $(ACL2_JOBS_OPT) all-plus

# For a HONS regression, we do regression-legacy-hons-only first to get the
# extra parallelism provided by cert.pl.  For regression-legacy-hons-only the
# default for ACL2 is saved_acl2h in the development directory; for
# regression-legacy, saved_acl2.  So the user might be happiest simply
# providing a value for ACL2.
.PHONY: regression-legacy-hons-only
regression-legacy-hons-only:
	uname -a
	cd books ; $(MAKE) -f Makefile.legacy $(ACL2_IGNORE) hons

.PHONY: regression-legacy-hons
# For a legacy HONS regression, we do regression-legacy-hons-only
# first to get the extra parallelism provided by cert.pl.  For
# regression-legacy-hons-only the default for ACL2 is saved_acl2h in
# the development directory; for regression-legacy, saved_acl2.  So
# the user might be happiest simply providing a value for ACL2.
regression-legacy-hons:
	$(MAKE) regression-legacy-hons-only
	$(MAKE) regression-legacy ACL2_CENTAUR=skip ACL2_HONS_REGRESSION=t

.PHONY: clean-books-nonstd-legacy
clean-books-legacy-nonstd:
	cd books/nonstd ; $(MAKE) -f Makefile.legacy $(ACL2_IGNORE) clean-nonstd

.PHONY: regression-legacy-nonstd
regression-legacy-nonstd:
	uname -a
	cd books/nonstd ; $(MAKE) -f Makefile.legacy $(ACL2_IGNORE) $(ACL2_JOBS_OPT) all-nonstd

# Warning: We are no longer actively maintaining books/Makefile-fast.
.PHONY: regression-legacy-fast
regression-legacy-fast:
	uname -a
	cd books ; pwd ; $(MAKE) $(ACL2_IGNORE) $(ACL2_JOBS_OPT) -f Makefile-fast

.PHONY: regression-legacy-fresh regression-legacy-fast-fresh regression-legacy-nonstd-fresh
regression-legacy-fresh: clean-books-legacy
	$(MAKE) $(ACL2_IGNORE) regression-legacy
regression-legacy-hons-fresh: clean-books-legacy
	$(MAKE) $(ACL2_IGNORE) regression-legacy-hons
regression-legacy-fast-fresh: clean-books-legacy
	$(MAKE) $(ACL2_IGNORE) regression-legacy-fast
regression-legacy-nonstd-fresh: clean-books-legacy-nonstd
	$(MAKE) $(ACL2_IGNORE) regression-legacy-nonstd

.PHONY: certify-books-legacy
certify-books-legacy:
	cd books ; $(MAKE) -f Makefile.legacy $(ACL2_JOBS_OPT) $(ACL2_IGNORE)

# Certify main books from scratch.
.PHONY: certify-books-legacy-fresh
certify-books-legacy-fresh: clean-books-legacy
	$(MAKE) $(ACL2_IGNORE) $(ACL2_JOBS_OPT) certify-books-legacy

# The following allows for a relatively short test, in response to a request
# from GCL maintainer Camm Maguire.
.PHONY: certify-books-legacy-short
certify-books-legacy-short:
	cd books ; $(MAKE) -f Makefile.legacy $(ACL2_JOBS_OPT) short-test

# Next is a legacy version of a developer target.
.PHONY: chk-include-book-worlds
chk-include-book-worlds-legacy:
	uname -a
	cd books ; $(MAKE) -f Makefile.legacy $(ACL2_IGNORE) chk-include-book-worlds-top

