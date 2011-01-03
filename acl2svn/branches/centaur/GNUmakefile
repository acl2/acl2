#  -*- Fundamental -*- 

# ACL2 Version 4.1 -- A Computational Logic for Applicative Common Lisp
# Copyright (C) 2010  University of Texas at Austin.

# This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
# (C) 1997 Computational Logic, Inc.  See the documentation topic NOTES-2-0.

# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

# Written by:  Matt Kaufmann                  and J Strother Moore
# email:       Kaufmann@cs.utexas.edu         and Moore@cs.utexas.edu
# Department of Computer Sciences
# University of Texas at Austin
# Austin, TX 78712-1188 U.S.A.

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
#                    ; Certify all the distributed books.
#   make regression
#                    ; Certify all the distributed books and, if present, the
#                    ; workshops/ books as well.
#   make regression ACL2=xxx
#                    ; Same as make regression, but use xxx as ACL2, which
#                    ; should either be an absolute filename or a command on
#                    ; one's path.
#   make regression-fast
#                    ; (WARNINGS:
#                       (1) This target should be considered a bit experimental:
#                    ;      It works only if the workshops books are included,
#                    ;      and also, we have seen failure messages on linux
#                    ;      (but not Mac) such as
#                    ;        /lusr/bin/bash: line 1: 25654 Bus error
#                    ;      without any actual certification failure.  But if
#                    ;      you follow "make -j n regression-fast" with "make -j
#                    ;      n regression", you may get some nice speed-up.)
#                    ;  (2) This target uses variable ACL2, with default value
#                    ;      "acl2", so it is probably a good idea to run with
#                    ;      explicit setting ACL2=<path_to_ACL2>.
#                    ;  [end of warnings])
#                    ; Certify a substantial portion of the books that would be
#                    ; certified by `make regression', but with better
#                    ; parallelism.  We have used this with option "-j 24" to
#                    ; obtain over a 12x speedup.  Note to those who use
#                    ; "alpha" versions of ACL2: You may want to update
#                    ; books/Makefile-fast occasionally; just follow
#                    ; instructions in books/regression-targets to update that
#                    ; file first and then update books/Makefile-fast as follows:
#                    ;   cd books/
#                    ;   ./cert.pl -s Makefile-fast --targets regression-targets -b .
#   make clean-books ; Remove certificate files, object files, log files,
#                    ; debris, ..., created by `make certify-books',
#                    ; `make regression', or `make regression-fast'.

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

#   make big-test
#                  ; Build the image from scratch, make the DOC files in
#                  ; EMACS, HTML, and TEX,
#                  ; certify all the books, prove through axioms.lisp.
#                  ; Typical invocations:

#   make big-test >& make-big-test.log&
#   make big-test LISP=cl PREFIX=cl- >& make-cl-big-test.log&

#   make test

#                  ; Build the system from scratch, certify all books, and
#                  ; prove through axioms.lisp.  Consider "make test DOC" if
#                  ; running late at night (so that you don't smash someone's
#                  ; documentation).

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
#
#   make arch      ; full init move-large certify-books
#                  ; Do this while logged onto the appropriate host.  For
#                  ; example:
#                  ;  tantallon% rm -r ../v2-8-aix
#                  ;  tantallon% make copy-distribution DIR=/projects/acl2/v2-8-aix
#                  ;  tantallon% xrsh bigbird emacs
#                  ;  bigbird%  cd /projects/acl2/v2-8-aix
#                  ;  bigbird%  make arch >& make.log &
#                  ; =======================================================
#                  ; Machine         DIR            Architecture
#                  ; beechbone       v2-8           Solaris 2.8 Sparc
#                  ; bigbird         v2-8-aix       AIX
#                  ; =======================================================
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

LISP = gcl
DIR = /tmp
ACL2_VERSION = v4-1

# The variable NONSTD should be defined for the non-standard version and not
# for the standard version.  Non-standard ACL2 images will end in saved_acl2r
# rather than saved_acl2.  ACL2_HONS, ACL2_PAR, and ACL2_WAG (for
# feature write-arithmetic-goals) are similar (with suffixes h,
# p, and w, resp., rather than r), but for the experimental hons and parallel
# versions and the feature that writes out arithmetic lemma data to
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

# The following causes the calls of make that use it to continue past errors.
# Delete -i if you want to stop at first error and return non-zero exit status
# in that case; or, instead of editing the line below, supply ACL2_IGNORE=''
# on the make command line.
ACL2_IGNORE = -i

# Avoid loading customization file.
export ACL2-CUSTOMIZATION = NONE

# The order of the files below is unimportant.

sources := axioms.lisp memoize.lisp hons.lisp boot-strap-pass-2.lisp\
           basis.lisp parallel.lisp translate.lisp\
           type-set-a.lisp linear-a.lisp\
           type-set-b.lisp linear-b.lisp\
           non-linear.lisp\
           rewrite.lisp simplify.lisp bdd.lisp\
           other-processes.lisp induct.lisp prove.lisp\
           proof-checker-a.lisp history-management.lisp defuns.lisp defthm.lisp\
           other-events.lisp ld.lisp proof-checker-b.lisp interface-raw.lisp\
           defpkgs.lisp

ifdef ACL2_HONS
	sources := $(sources) hons-raw.lisp memoize-raw.lisp
endif
ifdef ACL2_PAR
	sources := $(sources) multi-threading-raw.lisp parallel-raw.lisp
endif
# No change to sources for ACL2_WAG

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

.PHONY: protections
# Note: Removed line "chmod g+s saved" before the second chmod below, as it was
# causing errors in at least one environment.
protections:
	find . -type d | xargs chmod 775 
	# find . -type d | xargs chmod g+s
	find . -type f | xargs chmod 664 
	-chmod 775 *saved_acl2*
	chmod 775 doc/create-acl2-html 
	chmod 775 doc/create-acl2-texinfo

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
	rm -f acl2-fns.o acl2-fns.lbin acl2-fns.sbin acl2-fns.fasl acl2-fns.wfasl \
	  acl2-fns.fas acl2-fns.lib acl2-fns.sparcf acl2-fns.ufsl acl2-fns.x86f \
          acl2-fns.dfsl
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
# Keep this in sync with copy-workshop.
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

.PHONY: copy-workshops
copy-workshops:
# WARNING: Execute this from an ACL2 source directory.
# WARNING:  This should only be run after directory ${DIR} (hence ${DIR}/books) exists.
# See the comments for copy-distribution, and keep these in sync.  Use the same
# DIR for both.
	rm -f workxxx
	rm -f workyyy
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::copy-distribution "workyyy" "${CURDIR}" "${DIR}" "all-files-workshops.txt" t)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	${LISP} < workxxx
	chmod 777 workyyy
	./workyyy
	rm -f workxxx
	rm -f workyyy

.PHONY: copy-nonstd
copy-nonstd:
# WARNING: Execute this from an ACL2 source directory.
# WARNING:  This should only be run after directory ${DIR} (hence ${DIR}/books) exists.
# See the comments for copy-distribution, and keep these in sync.  Use the same
# DIR for both.
	rm -f workxxx
	rm -f workyyy
	echo '(load "init.lisp")' > workxxx
	echo '(acl2::copy-distribution "workyyy" "${CURDIR}" "${DIR}" "all-files-nonstd.txt" t)' >> workxxx
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

.PHONY: DOC HTML EMACS TEX

# See comment below about perhaps avoiding the TEX target.
DOC: HTML EMACS TEX

HTML:
	PREFIX=$(PREFIX) ; export PREFIX ; ACL2_SUFFIX=$(ACL2_SUFFIX) ; export ACL2_SUFFIX ; doc/create-acl2-html

EMACS: doc/write-acl2-texinfo.cert
	PREFIX=$(PREFIX) ; export PREFIX ; ACL2_SUFFIX=$(ACL2_SUFFIX) ; export ACL2_SUFFIX ; doc/create-acl2-texinfo

# Note: the TEX target, which builds a ps file, depends on texi2dvi
# and dvips.  These might not be present on some systems (but is
# present at UT CS and have been seen to be present on a Mac where
# Latex is installed).
TEX: doc/write-acl2-texinfo.cert
	PREFIX=$(PREFIX) ; export PREFIX ; ACL2_SUFFIX=$(ACL2_SUFFIX) ; export ACL2_SUFFIX ; doc/create-acl2-tex

doc/write-acl2-texinfo.cert: doc/write-acl2-texinfo.lisp
	echo '(value :q)' > doc/workxxx.write-acl2-texinfo
	echo '(lp)' >> doc/workxxx.write-acl2-texinfo
	echo '(certify-book "write-acl2-texinfo")' >> doc/workxxx.write-acl2-texinfo
	pushd doc ; (../${PREFIX}saved_acl2${ACL2_SUFFIX} < workxxx.write-acl2-texinfo) ; popd
	rm doc/workxxx.write-acl2-texinfo

.PHONY: clean
clean:
# Does not remove executable or corresponding scripts
# (since there could be many executables that one prefers not to delete),
# except for *osaved_acl2* files.
	rm -f *.o *#* *.c *.h *.data gazonk.* workxxx workyyy *.lib \
	  *.fasl *.fas *.sparcf *.ufsl *.dfsl \
	  *.d64fsl *.dx64fsl *.lx64fsl \
	  *.lx32fsl *.x86f *.o \
	  TAGS acl2-status.txt acl2r.lisp acl2-proclaims.lisp .acl2rc \
	  *osaved_acl2 *osaved_acl2.* \
	  *.log TMP*
	rm -rf saved
	rm -f doc/*.o doc/*#* doc/*.c doc/*.h doc/*.data doc/gazonk.* \
	   doc/workxxx doc/workyyy doc/*.lib \
	   doc/*.fasl doc/*.fas doc/*.sparcf doc/*.ufsl doc/*.dfsl \
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

# Certify books that are not up-to-date, but only those likely to be included
# in other books.
# NOTE:  None of the certify-books* targets use PREFIX.  They use saved_acl2
# (or for nonstd, saved_acl2r) in this directory by default, or one can
# provide an absolute pathname or a command on one's path that invokes ACL2.
# Success can generally be determined by checking for the absence of ** in the
# log.
.PHONY: certify-books
certify-books:
	cd books ; $(MAKE) $(ACL2_IGNORE)

# Certify books that are not up-to-date, even those less likely to be included
# in other books.  This does *not* certify the nonstd/ books.  It would be
# awkward to arrange for that here, because the ACL2 images are different;
# they might not even have the same prefix.  See target regression-nonstd.
# NOTE:  This target is for the developers, since not all books in the
# regression suite are necessarily distributed.
# Success can generally be determined by checking for the absence of ** in the
# log.
.PHONY: regression
regression:
	uname -a
	cd books ; $(MAKE) $(ACL2_IGNORE) all-plus

.PHONY: regression-fast
regression-fast:
	uname -a
	cd books ; pwd ; $(MAKE) $(ACL2_IGNORE) -f Makefile-fast

.PHONY: regression-nonstd
regression-nonstd:
	uname -a
	cd books/nonstd ; $(MAKE) $(ACL2_IGNORE) all-nonstd

# Certify main books from scratch.
.PHONY: certify-books-fresh
certify-books-fresh: clean-books
	$(MAKE) $(ACL2_IGNORE) certify-books

# Do regression tests from scratch.
# These targets are for developers (see comment for target regression).
# Success can generally be determined by checking for the absence of ** in the
# log.
.PHONY: regression-fresh regression-fast-fresh regression-nonstd-fresh
regression-fresh: clean-books
	$(MAKE) $(ACL2_IGNORE) regression
regression-fast-fresh: clean-books
	$(MAKE) $(ACL2_IGNORE) regression-fast
regression-nonstd-fresh: clean-books-nonstd
	$(MAKE) $(ACL2_IGNORE) regression-nonstd

# The following allows for a relatively short test, in response to a request
# from GCL maintainer Camm Maguire.
.PHONY: certify-books-short
certify-books-short:
	cd books ; $(MAKE) short-test

.PHONY: certify-books-test
certify-books-test: certify-books-fresh

# The next two targets can be used with certify-books-test to run the
# test with infix syntax output.  Just do

# make infix-init certify-books-test infix-fin >& make.log &

# If you want to do the certification twice, first with infix and then
# without, use
 
# make infix-init certify-books-test infix-fin certify-books-test >& make.log &

# To get the books certified while using infix printing we arrange for the
# connected directory to contain an init.lsp file which is not normally there.
# The init.lsp file we put there is just a symbolic link to our
# infix-patch.lisp which loads all the infix stuff.  If we do not want infix
# printing during the book certification, we must make sure to remove those
# init.lsp files, as done by infix-fin.  That also moves the .log and .out
# files to the ${ACL2_VERSION}/infix-logs/ subdirectory, where they overwrite the old
# files there, if any.

.PHONY: infix-init
infix-init:
	cd /projects/acl2/${ACL2_VERSION}/books ; \
	rm -f */init.lsp ; \
	rm -f *.log ; \
	rm -f public/*.cert ; \
	rm -f data-structures/*.cert ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch.lisp arithmetic/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch.lisp bdd/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch.lisp cowles/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch.lisp meta/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch.lisp nqthm/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch.lisp public/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch.lisp data-structures/init.lsp

.PHONY: infix-init10
infix-init10:
	cd /projects/acl2/${ACL2_VERSION}/books ; \
	rm -f */init.lsp ; \
	rm -f *.log ; \
	rm -f public/*.cert ; \
	rm -f data-structures/*.cert ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch-10.lisp arithmetic/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch-10.lisp bdd/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch-10.lisp cowles/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch-10.lisp meta/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch-10.lisp nqthm/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch-10.lisp public/init.lsp ; \
	ln -s /projects/acl2/${ACL2_VERSION}/infix-patch-10.lisp data-structures/init.lsp

.PHONY: infix-fin
infix-fin:
	rm -f /projects/acl2/${ACL2_VERSION}/infix-logs/*.* ; \
	cd /projects/acl2/${ACL2_VERSION}/books ; \
	cp *.log /projects/acl2/${ACL2_VERSION}/infix-logs/ ; \
	cp public/*.out /projects/acl2/${ACL2_VERSION}/infix-logs/ ; \
	cp data-structures/*.out /projects/acl2/${ACL2_VERSION}/infix-logs/ ; \
	rm -f */init.lsp

.PHONY: clean-doc
clean-doc:
	cd doc ; rm -f *.o *~* *#* TAGS *.c *.h *.data gazonk.* workxxx \
	  *.lbin *.sbin *.fasl *.wfasl *.fas *.lib *.sparcf *.ufsl *.x86f *.dfsl *.fn *.cert
	rm -rf doc/EMACS
	rm -rf doc/EMACS-old/
	rm -rf doc/HTML
	rm -rf doc/HTML-old
	rm -rf doc/TEX

.PHONY: clean-books
clean-books:
	cd books ; $(MAKE) $(ACL2_IGNORE) clean

.PHONY: clean-books-nonstd
clean-books-nonstd:
	cd books/nonstd ; $(MAKE) $(ACL2_IGNORE) clean-nonstd

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

# Consider "make test DOC" if running late at night.
.PHONY: test
test: full init certify-books-test proofs

# See comment for move-large:  i.e., avoid using Allegro for this
# target, since move-large will not move the .dxl file (similarly
# for cmulisp, SBCL, and CLISP).
.PHONY: big-test
big-test: full init DOC move-large certify-books-test proofs

# See comment for move-large:  i.e., avoid using Allegro for this
# target, since move-large will not move the .dxl file (similarly
# for cmulisp, SBCL, and CLISP).
arch: full init move-large regression-fresh proofs

.PHONY: mini-proveall
mini-proveall:
	@rm -rf mini-proveall.out
	@echo '(value :q) (lp) (mini-proveall)' | ./${PREFIXsaved_acl2} > mini-proveall.out
	@(grep '^ ORDERED-SYMBOL-ALISTP-REMOVE-FIRST-PAIR-TEST' mini-proveall.out > /dev/null) || \
	(echo 'Mini-proveall failed!' ; ls -l ./${PREFIXsaved_acl2}; cat mini-proveall.out ; exit 1)
	@echo 'Mini-proveall passed.'

.PHONY: small
small:
	@echo 'Target "small" is no longer supported.  Use "make large" or simply "make".'
	exit 1

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

# Developer target only:
.PHONY: update-books
update-books:
	@update-books.csh

# Developer target only.  WARNING: Be sure to run "make regression"
# first!  We could add a dependency on regression, but maybe there
# will be some case in which we know part of the regression fails but
# we want to run this anyhow and it would get in the way to have a
# regression failure (though I don't know how that might happen).
.PHONY: chk-include-book-worlds
chk-include-book-worlds:
	uname -a
	cd books ; $(MAKE) $(ACL2_IGNORE) chk-include-book-worlds-top
