cl-proc-top: top1 all
all: top1

# We avoid going into SULFA if the appropriate tool is not present.  The
# following is based on target "top" from ../Makefile-subdirs.

# Keep the minisat path below in sync with the definition of SAT_SOLVER in
# SULFA/Makefile.
.PHONY: top1
top1:
	@if [ -f ${PWD}/../../aux/minisat2/${HOSTTYPE}/minisat/core/minisat ] ; \
	then \
	(cd SULFA ; $(MAKE)) ; \
	my_status=$$? ; \
	if [ $$my_status -ne 0 ] ; then exit 1 ; fi ; \
	else \
	echo "*NOTE*: Skipping SULFA subdirectory (no SAT solver installed; see SULFA/README)." ; \
	fi
	@exit $$my_status

# Note that the call of $(MAKE) in support of target top1, above, deals with
# the SULFA directory.  It is tempting to include the Makefile-subdirs line in
# order to deal with compilation targets, e.g., supporting "make all-o" from
# the main books/ directory.  But some systems may skip certification of books
# under the SULFA directory.  Feel free to uncomment the Makefile-subdirs lines
# if you know that those books will be certified.  At any rate, we extend the
# clean target below to clean the SULFA directories whether or not the
# Makefile-subdirs line is uncommented.
DIRS = SULFA/books SULFA/c-files SULFA/scripts
# include ../Makefile-subdirs
include ../Makefile-generic

# Keep the following two targets, clean and clean-sulfa, in sync with the
# definitions of clean and clean-more in ../Makefile-subdirs above.  If the
# Makefile-subdirs line is uncommented above then the SULFA books will be
# cleaned twice, but there's no harm in that.

.PHONY: clean
clean: clean-sulfa

.PHONY: clean-sulfa
clean-sulfa:
	@for dir in $(DIRS) ; \
	do \
	if [ -f $$dir/Makefile ]; then \
	(cd $$dir ; \
	$(MAKE) clean ; \
	cd ..) ; \
	fi \
	done

# Dependencies:

-include Makefile-deps
