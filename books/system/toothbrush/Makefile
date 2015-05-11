# Copyright (C) 2014, ForrestHunt, Inc.
# Written by Matt Kaufmann, November, 2014
# License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

# The toothbrush is not part of the normal regression, because a lisp
# must be specified.  That lisp is currently required to be CCL or
# SBCL, because these compile on-the-fly and we load ACL2 source
# files, not compiled files -- though that restriction could possibly
# be removed.

# The next variable, TB_LISP, specifies the Lisp to be used.  We avoid
# using LISP since that is the name used in the main ACL2 GNUmakefile,
# and someone might set it without intending to run toothbrush tests.
# This variable must be set in order to run "make" with this Makefile.
# For regressions, books/GNUmakefile skips running "make" in this
# directory if TB_LISP is not defined.  To run directly in this
# directory, edit one the next lines or designate a Lisp executable
# for TB_LISP in the environment or on the command line.  As explained
# above, only CCL and SBCL are currently supported.

# TB_LISP ?= ccl
# TB_LISP ?= sbcl

# For example:
# make ACL2=/Users/kaufmann/acl2/acl2/saved_acl2 TB_LISP=ccl

ifneq ($(ACL2), $(notdir $(ACL2)))
ACL2_DIR := $(dir $(ACL2))
ACL2_SYSTEM_BOOKS ?= $(ACL2_DIR)books
else
ifneq ($(ACL2_SYSTEM_BOOKS), )
ACL2_DIR := $(dir $(ACL2_SYSTEM_BOOKS)/../)
endif
endif

# Note that ACL2 is typically set by the top-level GNUmakefile for a
# regression, but when using books/GNUmakefile directly, ACL2 is acl2
# by default.  If using cert.pl directly, then this directory will be
# skipped -- one must invoke this Makefile.

success.txt: acl2_check lisp_check defined-syms.lsp make-toothbrush.cert
	@(cd tests ; $(MAKE)) || \
	  (echo "`pwd`/$@: **CERTIFICATION FAILED**"; exit 1)
	@echo "Tests passed." > success.txt

.PHONY: acl2_check
acl2_check:
	@if [ "$(ACL2)" = "" ] ; then \
	echo "ERROR: Environment (or make) variable ACL2 must be";\
	echo "       defined.  It needs to be set to a pathname whose";\
	echo "       directory contains relevant ACL2 source files.";\
	exit 1 ;\
	fi
# The following test avoids failure to set ACL2_SYSTEM_BOOK suitably
# when, for example, specifying ACL2=acl2.
	@if [ "$(ACL2_SYSTEM_BOOKS)" = "" ] ; then \
	echo "ERROR: Environment (or make) variable ACL2_SYSTEM_BOOKS";\
	echo "       must be set.  This may happen automatically if ACL2";\
	echo "       is set not just to an executable, but to a pathname";\
	echo "       whose directory contains relevant ACL2 source files.";\
	exit 1 ;\
	fi
	@echo "Note: For toothbrush, ACL2_DIR = $(ACL2_DIR)."

.PHONY: lisp_check
lisp_check:
	@if [ "$(TB_LISP)" = "" ] ; then \
	echo "ERROR: Environment (or make) variable TB_LISP must be";\
	echo "       defined, to designate a Lisp executable.";\
	exit 1 ;\
	fi

# Note that ACL2_SYSTEM_BOOKS is what defines BOOKS_CERT.
ifneq ($(ACL2_SYSTEM_BOOKS), )
include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
-include Makefile-deps
endif

defined-syms.lsp: acl2_check lisp_check load-toothbrush.lsp make-defined-syms.lsp
	@echo '(defparameter COMMON-LISP-USER::*acl2-dir* "$(ACL2_DIR)") (load "make-defined-syms.lsp") (acl2::exit-lisp)' > workxxx.$@
	@($(TB_LISP) < workxxx.$@ 2>&1) > $@.out
	@echo "Created $@"

# We don't bother with a target for making make-toothbrush.cert, since
# such certification is not necessary.

clean: acl2_check clean-extras clean-tests

.PHONY: clean-extras clean-tests

clean-extras:
	rm -f defined-syms.lsp
	rm -f success.txt

clean-tests:
	cd tests ; $(MAKE) clean
