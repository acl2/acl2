# Copyright (C) 2014, ForrestHunt, Inc.
# Written by Matt Kaufmann, November, 2014
# License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

# The toothbrush is not part of the normal regression, because a lisp
# must be specified.  That lisp is currently required to be CCL or
# SBCL, because these compile on-the-fly and we load ACL2 source
# files, not compiled files -- though that restriction could possibly
# be removed.

# The next variable specifies the Lisp we will use.  We use LISP since
# that is the name used in the main ACL2 GNUmakefile; indeed, that
# value should be able to override this one.
LISP ?= ccl

# For example:
# make ACL2=/Users/kaufmann/acl2/acl2/saved_acl2h

ifneq ($(ACL2),)
ACL2_SYSTEM_BOOKS ?= $(dir $(ACL2))books
endif

# Note that ACL2 is typically set by the top-level GNUmakefile for a
# regression, but when using books/GNUmakefile directly, ACL2 is acl2
# by default.  If using cert.pl directly, then this directory will be
# skipped -- one must invoke this Makefile.

success.txt: defined-syms.lsp make-toothbrush.cert
	@(cd tests ; $(MAKE)) || \
	  (echo "`pwd`/$@: **CERTIFICATION FAILED**"; exit 1)
	@echo "Tests passed." > success.txt

# Note that ACL2_SYSTEM_BOOKS is what defines BOOKS_CERT.
ifneq ($(ACL2_SYSTEM_BOOKS),)
include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
-include Makefile-deps
endif

defined-syms.lsp: load-toothbrush.lsp make-defined-syms.lsp
ifeq ($(ACL2),)
	@echo "ERROR: Environment (or make) variable ACL2 must be defined."
	@echo "       It needs to be set to a file whose directory contains"
	@echo "       relevant ACL2 source files."
	@exit 1
else
	@echo '(defparameter COMMON-LISP-USER::*acl2-dir* "$(dir $(ACL2))") (load "make-defined-syms.lsp") (acl2::exit-lisp)' \
	  | $(LISP) > $@.out
	@echo "Created $@"
endif

# We don't bother with a target for making make-toothbrush.cert, since
# such certification is not necessary.

clean: clean-extras clean-tests

.PHONY: clean-extras clean-tests

clean-extras:
	rm -f defined-syms.lsp
	rm -f success.txt

clean-tests:
	cd tests ; $(MAKE) clean
