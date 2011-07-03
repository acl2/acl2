# ACL2 ?= ../../acl2/saved_acl2
# include ../../acl2/books/Makefile-generic
#
# # Dependencies:
#
# BOOKS := $(filter-out acl2-customization,$(BOOKS))
# COMPILE_FLG := t :ttags :all :skip-proofs-okp t
#
# LISPFILES = $(wildcard *.lisp)
# LSPFILES = $(wildcard *.lsp)
# ACL2FILES = $(wildcard *.acl2)
#
# TAGS: $(LISPFILES)
# 	etags *.lisp
#
# -include Makefile-deps


.PHONY: all regression full clean TAGS

all:
	@echo "Use cert.pl to build"
	@echo "Or use 'make full', which runs 'cert.pl -j 8' to build VL,"
	@echo "the VL Server, and VL-Prove and runs some regressions."
	@echo ""

allbooks:
	cert.pl -j 8 top.cert \
                     server/top.cert \
                     ../vl-prove/vl-prove.cert \
                     ../vl-equiv/vl-equiv.cert \
                     lint/lint.cert

full: allbooks
	cd regression; $(MAKE) clean
	cd regression; $(MAKE) all

TAGS:
	@echo "Building TAGS"
	etags `find . -name "*.lisp"` `find . -name "*.lsp"` `find . -name "*.acl2"`

regression:
	@echo "Running regression tests."
	cd regression; $(MAKE) clean
	cd regression; $(MAKE) all

CLEANFILES := *.cert *.lx64fsl *.out *.time *~

clean:
	rm -f $(CLEANFILES) TAGS 
	cd loader; rm -f $(CLEANFILES)
	cd util; rm -f $(CLEANFILES)
	cd transforms; rm -f $(CLEANFILES)
	cd transforms/occform; rm -f $(CLEANFILES)
	cd checkers; rm -f $(CLEANFILES)
	cd mlib; rm -f $(CLEANFILES)
	cd server; rm -f $(CLEANFILES)
	cd lint -f $(CLEANFILES)

