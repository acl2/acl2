include ../Makefile-generic
-include Makefile-deps

BOOKS := $(filter-out acl2-customization,$(BOOKS))

all: make-manual.out TAGS

make-manual.out: top.cert Makefile-trans $(wildcard *.xsl) xdoc.css frames.html make-manual.lsp
	$(ACL2) < make-manual.lsp > make-manual.out

TAGS: $(wildcard *.lisp)
	etags *.lisp