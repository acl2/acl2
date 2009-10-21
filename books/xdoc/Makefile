include ../Makefile-generic
-include Makefile-deps

BOOKS := $(filter-out acl2-customization,$(BOOKS))

all: make-manual.out

make-manual.out: top.cert Makefile-trans $(wildcard *.xsl) xdoc.css
	$(ACL2) < make-manual.lsp > make-manual.out