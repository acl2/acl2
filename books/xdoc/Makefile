include ../Makefile-generic
-include Makefile-deps

BOOKS := $(filter-out acl2-customization,$(BOOKS))

# This is really gross.
COMPILE_FLG := t :ttags :all

all: manual/success.txt TAGS

manual/success.txt: top.cert Makefile-trans $(wildcard *.xsl) xdoc.css frames.html make-manual.lsp
	rm -rf manual
	mkdir manual
	$(ACL2) < make-manual.lsp > make-manual.out

TAGS: $(wildcard *.lisp)
	etags *.lisp


.PHONY: moreclean
moreclean:
	rm -f .fmt-to-chars.tmp TAGS
	rm -rf manual

clean: moreclean
