include ../Makefile-generic
-include Makefile-deps

BOOKS := $(filter-out acl2-customization,$(BOOKS))

# This is really gross.
COMPILE_FLG := t :ttags :all

# Commenting out TAGS just below to avoid an error we've seen on Windows with etags missing:
# all: manual/success.txt TAGS
all: manual/success.txt

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
