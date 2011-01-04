include ../Makefile-generic
-include Makefile-deps

BOOKS := $(filter-out acl2-customization,$(BOOKS))

# This is really gross.
COMPILE_FLG := t


top.cert: save.cert display.cert topics.cert defxdoc-raw.cert mkdir-raw.cert

# Commenting out TAGS just below to avoid an error we've seen on Windows with etags missing:
# all: manual/success.txt TAGS
all: manual/success.txt

manual/success.txt: top.cert $(wildcard support/*) make-manual.lsp
	rm -rf manual
	mkdir manual
	$(ACL2) < make-manual.lsp > make-manual.out

TAGS: $(wildcard *.lisp)
	etags *.lisp


.PHONY: moreclean
moreclean:
	rm -f .fmt-to-chars.tmp TAGS
	rm -rf manual
	rm -rf *.time

clean: moreclean
