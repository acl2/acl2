include ../Makefile-generic

.PHONY: doc

-include Makefile-deps

doc: top.cert
	rm -rf doc
	mkdir doc
	echo '(ld "../doc/write-acl2-html.lisp" :dir :system)' > doc/workxxx
	echo '(ld "../package.lsp")' >> doc/workxxx
	echo '(include-book "../top")' >> doc/workxxx
	echo '(write-html-file :topics (quote (STR::STR)) :pkg "STR")' >> doc/workxxx
	echo '(quit)' >> doc/workxxx
	cd doc; ACL2_SYSTEM_BOOKS=$(abspath $(ACL2_SYSTEM_BOOKS)) $(abspath $(ACL2)) < workxxx
	ls doc/acl2-doc-index.html
