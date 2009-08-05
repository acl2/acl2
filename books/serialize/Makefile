include ../Makefile-generic

# Avoid serialize-tests.lisp since "make o" and such won't work
# properly when certification and subsequent compilation take place
# for different Lisps.

# BOOKS := $(filter-out acl2-customization,$(BOOKS))
BOOKS := serialize

-include Makefile-deps

serialize.cert: serialize-raw.lsp

clean: clean-sao

clean-sao:
	rm -f test.sao
