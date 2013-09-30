include ../Makefile-generic

# Note: Because of #+gcl and #-gcl readtime conditionals, "make o" for
# a GCL-based ACL2 will report uncertified books when certification
# was done with an ACL2 based on a different host Lisp -- and, vice
# versa (for "make fasl" etc.).  This seems like a reasonably harmless
# state of affairs, however.

BOOKS := $(filter-out acl2-customization,$(BOOKS))

-include Makefile-deps

serialize.cert: serialize-raw.lsp

clean: clean-sao

clean-sao:
	rm -f test.sao
