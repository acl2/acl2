include ../Makefile-generic
-include Makefile-deps

BOOKS := $(filter-out acl2-customization,$(BOOKS))

all: make-manual.out

make-manual.out: top.cert
	$(ACL2) < make-manual.lsp > make-manual.out