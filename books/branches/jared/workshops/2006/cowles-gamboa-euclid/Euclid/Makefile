include ../../../../Makefile-generic

# Note that ed5ba.lisp has been renamed to ed5ba.lsp, because it
# depends on ACL2(r).

# We skip all books for "make fasl" etc., i.e., for compiling
# already-certified books, because some .acl2 files specify no
# compilation, including ed3.acl2, and many books depend on ed3.
BOOKS_SKIP_COMP := $(BOOKS)

-include Makefile-deps
