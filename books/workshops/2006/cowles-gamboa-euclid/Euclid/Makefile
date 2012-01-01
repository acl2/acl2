include ../../../../Makefile-generic

# Omit ed5ba because it depends on ACL2(r):
BOOKS = ed1 ed2a ed2b ed3 ed4aa ed4ab ed4ba ed4bb ed4ca ed4cb ed4da ed4db ed5aa ed6a prime-fac

# We skip all books for "make fasl" etc., i.e., for compiling
# already-certified books, because some .acl2 files specify no
# compilation, including ed3.acl2, and many books depend on ed3.
BOOKS_SKIP_COMP := $(BOOKS)

-include Makefile-deps
