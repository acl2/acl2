include ../Makefile-generic
-include Makefile-deps

# We skip some books for "make fasl" etc., i.e., for
# compiling already-certified books:
# - dft-ex.acl2 specifies no compilation
# - getprop.lisp: got stack overflow, probably not surprising given (comp t) in book
BOOKS_SKIP_COMP := dft-ex getprop
