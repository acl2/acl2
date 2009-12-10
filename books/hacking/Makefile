include ../Makefile-generic
-include Makefile-deps

# Note: Because of Lisp-specific readtime conditionals in
# evalable-ld-printing.lisp (e.g., search for `gcl'), "make o" and
# such using one host Lisp may report uncertified books when
# certification was done with an ACL2 based on a different host Lisp.
# This seems like a reasonably harmless state of affairs, however.

# Override (ignore harmless warning printed by "make"):

chk-include-book-worlds:
	@echo "Note: Skipping chk-include-book-worlds."
