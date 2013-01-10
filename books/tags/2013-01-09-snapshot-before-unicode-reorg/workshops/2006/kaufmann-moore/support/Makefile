include ../../../../Makefile-generic

# Turn on warnings output but suppress summary, in order to be able to compare output.
INHIBIT = (assign inhibit-output-lst (list (quote prove) (quote proof-tree) (quote observation) (quote event)  (quote summary)))

# We skip some books for "make fasl" etc., i.e., for compiling
# already-certified books, because their .acl2 files specify no
# compilation.
BOOKS_SKIP_COMP := rhs1-iff rhs1 rhs2 warnings

-include Makefile-deps
