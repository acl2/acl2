include ../../../../Makefile-generic

# Turn on warnings output but suppress summary, in order to be able to compare output.
INHIBIT = (assign inhibit-output-lst (list (quote prove) (quote proof-tree) (quote observation) (quote event)  (quote summary)))

# We skip some books for "make fasl" etc., i.e., for compiling
# already-certified books, because their .acl2 files specify no
# compilation.
BOOKS_SKIP_COMP := rhs1-iff rhs1 rhs2 warnings

# Pasted in from "make dependencies":

austel.cert: austel.lisp

greve1.cert: greve1.lisp

greve2.cert: greve2.lisp

greve3.cert: greve3.lisp

mini-proveall-plus.cert: mini-proveall-plus.lisp
mini-proveall-plus.cert: mini-proveall.cert

mini-proveall.cert: mini-proveall.lisp

rhs1-iff.cert: rhs1-iff.lisp
rhs1-iff.cert: rhs1-iff.acl2

rhs1.cert: rhs1.lisp
rhs1.cert: rhs1.acl2

rhs2.cert: rhs2.lisp
rhs2.cert: rhs2.acl2

smith1.cert: smith1.lisp

sumners1.cert: sumners1.lisp

warnings.cert: warnings.lisp
warnings.cert: warnings.acl2

