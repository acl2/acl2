include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS = consensus tree-compat tree-support-in-set mast \
	multipolar-loose greedy mct top

consensus.cert: consensus.lisp
consensus.cert: ../code/build/build-term-guards.cert
consensus.cert: ../code/gen-trees/btrees-bdds.cert
consensus.cert: ../code/fringes/fringes-props.cert

tree-compat.cert: tree-compat.lisp
tree-compat.cert: ../code/build/build-term-guards.cert
tree-compat.cert: ../code/gen-trees/btrees-bdds.cert
tree-compat.cert: ../code/fringes/fringes-props.cert

tree-support-in-set.cert: tree-support-in-set.lisp
tree-support-in-set.cert: ../code/build/build-term-guards.cert

mast.cert: mast.lisp
mast.cert: ../single-input/taxa-based.cert

multipolar-loose.cert: multipolar-loose.lisp
multipolar-loose.cert: consensus.cert

greedy.cert: greedy.lisp
greedy.cert: consensus.cert

mct.cert: mct.lisp
mct.cert: mast.cert
mct.cert: ../code/build/build-term-guards.cert

top.cert: top.lisp
top.cert: consensus.cert
top.cert: tree-compat.cert
top.cert: tree-support-in-set.cert
top.cert: mast.cert
top.cert: multipolar-loose.cert
top.cert: greedy.cert
top.cert: mct.cert

