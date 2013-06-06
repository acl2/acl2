include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS = btrees btrees-bdds btrees-bdds-sets \
	app-rev-lists sets-lists-trees tree-predicates \
	top

btrees.cert: btrees.lisp
btrees.cert: ../gen-helper/fast-lists.cert
btrees.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
btrees.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert

btrees-bdds.cert: btrees-bdds.lisp
btrees-bdds.cert: ../gen-helper/extra.cert
btrees-bdds.cert: btrees.cert
btrees-bdds.cert: ../gen-helper/bdd-functions.cert

btrees-bdds-sets.cert: btrees-bdds-sets.lisp
btrees-bdds-sets.cert: btrees-bdds.cert
btrees-bdds-sets.cert: sets-lists-trees.cert

app-rev-lists.cert: app-rev-lists.lisp
app-rev-lists.cert: sets-lists-trees.cert

sets-lists-trees.cert: sets-lists-trees.lisp
sets-lists-trees.cert: ../gen-helper/sets.cert
sets-lists-trees.cert: ../gen-helper/fast-lists.cert
sets-lists-trees.cert: tree-predicates.cert

tree-predicates.cert: tree-predicates.lisp
tree-predicates.cert: ../gen-helper/extra.cert
tree-predicates.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert

top.cert: top.lisp
top.cert: btrees-bdds-sets.cert
top.cert: app-rev-lists.cert
top.cert: sets-lists-trees.cert
top.cert: tree-predicates.cert
