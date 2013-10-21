include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))
BOOKS = taxa-based tree-stats


taxa-based.cert: taxa-based.lisp
taxa-based.cert: ../code/fringes/fringes-guards.cert
taxa-based.cert: ../code/tree-manip/merge-based-sort.cert
taxa-based.cert: ../code/tree-manip/mv-root.cert

tree-stats.cert: tree-stats.lisp
tree-stats.cert: ../code/gen-trees/sets-lists-trees.cert
tree-stats.cert: taxa-based.cert
