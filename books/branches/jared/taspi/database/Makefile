include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS = props entry db filters db-from-list


props.cert: props.lisp
props.cert: ../code/gen-trees/sets-lists-trees.cert
props.cert: ../code/gen-trees/app-rev-lists.cert
props.cert: ../code/tree-manip/sort-help.cert
props.cert: $(ACL2_SYSTEM_BOOKS)/misc/hons-help2.cert

entry.cert: entry.lisp
entry.cert: props.cert

db.cert: db.lisp
db.cert: entry.cert
db.cert: ../code/tree-manip/top.cert

filters.cert: filters.lisp
filters.cert: db.cert

db-from-list.cert: db-from-list.lisp
