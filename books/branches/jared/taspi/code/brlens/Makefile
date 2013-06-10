include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS = brlens trees-with-brlens

brlens.cert: brlens.lisp
brlens.cert: ../gen-helper/extra.cert

trees-with-brlens.cert: trees-with-brlens.lisp
trees-with-brlens.cert: brlens.cert
trees-with-brlens.cert: ../gen-trees/tree-predicates.cert

