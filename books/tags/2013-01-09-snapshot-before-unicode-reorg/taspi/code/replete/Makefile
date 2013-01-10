include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS = replete-helper replete replete-guards

replete-helper.cert: replete-helper.lisp
replete-helper.cert: ../gen-trees/sets-lists-trees.cert

replete.cert: replete.lisp
replete.cert: replete-helper.cert

replete-guards.cert: replete-guards.lisp
replete-guards.cert: replete.cert
replete-guards.cert: ../brlens/trees-with-brlens.cert

