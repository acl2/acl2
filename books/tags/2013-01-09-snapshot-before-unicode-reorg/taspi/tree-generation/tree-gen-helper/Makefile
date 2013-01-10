include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))
BOOKS = basics

basics.cert: basics.lisp
basics.cert: ../../code/build/build-term-guards.cert
basics.cert: ../../tree-score/pscores.cert
