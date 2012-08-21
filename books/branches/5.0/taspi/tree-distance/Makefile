include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))
BOOKS = rf symm-diff

rf.cert: rf.lisp
rf.cert: ../code/fringes/fringes-guards.cert
rf.cert: ../database/props.cert

symm-diff.cert: symm-diff.lisp
symm-diff.cert: ../code/fringes/fringes-guards.cert
symm-diff.cert: ../database/props.cert
