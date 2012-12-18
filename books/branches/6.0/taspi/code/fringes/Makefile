include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS = fringes fringes-guards fringes-props

fringes.cert: fringes.lisp
fringes.cert: ../gen-trees/sets-lists-trees.cert
fringes.cert: ../replete/replete.cert
fringes.cert: ../gen-trees/btrees-bdds.cert

fringes-guards.cert: fringes-guards.lisp
fringes-guards.cert: fringes.cert
fringes-guards.cert: ../replete/replete-guards.cert
fringes-guards.cert: ../gen-trees/btrees-bdds-sets.cert
fringes-guards.cert: ../gen-trees/app-rev-lists.cert

fringes-props.cert: fringes-props.lisp
fringes-props.cert: fringes-guards.cert
