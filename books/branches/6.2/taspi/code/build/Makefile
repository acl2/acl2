include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS = build-term build-term-guards

build-term.cert: build-term.lisp
build-term.cert: ../fringes/fringes.cert

build-term-guards.cert: build-term-guards.lisp
build-term-guards.cert: build-term.cert
build-term-guards.cert: ../fringes/fringes-guards.cert

