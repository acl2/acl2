#ACL2_SYSTEM_BOOKS = /Users/smn4/software/acl2/v4-1/acl2-sources/books
#ACL2 = $(ACL2_SYSTEM_BOOKS)/../saved_acl2h
include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS = extra sets fast-lists bdd-functions top

extra.cert: extra.lisp
extra.cert: $(ACL2_SYSTEM_BOOKS)/misc/hons-help2.cert

sets.cert: sets.lisp
sets.cert: extra.cert

fast-lists.cert: fast-lists.lisp
fast-lists.cert: extra.cert

bdd-functions.cert: bdd-functions.lisp
bdd-functions.cert: sets.cert

top.cert: top.lisp
top.cert: sets.cert
top.cert: fast-lists.cert
top.cert: bdd-functions.cert
