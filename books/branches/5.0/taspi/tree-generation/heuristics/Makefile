include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))
BOOKS = spr tbr do-search

spr.cert: spr.lisp
spr.cert: ../tree-gen-helper/basics.cert
spr.cert: ../../code/tree-manip/top.cert

tbr.cert: tbr.lisp
tbr.cert: spr.cert

do-search.cert: do-search.lisp
do-search.cert: tbr.cert

