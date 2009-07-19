include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Dependencies:

bdd-mgr.cert: bdd-mgr.lisp

bdd-prf.cert: bdd-prf.lisp
bdd-prf.cert: bdd-spec.cert

bdd-spec.cert: bdd-spec.lisp
bdd-spec.cert: bdd-mgr.cert
