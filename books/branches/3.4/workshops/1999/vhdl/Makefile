include ../../../Makefile-generic

ACL2 = ../../../../saved_acl2

# Dependencies:

exercises.cert: exercises.lisp
exercises.cert: fact.cert

fact-proof.cert: fact-proof.lisp
fact-proof.cert: ../../../arithmetic/top.cert
fact-proof.cert: fact.cert

fact.cert: fact.lisp
fact.cert: vhdl.cert

vhdl.cert: vhdl.lisp
