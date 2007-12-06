include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2
 
# Dependencies:
 
basic.cert: basic.lisp
basic.cert: ../support/merge.cert
basic.cert: ../support/rewrite-theory.cert

bits.cert: bits.lisp
bits.cert: ../support/merge.cert
bits.cert: ../support/rewrite-theory.cert

brat.cert: brat.lisp
brat.cert: ../support/fp.cert

fadd.cert: fadd.lisp
fadd.cert: ../support/fadd/add3.cert
fadd.cert: float.cert
fadd.cert: bits.cert

float.cert: float.lisp
float.cert: ../support/proofs.cert

reps.cert: reps.lisp
reps.cert: ../support/proofs.cert
reps.cert: float.cert

round.cert: round.lisp
round.cert: ../support/proofs.cert
round.cert: float.cert

top.cert: top.lisp
top.cert: basic.cert
top.cert: bits.cert
top.cert: float.cert
top.cert: round.cert
top.cert: reps.cert
top.cert: fadd.cert
top.cert: ../support/fp.cert
top.cert: brat.cert
