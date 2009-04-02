include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2
 
# Dependencies:
 
basic.cert: basic.lisp
basic.cert: ../support/proofs.cert

bits.cert: bits.lisp
bits.cert: ../support/proofs.cert

brat.cert: brat.lisp
brat.cert: ../support/fp.cert

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
top.cert: brat.cert
