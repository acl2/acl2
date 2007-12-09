include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2
 
# Dependencies:
 
add.cert: add.lisp
add.cert: divsqrt.cert
add.cert: logxor-lemmas.cert
add.cert: rnd.cert

away.cert: away.lisp
away.cert: trunc.cert

basic.cert: basic.lisp
basic.cert: fp.cert

divsqrt.cert: divsqrt.lisp
divsqrt.cert: odd.cert
divsqrt.cert: loglemmas.cert

float.cert: float.lisp
float.cert: basic.cert
float.cert: x-2xx.cert

floor.cert: floor.lisp
floor.cert: basic.cert

fp.cert: fp.lisp
fp.cert: ../../../ihs/ihs-definitions.cert
fp.cert: ../../../ihs/ihs-lemmas.cert

logdefs.cert: logdefs.lisp
logdefs.cert: floor.cert

loglemmas.cert: loglemmas.lisp
loglemmas.cert: logdefs.cert

logxor-def.cert: logxor-def.lisp
logxor-def.cert: floor.cert

logxor-lemmas.cert: logxor-lemmas.lisp
logxor-lemmas.cert: logxor-def.cert
logxor-lemmas.cert: loglemmas.cert

merge.cert: merge.lisp
merge.cert: proofs.cert

near.cert: near.lisp
near.cert: away.cert

odd.cert: odd.lisp
odd.cert: near.cert

proofs.cert: proofs.lisp
proofs.cert: basic.cert
proofs.cert: x-2xx.cert
proofs.cert: float.cert
proofs.cert: trunc.cert
proofs.cert: away.cert
proofs.cert: near.cert
proofs.cert: odd.cert
proofs.cert: floor.cert
proofs.cert: logdefs.cert
proofs.cert: loglemmas.cert
proofs.cert: divsqrt.cert
proofs.cert: logxor-def.cert
proofs.cert: logxor-lemmas.cert
proofs.cert: reps.cert
proofs.cert: sticky.cert
proofs.cert: rnd.cert
proofs.cert: add.cert

reps.cert: reps.lisp
reps.cert: logdefs.cert
reps.cert: float.cert

rewrite-theory.cert: rewrite-theory.lisp

rnd.cert: rnd.lisp
rnd.cert: sticky.cert

sticky.cert: sticky.lisp
sticky.cert: divsqrt.cert

trunc.cert: trunc.lisp
trunc.cert: float.cert

x-2xx.cert: x-2xx.lisp
x-2xx.cert: ../../../arithmetic/top.cert
