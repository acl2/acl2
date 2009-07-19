include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Dependencies:

base.cert: base.lisp
base.cert: util.cert

compile.cert: compile.lisp
compile.cert: pstate.cert
compile.cert: gensym-e.cert

cstate.cert: cstate.lisp
cstate.cert: expr.cert

expr.cert: expr.lisp
expr.cert: base.cert

gensym-e.cert: gensym-e.lisp

lstate.cert: lstate.lisp
lstate.cert: base.cert
lstate.cert: cstate.cert

mstate.cert: mstate.lisp
mstate.cert: cstate.cert
mstate.cert: pstate.cert
mstate.cert: lstate.cert

pstate.cert: pstate.lisp
pstate.cert: expr.cert

setup.cert: setup.lisp
setup.cert: mstate.cert

simulator.cert: simulator.lisp
simulator.cert: stepprocess.cert
simulator.cert: ../../../../arithmetic/mod-gcd.cert

stepproc0.cert: stepproc0.lisp
stepproc0.cert: mstate.cert

stepproc1.cert: stepproc1.lisp
stepproc1.cert: mstate.cert

stepproc2.cert: stepproc2.lisp
stepproc2.cert: setup.cert

stepprocess.cert: stepprocess.lisp
stepprocess.cert: stepproc1.cert
stepprocess.cert: stepproc2.cert
stepprocess.cert: stepproc0.cert

util.cert: util.lisp
