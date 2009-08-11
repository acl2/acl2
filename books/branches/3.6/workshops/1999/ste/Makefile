include ../../../Makefile-generic


# Dependencies:

assertion.cert: assertion.lisp
assertion.cert: trajectory.cert

boolean.cert: boolean.lisp
boolean.cert: util.cert

circuit.cert: circuit.lisp
circuit.cert: expression.cert

example.cert: example.lisp
example.cert: inference.cert

expression.cert: expression.lisp
expression.cert: run.cert

fundamental.cert: fundamental.lisp
fundamental.cert: lemma-4.cert

inference.cert: inference.lisp
inference.cert: fundamental.cert

lemma-4.cert: lemma-4.lisp
lemma-4.cert: assertion.cert

run.cert: run.lisp
run.cert: state.cert

state.cert: state.lisp
state.cert: boolean.cert

trajectory.cert: trajectory.lisp
trajectory.cert: circuit.cert

util.cert: util.lisp
util.cert: ../../../data-structures/utilities.cert
util.cert: ../../../data-structures/list-theory.cert
util.cert: ../../../arithmetic/top-with-meta.cert
