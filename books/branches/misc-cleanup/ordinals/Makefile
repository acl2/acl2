include ../Makefile-generic

#Put dependencies (from `make -s dependencies, or other sources) below

e0-ordinal.cert: e0-ordinal.lisp
e0-ordinal.cert: ordinal-definitions.cert
e0-ordinal.cert: ordinal-isomorphism.cert

lexicographic-ordering.cert: lexicographic-ordering.lisp
lexicographic-ordering.cert: ordinals.cert

limits.cert: limits.lisp
limits.cert: ordinal-exponentiation.cert
limits.cert: top-with-meta.cert

ordinal-addition.cert: ordinal-addition.lisp
ordinal-addition.cert: ordinal-basic-thms.cert
ordinal-addition.cert: top-with-meta.cert

ordinal-basic-thms.cert: ordinal-basic-thms.lisp
ordinal-basic-thms.cert: ordinal-total-order.cert
ordinal-basic-thms.cert: top-with-meta.cert

ordinal-counter-examples.cert: ordinal-counter-examples.lisp
ordinal-counter-examples.cert: ordinal-definitions.cert

ordinal-definitions.cert: ordinal-definitions.lisp

ordinal-exponentiation.cert: ordinal-exponentiation.lisp
ordinal-exponentiation.cert: ordinal-multiplication.cert
ordinal-exponentiation.cert: top-with-meta.cert

ordinal-isomorphism.cert: ordinal-isomorphism.lisp
ordinal-isomorphism.cert: ordinal-addition.cert
ordinal-isomorphism.cert: top-with-meta.cert

ordinal-multiplication.cert: ordinal-multiplication.lisp
ordinal-multiplication.cert: ordinal-addition.cert
ordinal-multiplication.cert: top-with-meta.cert

ordinal-total-order.cert: ordinal-total-order.lisp
ordinal-total-order.cert: ordinal-definitions.cert

ordinals-without-arithmetic.cert: ordinals-without-arithmetic.lisp
ordinals-without-arithmetic.cert: limits.cert

ordinals.cert: ordinals.lisp
ordinals.cert: top-with-meta.cert
ordinals.cert: limits.cert

proof-of-well-foundedness.cert: proof-of-well-foundedness.lisp
proof-of-well-foundedness.cert: proof-of-well-foundedness.acl2

top-with-meta.cert: top-with-meta.lisp
top-with-meta.cert: ../arithmetic/top-with-meta.cert
