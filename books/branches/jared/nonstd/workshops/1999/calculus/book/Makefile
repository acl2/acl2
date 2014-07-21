include ../../../../../Makefile-generic

# Avoid provisional certification since we are not using Makefile-deps.
override ACL2_PCERT =

ACL2 = ../../../../../../saved_acl2r

include Makefile-essence 

nsa.cert: nsa.lisp
nsa.cert: ../../../../nsa/nsa.cert

top-with-meta.cert: top-with-meta.lisp
top-with-meta.cert: ../../../../../arithmetic/top-with-meta.cert

proof-outline.lisp: tree.lisp
