include ../../../Makefile-generic

ACL2 = ../../../../saved_acl2

# Dependencies:

arity.cert: arity.lisp
arity.cert: syntax.cert

de4.cert: de4.lisp
de4.cert: sts-okp.cert

examples.cert: examples.lisp
examples.cert: de4.cert

help-defuns.cert: help-defuns.lisp

measure.cert: measure.lisp
measure.cert: help-defuns.cert
measure.cert: ../../../ordinals/e0-ordinal.cert

primitives.cert: primitives.lisp
primitives.cert: measure.cert

sts-okp.cert: sts-okp.lisp
sts-okp.cert: arity.cert

syntax.cert: syntax.lisp
syntax.cert: primitives.cert

thm-example.cert: thm-example.lisp
thm-example.cert: de4.cert 
