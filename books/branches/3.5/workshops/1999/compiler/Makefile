include ../../../Makefile-generic

ACL2 = ../../../../saved_acl2

# Dependencies:

compiler.cert: compiler.lisp
compiler.cert: machine.cert

evaluator.cert: evaluator.lisp
evaluator.cert: compiler.cert
evaluator.cert: ../../../ordinals/e0-ordinal.cert

exercises.cert: exercises.lisp
exercises.cert: compiler.cert

machine.cert: machine.lisp
machine.cert: ../../../ordinals/e0-ordinal.cert

proof1.cert: proof1.lisp
proof1.cert: evaluator.cert
proof1.cert: ../../../arithmetic/equalities.cert

proof.cert: proof.lisp
proof.cert: proof1.cert
proof.cert: ../../../ordinals/e0-ordinal.cert
