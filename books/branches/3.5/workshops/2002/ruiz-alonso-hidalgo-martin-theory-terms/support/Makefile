# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Dependencies:

anti-unification.cert: anti-unification.lisp
anti-unification.cert: subsumption.cert

basic.cert: basic.lisp

lattice-of-terms.cert: lattice-of-terms.lisp
lattice-of-terms.cert: subsumption-well-founded.cert
lattice-of-terms.cert: mg-instance.cert
lattice-of-terms.cert: anti-unification.cert

matching.cert: matching.lisp
matching.cert: terms.cert

mg-instance.cert: mg-instance.lisp
mg-instance.cert: renamings.cert
mg-instance.cert: unification.cert

renamings.cert: renamings.lisp
renamings.cert: subsumption.cert

subsumption-definition-v0.cert: subsumption-definition-v0.lisp
subsumption-definition-v0.cert: terms.cert

subsumption.cert: subsumption.lisp
subsumption.cert: matching.cert
subsumption.cert: terms.cert
subsumption.cert: ../../../../ordinals/e0-ordinal.cert

subsumption-subst.cert: subsumption-subst.lisp
subsumption-subst.cert: subsumption.cert

subsumption-well-founded.cert: subsumption-well-founded.lisp
subsumption-well-founded.cert: renamings.cert
subsumption-well-founded.cert: subsumption.cert
subsumption-well-founded.cert: ../../../../ordinals/ordinals-without-arithmetic.cert

terms.cert: terms.lisp
terms.cert: basic.cert

unification.cert: unification.lisp
unification.cert: subsumption-subst.cert
unification.cert: unification-pattern.cert

unification-pattern.cert: unification-pattern.lisp
unification-pattern.cert: subsumption-subst.cert
unification-pattern.cert: ../../../../ordinals/e0-ordinal.cert

#==============================================================================
