# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
# ACL2_SYSTEM_BOOKS = /Research/ACL2/acl2-sources/books
ACL2_SYSTEM_BOOKS = ../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# Pasted in from "make dependencies":
bewijs.cert: bewijs.lisp

general.cert: general.lisp

paramod.cert: paramod.lisp
paramod.cert: weighting.cert

prover.cert: prover.lisp
prover.cert: general.cert
prover.cert: unification.cert
prover.cert: weighting.cert
prover.cert: resolution.cert
prover.cert: paramod.cert
prover.cert: bewijs.cert

resolution.cert: resolution.lisp
resolution.cert: general.cert
resolution.cert: unification.cert
resolution.cert: weighting.cert

unification.cert: unification.lisp
unification.cert: general.cert

weighting.cert: weighting.lisp
weighting.cert: unification.cert

