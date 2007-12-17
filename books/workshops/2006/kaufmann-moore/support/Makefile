# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS = ../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# Turn on warnings output but suppress summary, in order to be able to compare output.
INHIBIT = (assign inhibit-output-lst (list (quote prove) (quote proof-tree) (quote observation) (quote event)  (quote summary)))

# Pasted in from "make dependencies":

austel.cert: austel.lisp

greve1.cert: greve1.lisp

greve2.cert: greve2.lisp

greve3.cert: greve3.lisp

mini-proveall-plus.cert: mini-proveall-plus.lisp
mini-proveall-plus.cert: mini-proveall.cert

mini-proveall.cert: mini-proveall.lisp

rhs1-iff.cert: rhs1-iff.lisp
rhs1-iff.cert: rhs1-iff.acl2

rhs1.cert: rhs1.lisp
rhs1.cert: rhs1.acl2

rhs2.cert: rhs2.lisp
rhs2.cert: rhs2.acl2

smith1.cert: smith1.lisp

sumners1.cert: sumners1.lisp

warnings.cert: warnings.lisp
warnings.cert: warnings.acl2

