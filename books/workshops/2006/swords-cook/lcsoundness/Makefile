# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS = ../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# Pasted in from "make dependencies":
LambdaCalcBasis.cert: LambdaCalcBasis.lisp
LambdaCalcBasis.cert: defsum.cert
LambdaCalcBasis.cert: defsum-thms.cert
# LambdaCalcBasis.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-theory.cert

LambdaCalcSoundness.cert: LambdaCalcSoundness.lisp
LambdaCalcSoundness.cert: LambdaCalcBasis.cert

defsum-thms.cert: defsum-thms.lisp
# defsum-thms.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert

defsum.cert: defsum.lisp
defsum.cert: pattern-match.cert

pattern-match.cert: pattern-match.lisp
