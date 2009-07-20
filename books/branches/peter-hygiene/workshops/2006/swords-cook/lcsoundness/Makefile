include ../../../../Makefile-generic

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
