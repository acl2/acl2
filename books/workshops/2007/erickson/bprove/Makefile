# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS = ../../../../

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# Pasted in from "make dependencies":



gen.cert: gen.lisp
bash.cert: bash.lisp

# sub.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert

refute.cert: refute.lisp
refute.cert: bash.cert

lemgen.cert: lemgen.lisp
lemgen.cert: refute.cert
lemgen.cert: gen.cert

exdefs.cert: exdefs.lisp
exdefs.cert: lemgen.cert