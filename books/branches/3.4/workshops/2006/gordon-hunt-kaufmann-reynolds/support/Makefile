# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS = ../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

BOOKS = data basic guarded stobjs

# Pasted in from "make dependencies":

basic.cert: basic.lisp
basic.cert: data.cert

data.cert: data.lisp
# data.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert

guarded.cert: guarded.lisp
guarded.cert: data.cert

script.cert: script.lisp
script.cert: basic.cert
script.cert: guarded.cert
script.cert: stobjs.cert

stobjs.cert: stobjs.lisp
stobjs.cert: data.cert
