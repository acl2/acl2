include ../../../../Makefile-generic

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
