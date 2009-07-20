include ../../../../Makefile-generic

# Pasted in from "make dependencies":

bash.cert: bash.lisp

exdefs.cert: exdefs.lisp
exdefs.cert: lemgen.cert

gen.cert: gen.lisp

lemgen.cert: lemgen.lisp
lemgen.cert: refute.cert
lemgen.cert: gen.cert

refute.cert: refute.lisp
refute.cert: bash.cert
