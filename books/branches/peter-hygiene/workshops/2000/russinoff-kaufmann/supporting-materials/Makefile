include ../../../../Makefile-generic


# Dependencies:

constants.cert: constants.lisp
constants.cert: ../../../../rtl/rel1/lib3/top.cert
constants.cert: exec.cert
constants.cert: declarations.cert

declarations.cert: declarations.lisp
declarations.cert: ../../../../rtl/rel1/lib3/top.cert

exec.cert: exec.lisp
exec.cert: ../../../../rtl/rel1/lib3/top.cert

inputs.cert: inputs.lisp
inputs.cert: ../../../../rtl/rel1/lib3/top.cert
inputs.cert: model.cert

main.cert: main.lisp
main.cert: ../../../../rtl/rel1/lib3/top.cert
main.cert: constants.cert
main.cert: inputs.cert
main.cert: pipe.cert

model.cert: model.lisp
model.cert: ../../../../rtl/rel1/lib3/top.cert

pipe.cert: pipe.lisp
pipe.cert: ../../../../rtl/rel1/lib3/top.cert
pipe.cert: model.cert
pipe.cert: constants.cert
pipe.cert: inputs.cert
