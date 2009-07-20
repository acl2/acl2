include ../../../../../Makefile-generic


BOOKS = defstobj+ fib-def partial-clock-functions tiny tiny-rewrites

defstobj+.cert: defstobj+.lisp

fib-def.cert: fib-def.lisp
fib-def.cert: tiny.cert

partial-clock-functions.cert: partial-clock-functions.lisp
partial-clock-functions.cert: tiny-rewrites.cert
partial-clock-functions.cert: fib-def.cert

tiny.cert: tiny.lisp
tiny.cert: defstobj+.cert

tiny-rewrites.cert: tiny-rewrites.lisp
tiny-rewrites.cert: tiny.cert
