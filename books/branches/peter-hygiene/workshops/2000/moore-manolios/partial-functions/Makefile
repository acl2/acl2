include ../../../../Makefile-generic


# Dependencies:

defpun-original.cert: defpun-original.lisp

defpun.cert: defpun.lisp
# defpun.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert

examples.cert: examples.lisp
examples.cert: tjvm.cert
examples.cert: examples.acl2
examples.cert: tjvm.cert

mod-1-property.cert: mod-1-property.lisp
mod-1-property.cert: ../../../../ihs/quotient-remainder-lemmas.cert
mod-1-property.cert: ../../../../arithmetic/top-with-meta.cert

report.cert: report.lisp
report.cert: defpun.cert
report.cert: ../../../../ihs/quotient-remainder-lemmas.cert
report.cert: ../../../../arithmetic/top-with-meta.cert
report.cert: mod-1-property.cert
report.cert: tjvm-examples.cert

tjvm-examples.cert: tjvm-examples.lisp
tjvm-examples.cert: defpun.cert
tjvm-examples.cert: tjvm-examples.acl2
tjvm-examples.cert: examples.cert

tjvm.cert: tjvm.lisp
tjvm.cert: tjvm.acl2
