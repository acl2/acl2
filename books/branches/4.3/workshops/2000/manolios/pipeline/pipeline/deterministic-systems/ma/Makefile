include ../../../../../../../Makefile-generic


# Dependencies:

isa.cert: isa.lisp
isa.cert: ../../top/alist-thms.cert
isa.cert: ../top/inst.cert

ma-isa-flush.cert: ma-isa-flush.lisp
ma-isa-flush.cert: ../../top/nth-thms.cert
ma-isa-flush.cert: ../../top/meta.cert
ma-isa-flush.cert: ../top/det-encap-wfbisim.cert
ma-isa-flush.cert: isa.cert
ma-isa-flush.cert: ma.cert

ma-isa.cert: ma-isa.lisp
ma-isa.cert: ../../top/nth-thms.cert
ma-isa.cert: ../../top/meta.cert
ma-isa.cert: ../top/det-encap-wfbisim.cert
ma-isa.cert: isa.cert
ma-isa.cert: ma.cert

ma.cert: ma.lisp
ma.cert: ../../top/alist-thms.cert
ma.cert: ../top/inst.cert
ma.cert: ../top/det-macros.cert
