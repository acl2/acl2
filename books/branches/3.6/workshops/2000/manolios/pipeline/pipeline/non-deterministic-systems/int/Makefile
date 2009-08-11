include ../../../../../../../Makefile-generic


# Dependencies:

isa-int.cert: isa-int.lisp
isa-int.cert: ../../top/alist-thms.cert
isa-int.cert: ../top/inst.cert

ma-int-isa-int.cert: ma-int-isa-int.lisp
ma-int-isa-int.cert: ../../top/nth-thms.cert
ma-int-isa-int.cert: ../../top/meta.cert
ma-int-isa-int.cert: ../top/non-det-encap-wfbisim.cert
ma-int-isa-int.cert: ma-int.cert

ma-int.cert: ma-int.lisp
ma-int.cert: isa-int.cert
ma-int.cert: ../top/non-det-macros.cert
