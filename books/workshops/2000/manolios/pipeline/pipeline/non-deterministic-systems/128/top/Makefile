include ../../../../../../../../Makefile-generic

ACL2 = ../../../../../../../../../saved_acl2

# Dependencies:

isa128int.cert: isa128int.lisp
isa128int.cert: ../../top/inst.cert
isa128int.cert: ../../../top/alist-thms.cert
isa128int.cert: ../../top/non-det-macros.cert

ma128int-isa128int.cert: ma128int-isa128int.lisp
ma128int-isa128int.cert: ../../../top/nth-thms.cert
ma128int-isa128int.cert: ../../../top/meta.cert
ma128int-isa128int.cert: ../../../top/defun-weak-sk.cert
ma128int-isa128int.cert: ../../top/non-det-encap-wfbisim.cert
ma128int-isa128int.cert: ma128int.cert

ma128int.cert: ma128int.lisp
ma128int.cert: isa128int.cert
