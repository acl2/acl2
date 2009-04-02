include ../../../../../../../../Makefile-generic

ACL2 = ../../../../../../../../../saved_acl2

# Dependencies:

isa128.cert: isa128.lisp
isa128.cert: ../../../top/alist-thms.cert
isa128.cert: ../../top/inst.cert
isa128.cert: ../../top/det-macros.cert

ma128-isa128.cert: ma128-isa128.lisp
ma128-isa128.cert: ../../../top/nth-thms.cert
ma128-isa128.cert: ../../../top/meta.cert
ma128-isa128.cert: ../../../top/defun-weak-sk.cert
ma128-isa128.cert: ../../top/det-encap-wfbisim.cert
ma128-isa128.cert: ma128.cert

ma128.cert: ma128.lisp
ma128.cert: isa128.cert
