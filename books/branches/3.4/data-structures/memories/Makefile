include ../../Makefile-generic
ACL2 = ../../../saved_acl2 

BOOKS = log2 memtree memory-impl private memory 



log2.cert: log2.lisp
# log2.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
# log2.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert
log2.cert: cert.acl2

memtree.cert: memtree.lisp
# memtree.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
# memtree.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert
memtree.cert: cert.acl2

memory-impl.cert: memory-impl.lisp
memory-impl.cert: log2.cert
memory-impl.cert: memtree.cert
# memory-impl.cert: $(ACL2_SYSTEM_BOOKS)/misc/records.cert
memory-impl.cert: cert.acl2

private.cert: private.lisp
private.cert: cert.acl2

memory.cert: memory.lisp
memory.cert: memory-impl.cert
memory.cert: private.cert
# memory.cert: $(ACL2_SYSTEM_BOOKS)/misc/records.cert
memory.cert: cert.acl2

cert.acl2: package.lsp
