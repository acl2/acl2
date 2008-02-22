include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2

c2i-partial.cert: c2i-partial.lisp
# c2i-partial.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert

c2i-total.cert: c2i-total.lisp
# c2i-total.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert
# c2i-total.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert

clock-to-inv.cert: clock-to-inv.lisp
clock-to-inv.cert: c2i-total.cert
clock-to-inv.cert: c2i-partial.cert
# clock-to-inv.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert
