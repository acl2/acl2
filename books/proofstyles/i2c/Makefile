include ../../Makefile-generic
ACL2 = ../../../saved_acl2

i2c-partial.cert: i2c-partial.lisp
# i2c-partial.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert

i2c-total.cert: i2c-total.lisp
# i2c-total.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert
# i2c-total.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert

inv-to-clock.cert: inv-to-clock.lisp
inv-to-clock.cert: i2c-total.cert
inv-to-clock.cert: i2c-partial.cert
# inv-to-clock.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert
