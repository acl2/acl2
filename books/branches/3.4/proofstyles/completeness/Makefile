include ../../Makefile-generic
ACL2 = ../../../saved_acl2

assertions-partial.cert: assertions-partial.lisp
assertions-partial.cert: stepwise-invariants-partial.cert
# assertions-partial.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert
# assertions-partial.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/ordinals.cert

assertions-total.cert: assertions-total.lisp
assertions-total.cert: stepwise-invariants-total.cert
# assertions-total.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert
# assertions-total.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/ordinals.cert

clock-partial.cert: clock-partial.lisp
clock-partial.cert: generic-partial.cert
# clock-partial.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert
# clock-partial.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert

clock-total.cert: clock-total.lisp
clock-total.cert: generic-total.cert
# clock-total.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert
# clock-total.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert

generic-partial.cert: generic-partial.lisp

generic-total.cert: generic-total.lisp

stepwise-invariants-partial.cert: stepwise-invariants-partial.lisp
stepwise-invariants-partial.cert: clock-partial.cert
# stepwise-invariants-partial.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert

stepwise-invariants-total.cert: stepwise-invariants-total.lisp
stepwise-invariants-total.cert: clock-total.cert
# stepwise-invariants-total.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
# stepwise-invariants-total.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert