include ../../Makefile-generic

# Dependencies:

random.cert: random.lisp

encryption.cert: encryption.lisp

diffie-helman.cert: diffie-helman.lisp
# diffie-helman.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
# diffie-helman.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert

jfkr.cert: jfkr.lisp
jfkr.cert: encryption.cert
jfkr.cert: random.cert
jfkr.cert: diffie-helman.cert
# jfkr.cert: $(ACL2_SYSTEM_BOOKS)/make-event/assert.cert
