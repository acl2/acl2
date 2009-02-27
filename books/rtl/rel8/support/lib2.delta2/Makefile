include ../../../../Makefile-generic
ACL2 ?= ../../../../../saved_acl2

# Don't alphabetize this list!
BOOKS = base \
	add-lib \
	log bits add 

# Dependencies:

base.cert: base.lisp
base.cert: ../lib2.delta1/rtl.cert
base.cert: ../lib2.delta1/rtlarr.cert
base.cert: ../lib2/basic.cert
base.cert: ../lib2.delta1/bits.cert
base.cert: ../lib2.delta1/log.cert
base.cert: ../lib2.delta1/float.cert
base.cert: ../lib2.delta1/reps.cert
base.cert: ../lib2.delta1/round.cert
base.cert: ../lib2.delta1/add.cert
base.cert: ../lib2.delta1/mult.cert
base.cert: ../lib2.delta1/util.cert

add-lib.cert: add-lib.lisp
add-lib.cert: base.cert
add-lib.cert: ../lib2.delta1/arith.cert

log.cert: log.lisp
log.cert: base.cert
log.cert: add-lib.cert

bits.cert: bits.lisp
bits.cert: base.cert
bits.cert: add-lib.cert

add.cert: add.lisp
add.cert: base.cert
add.cert: add-lib.cert
