include ../../../../Makefile-generic
ACL2 ?= ../../../../../saved_acl2

# Don't alphabetize this list!
BOOKS = float-extra2 round-extra2 mult-proofs float round mult basic-extra basic arith-extra arith bvecp-raw-helpers simple-loop-helpers-extra simple-loop-helpers bits-extra bits
 
# Dependencies:

float-extra2.cert: float-extra2.lisp
float-extra2.cert: ../lib1/top.cert
float-extra2.cert: ../../arithmetic/basic.cert
float-extra2.cert: ../../arithmetic/basic.cert

round-extra2.cert: round-extra2.lisp
round-extra2.cert: ../lib1/top.cert
round-extra2.cert: ../support/trunc.cert
round-extra2.cert: ../support/trunc.cert
round-extra2.cert: ../../arithmetic/basic.cert
round-extra2.cert: ../../arithmetic/even-odd.cert
round-extra2.cert: ../support/away.cert
round-extra2.cert: ../../arithmetic/basic.cert
round-extra2.cert: ../../arithmetic/top.cert
round-extra2.cert: ../../arithmetic/expt.cert
round-extra2.cert: ../../arithmetic/expt.cert
round-extra2.cert: float-extra2.cert
round-extra2.cert: ../../arithmetic/basic.cert

mult-proofs.cert: mult-proofs.lisp
mult-proofs.cert: ../support/rtl.cert
mult-proofs.cert: ../support/sumbits.cert
mult-proofs.cert: ../support/util.cert
mult-proofs.cert: ../../arithmetic/top.cert
mult-proofs.cert: ../support/cat.cert
mult-proofs.cert: ../support/cat.cert
mult-proofs.cert: ../support/lior.cert
mult-proofs.cert: ../support/land.cert
mult-proofs.cert: ../support/lxor.cert

float.cert: float.lisp
float.cert: ../lib1/log.cert
float.cert: ../lib1/float.cert
float.cert: float-extra2.cert

round.cert: round.lisp
round.cert: float.cert
round.cert: ../lib1/round.cert
round.cert: round-extra2.cert

mult.cert: mult.lisp
mult.cert: ../lib1/add.cert
mult.cert: mult-proofs.cert

basic-extra.cert: basic-extra.lisp
basic-extra.cert: ../lib1/basic.cert
basic-extra.cert: ../../arithmetic/floor.cert
basic-extra.cert: ../../arithmetic/top.cert

basic.cert: basic.lisp
basic.cert: ../lib1/basic.cert
basic.cert: basic-extra.cert

arith-extra.cert: arith-extra.lisp
arith-extra.cert: ../lib1/arith.cert
arith-extra.cert: ../../arithmetic/top.cert

arith.cert: arith.lisp
arith.cert: ../lib1/arith.cert
arith.cert: arith-extra.cert
# arith.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert

bvecp-raw-helpers.cert: bvecp-raw-helpers.lisp
bvecp-raw-helpers.cert: ../lib1/rtl.cert
bvecp-raw-helpers.cert: ../lib1/rtlarr.cert
bvecp-raw-helpers.cert: ../lib1/bvecp-raw-helpers.cert
bvecp-raw-helpers.cert: ../lib1.delta1/bvecp-raw-helpers-extra.cert
bvecp-raw-helpers.cert: ../../arithmetic/expo.cert
bvecp-raw-helpers.cert: ../../arithmetic/basic.cert

simple-loop-helpers-extra.cert: simple-loop-helpers-extra.lisp
simple-loop-helpers-extra.cert: ../lib1/rtl.cert
simple-loop-helpers-extra.cert: ../lib1/rtlarr.cert
simple-loop-helpers-extra.cert: ../lib1/bits.cert

simple-loop-helpers.cert: simple-loop-helpers.lisp
simple-loop-helpers.cert: ../lib1/rtl.cert
simple-loop-helpers.cert: ../lib1/rtlarr.cert
simple-loop-helpers.cert: arith.cert
simple-loop-helpers.cert: ../lib1/log.cert
simple-loop-helpers.cert: ../lib1/simple-loop-helpers.cert
simple-loop-helpers.cert: simple-loop-helpers-extra.cert

bits-extra.cert: bits-extra.lisp
bits-extra.cert: ../lib1/top.cert

bits.cert: bits.lisp
bits.cert: ../lib1/bits.cert
bits.cert: bits-extra.cert
