include ../../../../Makefile-generic

# Don't alphabetize this list!
BOOKS = bits-new-proofs bits-new \
        log-new-proofs log-new \
        rtl-new-proofs rtl-new \
        float-new-proofs float-new \
        round-new-proofs round-new \
	add-new-proofs add-new \
	log-support-proofs log-support \
        mult-new-proofs mult-new \
        reps-new-proofs reps-new \
        rtlarr-new  \
        bits-proofs bits \
        log-proofs log \
	rtl-proofs rtl \
        float-proofs float  \
	round-proofs round \
        reps-proofs reps \
	add-proofs add \
	mult-proofs mult \
	rtlarr \
	logn-new-proofs logn-new \
	logn-proofs logn \
	bvecp-raw-helpers-proofs  bvecp-raw-helpers \
	simple-loop-helpers-proofs simple-loop-helpers \
	arith \
	bvecp-helpers \
	simplify-model-helpers-new-proofs simplify-model-helpers-new \
	simplify-model-helpers-proofs simplify-model-helpers \
	util \
	log-support-proofs log-support \
	logn2log-proofs logn2log \
	top

# Dependencies:


bits-new-proofs.cert: bits-new-proofs.lisp
bits-new-proofs.cert: ../lib2/bits.cert
bits-new-proofs.cert: ../lib2/top.cert
bits-new-proofs.cert: ../../arithmetic/top.cert
bits-new-proofs.cert: ../support/log.cert
bits-new-proofs.cert: ../support/merge.cert
bits-new-proofs.cert: ../support/logand.cert
bits-new-proofs.cert: ../support/badguys.cert
bits-new-proofs.cert: ../lib2/bits.cert

bits-new.cert: bits-new.lisp
bits-new.cert: ../lib2/basic.cert
bits-new.cert: bits-new-proofs.cert

log-new-proofs.cert: log-new-proofs.lisp
log-new-proofs.cert: bits-new.cert
log-new-proofs.cert: bits-new-proofs.cert
log-new-proofs.cert: ../lib2/top.cert
log-new-proofs.cert: ../../arithmetic/top.cert
log-new-proofs.cert: ../support/logand.cert
log-new-proofs.cert: ../support/logior.cert
log-new-proofs.cert: ../support/logxor.cert
log-new-proofs.cert: ../support/log.cert
log-new-proofs.cert: ../support/merge.cert
log-new-proofs.cert: ../support/lognot.cert
log-new-proofs.cert: ../support/lognot.cert
log-new-proofs.cert: ../support/merge.cert
log-new-proofs.cert: ../support/logior.cert

log-new.cert: log-new.lisp
log-new.cert: bits-new.cert
log-new.cert: log-new-proofs.cert

rtl-new-proofs.cert: rtl-new-proofs.lisp
rtl-new-proofs.cert: bits-new-proofs.cert
rtl-new-proofs.cert: log-new.cert
rtl-new-proofs.cert: ../lib2/top.cert
rtl-new-proofs.cert: ../../arithmetic/top.cert
rtl-new-proofs.cert: ../support/logior.cert

rtl-new.cert: rtl-new.lisp
rtl-new.cert: rtl-new-proofs.cert

float-new-proofs.cert: float-new-proofs.lisp
float-new-proofs.cert: log-new.cert
float-new-proofs.cert: ../lib2/top.cert
float-new-proofs.cert: bits-new-proofs.cert

float-new.cert: float-new.lisp
float-new.cert: log-new.cert
float-new.cert: float-new-proofs.cert

round-new-proofs.cert: round-new-proofs.lisp
round-new-proofs.cert: float-new.cert
round-new-proofs.cert: ../lib2/top.cert
round-new-proofs.cert: bits-new-proofs.cert
round-new-proofs.cert: ../support/land.cert
round-new-proofs.cert: ../../arithmetic/top.cert

round-new.cert: round-new.lisp
round-new.cert: float-new.cert
round-new.cert: round-new-proofs.cert

add-new-proofs.cert: add-new-proofs.lisp
add-new-proofs.cert: round-new.cert
add-new-proofs.cert: ../lib2/top.cert
add-new-proofs.cert: bits-new-proofs.cert
add-new-proofs.cert: ../../arithmetic/top.cert
add-new-proofs.cert: ../../arithmetic/top.cert
add-new-proofs.cert: ../support/logior.cert
add-new-proofs.cert: log-new.cert
add-new-proofs.cert: log-new-proofs.cert
add-new-proofs.cert: log-new-proofs.cert
add-new-proofs.cert: log-new-proofs.cert

add-new.cert: add-new.lisp
add-new.cert: round-new.cert
add-new.cert: add-new-proofs.cert

log-support-proofs.cert: log-support-proofs.lisp
log-support-proofs.cert: ../lib2/top.cert
log-support-proofs.cert: bits-new.cert
log-support-proofs.cert: ../../arithmetic/top.cert
log-support-proofs.cert: bits-new-proofs.cert
log-support-proofs.cert: log-new.cert
log-support-proofs.cert: log-new-proofs.cert
log-support-proofs.cert: log-new-proofs.cert
log-support-proofs.cert: log-new-proofs.cert
log-support-proofs.cert: log-new.cert

log-support.cert: log-support.lisp
log-support.cert: ../lib2/top.cert
log-support.cert: log-support-proofs.cert

mult-new-proofs.cert: mult-new-proofs.lisp
mult-new-proofs.cert: add-new.cert
mult-new-proofs.cert: ../lib2/top.cert
mult-new-proofs.cert: ../../arithmetic/top.cert
mult-new-proofs.cert: log-support.cert
mult-new-proofs.cert: bits-new-proofs.cert

mult-new.cert: mult-new.lisp
mult-new.cert: add-new.cert
mult-new.cert: mult-new-proofs.cert

reps-new-proofs.cert: reps-new-proofs.lisp
reps-new-proofs.cert: ../lib2/top.cert
reps-new-proofs.cert: log-new.cert
reps-new-proofs.cert: float-new.cert
reps-new-proofs.cert: log-support.cert
reps-new-proofs.cert: bits-new-proofs.cert
reps-new-proofs.cert: ../../arithmetic/top.cert

reps-new.cert: reps-new.lisp
reps-new.cert: log-new.cert
reps-new.cert: float-new.cert
reps-new.cert: reps-new-proofs.cert

rtlarr-new.cert: rtlarr-new.lisp
rtlarr-new.cert: ../lib2/top.cert
rtlarr-new.cert: rtl-new.cert
# rtlarr-new.cert: $(ACL2_SYSTEM_BOOKS)/misc/total-order.cert

bits-proofs.cert: bits-proofs.lisp
bits-proofs.cert: ../lib2/basic.cert
bits-proofs.cert: bits-new.cert
bits-proofs.cert: ../../arithmetic/top.cert
bits-proofs.cert: log-new.cert
bits-proofs.cert: log-new.cert
bits-proofs.cert: ../support/logand.cert
bits-proofs.cert: bits-new.cert
bits-proofs.cert: ../../arithmetic/top.cert
bits-proofs.cert: ../../arithmetic/top.cert

bits.cert: bits.lisp
bits.cert: ../lib2/basic.cert
bits.cert: bits-proofs.cert

log-proofs.cert: log-proofs.lisp
log-proofs.cert: ../lib2/basic.cert
log-proofs.cert: bits.cert
log-proofs.cert: log-new.cert

log.cert: log.lisp
log.cert: ../lib2/basic.cert
log.cert: bits.cert
log.cert: log-proofs.cert

rtl-proofs.cert: rtl-proofs.lisp
rtl-proofs.cert: rtl-new.cert
rtl-proofs.cert: bits.cert
rtl-proofs.cert: bits-new.cert
rtl-proofs.cert: log-new.cert
rtl-proofs.cert: ../../arithmetic/top.cert

rtl.cert: rtl.lisp
rtl.cert: rtl-proofs.cert

float-proofs.cert: float-proofs.lisp
float-proofs.cert: log.cert
float-proofs.cert: float-new.cert

float.cert: float.lisp
float.cert: log.cert
float.cert: float-proofs.cert

round-proofs.cert: round-proofs.lisp
round-proofs.cert: float.cert
round-proofs.cert: round-new.cert

round.cert: round.lisp
round.cert: float.cert
round.cert: round-proofs.cert

reps-proofs.cert: reps-proofs.lisp
reps-proofs.cert: log.cert
reps-proofs.cert: float.cert
reps-proofs.cert: reps-new.cert

reps.cert: reps.lisp
reps.cert: reps-proofs.cert
reps.cert: log.cert
reps.cert: float.cert

add-proofs.cert: add-proofs.lisp
add-proofs.cert: round.cert
add-proofs.cert: add-new.cert

add.cert: add.lisp
add.cert: round.cert
add.cert: add-proofs.cert

mult-proofs.cert: mult-proofs.lisp
mult-proofs.cert: add.cert
mult-proofs.cert: mult-new.cert

mult.cert: mult.lisp
mult.cert: add.cert
mult.cert: mult-proofs.cert

rtlarr.cert: rtlarr.lisp
rtlarr.cert: rtlarr-new.cert
rtlarr.cert: rtl.cert
# rtlarr.cert: $(ACL2_SYSTEM_BOOKS)/misc/total-order.cert

logn-new-proofs.cert: logn-new-proofs.lisp
logn-new-proofs.cert: bits-new.cert
logn-new-proofs.cert: rtl-new.cert
logn-new-proofs.cert: ../lib2/top.cert
logn-new-proofs.cert: bits-new-proofs.cert
logn-new-proofs.cert: log-new.cert

logn-new.cert: logn-new.lisp
logn-new.cert: bits-new.cert
logn-new.cert: rtl-new.cert
logn-new.cert: logn-new-proofs.cert

logn-proofs.cert: logn-proofs.lisp
logn-proofs.cert: bits.cert
logn-proofs.cert: rtl.cert
logn-proofs.cert: logn-new.cert
logn-proofs.cert: log-new.cert

logn.cert: logn.lisp
logn.cert: bits.cert
logn.cert: logn-proofs.cert

bvecp-raw-helpers-proofs.cert: bvecp-raw-helpers-proofs.lisp
bvecp-raw-helpers-proofs.cert: rtl.cert
bvecp-raw-helpers-proofs.cert: rtlarr.cert
bvecp-raw-helpers-proofs.cert: bits.cert
bvecp-raw-helpers-proofs.cert: float.cert
bvecp-raw-helpers-proofs.cert: logn.cert
bvecp-raw-helpers-proofs.cert: ../../arithmetic/top.cert
bvecp-raw-helpers-proofs.cert: ../support/logand.cert
bvecp-raw-helpers-proofs.cert: ../support/logior.cert
bvecp-raw-helpers-proofs.cert: ../support/encode.cert
bvecp-raw-helpers-proofs.cert: ../support/decode.cert

bvecp-raw-helpers.cert: bvecp-raw-helpers.lisp
bvecp-raw-helpers.cert: rtl.cert
bvecp-raw-helpers.cert: rtlarr.cert
bvecp-raw-helpers.cert: bits.cert
bvecp-raw-helpers.cert: float.cert
bvecp-raw-helpers.cert: bvecp-raw-helpers-proofs.cert

simple-loop-helpers-proofs.cert: simple-loop-helpers-proofs.lisp
simple-loop-helpers-proofs.cert: rtl.cert
simple-loop-helpers-proofs.cert: rtlarr.cert
simple-loop-helpers-proofs.cert: logn.cert
simple-loop-helpers-proofs.cert: ../../arithmetic/top.cert
simple-loop-helpers-proofs.cert: bits.cert

simple-loop-helpers.cert: simple-loop-helpers.lisp
simple-loop-helpers.cert: rtl.cert
simple-loop-helpers.cert: rtlarr.cert
simple-loop-helpers.cert: log.cert
simple-loop-helpers.cert: ../../arithmetic/top.cert
simple-loop-helpers.cert: simple-loop-helpers-proofs.cert

arith.cert: arith.lisp
arith.cert: ../lib2/top.cert
# arith.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert

bvecp-helpers.cert: bvecp-helpers.lisp
bvecp-helpers.cert: rtl.cert
bvecp-helpers.cert: rtlarr.cert
bvecp-helpers.cert: bvecp-raw-helpers.cert

simplify-model-helpers-new-proofs.cert: simplify-model-helpers-new-proofs.lisp
simplify-model-helpers-new-proofs.cert: bits-new.cert
simplify-model-helpers-new-proofs.cert: logn-new.cert
simplify-model-helpers-new-proofs.cert: arith.cert
simplify-model-helpers-new-proofs.cert: ../lib2/top.cert
simplify-model-helpers-new-proofs.cert: bits-new-proofs.cert
simplify-model-helpers-new-proofs.cert: ../lib2/simplify-model-helpers.cert

simplify-model-helpers-new.cert: simplify-model-helpers-new.lisp
simplify-model-helpers-new.cert: bits-new.cert
simplify-model-helpers-new.cert: logn-new.cert
simplify-model-helpers-new.cert: arith.cert
simplify-model-helpers-new.cert: simplify-model-helpers-new-proofs.cert

simplify-model-helpers-proofs.cert: simplify-model-helpers-proofs.lisp
simplify-model-helpers-proofs.cert: rtl.cert
simplify-model-helpers-proofs.cert: bits.cert
simplify-model-helpers-proofs.cert: logn.cert
simplify-model-helpers-proofs.cert: arith.cert
simplify-model-helpers-proofs.cert: simplify-model-helpers-new.cert

simplify-model-helpers.cert: simplify-model-helpers.lisp
simplify-model-helpers.cert: rtl.cert
simplify-model-helpers.cert: arith.cert
simplify-model-helpers.cert: bits.cert
simplify-model-helpers.cert: simplify-model-helpers-proofs.cert

util.cert: util.lisp
util.cert: ../lib2/top.cert

log-support-proofs.cert: log-support-proofs.lisp
log-support-proofs.cert: ../lib2/top.cert
log-support-proofs.cert: bits-new.cert
log-support-proofs.cert: ../../arithmetic/top.cert
log-support-proofs.cert: bits-new-proofs.cert
log-support-proofs.cert: log-new.cert
log-support-proofs.cert: log-new-proofs.cert
log-support-proofs.cert: log-new-proofs.cert
log-support-proofs.cert: log-new-proofs.cert
log-support-proofs.cert: log-new.cert

log-support.cert: log-support.lisp
log-support.cert: ../lib2/top.cert
log-support.cert: log-support-proofs.cert

logn2log-proofs.cert: logn2log-proofs.lisp
logn2log-proofs.cert: log.cert
logn2log-proofs.cert: logn.cert
logn2log-proofs.cert: ../../arithmetic/top.cert
logn2log-proofs.cert: log.cert
logn2log-proofs.cert: bvecp-raw-helpers.cert

logn2log.cert: logn2log.lisp
logn2log.cert: log.cert
logn2log.cert: logn.cert
logn2log.cert: logn2log-proofs.cert
logn2log.cert: ../../arithmetic/top.cert

top.cert: top.lisp
top.cert: rtl.cert
top.cert: rtlarr.cert
top.cert: bits.cert
top.cert: log.cert
top.cert: float.cert
top.cert: reps.cert
top.cert: round.cert
top.cert: add.cert
top.cert: mult.cert
top.cert: bvecp-raw-helpers.cert
top.cert: simple-loop-helpers.cert
top.cert: arith.cert
top.cert: bvecp-helpers.cert
top.cert: logn.cert
top.cert: simplify-model-helpers.cert
