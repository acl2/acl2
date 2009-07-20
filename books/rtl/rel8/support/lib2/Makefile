include ../../../../Makefile-generic

# Don't alphabetize this list!
BOOKS = base arith basic bits log float reps round \
        rtl rtlarr bvecp-raw-helpers bvecp-helpers simple-loop-helpers \
        simplify-model-helpers util add top rom-helpers clocks package-defs \
        openers mult 
 
# Dependencies:


base.cert: base.lisp
base.cert: ../lib1/rtl.cert
base.cert: ../lib1/rtlarr.cert
base.cert: ../lib1.delta1/basic.cert
base.cert: ../lib1.delta1/bits.cert
base.cert: ../lib1/log.cert
base.cert: ../lib1.delta2/float.cert
base.cert: ../lib1/reps.cert
base.cert: ../lib1.delta1/round.cert
base.cert: ../lib1/add.cert
base.cert: ../lib1.delta1/mult.cert
base.cert: ../lib1.delta1/arith.cert
base.cert: ../lib1/util.cert
base.cert: ../lib1.delta1/bvecp-raw-helpers.cert
base.cert: ../lib1.delta1/simple-loop-helpers.cert

arith.cert: arith.lisp
arith.cert: base.cert
# arith.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert

basic.cert: basic.lisp
basic.cert: base.cert

bits.cert: bits.lisp
bits.cert: basic.cert
bits.cert: base.cert

log.cert: log.lisp
log.cert: bits.cert
log.cert: base.cert

float.cert: float.lisp
float.cert: log.cert
float.cert: base.cert

reps.cert: reps.lisp
reps.cert: base.cert
reps.cert: log.cert
reps.cert: float.cert

round.cert: round.lisp
round.cert: float.cert
round.cert: base.cert

rtl.cert: rtl.lisp
rtl.cert: base.cert

rtlarr.cert: rtlarr.lisp
rtlarr.cert: base.cert
rtlarr.cert: rtl.cert
# rtlarr.cert: $(ACL2_SYSTEM_BOOKS)/misc/total-order.cert

bvecp-raw-helpers.cert: bvecp-raw-helpers.lisp
bvecp-raw-helpers.cert: rtl.cert
bvecp-raw-helpers.cert: rtlarr.cert
bvecp-raw-helpers.cert: base.cert

bvecp-helpers.cert: bvecp-helpers.lisp
bvecp-helpers.cert: rtl.cert
bvecp-helpers.cert: rtlarr.cert
bvecp-helpers.cert: ../support/bvecp-helpers.cert
bvecp-helpers.cert: ../../arithmetic/basic.cert

simple-loop-helpers.cert: simple-loop-helpers.lisp
simple-loop-helpers.cert: rtl.cert
simple-loop-helpers.cert: rtlarr.cert
simple-loop-helpers.cert: arith.cert
simple-loop-helpers.cert: log.cert
simple-loop-helpers.cert: base.cert

simplify-model-helpers.cert: simplify-model-helpers.lisp
simplify-model-helpers.cert: rtl.cert
simplify-model-helpers.cert: arith.cert
simplify-model-helpers.cert: bits.cert
simplify-model-helpers.cert: ../support/simplify-model-helpers.cert

util.cert: util.lisp
util.cert: base.cert

add.cert: add.lisp
add.cert: round.cert
add.cert: base.cert

top.cert: top.lisp
top.cert: rtl.cert
top.cert: rtlarr.cert
top.cert: basic.cert
top.cert: bits.cert
top.cert: log.cert
top.cert: float.cert
top.cert: reps.cert
top.cert: round.cert
top.cert: add.cert
top.cert: mult.cert
top.cert: arith.cert
top.cert: util.cert

rom-helpers.cert: rom-helpers.lisp
rom-helpers.cert: ../support/rom-helpers.cert

clocks.cert: clocks.lisp
clocks.cert: ../support/clocks.cert

package-defs.cert: package-defs.lisp
package-defs.cert: ../support/package-defs.cert

openers.cert: openers.lisp
openers.cert: ../support/openers.cert

mult.cert: mult.lisp
mult.cert: add.cert
mult.cert: base.cert
