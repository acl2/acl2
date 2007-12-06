include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2

# Don't alphabetize this list!
BOOKS = arith basic bits log float reps round \
        rtl rtlarr bvecp-raw-helpers bvecp-helpers simple-loop-helpers \
        simplify-model-helpers util add top rom-helpers clocks package-defs \
        openers
 
# Dependencies:

arith.cert: arith.lisp
arith.cert: ../arithmetic/fp.cert
arith.cert: ../arithmetic/fp2.cert
arith.cert: ../arithmetic/fl.cert
arith.cert: ../arithmetic/expt.cert
arith.cert: ../arithmetic/expo.cert
arith.cert: ../arithmetic/extra-rules.cert
arith.cert: ../support/ash.cert
arith.cert: ../../../ordinals/e0-ordinal.cert

basic.cert: basic.lisp
basic.cert: ../support/top.cert

bits.cert: bits.lisp
bits.cert: basic.cert
bits.cert: ../support/top.cert

log.cert: log.lisp
log.cert: bits.cert
log.cert: ../support/top.cert

float.cert: float.lisp
float.cert: log.cert
float.cert: ../support/top.cert

reps.cert: reps.lisp
reps.cert: ../support/ereps.cert
reps.cert: ../support/ireps.cert
reps.cert: ../support/guards.cert
reps.cert: log.cert
reps.cert: float.cert

round.cert: round.lisp
round.cert: ../support/top.cert
round.cert: reps.cert

rtl.cert: rtl.lisp
rtl.cert: ../support/top.cert

rtlarr.cert: rtlarr.lisp
rtlarr.cert: ../support/rtlarr.cert
rtlarr.cert: ../support/bvecp-helpers.cert
rtlarr.cert: ../support/guards.cert
rtlarr.cert: ../../../misc/total-order.cert
rtlarr.cert: rtl.cert

bvecp-raw-helpers.cert: bvecp-raw-helpers.lisp
bvecp-raw-helpers.cert: rtl.cert
bvecp-raw-helpers.cert: rtlarr.cert
bvecp-raw-helpers.cert: ../support/bvecp-helpers.cert
bvecp-raw-helpers.cert: ../support/bits.cert
bvecp-raw-helpers.cert: ../support/bitn.cert
bvecp-raw-helpers.cert: ../support/setbits.cert
bvecp-raw-helpers.cert: ../support/setbitn.cert
bvecp-raw-helpers.cert: ../support/logs.cert
bvecp-raw-helpers.cert: ../support/lnot.cert
bvecp-raw-helpers.cert: ../support/shft.cert
bvecp-raw-helpers.cert: ../support/cat.cert
bvecp-raw-helpers.cert: ../support/mulcat.cert
bvecp-raw-helpers.cert: ../support/encode.cert
bvecp-raw-helpers.cert: ../support/decode.cert
bvecp-raw-helpers.cert: ../support/land.cert
bvecp-raw-helpers.cert: ../support/lior.cert
bvecp-raw-helpers.cert: ../support/lxor.cert
bvecp-raw-helpers.cert: ../support/guards.cert
bvecp-raw-helpers.cert: ../arithmetic/expo.cert
bvecp-raw-helpers.cert: ../arithmetic/basic.cert

bvecp-helpers.cert: bvecp-helpers.lisp
bvecp-helpers.cert: rtl.cert
bvecp-helpers.cert: rtlarr.cert
bvecp-helpers.cert: ../support/bvecp-helpers.cert
bvecp-helpers.cert: ../arithmetic/basic.cert

simple-loop-helpers.cert: simple-loop-helpers.lisp
simple-loop-helpers.cert: rtl.cert
simple-loop-helpers.cert: rtlarr.cert
simple-loop-helpers.cert: arith.cert
simple-loop-helpers.cert: log.cert
simple-loop-helpers.cert: ../support/simple-loop-helpers.cert

simplify-model-helpers.cert: simplify-model-helpers.lisp
simplify-model-helpers.cert: rtl.cert
simplify-model-helpers.cert: arith.cert
simplify-model-helpers.cert: bits.cert
simplify-model-helpers.cert: ../support/simplify-model-helpers.cert

util.cert: util.lisp
util.cert: ../support/util.cert

add.cert: add.lisp
add.cert: round.cert
add.cert: ../support/top.cert

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
