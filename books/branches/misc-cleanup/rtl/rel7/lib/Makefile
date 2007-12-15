include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2

# Don't alphabetize this list!
BOOKS = arith basic bits log float reps round \
        rtl rtlarr bvecp-raw-helpers bvecp-helpers simple-loop-helpers \
        simplify-model-helpers util add top rom-helpers clocks package-defs \
        openers mult
 
# Dependencies:
arith.cert: arith.lisp
arith.cert: ../support/top/top.cert
# arith.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert

basic.cert: basic.lisp
basic.cert: ../support/top/top.cert

bits.cert: bits.lisp
bits.cert: basic.cert
bits.cert: ../support/top/top.cert

log.cert: log.lisp
log.cert: bits.cert
log.cert: ../support/top/top.cert

float.cert: float.lisp
float.cert: log.cert
float.cert: ../support/top/top.cert

reps.cert: reps.lisp
reps.cert: ../support/top/top.cert
reps.cert: log.cert
reps.cert: float.cert

round.cert: round.lisp
round.cert: float.cert
round.cert: ../support/top/top.cert

rtl.cert: rtl.lisp
rtl.cert: ../support/top/top.cert

rtlarr.cert: rtlarr.lisp
rtlarr.cert: ../support/top/top.cert
rtlarr.cert: rtl.cert
# rtlarr.cert: $(ACL2_SYSTEM_BOOKS)/misc/total-order.cert

bvecp-raw-helpers.cert: bvecp-raw-helpers.lisp
bvecp-raw-helpers.cert: rtl.cert
bvecp-raw-helpers.cert: rtlarr.cert
bvecp-raw-helpers.cert: ../support/support/bvecp-helpers.cert
bvecp-raw-helpers.cert: ../support/support/bits.cert
bvecp-raw-helpers.cert: ../support/support/bitn.cert
bvecp-raw-helpers.cert: ../support/support/setbits.cert
bvecp-raw-helpers.cert: ../support/support/setbitn.cert
bvecp-raw-helpers.cert: ../support/support/logs.cert
bvecp-raw-helpers.cert: ../support/support/lnot.cert
bvecp-raw-helpers.cert: ../support/support/shft.cert
bvecp-raw-helpers.cert: ../support/support/cat.cert
bvecp-raw-helpers.cert: ../support/support/mulcat.cert
bvecp-raw-helpers.cert: ../support/support/encode.cert
bvecp-raw-helpers.cert: ../support/support/decode.cert
bvecp-raw-helpers.cert: ../support/support/land.cert
bvecp-raw-helpers.cert: ../support/support/lior.cert
bvecp-raw-helpers.cert: ../support/support/lxor.cert
bvecp-raw-helpers.cert: ../support/support/guards.cert
bvecp-raw-helpers.cert: ../arithmetic/expo.cert
bvecp-raw-helpers.cert: ../arithmetic/basic.cert

bvecp-helpers.cert: bvecp-helpers.lisp
bvecp-helpers.cert: rtl.cert
bvecp-helpers.cert: rtlarr.cert
bvecp-helpers.cert: ../support/support/bvecp-helpers.cert
bvecp-helpers.cert: ../arithmetic/basic.cert

simple-loop-helpers.cert: simple-loop-helpers.lisp
simple-loop-helpers.cert: rtl.cert
simple-loop-helpers.cert: rtlarr.cert
simple-loop-helpers.cert: arith.cert
simple-loop-helpers.cert: log.cert
simple-loop-helpers.cert: ../support/support/simple-loop-helpers.cert

simplify-model-helpers.cert: simplify-model-helpers.lisp
simplify-model-helpers.cert: rtl.cert
simplify-model-helpers.cert: arith.cert
simplify-model-helpers.cert: bits.cert
simplify-model-helpers.cert: ../support/support/simplify-model-helpers.cert

util.cert: util.lisp
util.cert: ../support/top/top.cert

add.cert: add.lisp
add.cert: round.cert
add.cert: ../support/top/top.cert

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
rom-helpers.cert: ../support/support/rom-helpers.cert

clocks.cert: clocks.lisp
clocks.cert: ../support/support/clocks.cert

package-defs.cert: package-defs.lisp
package-defs.cert: ../support/support/package-defs.cert

openers.cert: openers.lisp
openers.cert: ../support/support/openers.cert

mult.cert: mult.lisp
mult.cert: add.cert
mult.cert: ../support/top/top.cert
