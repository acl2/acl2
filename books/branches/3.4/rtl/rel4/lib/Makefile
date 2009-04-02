include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2

# Don't alphabetize this list!
BOOKS = arith basic bits float reps round \
        rtl rtlarr bvecp-raw-helpers bvecp-helpers simple-loop-helpers \
        simplify-model-helpers util fadd top rom-helpers clocks package-defs \
        openers
 
# Dependencies:

arith.cert: arith.lisp
arith.cert: ../arithmetic/fp.cert
arith.cert: ../arithmetic/fp2.cert
arith.cert: ../arithmetic/fl.cert
arith.cert: ../arithmetic/expt.cert
arith.cert: ../arithmetic/expo.cert
arith.cert: ../../../ordinals/e0-ordinal.cert

basic.cert: basic.lisp
basic.cert: ../arithmetic/fl.cert
basic.cert: ../support/merge.cert
basic.cert: ../support/guards.cert
basic.cert: ../arithmetic/hacks.cert
basic.cert: ../arithmetic/cg.cert
basic.cert: ../support/ash.cert
basic.cert: ../arithmetic/fl-hacks.cert
basic.cert: ../arithmetic/mod.cert
basic.cert: ../arithmetic/even-odd.cert
basic.cert: ../arithmetic/extra-rules.cert
basic.cert: ../arithmetic/top.cert
basic.cert: rtl.cert
basic.cert: rtlarr.cert

bits.cert: bits.lisp
bits.cert: basic.cert
bits.cert: ../support/top.cert

float.cert: float.lisp
float.cert: ../support/merge.cert
float.cert: ../support/guards.cert
float.cert: bits.cert

reps.cert: reps.lisp
reps.cert: ../support/ereps.cert
reps.cert: ../support/ireps.cert
reps.cert: ../support/guards.cert
reps.cert: float.cert

round.cert: round.lisp
round.cert: ../support/trunc.cert
round.cert: ../support/away.cert
round.cert: ../support/near.cert
round.cert: ../support/near+.cert
round.cert: ../support/oddr.cert
round.cert: ../support/rnd.cert
round.cert: ../support/drnd.cert
round.cert: ../support/bits-trunc.cert
round.cert: ../support/sticky.cert
round.cert: ../support/guards.cert
round.cert: reps.cert

rtl.cert: rtl.lisp
rtl.cert: ../support/rtl.cert
rtl.cert: ../support/mulcat.cert
rtl.cert: ../support/bvecp.cert
rtl.cert: ../support/guards.cert

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
simple-loop-helpers.cert: bits.cert
simple-loop-helpers.cert: ../support/simple-loop-helpers.cert

simplify-model-helpers.cert: simplify-model-helpers.lisp
simplify-model-helpers.cert: rtl.cert
simplify-model-helpers.cert: arith.cert
simplify-model-helpers.cert: bits.cert
simplify-model-helpers.cert: ../support/simplify-model-helpers.cert

util.cert: util.lisp
util.cert: ../support/util.cert

fadd.cert: fadd.lisp
fadd.cert: float.cert
fadd.cert: ../support/fadd.cert
fadd.cert: ../support/bits-extra.cert
fadd.cert: ../support/guards.cert

top.cert: top.lisp
top.cert: rtl.cert
top.cert: rtlarr.cert
top.cert: basic.cert
top.cert: bits.cert
top.cert: float.cert
top.cert: reps.cert
top.cert: round.cert
top.cert: fadd.cert
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
