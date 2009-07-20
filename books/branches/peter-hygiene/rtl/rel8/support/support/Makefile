include ../../../../Makefile-generic

# don't alphabetize this list!
BOOKS = mod4 add3-proofs add3 all-ones ash bias-proofs bias bitn bitn-proofs						\
        bits bits-proofs bvecp-proofs bvecp bvecp-helpers bvecp-lemmas ocat						\
        lnot-proofs lnot decode-proofs decode encode fast-and ground-zero ireps log-proofs log land0-proofs land0		\
	lextra-proofs lextra0 lextra cat-proofs cat cat-def									\
        lior0-proofs lior0 logand logand-proofs logeqv logior-proofs logior logior1-proofs logior1 lognot logorc1 logs	\
        logxor lop1-proofs lop1 lop2-proofs lop2 lop3-proofs lop3 lxor0-proofs lxor0 float sumbits merge model-helpers  \
	badguys mulcat-proofs mulcat rewrite-theory rnd rom-helpers rtl rtlarr						\
        setbits-proofs setbits setbitn-proofs setbitn shft sgn simple-loop-helpers					\
        sticky-proofs sticky trunc-proofs trunc bits-trunc-proofs bits-trunc away-proofs away near-proofs		\
	near near+-proofs near+ oddr-proofs oddr rnd util log-equal lop1 lop2 lop3 ereps-proofs ereps ireps		\
	stick-proofs stick drnd-original merge2 fadd clocks openers package-defs simplify-model-helpers                          \
	top1 land lior lxor guards \
	fadd-extra fadd-extra0 float-extra round-extra top

# Dependencies:

mod4.cert: mod4.lisp
mod4.cert: ../../arithmetic/top.cert

add3-proofs.cert: add3-proofs.lisp
add3-proofs.cert: merge.cert
add3-proofs.cert: bitn.cert
add3-proofs.cert: bits.cert
add3-proofs.cert: ../../arithmetic/top.cert
add3-proofs.cert: ../../arithmetic/arith2.cert
add3-proofs.cert: land0.cert
add3-proofs.cert: lior0.cert
add3-proofs.cert: lxor0.cert
# add3-proofs.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert

add3.cert: add3.lisp
add3.cert: merge.cert
add3.cert: add3-proofs.cert
add3.cert: land0.cert
add3.cert: lior0.cert
add3.cert: lxor0.cert

all-ones.cert: all-ones.lisp

ash.cert: ash.lisp
ash.cert: ground-zero.cert
ash.cert: ../../arithmetic/fl.cert
ash.cert: ../../arithmetic/expt.cert
ash.cert: ../../arithmetic/expo.cert

bias-proofs.cert: bias-proofs.lisp
bias-proofs.cert: ../../arithmetic/expt.cert
bias-proofs.cert: bvecp.cert
bias-proofs.cert: ../../arithmetic/integerp.cert

bias.cert: bias.lisp
bias.cert: bias-proofs.cert

bitn.cert: bitn.lisp
bitn.cert: ground-zero.cert
bitn.cert: ../../arithmetic/power2p.cert
bitn.cert: ../../arithmetic/negative-syntaxp.cert
bitn.cert: bitn-proofs.cert

bitn-proofs.cert: bitn-proofs.lisp
bitn-proofs.cert: ../../arithmetic/top.cert
bitn-proofs.cert: ../../arithmetic/negative-syntaxp.cert
bitn-proofs.cert: ../../arithmetic/power2p.cert
bitn-proofs.cert: ground-zero.cert
bitn-proofs.cert: bits.cert
bitn-proofs.cert: bvecp.cert

bits.cert: bits.lisp
bits.cert: bits-proofs.cert
bits.cert: ../../arithmetic/negative-syntaxp.cert
bits.cert: ../../arithmetic/power2p.cert

bits-proofs.cert: bits-proofs.lisp
bits-proofs.cert: ground-zero.cert
bits-proofs.cert: ../../arithmetic/negative-syntaxp.cert
bits-proofs.cert: ../../arithmetic/power2p.cert
bits-proofs.cert: ../../arithmetic/top.cert
bits-proofs.cert: bvecp.cert

bvecp-proofs.cert: bvecp-proofs.lisp
bvecp-proofs.cert: ../../arithmetic/top.cert

bvecp.cert: bvecp.lisp
bvecp.cert: bvecp-proofs.cert

bvecp-helpers.cert: bvecp-helpers.lisp
bvecp-helpers.cert: rtl.cert
bvecp-helpers.cert: bvecp-lemmas.cert
bvecp-helpers.cert: ../../arithmetic/top.cert
bvecp-helpers.cert: bits.cert

bvecp-lemmas.cert: bvecp-lemmas.lisp
bvecp-lemmas.cert: ../../arithmetic/expo.cert
bvecp-lemmas.cert: bits.cert
bvecp-lemmas.cert: setbits.cert
bvecp-lemmas.cert: setbitn.cert
bvecp-lemmas.cert: encode.cert
bvecp-lemmas.cert: decode.cert
bvecp-lemmas.cert: logs.cert
bvecp-lemmas.cert: lnot.cert
bvecp-lemmas.cert: bitn.cert
bvecp-lemmas.cert: shft.cert
bvecp-lemmas.cert: cat.cert
bvecp-lemmas.cert: logand.cert
bvecp-lemmas.cert: merge.cert
bvecp-lemmas.cert: mulcat.cert
bvecp-lemmas.cert: land0.cert
bvecp-lemmas.cert: lior0.cert
bvecp-lemmas.cert: lxor0.cert
bvecp-lemmas.cert: cat.cert
bvecp-lemmas.cert: rtl.cert

ocat.cert: ocat.lisp
ocat.cert: ../../arithmetic/expt.cert
ocat.cert: ../../arithmetic/expo.cert
ocat.cert: ../../arithmetic/arith2.cert
ocat.cert: ../../arithmetic/fp2.cert
ocat.cert: ../../arithmetic/integerp.cert

lnot-proofs.cert: lnot-proofs.lisp
lnot-proofs.cert: bits.cert
lnot-proofs.cert: bitn.cert
lnot-proofs.cert: ../../arithmetic/expt.cert
lnot-proofs.cert: ../../arithmetic/mod.cert
lnot-proofs.cert: ../../arithmetic/mod.cert
lnot-proofs.cert: ../../arithmetic/arith.cert
lnot-proofs.cert: ../../arithmetic/arith2.cert
lnot-proofs.cert: ../../arithmetic/integerp.cert
lnot-proofs.cert: bvecp.cert
lnot-proofs.cert: ../../arithmetic/fl.cert
lnot-proofs.cert: ../../arithmetic/top.cert

lnot.cert: lnot.lisp
lnot.cert: lnot-proofs.cert

decode-proofs.cert: decode-proofs.lisp
decode-proofs.cert: ground-zero.cert
decode-proofs.cert: ../../arithmetic/fl.cert
decode-proofs.cert: ash.cert
decode-proofs.cert: bvecp.cert

decode.cert: decode.lisp
decode.cert: ground-zero.cert
decode.cert: decode-proofs.cert

encode.cert: encode.lisp
encode.cert: ../../arithmetic/top.cert
encode.cert: ground-zero.cert
encode.cert: bvecp.cert
encode.cert: ash.cert
encode.cert: float.cert

fast-and.cert: fast-and.lisp

ground-zero.cert: ground-zero.lisp
ground-zero.cert: ../../arithmetic/ground-zero.cert
ground-zero.cert: util.cert

ireps.cert: ireps.lisp
ireps.cert: rtl.cert
ireps.cert: bias.cert
ireps.cert: float.cert
ireps.cert: merge.cert
ireps.cert: cat.cert
ireps.cert: bvecp.cert
ireps.cert: bits.cert
ireps.cert: bitn.cert
ireps.cert: ../../arithmetic/top.cert

log-proofs.cert: log-proofs.lisp
log-proofs.cert: ground-zero.cert
log-proofs.cert: ../../arithmetic/top.cert
log-proofs.cert: lognot.cert
log-proofs.cert: bits.cert
log-proofs.cert: bitn.cert
log-proofs.cert: lnot.cert
log-proofs.cert: logior.cert
log-proofs.cert: logand.cert
log-proofs.cert: logxor.cert

log.cert: log.lisp
log.cert: ground-zero.cert
log.cert: log-proofs.cert
log.cert: lnot.cert
log.cert: logand.cert
log.cert: logior.cert
log.cert: logxor.cert

land0-proofs.cert: land0-proofs.lisp
land0-proofs.cert: bvecp.cert
land0-proofs.cert: all-ones.cert
land0-proofs.cert: log.cert
land0-proofs.cert: merge.cert
land0-proofs.cert: bvecp.cert
land0-proofs.cert: logand.cert
land0-proofs.cert: bits.cert
land0-proofs.cert: bitn.cert
land0-proofs.cert: ../../arithmetic/top.cert
land0-proofs.cert: ../../arithmetic/fl-hacks.cert

land0.cert: land0.lisp
land0.cert: land0-proofs.cert

lextra-proofs.cert: lextra-proofs.lisp
lextra-proofs.cert: land0.cert
lextra-proofs.cert: lior0.cert
lextra-proofs.cert: lxor0.cert
lextra-proofs.cert: ../../arithmetic/top.cert
lextra-proofs.cert: logand.cert
lextra-proofs.cert: logior.cert
lextra-proofs.cert: logxor.cert
lextra-proofs.cert: merge.cert
lextra-proofs.cert: bvecp.cert
lextra-proofs.cert: bits.cert

lextra0.cert: lextra0.lisp
lextra0.cert: land0.cert
lextra0.cert: lior0.cert
lextra0.cert: lxor0.cert
lextra0.cert: lextra-proofs.cert

lextra.cert: lextra.lisp
lextra.cert: land.cert
lextra.cert: lior.cert
lextra.cert: lxor.cert
lextra.cert: cat.cert
lextra.cert: lextra0.cert
lextra.cert: land0.cert
lextra.cert: lior0.cert
lextra.cert: lxor0.cert
lextra.cert: merge2.cert
lextra.cert: ../../arithmetic/top.cert
lextra.cert: bits-trunc.cert
lextra.cert: fadd.cert

cat-proofs.cert: cat-proofs.lisp
cat-proofs.cert: cat-def.cert
cat-proofs.cert: ../../arithmetic/top.cert
cat-proofs.cert: bits.cert
cat-proofs.cert: bvecp.cert

cat.cert: cat.lisp
cat.cert: cat-def.cert
cat.cert: cat-proofs.cert

cat-def.cert: cat-def.lisp

lior0-proofs.cert: lior0-proofs.lisp
lior0-proofs.cert: all-ones.cert
lior0-proofs.cert: merge.cert
lior0-proofs.cert: bvecp.cert
lior0-proofs.cert: logior.cert
lior0-proofs.cert: bits.cert
lior0-proofs.cert: bitn.cert
lior0-proofs.cert: ../../arithmetic/top.cert

lior0.cert: lior0.lisp
lior0.cert: lior0-proofs.cert

logand.cert: logand.lisp
logand.cert: ground-zero.cert
logand.cert: logand-proofs.cert

logand-proofs.cert: logand-proofs.lisp
logand-proofs.cert: ground-zero.cert
logand-proofs.cert: ../../arithmetic/fl.cert
logand-proofs.cert: ../../arithmetic/induct.cert
logand-proofs.cert: lognot.cert
logand-proofs.cert: ../../arithmetic/top.cert

logeqv.cert: logeqv.lisp
logeqv.cert: ground-zero.cert
logeqv.cert: ../../arithmetic/top.cert
logeqv.cert: logior.cert
logeqv.cert: logand.cert
logeqv.cert: logorc1.cert
logeqv.cert: lognot.cert

logior-proofs.cert: logior-proofs.lisp
logior-proofs.cert: ground-zero.cert
logior-proofs.cert: logand.cert
logior-proofs.cert: lognot.cert
logior-proofs.cert: ../../arithmetic/top.cert
logior-proofs.cert: bvecp.cert

logior.cert: logior.lisp
logior.cert: ground-zero.cert
logior.cert: logior-proofs.cert

logior1-proofs.cert: logior1-proofs.lisp

logior1.cert: logior1.lisp
logior1.cert: logior1-proofs.cert

lognot.cert: lognot.lisp
lognot.cert: ground-zero.cert
lognot.cert: ../../arithmetic/top.cert

logorc1.cert: logorc1.lisp
logorc1.cert: ground-zero.cert
logorc1.cert: logior.cert
logorc1.cert: ../../arithmetic/fl.cert
logorc1.cert: lognot.cert

logs.cert: logs.lisp

logxor.cert: logxor.lisp
logxor.cert: ground-zero.cert
logxor.cert: logeqv.cert
logxor.cert: logorc1.cert
logxor.cert: lognot.cert
logxor.cert: ../../arithmetic/top.cert

lop1-proofs.cert: lop1-proofs.lisp
lop1-proofs.cert: merge.cert
lop1-proofs.cert: bitn.cert
lop1-proofs.cert: bits.cert
lop1-proofs.cert: ../../arithmetic/top.cert

lop1.cert: lop1.lisp
lop1.cert: lop1-proofs.cert
lop1.cert: merge.cert

lop2-proofs.cert: lop2-proofs.lisp
lop2-proofs.cert: lop1.cert
lop2-proofs.cert: lior0.cert
lop2-proofs.cert: ../../arithmetic/top.cert
lop2-proofs.cert: bitn.cert
lop2-proofs.cert: bits.cert
lop2-proofs.cert: logior.cert

lop2.cert: lop2.lisp
lop2.cert: lop1.cert
lop2.cert: lior0.cert
lop2.cert: lop2-proofs.cert

lop3-proofs.cert: lop3-proofs.lisp
lop3-proofs.cert: lop2.cert
lop3-proofs.cert: ../../arithmetic/top.cert
lop3-proofs.cert: bitn.cert
lop3-proofs.cert: bits.cert
lop3-proofs.cert: land0.cert
lop3-proofs.cert: lior0.cert
lop3-proofs.cert: lxor0.cert

lop3.cert: lop3.lisp
lop3.cert: lop2.cert
lop3.cert: lop3-proofs.cert
lop3.cert: land0.cert
lop3.cert: lior0.cert
lop3.cert: lxor0.cert

lxor0-proofs.cert: lxor0-proofs.lisp
lxor0-proofs.cert: all-ones.cert
lxor0-proofs.cert: merge.cert
lxor0-proofs.cert: bvecp.cert
lxor0-proofs.cert: logand.cert
lxor0-proofs.cert: bits.cert
lxor0-proofs.cert: bitn.cert
lxor0-proofs.cert: ../../arithmetic/top.cert

lxor0.cert: lxor0.lisp
lxor0.cert: lxor0-proofs.cert

float.cert: float.lisp
float.cert: ../../arithmetic/top.cert
float.cert: ../../arithmetic/negative-syntaxp.cert
float.cert: ../../arithmetic/basic.cert
float.cert: ../../arithmetic/power2p.cert
float.cert: ../../arithmetic/fl.cert
float.cert: ../../arithmetic/cg.cert

sumbits.cert: sumbits.lisp
sumbits.cert: bitn.cert
sumbits.cert: bits.cert

merge.cert: merge.lisp
merge.cert: ground-zero.cert
merge.cert: log.cert
merge.cert: float.cert
merge.cert: ../../arithmetic/top.cert
merge.cert: bvecp.cert
merge.cert: bitn.cert
merge.cert: lnot.cert
merge.cert: bits.cert
merge.cert: logior.cert
merge.cert: logand.cert
merge.cert: logxor.cert
merge.cert: ocat.cert
merge.cert: sumbits.cert
merge.cert: cat.cert

model-helpers.cert: model-helpers.lisp
model-helpers.cert: rtl.cert
model-helpers.cert: bits.cert

badguys.cert: badguys.lisp
badguys.cert: merge.cert

mulcat-proofs.cert: mulcat-proofs.lisp
mulcat-proofs.cert: ../../arithmetic/top.cert
mulcat-proofs.cert: bvecp.cert
mulcat-proofs.cert: cat-def.cert
mulcat-proofs.cert: bits.cert
mulcat-proofs.cert: bitn.cert
mulcat-proofs.cert: cat.cert
mulcat-proofs.cert: merge.cert

mulcat.cert: mulcat.lisp
mulcat.cert: cat-def.cert
mulcat.cert: mulcat-proofs.cert

rewrite-theory.cert: rewrite-theory.lisp

rnd.cert: rnd.lisp
rnd.cert: float.cert
rnd.cert: trunc.cert
rnd.cert: away.cert
rnd.cert: near.cert
rnd.cert: near+.cert
rnd.cert: sticky.cert
rnd.cert: bitn.cert
rnd.cert: land0.cert
rnd.cert: lior0.cert
rnd.cert: merge.cert
rnd.cert: bits-trunc.cert

rom-helpers.cert: rom-helpers.lisp

rtl.cert: rtl.lisp
rtl.cert: ground-zero.cert
rtl.cert: rtlarr.cert
rtl.cert: cat-def.cert

rtlarr.cert: rtlarr.lisp
# rtlarr.cert: $(ACL2_SYSTEM_BOOKS)/misc/total-order.cert

setbits-proofs.cert: setbits-proofs.lisp
setbits-proofs.cert: cat-def.cert
setbits-proofs.cert: ../../arithmetic/top.cert
setbits-proofs.cert: bits.cert
setbits-proofs.cert: bitn.cert
setbits-proofs.cert: bvecp.cert
setbits-proofs.cert: cat.cert

setbits.cert: setbits.lisp
setbits.cert: cat-def.cert
setbits.cert: setbits-proofs.cert

setbitn-proofs.cert: setbitn-proofs.lisp
setbitn-proofs.cert: cat-def.cert
setbitn-proofs.cert: setbits.cert
setbitn-proofs.cert: ../../arithmetic/top.cert
setbitn-proofs.cert: bits.cert
setbitn-proofs.cert: cat.cert

setbitn.cert: setbitn.lisp
setbitn.cert: cat-def.cert
setbitn.cert: setbitn-proofs.cert

shft.cert: shft.lisp
shft.cert: ../../arithmetic/top.cert
shft.cert: bvecp.cert

sgn.cert: sgn.lisp
sgn.cert: float.cert

simple-loop-helpers.cert: simple-loop-helpers.lisp
simple-loop-helpers.cert: rtl.cert
simple-loop-helpers.cert: merge.cert
simple-loop-helpers.cert: bits.cert
simple-loop-helpers.cert: bitn.cert
simple-loop-helpers.cert: setbitn.cert

sticky-proofs.cert: sticky-proofs.lisp
sticky-proofs.cert: ../../arithmetic/arith.cert
sticky-proofs.cert: float.cert
sticky-proofs.cert: trunc.cert
sticky-proofs.cert: away.cert
sticky-proofs.cert: near.cert
sticky-proofs.cert: near+.cert

sticky.cert: sticky.lisp
sticky.cert: sticky-proofs.cert

trunc-proofs.cert: trunc-proofs.lisp
trunc-proofs.cert: ground-zero.cert
trunc-proofs.cert: float.cert
trunc-proofs.cert: ../../arithmetic/top.cert

trunc.cert: trunc.lisp
trunc.cert: ground-zero.cert
trunc.cert: trunc-proofs.cert

bits-trunc-proofs.cert: bits-trunc-proofs.lisp
bits-trunc-proofs.cert: trunc.cert
bits-trunc-proofs.cert: log.cert
bits-trunc-proofs.cert: float.cert
bits-trunc-proofs.cert: trunc.cert
bits-trunc-proofs.cert: bits.cert
bits-trunc-proofs.cert: ../../arithmetic/top.cert
bits-trunc-proofs.cert: land0.cert
bits-trunc-proofs.cert: merge.cert

bits-trunc.cert: bits-trunc.lisp
bits-trunc.cert: log.cert
bits-trunc.cert: float.cert
bits-trunc.cert: trunc.cert
bits-trunc.cert: land0.cert
bits-trunc.cert: bits-trunc-proofs.cert

away-proofs.cert: away-proofs.lisp
away-proofs.cert: trunc.cert
away-proofs.cert: ../../arithmetic/top.cert
away-proofs.cert: float.cert

away.cert: away.lisp
away.cert: away-proofs.cert

near-proofs.cert: near-proofs.lisp
near-proofs.cert: ../../arithmetic/top.cert
near-proofs.cert: float.cert
near-proofs.cert: away.cert
near-proofs.cert: trunc.cert

near.cert: near.lisp
near.cert: near-proofs.cert

near+-proofs.cert: near+-proofs.lisp
near+-proofs.cert: trunc.cert
near+-proofs.cert: away.cert
near+-proofs.cert: float.cert
near+-proofs.cert: ../../arithmetic/predicate.cert
near+-proofs.cert: ../../arithmetic/cg.cert
near+-proofs.cert: ../../arithmetic/fl.cert
near+-proofs.cert: ../../arithmetic/fl.cert
near+-proofs.cert: ../../arithmetic/integerp.cert
near+-proofs.cert: ../../arithmetic/top.cert

near+.cert: near+.lisp
near+.cert: near+-proofs.cert

oddr-proofs.cert: oddr-proofs.lisp
oddr-proofs.cert: ../../arithmetic/top.cert
oddr-proofs.cert: float.cert
oddr-proofs.cert: trunc.cert
oddr-proofs.cert: away.cert
oddr-proofs.cert: near.cert

oddr.cert: oddr.lisp
oddr.cert: oddr-proofs.cert

rnd.cert: rnd.lisp
rnd.cert: float.cert
rnd.cert: trunc.cert
rnd.cert: away.cert
rnd.cert: near.cert
rnd.cert: near+.cert
rnd.cert: sticky.cert
rnd.cert: bitn.cert
rnd.cert: land0.cert
rnd.cert: lior0.cert
rnd.cert: merge.cert
rnd.cert: bits-trunc.cert

util.cert: util.lisp

log-equal.cert: log-equal.lisp

lop1.cert: lop1.lisp
lop1.cert: lop1-proofs.cert
lop1.cert: merge.cert

lop2.cert: lop2.lisp
lop2.cert: lop1.cert
lop2.cert: lior0.cert
lop2.cert: lop2-proofs.cert

lop3.cert: lop3.lisp
lop3.cert: lop2.cert
lop3.cert: lop3-proofs.cert
lop3.cert: land0.cert
lop3.cert: lior0.cert
lop3.cert: lxor0.cert

ereps-proofs.cert: ereps-proofs.lisp
ereps-proofs.cert: rtl.cert
ereps-proofs.cert: float.cert
ereps-proofs.cert: bias.cert
ereps-proofs.cert: merge.cert
ereps-proofs.cert: cat.cert
ereps-proofs.cert: bvecp.cert
ereps-proofs.cert: bits.cert
ereps-proofs.cert: bitn.cert
ereps-proofs.cert: ../../arithmetic/top.cert
ereps-proofs.cert: mulcat.cert

ereps.cert: ereps.lisp
ereps.cert: rtl.cert
ereps.cert: float.cert
ereps.cert: ereps-proofs.cert

ireps.cert: ireps.lisp
ireps.cert: rtl.cert
ireps.cert: bias.cert
ireps.cert: float.cert
ireps.cert: merge.cert
ireps.cert: cat.cert
ireps.cert: bvecp.cert
ireps.cert: bits.cert
ireps.cert: bitn.cert
ireps.cert: ../../arithmetic/top.cert

stick-proofs.cert: stick-proofs.lisp
stick-proofs.cert: merge.cert
stick-proofs.cert: land0.cert
stick-proofs.cert: lior0.cert
stick-proofs.cert: lxor0.cert
stick-proofs.cert: ../../arithmetic/top.cert
stick-proofs.cert: bvecp.cert
stick-proofs.cert: bits.cert
stick-proofs.cert: bitn.cert
stick-proofs.cert: lnot.cert

stick.cert: stick.lisp
stick.cert: rtl.cert
stick.cert: stick-proofs.cert

drnd-original.cert: drnd-original.lisp
drnd-original.cert: merge.cert
drnd-original.cert: ireps.cert
drnd-original.cert: rnd.cert
drnd-original.cert: bias.cert
drnd-original.cert: sgn.cert
drnd-original.cert: bits.cert
drnd-original.cert: trunc.cert
drnd-original.cert: away.cert
drnd-original.cert: near.cert
drnd-original.cert: near+.cert
drnd-original.cert: sticky.cert
drnd-original.cert: ../../arithmetic/top.cert

merge2.cert: merge2.lisp
merge2.cert: merge.cert
merge2.cert: lior0.cert
merge2.cert: land0.cert
merge2.cert: lxor0.cert
merge2.cert: logs.cert
merge2.cert: bvecp.cert

fadd.cert: fadd.lisp
fadd.cert: stick.cert
fadd.cert: lop3.cert
fadd.cert: add3.cert
fadd.cert: bitn.cert
fadd.cert: bits.cert
fadd.cert: ../../arithmetic/top.cert
fadd.cert: rtl.cert
fadd.cert: float.cert
fadd.cert: lextra0.cert

clocks.cert: clocks.lisp
clocks.cert: mod4.cert
clocks.cert: ../../arithmetic/even-odd2.cert

openers.cert: openers.lisp

package-defs.cert: package-defs.lisp

simplify-model-helpers.cert: simplify-model-helpers.lisp
simplify-model-helpers.cert: rtl.cert
simplify-model-helpers.cert: bits.cert
simplify-model-helpers.cert: cat.cert

top1.cert: top1.lisp
top1.cert: util.cert
top1.cert: ground-zero.cert
top1.cert: rewrite-theory.cert
top1.cert: rtl.cert
top1.cert: rtlarr.cert
top1.cert: bvecp-lemmas.cert
top1.cert: bits.cert
top1.cert: bitn.cert
top1.cert: ocat.cert
top1.cert: cat-def.cert
top1.cert: cat.cert
top1.cert: bvecp.cert
top1.cert: ash.cert
top1.cert: decode.cert
top1.cert: encode.cert
top1.cert: mulcat.cert
top1.cert: shft.cert
top1.cert: all-ones.cert
top1.cert: merge2.cert
top1.cert: logior1.cert
top1.cert: setbits.cert
top1.cert: setbitn.cert
top1.cert: float.cert
top1.cert: bias.cert
top1.cert: ereps.cert
top1.cert: ireps.cert
top1.cert: logeqv.cert
top1.cert: logorc1.cert
top1.cert: lognot.cert
top1.cert: logand.cert
top1.cert: logior.cert
top1.cert: logxor.cert
top1.cert: log.cert
top1.cert: lnot.cert
top1.cert: land0.cert
top1.cert: lior0.cert
top1.cert: lxor0.cert
top1.cert: lextra0.cert
top1.cert: logs.cert
top1.cert: trunc.cert
top1.cert: away.cert
top1.cert: near.cert
top1.cert: near+.cert
top1.cert: oddr.cert
top1.cert: sticky.cert
top1.cert: rnd.cert
top1.cert: drnd-original.cert
top1.cert: bits-trunc.cert
top1.cert: add3.cert
top1.cert: lop1.cert
top1.cert: lop2.cert
top1.cert: lop3.cert
top1.cert: stick.cert
top1.cert: bvecp-helpers.cert
top1.cert: model-helpers.cert
top1.cert: rom-helpers.cert
top1.cert: simple-loop-helpers.cert
top1.cert: clocks.cert
top1.cert: openers.cert
top1.cert: package-defs.cert
top1.cert: simplify-model-helpers.cert
top1.cert: ../../arithmetic/top.cert
top1.cert: ../../arithmetic/fp.cert
top1.cert: fadd.cert

land.cert: land.lisp
land.cert: land0.cert
land.cert: top1.cert

lior.cert: lior.lisp
lior.cert: lior0.cert
lior.cert: top1.cert

lxor.cert: lxor.lisp
lxor.cert: lxor0.cert
lxor.cert: top1.cert

guards.cert: guards.lisp
guards.cert: rtl.cert
guards.cert: top1.cert
guards.cert: land.cert
guards.cert: lior.cert
guards.cert: lxor.cert

fadd-extra.cert: fadd-extra.lisp
fadd-extra.cert: fadd-extra0.cert
fadd-extra.cert: land.cert
fadd-extra.cert: lior.cert
fadd-extra.cert: lxor.cert
fadd-extra.cert: top1.cert

fadd-extra0.cert: fadd-extra0.lisp
fadd-extra0.cert: rtl.cert
fadd-extra0.cert: fadd.cert
fadd-extra0.cert: top1.cert

float-extra.cert: float-extra.lisp
float-extra.cert: sticky.cert
float-extra.cert: util.cert
float-extra.cert: top1.cert
# float-extra.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/inequalities.cert

round-extra.cert: round-extra.lisp
round-extra.cert: sticky.cert
round-extra.cert: util.cert
round-extra.cert: top1.cert
round-extra.cert: trunc.cert

top.cert: top.lisp
top.cert: top1.cert
top.cert: lextra.cert
top.cert: fadd-extra.cert
top.cert: float-extra.cert
top.cert: round-extra.cert
top.cert: guards.cert
top.cert: badguys.cert
