include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2

# don't alphabetize this list!
BOOKS = bias bitn bits away trunc near bits-trunc bvecp cat ereps land lior decode lnot lxor lextra logior1 mulcat setbits setbitn stick sumbits brat top

# Dependencies:

bias.cert: bias.lisp
bias.cert: ../support/bias.cert

bitn.cert: bitn.lisp
bitn.cert: ../arithmetic/power2p.cert
bitn.cert: ../arithmetic/negative-syntaxp.cert
bitn.cert: ../support/bitn.cert
bitn.cert: ../support/guards.cert

bits.cert: bits.lisp
bits.cert: ../arithmetic/negative-syntaxp.cert
bits.cert: ../arithmetic/power2p.cert
bits.cert: ../support/bits.cert
bits.cert: ../support/guards.cert

away.cert: away.lisp
away.cert: trunc.cert
away.cert: ../support/away.cert

trunc.cert: trunc.lisp
trunc.cert: ../support/trunc.cert

near.cert: near.lisp
near.cert: ../support/near.cert

bits-trunc.cert: bits-trunc.lisp
bits-trunc.cert: land.cert
bits-trunc.cert: ../support/bits-trunc.cert

bvecp.cert: bvecp.lisp
bvecp.cert: ../support/bvecp.cert

cat.cert: cat.lisp
cat.cert: ../support/cat.cert
cat.cert: ../support/guards.cert

ereps.cert: ereps.lisp
ereps.cert: ../support/ereps.cert
ereps.cert: ../support/guards.cert

land.cert: land.lisp
land.cert: ../support/guards.cert
land.cert: ../support/land0.cert

lior.cert: lior.lisp
lior.cert: ../support/lior0.cert
lior.cert: ../support/guards.cert

decode.cert: decode.lisp
decode.cert: ../support/decode.cert

lnot.cert: lnot.lisp
lnot.cert: ../support/guards.cert
lnot.cert: ../support/lnot.cert

lxor.cert: lxor.lisp
lxor.cert: ../support/guards.cert
lxor.cert: ../support/lxor0.cert

lextra.cert: lextra.lisp
lextra.cert: land.cert
lextra.cert: lior.cert
lextra.cert: lxor.cert
lextra.cert: ../support/lextra0.cert

logior1.cert: logior1.lisp
logior1.cert: ../support/logior1.cert

mulcat.cert: mulcat.lisp
mulcat.cert: ../support/mulcat.cert
mulcat.cert: ../support/guards.cert

setbits.cert: setbits.lisp
setbits.cert: ../support/setbits.cert
setbits.cert: ../support/guards.cert

setbitn.cert: setbitn.lisp
setbitn.cert: ../support/setbitn.cert
setbitn.cert: ../support/guards.cert

stick.cert: stick.lisp
stick.cert: land.cert
stick.cert: lior.cert
stick.cert: lxor.cert
stick.cert: lnot.cert
stick.cert: ../support/stick.cert

sumbits.cert: sumbits.lisp
sumbits.cert: ../support/sumbits.cert
sumbits.cert: ../support/guards.cert

brat.cert: brat.lisp
brat.cert: ../arithmetic/fl.cert

top.cert: top.lisp
top.cert: bits.cert
top.cert: bitn.cert
top.cert: cat.cert
top.cert: bvecp.cert
top.cert: mulcat.cert
top.cert: logior1.cert
top.cert: setbits.cert
top.cert: setbitn.cert
top.cert: bias.cert
top.cert: ereps.cert
top.cert: lnot.cert
top.cert: land.cert
top.cert: lior.cert
top.cert: lxor.cert
top.cert: lextra.cert
top.cert: trunc.cert
top.cert: away.cert
top.cert: near.cert
top.cert: bits-trunc.cert
top.cert: stick.cert
top.cert: sumbits.cert
