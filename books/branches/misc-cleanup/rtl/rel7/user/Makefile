include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2

# don't alphabetize this list!
BOOKS = bias bitn bits away trunc near bits-trunc bvecp cat ereps land lior decode lnot lxor lextra logior1 mulcat setbits setbitn stick sumbits brat top

# Dependencies:
bias.cert: bias.lisp
bias.cert: ../support/support/bias.cert

bitn.cert: bitn.lisp
bitn.cert: ../arithmetic/power2p.cert
bitn.cert: ../arithmetic/negative-syntaxp.cert
bitn.cert: ../support/support/bitn.cert
bitn.cert: ../support/support/guards.cert

bits.cert: bits.lisp
bits.cert: ../arithmetic/negative-syntaxp.cert
bits.cert: ../arithmetic/power2p.cert
bits.cert: ../support/support/bits.cert
bits.cert: ../support/support/guards.cert

away.cert: away.lisp
away.cert: trunc.cert
away.cert: ../support/support/away.cert

trunc.cert: trunc.lisp
trunc.cert: ../support/support/trunc.cert

near.cert: near.lisp
near.cert: ../support/support/near.cert

bits-trunc.cert: bits-trunc.lisp
bits-trunc.cert: land.cert
bits-trunc.cert: ../support/support/bits-trunc.cert

bvecp.cert: bvecp.lisp
bvecp.cert: ../support/support/bvecp.cert

cat.cert: cat.lisp
cat.cert: ../support/support/cat.cert
cat.cert: ../support/support/guards.cert

ereps.cert: ereps.lisp
ereps.cert: ../support/support/ereps.cert
ereps.cert: ../support/support/guards.cert

land.cert: land.lisp
land.cert: ../support/support/guards.cert
land.cert: ../support/support/land0.cert

lior.cert: lior.lisp
lior.cert: ../support/support/lior0.cert
lior.cert: ../support/support/guards.cert

decode.cert: decode.lisp
decode.cert: ../support/support/decode.cert

lnot.cert: lnot.lisp
lnot.cert: ../support/support/guards.cert
lnot.cert: ../support/support/lnot.cert

lxor.cert: lxor.lisp
lxor.cert: ../support/support/guards.cert
lxor.cert: ../support/support/lxor0.cert

lextra.cert: lextra.lisp
lextra.cert: land.cert
lextra.cert: lior.cert
lextra.cert: lxor.cert
lextra.cert: ../support/support/lextra0.cert

logior1.cert: logior1.lisp
logior1.cert: ../support/support/logior1.cert

mulcat.cert: mulcat.lisp
mulcat.cert: ../support/support/mulcat.cert
mulcat.cert: ../support/support/guards.cert

setbits.cert: setbits.lisp
setbits.cert: ../support/support/setbits.cert
setbits.cert: ../support/support/guards.cert

setbitn.cert: setbitn.lisp
setbitn.cert: ../support/support/setbitn.cert
setbitn.cert: ../support/support/guards.cert

stick.cert: stick.lisp
stick.cert: land.cert
stick.cert: lior.cert
stick.cert: lxor.cert
stick.cert: lnot.cert
stick.cert: ../support/support/stick.cert

sumbits.cert: sumbits.lisp
sumbits.cert: ../support/support/sumbits.cert
sumbits.cert: ../support/support/guards.cert

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
