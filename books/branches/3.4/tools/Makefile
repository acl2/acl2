include ../Makefile-generic

# Dependencies:

bstar.cert: bstar.lisp
bstar.cert: pack.cert

cws.cert: cws.lisp
cws.cert: progndollar.cert

defsum.cert: defsum.lisp
defsum.cert: pattern-match.cert
defsum.cert: types-misc.cert
#defsum.cert: arithmetic/top-with-meta.cert

deftuple.cert: deftuple.lisp
deftuple.cert: types-misc.cert
deftuple.cert: bstar.cert
#deftuple.cert: arithmetic/top-with-meta.cert

pack.cert: pack.lisp

pattern-match.cert: pattern-match.lisp

progndollar.cert: progndollar.lisp

theory-tools.cert: theory-tools.lisp

types-misc.cert: types-misc.lisp
types-misc.cert: theory-tools.cert