include ../Makefile-generic

#  Put dependencies (from `make -s dependencies', or other sources) below.

BOOKS = euclid fermat euler gauss eisenstein mersenne

euclid.cert: euclid.lisp
# euclid.cert: $(ACL2_SYSTEM_BOOKS)/rtl/rel7/lib/arith.cert
# euclid.cert: $(ACL2_SYSTEM_BOOKS)/rtl/rel7/lib/basic.cert

fermat.cert: fermat.lisp
fermat.cert: euclid.cert

euler.cert: euler.lisp
euler.cert: fermat.cert

gauss.cert: gauss.lisp
gauss.cert: euler.cert

eisenstein.cert: eisenstein.lisp
eisenstein.cert: gauss.cert

mersenne.cert: mersenne.lisp
mersenne.cert: gauss.cert
