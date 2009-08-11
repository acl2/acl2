include ../../../../Makefile-generic


BOOKS = instance computed-hints \
        primitives membership fast outer sort \
        sets set-order \
        quantify map

instance.cert: instance.lisp
instance.cert: package.lisp

primitives.cert: primitives.lisp
primitives.cert: package.lisp

computed-hints.cert: instance.cert
computed-hints.cert: computed-hints.lisp 

membership.cert: membership.lisp
membership.cert: primitives.cert
membership.cert: computed-hints.cert

fast.cert: fast.lisp
fast.cert: membership.cert

outer.cert: outer.lisp
outer.cert: fast.cert

sort.cert: sort.lisp
sort.cert: outer.cert

set-order.cert: set-order.lisp
set-order.cert: primitives.cert
set-order.cert: membership.cert
set-order.cert: fast.cert
set-order.cert: sets.cert

sets.cert: sets.lisp
sets.cert: primitives.cert
sets.cert: membership.cert
sets.cert: fast.cert
sets.cert: outer.cert
sets.cert: sort.cert

quantify.cert : quantify.lisp
quantify.cert : sets.cert

map.cert: quantify.cert
map.cert: map.lisp

