include ../../Makefile-generic
ACL2 = ../../../saved_acl2

BOOKS = instance computed-hints \
        primitives membership fast outer sort \
        sets set-order \
        quantify map

reallyclean:
	rm -f *~ \#*

# dependencies...

instance.cert: instance.lisp
instance.cert: cert.acl2

computed-hints.cert: computed-hints.lisp
computed-hints.cert: instance.cert
computed-hints.cert: cert.acl2

primitives.cert: primitives.lisp
primitives.cert: cert.acl2

membership.cert: membership.lisp
membership.cert: primitives.cert
membership.cert: computed-hints.cert
membership.cert: cert.acl2

fast.cert: fast.lisp
fast.cert: membership.cert
fast.cert: cert.acl2

outer.cert: outer.lisp
outer.cert: fast.cert
outer.cert: cert.acl2

sort.cert: sort.lisp
sort.cert: outer.cert
sort.cert: cert.acl2

sets.cert: sets.lisp
sets.cert: computed-hints.cert
sets.cert: primitives.cert
sets.cert: membership.cert
sets.cert: fast.cert
sets.cert: outer.cert
sets.cert: sort.cert
sets.cert: cert.acl2

set-order.cert: set-order.lisp
set-order.cert: primitives.cert
set-order.cert: membership.cert
set-order.cert: fast.cert
set-order.cert: sets.cert
set-order.cert: cert.acl2

quantify.cert: quantify.lisp
quantify.cert: sets.cert
quantify.cert: sets.cert
quantify.cert: cert.acl2

map.cert: map.lisp
# map.cert: sets.cert # from a comment
map.cert: quantify.cert
map.cert: cert.acl2

cert.acl2: sets.defpkg
