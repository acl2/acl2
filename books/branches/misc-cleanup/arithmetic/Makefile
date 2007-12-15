include ../Makefile-generic

# Unfortunately, we cannot certify top-with-meta until we have completed
# certification in the meta/ directory.  So we set BOOKS so that
# top-with-meta.cert is not made by default.  The ":=" makes the assignment
# non-recursive.

BOOKS := $(filter-out top-with-meta,$(BOOKS))

# Dependencies:

abs.cert: abs.lisp
abs.cert: top.cert

binomial.cert: binomial.lisp
binomial.cert: top.cert
binomial.cert: factorial.cert
binomial.cert: sumlist.cert

equalities.cert: equalities.lisp
equalities.cert: ../cowles/acl2-crg.cert
equalities.cert: equalities.acl2

factorial.cert: factorial.lisp

idiv.cert: idiv.lisp
idiv.cert: top.cert

inequalities.cert: inequalities.lisp
inequalities.cert: equalities.cert

mod-gcd.cert: mod-gcd.lisp
mod-gcd.cert: inequalities.cert

natp-posp.cert: natp-posp.lisp
natp-posp.cert: inequalities.cert

rational-listp.cert: rational-listp.lisp

rationals.cert: rationals.lisp
rationals.cert: inequalities.cert
rationals.cert: inequalities.cert
rationals.cert: mod-gcd.cert

sumlist.cert: sumlist.lisp

# Added manually:
top-with-meta.cert: top-with-meta.lisp
top-with-meta.cert: top.cert
top-with-meta.cert: ../meta/meta.cert

top.cert: top.lisp
top.cert: equalities.cert
top.cert: rational-listp.cert
# The following two are for the nonstd books (ACL2(r)) only.
# top.cert: realp.cert
# top.cert: real-listp.cert
top.cert: inequalities.cert
top.cert: natp-posp.cert
top.cert: rationals.cert
