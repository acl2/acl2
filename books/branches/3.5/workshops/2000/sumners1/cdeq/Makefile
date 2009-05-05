include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Dependencies:

cdeq-defs.cert: cdeq-defs.lisp
cdeq-defs.cert: records.cert
cdeq-defs.cert: ../../../../ordinals/e0-ordinal.cert

cdeq-phase1.cert: cdeq-phase1.lisp
cdeq-phase1.cert: cdeq-defs.cert

cdeq-phase2.cert: cdeq-phase2.lisp
cdeq-phase2.cert: cdeq-defs.cert

cdeq-phase3.cert: cdeq-phase3.lisp
cdeq-phase3.cert: cdeq-defs.cert

cdeq-phase4.cert: cdeq-phase4.lisp
cdeq-phase4.cert: cdeq-defs.cert

records.cert: records.lisp
records.cert: ../../../../misc/total-order.cert
