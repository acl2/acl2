include ../../../../Makefile-generic
ACL2 = ../../../../../saved_acl2

# Omit ed5ba because it depends on ACL2(r):
BOOKS = ed1 ed2a ed2b ed3 ed4aa ed4ab ed4ba ed4bb ed4ca ed4cb ed4da ed4db ed5aa ed6a prime-fac

# From make dependencies:

ed1.cert: ed1.lisp
# ed1.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
ed1.cert: ed1.acl2

ed2a.cert: ed2a.lisp
# ed2a.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert

ed2b.cert: ed2b.lisp
# ed2b.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# ed2b.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert

ed3.cert: ed3.lisp
# ed3.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
ed3.cert: ed3.acl2

ed4aa.cert: ed4aa.lisp
ed4aa.cert: ed3.cert
# ed4aa.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# ed4aa.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
ed4aa.cert: ed4aa.acl2

ed4ab.cert: ed4ab.lisp
ed4ab.cert: ed3.cert
# ed4ab.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# ed4ab.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
ed4ab.cert: ed4ab.acl2

ed4ba.cert: ed4ba.lisp
ed4ba.cert: ed3.cert
# ed4ba.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# ed4ba.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
ed4ba.cert: ed4ba.acl2

ed4bb.cert: ed4bb.lisp
ed4bb.cert: ed3.cert
# ed4bb.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# ed4bb.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
ed4bb.cert: ed4bb.acl2

ed4ca.cert: ed4ca.lisp
ed4ca.cert: ed3.cert
# ed4ca.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# ed4ca.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
ed4ca.cert: ed4ca.acl2

ed4cb.cert: ed4cb.lisp
ed4cb.cert: ed3.cert
# ed4cb.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# ed4cb.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
ed4cb.cert: ed4cb.acl2

ed4da.cert: ed4da.lisp
ed4da.cert: ed3.cert
# ed4da.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# ed4da.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
ed4da.cert: ed4da.acl2

ed4db.cert: ed4db.lisp
ed4db.cert: ed3.cert
# ed4db.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# ed4db.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
ed4db.cert: ed4db.acl2

ed5aa.cert: ed5aa.lisp
ed5aa.cert: ed3.cert
# ed5aa.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# ed5aa.cert: $(ACL2_SYSTEM_BOOKS)/ihs/quotient-remainder-lemmas.cert
ed5aa.cert: ed5aa.acl2

ed6a.cert: ed6a.lisp
ed6a.cert: fld-u-poly/fuquot-rem.cert
ed6a.cert: ed3.cert
ed6a.cert: ed6a.acl2

prime-fac.cert: prime-fac.lisp
# prime-fac.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
# prime-fac.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/mod-gcd.cert
prime-fac.cert: prime-fac.acl2
