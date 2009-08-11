include ../../../../../Makefile-generic

# Pasted in from "make dependencies":

abstract-proofs.cert: abstract-proofs.lisp
# abstract-proofs.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/structures.cert

confluence.cert: confluence.lisp
confluence.cert: abstract-proofs.cert
confluence.cert: confluence.acl2

convergent.cert: convergent.lisp
convergent.cert: confluence.cert
convergent.cert: newman.cert
convergent.cert: convergent.acl2

newman.cert: newman.lisp
newman.cert: ../multisets/defmul.cert
newman.cert: abstract-proofs.cert
newman.cert: newman.acl2
