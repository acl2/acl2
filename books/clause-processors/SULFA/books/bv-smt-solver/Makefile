
# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
#ACL2_SYSTEM_BOOKS = /projects/hvg/reeber-local/v2-9-4-linux/books

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

BOOKS = translation \
        bv-lib-definitions \
        bv-lib-lemmas \
        bv-lib \
        redundancy-removal \
        smt

clean: sat-clean

# Pasted in from "make dependencies":
sat-clean: 
	rm -f *.cert *~ *.sexpr *.d *.sot *~ \#*\# *.smt *.prepped
	rm -fr sat-temp-files 
	rm -f *.bak

translation.cert: translation.lisp
bv-lib-definitions.cert: bv-lib-definitions.lisp
bv-lib-lemmas.cert: bv-lib-lemmas.lisp
bv-lib.cert: bv-lib.lisp
smt.cert: smt.lisp
redundancy-removal.cert: redundancy-removal.lisp

redundancy-removal.cert: redundancy-removal.acl2
translation.cert: translation.acl2
bv-lib-definitions.cert: bv-lib-definitions.acl2
bv-lib-lemmas.cert: bv-lib-lemmas.acl2
bv-lib.cert: bv-lib.acl2
smt.cert: smt.acl2

bv-lib-lemmas.cert: bv-lib-definitions.cert
bv-lib-lemmas.cert: ../clause-processors/sat-clause-processor.cert

bv-lib.cert: bv-lib-lemmas.cert

smt.cert: bv-lib.cert
smt.cert: redundancy-removal.cert

#smt.cert: ${ACL2_SYSTEM_BOOKS}/misc/expander.cert

#${ACL2_SYSTEM_BOOKS}/misc/expander.cert:
#	${MAKE} -C ${ACL2_SYSTEM_BOOKS}/misc/expander.cert

bv-lib-definitions.cert: ../clause-processors/sym-str.cert

translation.cert: ../clause-processors/sym-str.cert
translation.cert: bv-lib.cert

redundancy-removal.cert: ../sat/sat.cert



