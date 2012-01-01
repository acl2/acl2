
# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
#ACL2_SYSTEM_BOOKS = /projects/hvg/reeber-local/v2-9-4-linux/books
ACL2_SYSTEM_BOOKS = ../../../..

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

sat-clean: 
	rm -f *.cert *~ *.sexpr *.d *.sot *~ \#*\# *.smt *.prepped
	rm -fr sat-temp-files 
	rm -f *.bak

-include Makefile-deps

#${ACL2_SYSTEM_BOOKS}/misc/expander.cert:
#	${MAKE} -C ${ACL2_SYSTEM_BOOKS}/misc/expander.cert
