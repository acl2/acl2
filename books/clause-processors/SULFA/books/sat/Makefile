
# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS ?= $(shell cd ../../../.. ; pwd)

# Avoid provisional certification since we are not using Makefile-deps
# (which is because there is a generated .lisp file and the existing
# dependencies in this file appear rather complicated).
override ACL2_PCERT =

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 ?= ${ACL2_SYSTEM_BOOKS}/../saved_acl2

BOOKS = sat \
        local-clause-simp \
        check-output \
        convert-to-cnf \
        sat-setup \
        neq-implication \
        user-entry-data-structure \
        sulfa-dir-const \
        recognizer

clean: sat-clean

# Pasted in from "make dependencies":
sat-clean: 
	rm -f \#*\# *.cert *~ *.sexpr *.d *.sot sulfa-dir-const.lisp sat-setup.data
	rm -f -r sat-temp-files

.PHONY: sat-clean

sulfa-dir-const.lisp:
	rm -f ${@} ; \
${PERL} ../../scripts/interpret_sulfa_file < ${@}.isf > ${@} ; \
chmod ug+x-w ${@} ; \
sleep 2

sulfa-dir-const.lisp: sulfa-dir-const.lisp.isf

sulfa-dir-const.lisp: ../../scripts/interpret_sulfa_file

sat.cert: sat.lisp
local-clause-simp.cert: local-clause-simp.lisp
check-output.cert: check-output.lisp
convert-to-cnf.cert: convert-to-cnf.lisp
sat-setup.cert: sat-setup.lisp
user-entry-data-structure.cert: user-entry-data-structure.lisp
recognizer.cert: recognizer.lisp
neq-implication.cert: neq-implication.lisp
sulfa-dir-const.cert: sulfa-dir-const.lisp

sat.cert: sat.acl2
local-clause-simp.cert: cert.acl2
check-output.cert: cert.acl2 
convert-to-cnf.cert: cert.acl2 
sat-setup.cert: cert.acl2 
user-entry-data-structure.cert: cert.acl2 
recognizer.cert: cert.acl2 
neq-implication.cert: cert.acl2 
sulfa-dir-const.cert: cert.acl2 

user-entry-data-structure.cert: sat-package.acl2
recognizer.cert: sat-package.acl2
sat.cert: sat-package.acl2
local-clause-simp.cert: sat-package.acl2
check-output.cert: sat-package.acl2
convert-to-cnf.cert: sat-package.acl2
sat-setup.cert: sat-package.acl2

sat.cert: sulfa-dir-const.cert
sat.cert: convert-to-cnf.cert
sat.cert: local-clause-simp.cert
sat.cert: check-output.cert
sat.cert: recognizer.cert
sat.cert: user-entry-data-structure.cert
#sat.cert: ../external/external.cert

user-entry-data-structure.cert: convert-to-cnf.cert
user-entry-data-structure.cert: check-output.cert

local-clause-simp.cert: sat-setup.cert

recognizer.cert: sat-setup.cert

check-output.cert: convert-to-cnf.cert
check-output.cert: recognizer.cert

neq-implication.cert: sat-setup.cert
neq-implication.cert: local-clause-simp.cert

convert-to-cnf.cert: sat-setup.cert
convert-to-cnf.cert: local-clause-simp.cert
convert-to-cnf.cert: neq-implication.cert



