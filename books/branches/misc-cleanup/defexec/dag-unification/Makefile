# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../Makefile-generic

ACL2 = ../../../saved_acl2

# Dependencies:
# In the shell, execute
# make dependencies
# to obtain the result below.

basic.cert: basic.lisp
# basic.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert

dag-unification-l.cert: dag-unification-l.lisp
dag-unification-l.cert: dag-unification-rules.cert
dag-unification-l.cert: terms-as-dag.cert

dag-unification-rules.cert: dag-unification-rules.lisp
dag-unification-rules.cert: dags.cert
dag-unification-rules.cert: list-unification-rules.cert

dag-unification-st.cert: dag-unification-st.lisp
dag-unification-st.cert: dag-unification-l.cert
dag-unification-st.cert: terms-dag-stobj.cert

dags.cert: dags.lisp
dags.cert: basic.cert

list-unification-rules.cert: list-unification-rules.lisp
list-unification-rules.cert: subsumption-subst.cert

matching.cert: matching.lisp
matching.cert: terms.cert

subsumption.cert: subsumption.lisp
subsumption.cert: matching.cert
subsumption.cert: terms.cert

subsumption-subst.cert: subsumption-subst.lisp
subsumption-subst.cert: subsumption.cert

terms-as-dag.cert: terms-as-dag.lisp
terms-as-dag.cert: dag-unification-rules.cert

terms-dag-stobj.cert: terms-dag-stobj.lisp
terms-dag-stobj.cert: dag-unification-rules.cert

terms.cert: terms.lisp
terms.cert: basic.cert
