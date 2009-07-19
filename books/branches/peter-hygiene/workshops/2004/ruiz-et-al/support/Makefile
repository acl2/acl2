# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

basic.cert: basic.lisp
# basic.cert: arithmetic/top-with-meta.cert

dags.cert: dags.lisp
dags.cert: basic.cert
dags.cert: lists.cert

dag-unification-rules.cert: dag-unification-rules.lisp
dag-unification-rules.cert: dags.cert
dag-unification-rules.cert: prefix-unification-rules.cert

lists.cert: lists.lisp

matching.cert: matching.lisp
matching.cert: terms.cert

prefix-unification-rules.cert: prefix-unification-rules.lisp
prefix-unification-rules.cert: subsumption-subst.cert

q-dag-unification.cert: q-dag-unification.lisp
q-dag-unification.cert: q-dag-unification-rules.cert
q-dag-unification.cert: terms-as-dag.cert

q-dag-unification-rules.cert: q-dag-unification-rules.lisp
q-dag-unification-rules.cert: dag-unification-rules.cert

q-dag-unification-st.cert: q-dag-unification-st.lisp
q-dag-unification-st.cert: q-dag-unification.cert

subsumption.cert: subsumption.lisp
subsumption.cert: matching.cert
subsumption.cert: terms.cert

subsumption-subst.cert: subsumption-subst.lisp
subsumption-subst.cert: subsumption.cert

terms-as-dag.cert: terms-as-dag.lisp
terms-as-dag.cert: dag-unification-rules.cert

terms.cert: terms.lisp
terms.cert: basic.cert
