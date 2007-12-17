# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Override default setting since TMP.lisp, TMP1.lisp, and
# dag-unification-examples.lisp are not intended to be certified.
BOOKS = basic dag-unification dags defpun terms

# Extend clean target to remove TMP.lisp and TMP1.lisp
clean: clean-TMPs

clean-TMPs:
	rm -f TMP.lisp TMP1.lisp

# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

basic.cert: basic.lisp
basic.cert: ../../../../arithmetic/top-with-meta.cert

dag-unification.cert: dag-unification.lisp
dag-unification.cert: terms.cert

dags.cert: dags.lisp
dags.cert: basic.cert
dags.cert: ../../../../ordinals/e0-ordinal.cert

defpun.cert: defpun.lisp

terms.cert: terms.lisp
terms.cert: basic.cert
