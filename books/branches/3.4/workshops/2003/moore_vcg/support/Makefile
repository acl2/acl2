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

demo.cert: demo.lisp
demo.cert: utilities.cert

m5.cert: m5.lisp
m5.cert: ../../../../ordinals/e0-ordinal.cert

utilities.cert: utilities.lisp
utilities.cert: m5.cert
utilities.cert: ../../../../arithmetic/top-with-meta.cert
utilities.cert: ../../../../ihs/quotient-remainder-lemmas.cert

vcg-examples.cert: vcg-examples.lisp
vcg-examples.cert: utilities.cert
vcg-examples.cert: ../../../../misc/defpun.cert
vcg-examples.cert: demo.cert
