# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../../../../Makefile-generic

ACL2 = ../../../../../../saved_acl2

# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

set-theory-original.cert: set-theory-original.lisp
set-theory-original.cert: total-ordering-original.cert
set-theory-original.cert: ../../../../../arithmetic/top-with-meta.cert

set-theory.cert: set-theory.lisp
set-theory.cert: total-ordering.cert
set-theory.cert: ../../../../../arithmetic/top-with-meta.cert

total-ordering-original.cert: total-ordering-original.lisp

total-ordering.cert: total-ordering.lisp
