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

alist2.cert: alist2.lisp

array2.cert: array2.lisp

matalg.cert: matalg.lisp
matalg.cert: alist2.cert
matalg.cert: matrix.cert

matrix.cert: matrix.lisp
matrix.cert: ../../../../arithmetic/top.cert
matrix.cert: array2.cert
matrix.cert: alist2.cert
