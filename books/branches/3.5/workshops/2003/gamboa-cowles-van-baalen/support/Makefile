# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

BOOKS = kalman-defs kalman-demo kalman-proof linalg

# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

kalman-defs.cert: kalman-defs.lisp
kalman-defs.cert: linalg.cert

kalman-demo.cert: kalman-demo.lisp
kalman-demo.cert: kalman-proof.cert

kalman-proof.cert: kalman-proof.lisp
kalman-proof.cert: kalman-defs.cert

linalg.cert: linalg.lisp
linalg.cert: ../../../../arithmetic/top.cert
linalg.cert: ../../cowles-gamboa-van-baalen_matrix/support/matalg.cert
