# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../../../../Makefile-generic


# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

records-original.cert: records-original.lisp

records.cert: records.lisp
records.cert: total-order.cert

total-order.cert: total-order.lisp
total-order.cert: ../../../../../misc/total-order.cert
