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

insertion-sort.cert: insertion-sort.lisp
insertion-sort.cert: perm-order.cert

perm-order.cert: perm-order.lisp
perm-order.cert: perm.cert
perm-order.cert: total-order.cert

perm.cert: perm.lisp

quicksort.cert: quicksort.lisp
quicksort.cert: insertion-sort.cert

total-order.cert: total-order.lisp
total-order.cert: ../../../../../misc/total-order.cert
