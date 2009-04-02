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

generic-theory.cert: generic-theory.lisp

generic-multiset.cert: generic-multiset.lisp
generic-multiset.cert: generic-theory.cert

multiset-list.cert: multiset-list.lisp
multiset-list.cert: generic-multiset.cert

multiset-assoc.cert: multiset-assoc.lisp
multiset-assoc.cert: generic-multiset.cert

#==============================================================================