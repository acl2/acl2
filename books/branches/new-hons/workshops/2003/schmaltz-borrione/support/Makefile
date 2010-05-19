# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../../../Makefile-generic


# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

arbiter.cert: arbiter.lisp
arbiter.cert: inequalities.cert
arbiter.cert: decoder.cert
arbiter.cert: predicates.cert

decoder.cert: decoder.lisp
decoder.cert: ../../../../arithmetic/top.cert
decoder.cert: ../../../../arithmetic-2/floor-mod/floor-mod.cert

inequalities.cert: inequalities.lisp
inequalities.cert: ../../../../arithmetic/top.cert

predicates.cert: predicates.lisp

transfers.cert: transfers.lisp
transfers.cert: decoder.cert
transfers.cert: arbiter.cert

