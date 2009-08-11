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

cfair.cert: cfair.lisp
cfair.cert: n2n.cert
cfair.cert: ../../../../ordinals/e0-ordinal.cert

example1.cert: example1.lisp
example1.cert: fair1.cert

example2.cert: example2.lisp
example2.cert: fair2.cert

example3.cert: example3.lisp
example3.cert: fair2.cert
example3.cert: ../../../../ordinals/e0-ordinal.cert

fair1.cert: fair1.lisp
fair1.cert: ../../../../ordinals/e0-ordinal.cert

fair2.cert: fair2.lisp
fair2.cert: ../../../../ordinals/e0-ordinal.cert
fair2.cert: n2n.cert

n2n.cert: n2n.lisp

simple.cert: simple.lisp
