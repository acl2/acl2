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

monomial.cert: monomial.lisp
monomial.cert: term.cert
# Added manually:
monomial.cert: monomial.acl2

npol-ordering-1.cert: npol-ordering-1.lisp
npol-ordering-1.cert: upol.cert
npol-ordering-1.cert: ordinal-ordering.cert
npol-ordering-1.cert: ../../../../../ordinals/ordinals-without-arithmetic.cert
# Added manually:
npol-ordering-1.cert: npol-ordering-1.acl2

npol-ordering-2.cert: npol-ordering-2.lisp
npol-ordering-2.cert: upol.cert
npol-ordering-2.cert: ordinal-ordering.cert
npol-ordering-2.cert: ../../../../../ordinals/ordinals-without-arithmetic.cert
# Added manually:
npol-ordering-2.cert: npol-ordering-2.acl2

ordinal-ordering.cert: ordinal-ordering.lisp
# Added manually:
ordinal-ordering.cert: ordinal-ordering.acl2

term.cert: term.lisp
# Added manually:
term.cert: term.acl2

upol.cert: upol.lisp
upol.cert: monomial.cert
# Added manually:
upol.cert: upol.acl2
