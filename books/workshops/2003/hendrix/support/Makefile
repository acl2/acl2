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

madd.cert: madd.lisp
madd.cert: mdefthms.cert
madd.cert: mzero.cert
madd.cert: mentry.cert

matrices.cert: matrices.lisp
matrices.cert: vector.cert
matrices.cert: mdefuns.cert
matrices.cert: mdefthms.cert
matrices.cert: mentry.cert
matrices.cert: mzero.cert
matrices.cert: madd.cert
matrices.cert: mscal.cert
matrices.cert: msub.cert
matrices.cert: mid.cert
matrices.cert: mmult.cert
matrices.cert: mtrans.cert

mdefthms.cert: mdefthms.lisp
mdefthms.cert: mdefuns.cert

mdefuns.cert: mdefuns.lisp
mdefuns.cert: vector.cert

mentry.cert: mentry.lisp
mentry.cert: mdefthms.cert

mid.cert: mid.lisp
mid.cert: mdefthms.cert

mmult.cert: mmult.lisp
mmult.cert: mdefthms.cert
mmult.cert: mzero.cert
mmult.cert: madd.cert
mmult.cert: mscal.cert
mmult.cert: mid.cert
mmult.cert: mentry.cert

mscal.cert: mscal.lisp
mscal.cert: mdefthms.cert
mscal.cert: mzero.cert
mscal.cert: madd.cert
mscal.cert: mentry.cert

msub.cert: msub.lisp
msub.cert: mdefthms.cert
msub.cert: madd.cert
msub.cert: mscal.cert

mtrans.cert: mtrans.lisp
mtrans.cert: mdefthms.cert
mtrans.cert: mzero.cert
mtrans.cert: madd.cert
mtrans.cert: mid.cert
mtrans.cert: mscal.cert
mtrans.cert: mmult.cert
mtrans.cert: mentry.cert

mzero.cert: mzero.lisp
mzero.cert: mdefthms.cert

vector.cert: vector.lisp
vector.cert: ../../../../arithmetic/top-with-meta.cert
