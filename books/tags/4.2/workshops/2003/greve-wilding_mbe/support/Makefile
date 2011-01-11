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

fpst.cert: fpst.lisp
fpst.cert: ../../../1999/graph/linear-find-path.cert
fpst.cert: ../../../../ordinals/e0-ordinal.cert

run-fpst.cert: run-fpst.lisp
run-fpst.cert: fpst.cert
