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

WyoM1-correct.cert: WyoM1-correct.lisp
WyoM1-correct.cert: WyoM1-utilities.cert
WyoM1-correct.cert: WyoM1-utilities.cert
WyoM1-correct.cert: ../../../../misc/defpun.cert

WyoM1-utilities.cert: WyoM1-utilities.lisp
WyoM1-utilities.cert: WyoM1.cert
WyoM1-utilities.cert: WyoM1.cert
WyoM1-utilities.cert: ../../../../arithmetic/top.cert

WyoM1.cert: WyoM1.lisp

knuth.cert: knuth.lisp
knuth.cert: ../../../../arithmetic/top.cert

tail-rec.cert: tail-rec.lisp
tail-rec.cert: ../../../../misc/defpun.cert
