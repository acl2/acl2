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

bv-op-defthms.cert: bv-op-defthms.lisp
bv-op-defthms.cert: bv-op-defuns.cert

bv-op-defuns.cert: bv-op-defuns.lisp
bv-op-defuns.cert: misc.cert

misc.cert: misc.lisp
misc.cert: ../../../../arithmetic/equalities.cert
misc.cert: ../../../../arithmetic/inequalities.cert
misc.cert: ../../../../arithmetic-2/floor-mod/floor-mod.cert
misc.cert: ../../../../data-structures/list-defuns.cert
misc.cert: ../../../../data-structures/list-defthms.cert

padding-1-256.cert: padding-1-256.lisp
padding-1-256.cert: bv-op-defthms.cert

padding-384-512.cert: padding-384-512.lisp
padding-384-512.cert: bv-op-defthms.cert

parsing.cert: parsing.lisp
parsing.cert: padding-1-256.cert
parsing.cert: padding-384-512.cert

sha-1.cert: sha-1.lisp
sha-1.cert: parsing.cert
sha-1.cert: sha-functions.cert

sha-256.cert: sha-256.lisp
sha-256.cert: parsing.cert
sha-256.cert: sha-functions.cert

sha-384-512.cert: sha-384-512.lisp
sha-384-512.cert: parsing.cert
sha-384-512.cert: sha-functions.cert

sha-functions.cert: sha-functions.lisp
sha-functions.cert: bv-op-defthms.cert
