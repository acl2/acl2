# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# List books explicitly to avoid vhdl-acl2, which is not certifiable (has forms
# that are not embedded event forms).
BOOKS = acl2-transl generates-functions generates-theorems utils

# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

acl2-transl.cert: acl2-transl.lisp
acl2-transl.cert: utils.cert
acl2-transl.cert: generates-functions.cert
acl2-transl.cert: generates-theorems.cert

generates-functions.cert: generates-functions.lisp
generates-functions.cert: utils.cert

generates-theorems.cert: generates-theorems.lisp
generates-theorems.cert: utils.cert

utils.cert: utils.lisp
utils.cert: ../../../../arithmetic/top.cert
utils.cert: ../../../../ihs/ihs-definitions.cert
utils.cert: ../../../../ihs/ihs-lemmas.cert
utils.cert: ../../../../misc/expander.cert

vhdl-acl2.cert: vhdl-acl2.lisp
vhdl-acl2.cert: acl2-transl.cert
