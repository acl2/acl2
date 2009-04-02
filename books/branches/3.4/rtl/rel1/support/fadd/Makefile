include ../../../../Makefile-generic
ACL2 = ../../../../../saved_acl2
 
# Dependencies:
 
add3.cert: add3.lisp
add3.cert: stick.cert

lop1.cert: lop1.lisp
lop1.cert: ../../lib1/top.cert
lop1.cert: ../fp.cert

lop2.cert: lop2.lisp
lop2.cert: lop1.cert

lop3.cert: lop3.lisp
lop3.cert: lop2.cert

stick.cert: stick.lisp
stick.cert: lop3.cert

top.cert: top.lisp
top.cert: lop3.cert
