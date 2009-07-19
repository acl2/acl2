include ../../../Makefile-generic

ACL2 = ../../../../saved_acl2

# Override default setting since solutions.lisp is not intended to be certified.
BOOKS = find-path1 find-path2 find-path3 helpers linear-find-path

# Dependencies:

find-path1.cert: find-path1.lisp
find-path1.cert: ../../../arithmetic/top.cert
find-path1.cert: ../../../ordinals/e0-ordinal.cert

find-path2.cert: find-path2.lisp
find-path2.cert: ../../../arithmetic/top.cert
find-path2.cert: helpers.cert
find-path2.cert: ../../../ordinals/e0-ordinal.cert

find-path3.cert: find-path3.lisp
find-path3.cert: ../../../arithmetic/top.cert
find-path3.cert: helpers.cert
find-path3.cert: ../../../ordinals/e0-ordinal.cert

helpers.cert: helpers.lisp

linear-find-path.cert: linear-find-path.lisp
linear-find-path.cert: find-path3.cert

# solutions.cert: solutions.lisp
# solutions.cert: find-path3.cert
# solutions.cert: linear-find-path.cert
