include ../../../../../../Makefile-generic

ACL2 = ../../../../../../../saved_acl2

# Override default setting since only the solutions are to be certified.

BOOKS = solution1 solution2 solution3 solution4 solution5 solution6

solution1.cert: solution1.lisp
solution1.cert: ../base.cert

solution2.cert: solution2.lisp
solution2.cert: ../sk-misc-lemmas.cert

solution3.cert: solution3.lisp
solution3.cert: ../wfftype.cert

solution4.cert: solution4.lisp
solution4.cert: ../stage.cert
solution4.cert: ../close.cert
solution4.cert: ../../../../../../ordinals/e0-ordinal.cert

solution5.cert: solution5.lisp
solution5.cert: ../base.cert
solution5.cert: ../../../../../../ordinals/e0-ordinal.cert

solution6.cert: solution6.lisp
