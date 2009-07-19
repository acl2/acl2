include ../../../../../Makefile-generic

ACL2 = ../../../../../../saved_acl2

# Dependencies:

Exercise1.2.cert: Exercise1.2.lisp
Exercise1.2.cert: ../../../../../arithmetic/mod-gcd.cert
Exercise1.2.cert: ../../../../../rtl/rel1/lib1/basic.cert
Exercise1.2.cert: ../../../../../rtl/rel1/support/fp.cert
Exercise1.2.cert: ../../../../../arithmetic/top-with-meta.cert
Exercise1.2.cert: Minimal-Mod-Lemmas.cert

Minimal-Mod-Lemmas.cert: Minimal-Mod-Lemmas.lisp
Minimal-Mod-Lemmas.cert: private-qr-lemmas.cert

private-qr-lemmas.cert: private-qr-lemmas.lisp
private-qr-lemmas.cert: ../../../../../ihs/ihs-init.cert
private-qr-lemmas.cert: ../../../../../ihs/ihs-theories.cert
private-qr-lemmas.cert: ../../../../../ihs/math-lemmas.cert
