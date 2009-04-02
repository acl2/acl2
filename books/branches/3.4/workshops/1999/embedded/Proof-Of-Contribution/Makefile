include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Dependencies:

CRT.cert: CRT.lisp
CRT.cert: ../../../../arithmetic/mod-gcd.cert
CRT.cert: ../../../../rtl/rel1/lib1/basic.cert
CRT.cert: ../../../../rtl/rel1/support/fp.cert

CRTcorollaries.cert: CRTcorollaries.lisp
CRTcorollaries.cert: CRT.cert
CRTcorollaries.cert: ../../../../arithmetic/top-with-meta.cert
CRTcorollaries.cert: Minimal-Mod-Lemmas.cert

Disjoint-lists.cert: Disjoint-lists.lisp
Disjoint-lists.cert: Proof-Of-Equiv-From-M-Corr.cert

Generic.cert: Generic.lisp

Mapping.cert: Mapping.lisp
Mapping.cert: Generic.cert
Mapping.cert: Memory-Assoc.cert

Memory-Assoc.cert: Memory-Assoc.lisp

Minimal-Mod-Lemmas.cert: Minimal-Mod-Lemmas.lisp
Minimal-Mod-Lemmas.cert: private-qr-lemmas.cert

Proof-Of-Correctness-OneCycle.cert: Proof-Of-Correctness-OneCycle.lisp
Proof-Of-Correctness-OneCycle.cert: Disjoint-lists.cert

Proof-Of-Correctness.cert: Proof-Of-Correctness.lisp
Proof-Of-Correctness.cert: Proof-Of-Correctness-OneCycle.cert

Proof-Of-Equiv-From-M-Corr.cert: Proof-Of-Equiv-From-M-Corr.lisp
Proof-Of-Equiv-From-M-Corr.cert: CRTcorollaries.cert
Proof-Of-Equiv-From-M-Corr.cert: Mapping.cert

private-qr-lemmas.cert: private-qr-lemmas.lisp
private-qr-lemmas.cert: ../../../../ihs/ihs-init.cert
private-qr-lemmas.cert: ../../../../ihs/ihs-theories.cert
private-qr-lemmas.cert: ../../../../ihs/math-lemmas.cert

