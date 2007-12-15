include ../Makefile-generic

# Dependencies:


csort.cert: csort.lisp

dft-ex.cert: dft-ex.lisp
dft-ex.cert: dft.cert
dft-ex.cert: ../arithmetic/top-with-meta.cert
dft-ex.cert: dft-ex.acl2

dft.cert: dft.lisp

fibonacci.cert: fibonacci.lisp
fibonacci.cert: int-division.cert
fibonacci.cert: grcd.cert

file-io.cert: file-io.lisp

goodstein.cert: goodstein.lisp
# goodstein.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert

grcd.cert: grcd.lisp
grcd.cert: int-division.cert
grcd.cert: ../ordinals/e0-ordinal.cert

hanoi.cert: hanoi.lisp
hanoi.cert: hanoi.acl2

hons-help2.cert: hons-help2.lisp
hons-help2.cert: hons-help.cert

hons-help.cert: hons-help.lisp

hons-tests.cert: hons-tests.lisp
hons-tests.cert: qi.cert

how-to-prove-thms.cert: how-to-prove-thms.lisp

int-division.cert: int-division.lisp
int-division.cert: ../arithmetic/equalities.cert
int-division.cert: ../arithmetic/inequalities.cert

integer-type-set-test.cert: integer-type-set-test.lisp

meta-lemmas.cert: meta-lemmas.lisp

misc.cert: misc.lisp
# misc.cert: $(ACL2_SYSTEM_BOOKS)/rtl/rel7/arithmetic/top.cert

mult.cert: mult.lisp
# mult.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
# mult.cert: $(ACL2_SYSTEM_BOOKS)/ihs/ihs-definitions.cert
# mult.cert: $(ACL2_SYSTEM_BOOKS)/ihs/ihs-lemmas.cert
# mult.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/structures.cert
# mult.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/array1.cert
# mult.cert: $(ACL2_SYSTEM_BOOKS)/ihs/@logops.cert
# mult.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defuns.cert
# mult.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/list-defthms.cert
# mult.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/deflist.cert
# mult.cert: $(ACL2_SYSTEM_BOOKS)/data-structures/defalist.cert
# mult.cert: $(ACL2_SYSTEM_BOOKS)/tools/meta-lemmas.cert

problem13.cert: problem13.lisp
problem13.cert: ../arithmetic/equalities.cert
problem13.cert: ../arithmetic/inequalities.cert
problem13.cert: ../ordinals/e0-ordinal.cert

process-book-readme.cert: process-book-readme.lisp

qi-correct.cert: qi-correct.lisp
# qi-correct.cert: $(ACL2_SYSTEM_BOOKS)/misc/qi.cert

qi.cert: qi.lisp
qi.cert: hons-help2.cert

radix.cert: radix.lisp
radix.cert: ../arithmetic-2/meta/top.cert
radix.cert: ../arithmetic-2/floor-mod/floor-mod.cert
radix.cert: radix.acl2

records0.cert: records0.lisp
records0.cert: total-order.cert

records.cert: records.lisp
records.cert: total-order.cert

rtl-untranslate.cert: rtl-untranslate.lisp
rtl-untranslate.cert: symbol-btree.cert

sin-cos.cert: sin-cos.lisp

sort-symbols.cert: sort-symbols.lisp

symbol-btree.cert: symbol-btree.lisp

total-order.cert: total-order.lisp

transfinite.cert: transfinite.lisp