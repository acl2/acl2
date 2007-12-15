include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2

# Dependencies:

extraction.cert: extraction.lisp
extraction.cert: programs.cert
extraction.cert: intermediate-program.cert
extraction.cert: first-last.cert

final-theorem.cert: final-theorem.lisp
final-theorem.cert: sort-qs-properties.cert
final-theorem.cert: load-extract.cert

first-last.cert: first-last.lisp
first-last.cert: programs.cert

intermediate-program.cert: intermediate-program.lisp
intermediate-program.cert: total-order.cert
intermediate-program.cert: permutations.cert

intermediate-to-spec.cert: intermediate-to-spec.lisp
intermediate-to-spec.cert: intermediate-program.cert
intermediate-to-spec.cert: spec-properties.cert

load-extract.cert: load-extract.lisp
load-extract.cert: programs.cert
load-extract.cert: first-last.cert
load-extract.cert: extraction.cert

merge-intermediate.cert: merge-intermediate.lisp
merge-intermediate.cert: programs.cert
merge-intermediate.cert: intermediate-to-spec.cert
merge-intermediate.cert: first-last.cert

nth-update-nth.cert: nth-update-nth.lisp

permutations.cert: permutations.lisp

programs.cert: programs.lisp
programs.cert: total-order.cert
programs.cert: nth-update-nth.cert
# programs.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert

sort-qs-properties.cert: sort-qs-properties.lisp
sort-qs-properties.cert: split-qs-properties.cert
sort-qs-properties.cert: load-extract.cert
# sort-qs-properties.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert

spec-properties.cert: spec-properties.lisp
spec-properties.cert: programs.cert
spec-properties.cert: permutations.cert

split-qs-properties.cert: split-qs-properties.lisp
split-qs-properties.cert: programs.cert
split-qs-properties.cert: merge-intermediate.cert
split-qs-properties.cert: extraction.cert
# split-qs-properties.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert

total-order.cert: total-order.lisp
