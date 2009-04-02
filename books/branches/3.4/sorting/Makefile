include ../Makefile-generic
ACL2 = ../../saved_acl2

# Dependencies:

bsort.cert: bsort.lisp
bsort.cert: ordered-perms.cert
bsort.cert: convert-perm-to-how-many.cert

convert-perm-to-how-many.cert: convert-perm-to-how-many.lisp
convert-perm-to-how-many.cert: perm.cert

equisort.cert: equisort.lisp
equisort.cert: perm.cert
equisort.cert: ordered-perms.cert
equisort.cert: convert-perm-to-how-many.cert

equisort2.cert: equisort2.lisp
equisort2.cert: perm.cert
equisort2.cert: ordered-perms.cert
equisort2.cert: convert-perm-to-how-many.cert

equisort3.cert: equisort3.lisp
equisort3.cert: perm.cert
equisort3.cert: ordered-perms.cert
equisort3.cert: convert-perm-to-how-many.cert

isort.cert: isort.lisp
isort.cert: perm.cert
isort.cert: ordered-perms.cert
isort.cert: convert-perm-to-how-many.cert

msort.cert: msort.lisp
msort.cert: perm.cert
msort.cert: ordered-perms.cert
msort.cert: convert-perm-to-how-many.cert

no-dups-qsort.cert: no-dups-qsort.lisp
no-dups-qsort.cert: qsort.cert

ordered-perms.cert: ordered-perms.lisp
ordered-perms.cert: perm.cert

perm.cert: perm.lisp

qsort.cert: qsort.lisp
qsort.cert: perm.cert
qsort.cert: ordered-perms.cert
qsort.cert: convert-perm-to-how-many.cert
# qsort.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/extra/top-ext.cert

sorts-equivalent.cert: sorts-equivalent.lisp
sorts-equivalent.cert: equisort.cert
sorts-equivalent.cert: isort.cert
sorts-equivalent.cert: msort.cert
sorts-equivalent.cert: qsort.cert
sorts-equivalent.cert: bsort.cert

sorts-equivalent2.cert: sorts-equivalent2.lisp
sorts-equivalent2.cert: equisort2.cert
sorts-equivalent2.cert: isort.cert
sorts-equivalent2.cert: msort.cert
sorts-equivalent2.cert: qsort.cert
sorts-equivalent2.cert: bsort.cert

sorts-equivalent3.cert: sorts-equivalent3.lisp
sorts-equivalent3.cert: equisort3.cert
sorts-equivalent3.cert: isort.cert
sorts-equivalent3.cert: msort.cert
sorts-equivalent3.cert: qsort.cert
sorts-equivalent3.cert: bsort.cert
