(
 (:files
 "
.:
Makefile
Readme.lsp
cantor-pairing-bijective.lisp
compare-out-files.lisp
convert-normalized-term-to-pairs.lisp
dead-source-code.lisp
deps-pcert.lisp
extend-pathname.lisp
f-put-global.lisp
fancy-string-reader-test.lisp
hl-addr-combine.lisp
hl-nat-combine-onto.acl2
hl-nat-combine-onto.lisp
legal-variablep.lisp
merge-sort-term-order.lisp
meta-extract.lisp
optimize-check-aux.lisp
optimize-check.lisp
origin.acl2
origin.lisp
pseudo-good-worldp.lisp
pseudo-termp-lemmas.lisp
random.lisp
subcor-var.lisp
sublis-var.lisp
subst-expr.lisp
subst-var.lisp
termp.lisp
too-many-ifs.acl2
too-many-ifs.lisp
toothbrush-deps.lisp
top.lisp
untranslate-car-cdr.lisp
update-state.lisp
verified-termination-and-guards.lisp
worldp-check.acl2
worldp-check.lisp
"
 )
 (:TITLE "System Books")
 (:AUTHOR/S
  "See individual files")
 (:Keywords "Logical World")
 (:ABSTRACT

"These books are about system-level properties, for example checking invariants
on the ACL2 logical world and verifying termination and guards of some system
functions.  The scope may broaden in the future.

The book top.lisp includes books verifying termination and guards of system
functions.  Add an include-book to top.lisp for each new such book.

verified-termination-and-guards.lisp admits some :program mode ACL2 system
functions into the logic by verifying their termination.  It is also a good
place to verify the guards of :logic mode system functions."

)
 (:PERMISSION

"
See individual books for copyright and license information."
))
