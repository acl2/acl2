include ../../../../../Makefile-generic

BOOKS = bag-pkg bag-exports cons basic meta bind-free-rules two-level two-level-meta neq eric-meta top #foo

bag-pkg.cert: bag-pkg.lisp
bag-pkg.cert: bag-pkg.acl2
bag-pkg.acl2: ../lists/list-exports.cert
bag-pkg.acl2: ../syntax/syn-pkg.cert

bag-exports.cert: bag-exports.lisp
bag-exports.cert: bag-exports.acl2
bag-exports.acl2: bag-pkg.cert

cons.cert: cons.lisp

basic.cert: basic.lisp
# basic.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
basic.cert: basic.acl2
basic.acl2: ../lists/lists.cert
basic.acl2: bag-exports.cert

meta.cert: meta.lisp
meta.cert: basic.cert
# meta.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert
meta.cert: meta.acl2
meta.acl2: bag-exports.cert
meta.acl2: ../lists/mv-nth.cert
meta.acl2: ../syntax/syntax.cert

bind-free-rules.cert: bind-free-rules.lisp
bind-free-rules.cert: meta.cert
bind-free-rules.cert: bind-free-rules.acl2
bind-free-rules.acl2: bag-exports.cert

two-level.cert: two-level.lisp
two-level.cert: bind-free-rules.cert
two-level.cert: two-level.acl2
two-level.acl2: bag-exports.cert

two-level-meta.cert: two-level-meta.lisp
two-level-meta.cert: two-level.cert
two-level-meta.cert: two-level-meta.acl2
two-level-meta.acl2: bag-exports.cert

neq.cert: neq.lisp
neq.cert: bind-free-rules.cert
neq.cert: neq.acl2
neq.acl2: bag-exports.cert

eric-meta.cert: eric-meta.lisp
eric-meta.cert: bind-free-rules.cert
# eric-meta.cert: $(ACL2_SYSTEM_BOOKS)/rtl/rel4/support/logand.cert
eric-meta.cert: eric-meta.acl2
eric-meta.acl2: bag-exports.cert

top.cert: top.lisp
top.cert: bind-free-rules.cert
top.cert: cons.cert
top.cert: neq.cert
top.cert: eric-meta.cert
top.cert: top.acl2
top.acl2: bag-exports.cert
