include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Override default setting since build.lisp is not intended to be certified.
BOOKS = ctl defung fast-sets fixpoints meta models perm relations semantics sets syntax

# Dependencies:

# build.cert: build.lisp

ctl.cert: ctl.lisp
ctl.cert: semantics.cert

defung.cert: defung.lisp

fast-sets.cert: fast-sets.lisp
fast-sets.cert: sets.cert

fixpoints.cert: fixpoints.lisp
fixpoints.cert: sets.cert

meta.cert: meta.lisp
meta.cert: ../../../../arithmetic/top-with-meta.cert

models.cert: models.lisp
models.cert: relations.cert

perm.cert: perm.lisp
perm.cert: defung.cert

relations.cert: relations.lisp
relations.cert: fast-sets.cert

semantics.cert: semantics.lisp
semantics.cert: syntax.cert
semantics.cert: fixpoints.cert
semantics.cert: ../../../../ordinals/e0-ordinal.cert

sets.cert: sets.lisp
sets.cert: defung.cert
sets.cert: meta.cert
sets.cert: perm.cert

syntax.cert: syntax.lisp
syntax.cert: models.cert
