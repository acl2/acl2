include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Override default setting since build.lisp is not intended to be certified.
BOOKS = fast-sets fixpoints models relations semantics sets syntax

# Dependencies:

# build.cert: build.lisp

fast-sets.cert: fast-sets.lisp
fast-sets.cert: sets.cert

fixpoints.cert: fixpoints.lisp
fixpoints.cert: sets.cert

models.cert: models.lisp
models.cert: relations.cert
models.cert: fixpoints.cert

relations.cert: relations.lisp
relations.cert: fast-sets.cert

semantics.cert: semantics.lisp
semantics.cert: syntax.cert
semantics.cert: ../../../../ordinals/e0-ordinal.cert

sets.cert: sets.lisp

syntax.cert: syntax.lisp
syntax.cert: models.cert
