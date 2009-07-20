include ../../../Makefile-generic


# Override default setting since define-u-package.lisp is not intended to be certified.
BOOKS = b-ops-aux-def b-ops-aux basic-def basic-lemmas exercise ihs model proof table-def trivia utils

# Dependencies:

b-ops-aux-def.cert: b-ops-aux-def.lisp
b-ops-aux-def.cert: trivia.cert
b-ops-aux-def.cert: ihs.cert

b-ops-aux.cert: b-ops-aux.lisp
b-ops-aux.cert: b-ops-aux-def.cert

basic-def.cert: basic-def.lisp
basic-def.cert: ../../../data-structures/array1.cert
basic-def.cert: ../../../data-structures/deflist.cert
basic-def.cert: ../../../data-structures/list-defthms.cert
basic-def.cert: ../../../data-structures/structures.cert
basic-def.cert: ihs.cert
basic-def.cert: trivia.cert
basic-def.cert: b-ops-aux.cert
basic-def.cert: basic-def.acl2
basic-def.cert: define-u-package.lisp

basic-lemmas.cert: basic-lemmas.lisp
basic-lemmas.cert: basic-def.cert
basic-lemmas.cert: model.cert
basic-lemmas.cert: table-def.cert

exercise.cert: exercise.lisp

ihs.cert: ihs.lisp
ihs.cert: ../../../ihs/ihs-definitions.cert
ihs.cert: ../../../ihs/ihs-lemmas.cert

model.cert: model.lisp
model.cert: basic-def.cert

proof.cert: proof.lisp
proof.cert: basic-def.cert
proof.cert: model.cert
proof.cert: table-def.cert
proof.cert: basic-lemmas.cert

table-def.cert: table-def.lisp
table-def.cert: utils.cert
table-def.cert: basic-def.cert
table-def.cert: model.cert

trivia.cert: trivia.lisp
trivia.cert: ../../../data-structures/array1.cert
trivia.cert: ../../../arithmetic/top.cert

utils.cert: utils.lisp
utils.cert: ../../../data-structures/utilities.cert
utils.cert: utils.acl2
utils.cert: define-u-package.lisp
