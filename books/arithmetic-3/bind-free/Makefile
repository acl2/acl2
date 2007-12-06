include ../../Makefile-generic
ACL2 = ../../../saved_acl2

# Dependencies:

# From make -s dependencies:

arithmetic-theory.cert: arithmetic-theory.lisp
arithmetic-theory.cert: basic.cert
arithmetic-theory.cert: common.cert
arithmetic-theory.cert: building-blocks.cert
arithmetic-theory.cert: collect.cert

banner.cert: banner.lisp

basic-helper.cert: basic-helper.lisp
basic-helper.cert: ../pass1/top.cert
basic-helper.cert: default-hint.cert

basic.cert: basic.lisp
basic.cert: ../pass1/top.cert
basic.cert: basic-helper.cert
basic.cert: building-blocks.cert

building-blocks.cert: building-blocks.lisp

collect.cert: collect.lisp
collect.cert: ../pass1/top.cert
collect.cert: basic-helper.cert

common.cert: common.lisp
common.cert: ../pass1/top.cert
common.cert: building-blocks.cert

default-hint.cert: default-hint.lisp

integerp-meta.cert: integerp-meta.lisp
integerp-meta.cert: ../pass1/top.cert
integerp-meta.cert: default-hint.cert

integerp.cert: integerp.lisp
integerp.cert: ../pass1/top.cert
integerp.cert: building-blocks.cert
integerp.cert: default-hint.cert

mini-theories-helper.cert: mini-theories-helper.lisp
mini-theories-helper.cert: ../pass1/top.cert
mini-theories-helper.cert: default-hint.cert

mini-theories.cert: mini-theories.lisp
mini-theories.cert: mini-theories-helper.cert

normalize.cert: normalize.lisp
normalize.cert: basic.cert
normalize.cert: common.cert
normalize.cert: ../pass1/top.cert

numerator-and-denominator.cert: numerator-and-denominator.lisp
numerator-and-denominator.cert: ../pass1/top.cert

remove-weak-inequalities.cert: remove-weak-inequalities.lisp
remove-weak-inequalities.cert: building-blocks.cert

simplify-helper.cert: simplify-helper.lisp
simplify-helper.cert: ../pass1/top.cert
simplify-helper.cert: default-hint.cert

simplify.cert: simplify.lisp
simplify.cert: simplify-helper.cert
simplify.cert: basic.cert
simplify.cert: common.cert
simplify.cert: ../pass1/top.cert

top.cert: top.lisp
top.cert: default-hint.cert
top.cert: building-blocks.cert
top.cert: mini-theories.cert
top.cert: common.cert
top.cert: normalize.cert
top.cert: simplify.cert
top.cert: numerator-and-denominator.cert
top.cert: integerp.cert
top.cert: integerp-meta.cert
top.cert: basic.cert
top.cert: collect.cert
top.cert: remove-weak-inequalities.cert
top.cert: arithmetic-theory.cert
top.cert: banner.cert
