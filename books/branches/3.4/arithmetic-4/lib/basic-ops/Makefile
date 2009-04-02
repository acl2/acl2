include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2

# Dependencies:

# From make -s dependencies:


arithmetic-theory.cert: arithmetic-theory.lisp
arithmetic-theory.cert: common.cert
arithmetic-theory.cert: building-blocks.cert
arithmetic-theory.cert: basic.cert
arithmetic-theory.cert: simple-equalities-and-inequalities.cert
arithmetic-theory.cert: expt.cert
arithmetic-theory.cert: collect.cert

banner.cert: banner.lisp

basic.cert: basic.lisp
basic.cert: building-blocks.cert
basic.cert: ../../support/top.cert

building-blocks-helper.cert: building-blocks-helper.lisp
building-blocks-helper.cert: ../../support/top.cert

building-blocks.cert: building-blocks.lisp
building-blocks.cert: building-blocks-helper.cert

collect.cert: collect.lisp
collect.cert: building-blocks.cert
collect.cert: ../../support/top.cert
collect.cert: expt-helper.cert

common.cert: common.lisp
common.cert: building-blocks.cert
common.cert: ../../support/top.cert

default-hint.cert: default-hint.lisp
default-hint.cert: dynamic-e-d.cert

distributivity.cert: distributivity.lisp

dynamic-e-d.cert: dynamic-e-d.lisp

elim-hint.cert: elim-hint.lisp
elim-hint.cert: default-hint.cert
elim-hint.cert: elim-hint.acl2

expt-helper.cert: expt-helper.lisp
expt-helper.cert: ../../support/top.cert
expt-helper.cert: default-hint.cert

expt.cert: expt.lisp
expt.cert: building-blocks.cert
expt.cert: ../../support/top.cert
expt.cert: expt-helper.cert
expt.cert: types.cert

forcing-types.cert: forcing-types.lisp
forcing-types.cert: building-blocks.cert

if-normalization.cert: if-normalization.lisp
if-normalization.cert: building-blocks.cert

integerp-helper.cert: integerp-helper.lisp
integerp-helper.cert: ../../support/top.cert
integerp-helper.cert: building-blocks.cert
integerp-helper.cert: default-hint.cert

integerp-meta.cert: integerp-meta.lisp
integerp-meta.cert: building-blocks.cert
integerp-meta.cert: ../../support/top.cert
integerp-meta.cert: default-hint.cert

integerp.cert: integerp.lisp
integerp.cert: building-blocks.cert
integerp.cert: default-hint.cert
integerp.cert: ../../support/top.cert
integerp.cert: integerp-helper.cert
integerp.cert: common.cert
integerp.cert: normalize.cert
integerp.cert: simplify.cert
integerp.cert: collect.cert

mini-theories.cert: mini-theories.lisp

natp-posp.cert: natp-posp.lisp
natp-posp.cert: building-blocks.cert
natp-posp.cert: ../../support/top.cert

normalize.cert: normalize.lisp
normalize.cert: common.cert
normalize.cert: basic.cert
normalize.cert: ../../support/top.cert

numerator-and-denominator.cert: numerator-and-denominator.lisp
numerator-and-denominator.cert: ../../support/top.cert

remove-weak-inequalities.cert: remove-weak-inequalities.lisp
remove-weak-inequalities.cert: building-blocks.cert

simple-equalities-and-inequalities-helper.cert: simple-equalities-and-inequalities-helper.lisp
simple-equalities-and-inequalities-helper.cert: ../../support/top.cert
simple-equalities-and-inequalities-helper.cert: building-blocks.cert

simple-equalities-and-inequalities.cert: simple-equalities-and-inequalities.lisp
simple-equalities-and-inequalities.cert: building-blocks.cert
simple-equalities-and-inequalities.cert: ../../support/top.cert
simple-equalities-and-inequalities.cert: simplify-helper.cert
simple-equalities-and-inequalities.cert: simple-equalities-and-inequalities-helper.cert

simplify-helper.cert: simplify-helper.lisp
simplify-helper.cert: ../../support/top.cert
simplify-helper.cert: default-hint.cert

simplify.cert: simplify.lisp
simplify.cert: common.cert
simplify.cert: simplify-helper.cert
simplify.cert: basic.cert
simplify.cert: ../../support/top.cert
simplify.cert: ../../support/top.cert

top.cert: top.lisp
top.cert: distributivity.cert
top.cert: default-hint.cert
top.cert: building-blocks.cert
top.cert: common.cert
top.cert: normalize.cert
top.cert: simplify.cert
top.cert: mini-theories.cert
top.cert: numerator-and-denominator.cert
top.cert: natp-posp.cert
top.cert: integerp-meta.cert
top.cert: integerp.cert
top.cert: basic.cert
top.cert: expt.cert
top.cert: collect.cert
top.cert: remove-weak-inequalities.cert
top.cert: arithmetic-theory.cert
top.cert: types.cert
top.cert: simple-equalities-and-inequalities.cert
top.cert: if-normalization.cert
top.cert: forcing-types.cert
top.cert: banner.cert

types-helper.cert: types-helper.lisp
types-helper.cert: ../../support/top.cert

types.cert: types.lisp
types.cert: building-blocks.cert
types.cert: types-helper.cert
