include ../../Makefile-generic
ACL2 = ../../../saved_acl2

# Dependencies:

# From make -s dependencies:

basic-arithmetic-helper.cert: basic-arithmetic-helper.lisp

basic-arithmetic.cert: basic-arithmetic.lisp
basic-arithmetic.cert: basic-arithmetic-helper.cert

expt-helper.cert: expt-helper.lisp
expt-helper.cert: basic-arithmetic.cert
expt-helper.cert: inequalities.cert
expt-helper.cert: prefer-times.cert

expt.cert: expt.lisp
expt.cert: basic-arithmetic.cert
expt.cert: inequalities.cert
expt.cert: prefer-times.cert
expt.cert: expt-helper.cert

inequalities.cert: inequalities.lisp
inequalities.cert: basic-arithmetic.cert

mini-theories.cert: mini-theories.lisp
mini-theories.cert: basic-arithmetic.cert
mini-theories.cert: inequalities.cert
mini-theories.cert: prefer-times.cert
mini-theories.cert: expt.cert

numerator-and-denominator-helper.cert: numerator-and-denominator-helper.lisp
numerator-and-denominator-helper.cert: basic-arithmetic.cert
numerator-and-denominator-helper.cert: inequalities.cert
numerator-and-denominator-helper.cert: prefer-times.cert

numerator-and-denominator.cert: numerator-and-denominator.lisp
numerator-and-denominator.cert: basic-arithmetic.cert
numerator-and-denominator.cert: inequalities.cert
numerator-and-denominator.cert: prefer-times.cert
numerator-and-denominator.cert: numerator-and-denominator-helper.cert

prefer-times.cert: prefer-times.lisp
prefer-times.cert: basic-arithmetic.cert
prefer-times.cert: inequalities.cert

top.cert: top.lisp
top.cert: basic-arithmetic.cert
top.cert: inequalities.cert
top.cert: expt.cert
top.cert: prefer-times.cert
top.cert: mini-theories.cert
top.cert: numerator-and-denominator.cert
