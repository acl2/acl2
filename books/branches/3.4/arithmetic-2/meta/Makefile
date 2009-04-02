include ../../Makefile-generic
ACL2 = ../../../saved_acl2

# Dependencies:

# From make -s dependencies:

cancel-terms-helper.cert: cancel-terms-helper.lisp
cancel-terms-helper.cert: ../pass1/top.cert

cancel-terms-meta.cert: cancel-terms-meta.lisp
cancel-terms-meta.cert: common-meta.cert
cancel-terms-meta.cert: ../pass1/top.cert
cancel-terms-meta.cert: cancel-terms-helper.cert

collect-terms-meta.cert: collect-terms-meta.lisp
collect-terms-meta.cert: common-meta.cert
collect-terms-meta.cert: ../pass1/top.cert

common-meta.cert: common-meta.lisp
common-meta.cert: ../pass1/top.cert

expt-helper.cert: expt-helper.lisp
expt-helper.cert: ../pass1/top.cert

expt.cert: expt.lisp
expt.cert: ../pass1/top.cert
expt.cert: expt-helper.cert

integerp-meta.cert: integerp-meta.lisp
integerp-meta.cert: ../pass1/top.cert

integerp.cert: integerp.lisp
integerp.cert: ../pass1/top.cert

mini-theories.cert: mini-theories.lisp
mini-theories.cert: ../pass1/top.cert

non-linear.cert: non-linear.lisp
non-linear.cert: ../pass1/top.cert
non-linear.cert: cancel-terms-helper.cert

numerator-and-denominator.cert: numerator-and-denominator.lisp
numerator-and-denominator.cert: ../pass1/top.cert

post.cert: post.lisp
post.cert: ../pass1/top.cert

pre.cert: pre.lisp
pre.cert: ../pass1/top.cert

top.cert: top.lisp
top.cert: pre.cert
top.cert: integerp.cert
top.cert: integerp-meta.cert
top.cert: cancel-terms-meta.cert
top.cert: collect-terms-meta.cert
top.cert: numerator-and-denominator.cert
top.cert: expt.cert
top.cert: non-linear.cert
top.cert: mini-theories.cert
top.cert: post.cert
