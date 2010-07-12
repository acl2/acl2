# This Makefile is for use with ACL2 only, not ACL2(r), because of the
# depedency for top-with-meta.cert.

include ../../../../Makefile-generic


# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

interval.cert: interval.lisp
interval.cert: top-with-meta.cert
interval.cert: nth-thms.cert

nth-thms.cert: nth-thms.lisp

top-with-meta.cert: top-with-meta.lisp
top-with-meta.cert: ../../../../arithmetic/top-with-meta.cert
# top-with-meta.cert: ../../../../nonstd/arithmetic/top-with-meta.cert

transversality.cert: transversality.lisp
transversality.cert: interval.cert
