# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS ?= ../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# We only certify kas by default, because examples requires a Common
# Lisp with fixnums of 60 bits or more, and not every Common Lisp has
# that property (as of April 2009).
# If you want to certify examples in such a Lisp, then:
# make examples.cert
BOOKS = kas

# From make dependencies:

examples.cert: examples.lisp
examples.cert: kas.cert
examples.cert: examples.acl2

kas.cert: kas.lisp
kas.cert: kas.acl2

