# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS ?= ../../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# From make dependencies:

ack.cert: ack.lisp
ack.cert: defminterm.cert

defminterm.cert: defminterm.lisp
defminterm.cert: defxch.cert
defminterm.cert: defpun.cert

defpun.cert: defpun.lisp

defxch.cert: defxch.lisp
# defxch.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert
# defxch.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert

while.cert: while.lisp
while.cert: defminterm.cert
while.cert: ack.cert
