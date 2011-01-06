include ../../../../../Makefile-generic

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
