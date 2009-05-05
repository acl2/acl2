include ../../../../../../../../Makefile-generic

ACL2 = ../../../../../../../../../saved_acl2

# Dependencies:

ma128intserial-ma128int.cert: ma128intserial-ma128int.lisp
ma128intserial-ma128int.cert: ma128intserial.cert

ma128intserial.cert: ma128intserial.lisp
ma128intserial.cert: ../../../deterministic-systems/128/serial/serial.cert
ma128intserial.cert: ../../../top/nth-thms.cert
ma128intserial.cert: ../../../top/meta.cert
ma128intserial.cert: ../../../top/defun-weak-sk.cert
ma128intserial.cert: ../../top/non-det-encap-wfbisim.cert
ma128intserial.cert: ../top/ma128int.cert
