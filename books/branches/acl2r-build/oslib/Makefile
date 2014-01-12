include ../Makefile-generic
# The following line excludes books that contain the stub marker
BOOKS := $(patsubst %.lisp, %, $(shell fgrep -L 'cert_param: (reloc_stub)' *.lisp))
# This tells ACL2's Make system it's okay to use ttags in these books
ACL2_COMPILE_FLG := t :ttags :all
-include Makefile-deps
