include ../Makefile-generic
# The following line excludes books that contain the stub marker
BOOKS := $(patsubst %.lisp, %, $(shell fgrep -L 'cert_param: (reloc_stub)' *.lisp))
-include Makefile-deps
