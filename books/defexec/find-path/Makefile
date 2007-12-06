# NOTE: This Makefile assumes that make has already been run in subdirectory
# graph/.

include ../../Makefile-generic
ACL2 = ../../../saved_acl2

# Dependencies:

fpst.cert: fpst.lisp
fpst.cert: graph/linear-find-path.cert

run-fpst.cert: run-fpst.lisp
run-fpst.cert: fpst.cert
