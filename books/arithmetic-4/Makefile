ACL2 = ../../saved_acl2

arith-top: top all
all: top

DIRS = support lib
include ../Makefile-subdirs
include ../Makefile-generic

top.cert: top.lisp
top.cert: lib/basic-ops/top.cert
top.cert: lib/floor-mod/top.cert

