ACL2 = ../../saved_acl2

arith-top: top all
all: top

DIRS = pass1 bind-free floor-mod
include ../Makefile-subdirs
include ../Makefile-generic

top.cert: top.lisp
top.cert: bind-free/top.cert
top.cert: floor-mod/floor-mod.cert
top.cert: floor-mod/mod-expt-fast.cert
