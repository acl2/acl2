include ../../Makefile-generic
ACL2 = ../../../saved_acl2

# Dependencies:

# From make -s dependencies:

floor-mod.cert: floor-mod.lisp
floor-mod.cert: ../bind-free/top.cert
floor-mod.cert: ../bind-free/building-blocks.cert

mod-expt-fast.cert: mod-expt-fast.lisp
mod-expt-fast.cert: ../bind-free/top.cert
mod-expt-fast.cert: floor-mod.cert

