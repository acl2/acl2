include ../../../Makefile-generic
ACL2 = ../../../../saved_acl2

# Dependencies:

# From make -s dependencies:


floor-mod-basic-helper.cert: floor-mod-basic-helper.lisp
floor-mod-basic-helper.cert: ../basic-ops/building-blocks.cert
floor-mod-basic-helper.cert: forcing-types.cert
floor-mod-basic-helper.cert: ../basic-ops/top.cert

floor-mod-basic.cert: floor-mod-basic.lisp
floor-mod-basic.cert: ../basic-ops/building-blocks.cert
floor-mod-basic.cert: forcing-types.cert
floor-mod-basic.cert: ../basic-ops/top.cert
floor-mod-basic.cert: floor-mod-basic-helper.cert

floor-mod-helper.cert: floor-mod-helper.lisp
floor-mod-helper.cert: ../basic-ops/top.cert
floor-mod-helper.cert: floor-mod-basic.cert
floor-mod-helper.cert: forcing-types.cert

floor-mod.cert: floor-mod.lisp
floor-mod.cert: ../basic-ops/building-blocks.cert
floor-mod.cert: ../basic-ops/top.cert
floor-mod.cert: floor-mod-basic.cert
floor-mod.cert: forcing-types.cert
floor-mod.cert: floor-mod-helper.cert

forcing-types.cert: forcing-types.lisp
forcing-types.cert: ../basic-ops/building-blocks.cert

if-normalization.cert: if-normalization.lisp
if-normalization.cert: ../basic-ops/building-blocks.cert

logand-helper.cert: logand-helper.lisp
logand-helper.cert: ../basic-ops/top.cert
logand-helper.cert: more-floor-mod.cert
logand-helper.cert: floor-mod.cert
logand-helper.cert: floor-mod-basic.cert
logand-helper.cert: truncate-rem.cert

logand.cert: logand.lisp
logand.cert: ../basic-ops/building-blocks.cert
logand.cert: ../basic-ops/top.cert
logand.cert: more-floor-mod.cert
logand.cert: floor-mod.cert
logand.cert: floor-mod-basic.cert
logand.cert: truncate-rem.cert
logand.cert: logand-helper.cert

mod-expt-fast.cert: mod-expt-fast.lisp
mod-expt-fast.cert: ../basic-ops/top.cert
mod-expt-fast.cert: floor-mod-basic.cert
mod-expt-fast.cert: floor-mod.cert
mod-expt-fast.cert: more-floor-mod.cert
mod-expt-fast.cert: truncate-rem.cert

more-floor-mod.cert: more-floor-mod.lisp
more-floor-mod.cert: ../basic-ops/top.cert
more-floor-mod.cert: floor-mod.cert
more-floor-mod.cert: floor-mod-basic.cert
more-floor-mod.cert: if-normalization.cert
more-floor-mod.cert: forcing-types.cert

top.cert: top.lisp
top.cert: logand.cert
top.cert: truncate-rem.cert
top.cert: mod-expt-fast.cert
top.cert: more-floor-mod.cert
top.cert: floor-mod.cert
top.cert: floor-mod-basic.cert
top.cert: if-normalization.cert
top.cert: forcing-types.cert

truncate-rem.cert: truncate-rem.lisp
truncate-rem.cert: ../basic-ops/top.cert
truncate-rem.cert: floor-mod.cert
truncate-rem.cert: floor-mod-basic.cert
