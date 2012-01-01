include ../Makefile-generic
-include Makefile-deps

# Added manually, for the case of provisional certification
# (ACL2_PCERT=t), since otherwise we can get a complaint with "make -j
# 4" that ttag :MY-TTAG is associated with file
# double-cert-test-1.lisp.
double-cert-test.acl2x: double-cert-test-1.cert

# Added manually, for the case of provisional certification
# (ACL2_PCERT=t), because the .lisp file for the indicated .acl2x
# explicitly reads the indicated .cert file.
local-elided-include.acl2x: local-elided.cert
local-requires-skip-check-include.acl2x: local-requires-skip-check.cert
macros-include.acl2x: macros.cert
macros-skip-proofs-include.acl2x: macros-skip-proofs.cert

# Added manually, based on *default-arith-book-alist*:
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/rtl/rel5/arithmetic/top.cert
