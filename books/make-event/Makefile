include ../Makefile-generic
-include Makefile-deps

# Added manually, for the case of provisional certification
# (ACL2_PCERT=t); see last form in .lisp file.
local-requires-skip-check-include.pcert0: local-requires-skip-check.cert
local-elided-include.pcert0: local-elided.cert

# Added manually, based on *default-arith-book-alist*:
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/rtl/rel5/arithmetic/top.cert
