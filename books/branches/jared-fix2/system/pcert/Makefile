# Cause provisional certification in this directory
ACL2_PCERT ?= t
include ../../Makefile-generic
-include Makefile-deps

# Added manually, for the case of provisional certification
# (ACL2_PCERT=t); see last form in .lisp file.
acl2x-pcert-test-2-include.pcert0: acl2x-pcert-test-2.cert

# Override:
acl2x-pcert-test-2.acl2x:
	cp acl2x-pcert-test-2.acl2x-source acl2x-pcert-test-2.acl2x
