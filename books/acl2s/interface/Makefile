all: cert

ACL2_CERT_PL ?= ${ACL2_SYSTEM_BOOKS}/build/cert.pl
ACL2_CLEAN_PL ?= ${ACL2_SYSTEM_BOOKS}/build/clean.pl
ACL2S_NUM_JOBS ?= 8

cert: top.lisp acl2s-interface.lsp acl2s-interface-utils.lsp cert.acl2
	$(ACL2_CERT_PL) -j $(ACL2S_NUM_JOBS) top.lisp

acl2s-utils-cert: acl2s-utils/itest-ithm.lisp acl2s-utils/itest-cgen.lisp acl2s-utils/cert.acl2 acl2s-utils/top.lisp acl2s-utils/additions.lsp
	$(ACL2_CERT_PL) -j $(ACL2S_NUM_JOBS) acl2s-utils/top.lisp

clean:
	$(ACL2_CLEAN_PL) *.lisp acl2s-utils/*.lisp

.PHONY: clean
