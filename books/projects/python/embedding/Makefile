all: cert
.PHONY: clean cert

ACL2S ?= acl2s
ACL2_CERT_PL ?= ${ACL2_SYSTEM_BOOKS}/build/cert.pl
ACL2_CLEAN_PL ?= ${ACL2_SYSTEM_BOOKS}/build/clean.pl
ACL2S_NUM_JOBS ?= 8

cert: top.lisp
	$(ACL2_CERT_PL) -j $(ACL2S_NUM_JOBS) top.lisp

clean:
	rm -f server.core server
	$(ACL2_CLEAN_PL) top.lisp
