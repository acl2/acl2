all: build

.PHONY: all clean build

ACL2_EXE ?= ${ACL2_SYSTEM_BOOKS}/../saved_acl2

clean:
	rm -f server server.core

build:
	${ACL2_EXE} < build.lsp

