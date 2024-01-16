all: build-debug-binary build-java-binary parser-cli

ACL2S_EXE ?= acl2s
ACL2_CERT_PL ?= ${ACL2_SYSTEM_BOOKS}/build/cert.pl
ACL2_CLEAN_PL ?= ${ACL2_SYSTEM_BOOKS}/build/clean.pl
DOCKER_CMD ?= docker
ACL2S_NUM_JOBS ?= 4

cert: induction-proof-checker.cert acl2s-setup.cert arith-theory.cert

acl2s-setup.cert: acl2s-setup.lisp
	$(ACL2_CERT_PL) -j $(ACL2S_NUM_JOBS) acl2s-setup.lisp

arith-theory.cert: arith-theory.lisp
	$(ACL2_CERT_PL) -j $(ACL2S_NUM_JOBS) arith-theory.lisp

induction-proof-checker.cert: induction-proof-checker.lisp
	$(ACL2_CERT_PL) -j $(ACL2S_NUM_JOBS) induction-proof-checker.lisp

proof-checker-cli: docker/Dockerfile-check-file docker/docker-check-file.sh
	$(DOCKER_CMD) build -f docker/Dockerfile-check-file -t atwalter/proof-checker-cli .

DEPS = prover.lsp structs.lsp conditions.lsp print.lsp util.lsp package.lsp acl2s-high-level-interface.lsp prop-skel.lsp prop-equiv.lsp

build-java-binary: build-java-binary.lsp $(DEPS) cert
	$(ACL2S_EXE) < build-java-binary.lsp

build-debug-binary: build-debug-binary.lsp $(DEPS) cert
	$(ACL2S_EXE) < build-debug-binary.lsp

parser-cli:
	cd parser &&\
	./gradlew shadowJar

# Plugin
build-and-extract-plugin: build-plugin extract-plugin

build-plugin:
	docker build -f docker/Dockerfile-build-plugin . -t checker-plugin:latest

extract-plugin:
	$(eval TMP_CONTAINER := $(shell docker create checker-plugin:latest))
	docker cp $(TMP_CONTAINER):/root/plugin-repo/ .
	docker rm -f $(TMP_CONTAINER)

clean:
	rm -f prover-java.core
	rm -f prover-java
	rm -f prover-debug.core
	rm -f prover-debug
	$(ACL2_CLEAN_PL) *.lisp
	cd parser; ./gradlew clean

.PHONY: clean proof-checker-cli
