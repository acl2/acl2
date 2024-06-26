.PHONY: docker books

%.cert: %.lisp
	$(ACL2_SYSTEM_BOOKS)/build/cert.pl $@

all: books

docker:
	docker build --rm -f Dockerfile . -t z3

books: left-coordinated.cert phased-delay.cert worst.cert scalar.cert density.cert
	$(ACL2_SYSTEM_BOOKS)/build/cert.pl run.lisp

clean-docker:
	@docker rmi -f z3 > /dev/null 2>&1 

clean: clean-docker
	$(ACL2_SYSTEM_BOOKS)/build/clean.pl
	echo "Done."

dpss.cert: util.cert binder.cert

step.cert: dpss.cert events.cert equiv.cert

run.cert: step.cert

