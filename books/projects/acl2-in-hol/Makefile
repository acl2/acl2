LISP_FILES := $(wildcard lisp/*.lisp)
CERT_FILES := $(patsubst %.cert,%.lisp,$(LISP_FILES))

tests/success.txt: $(CERT_FILES)
	@echo "Invoking books/projects/acl2-in-hol/Makefile."
	@cd tests ; ./doit

clean: clean-more

clean-more:
	rm -f tests/success.txt
	cd tests ; ./doit clean+
