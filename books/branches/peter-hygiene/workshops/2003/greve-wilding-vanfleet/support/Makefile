include ../../../../Makefile-generic
BOOKS = firewallworks

separation.cert: separation.lisp 

firewallspec.cert: separation.cert firewallspec.lisp

consistency-test.lisp: separation.lisp firewallspec.lisp firewallworks.lisp make-consistency-test.lisp
	rm -f make.lisp
	rm -f consistency-test.lisp
	echo "(value :q)" > make.lisp
	echo "(load \"make-consistency-test.lisp\")" >> make.lisp
	echo "(make-test \"consistency-test.lisp\")" >> make.lisp
# Deleted by Matt K., May 2006, to avoid STATE warning in CMUCL.
#	echo '(acl2::value :q)' >> make.lisp
	echo '(acl2::exit-lisp)' >> make.lisp
	$(ACL2) < make.lisp > consistency.out

## This book will be certified if the axioms are proved consistent
consistency-test-passed.cert: consistency-test.lisp
	rm -f make.lisp
	rm -f consistency-test-passed.lisp
	rm -f consistency-test-passed.cert
	echo "(in-package \"ACL2\")" >> consistency-test-passed.lisp
	echo "(value :q) (lp)" > make.lisp
	echo "(ld \"consistency-test.lisp\" :ld-error-triples t :ld-error-action :error)" >> make.lisp
	echo '(acl2::value :q)' >> make.lisp
	echo '(acl2::exit-lisp)' >> make.lisp
	$(ACL2) < make.lisp > consistency-test-passed.out

## This book will be certified if the axioms are proved consistent
compatible.cert: compatible.lisp separation.cert

## Note: this will fail if the consistency-check is not passed, or the compatibility
## test did not work
firewallworks.cert: firewallspec.cert firewallworks.lisp consistency-test-passed.cert compatible.cert

newclean:
	rm -f consistency-test.lisp make.lisp consistency-test-passed.lisp

clean: newclean
