top1:
	@echo "Using ACL2=$(ACL2)"
	$(MAKE) top

top: fmul.lisp proof.cert

include ../../../Makefile-generic


compiler.cert: compiler.lisp
# compiler.cert: rtl.cert
# compiler.cert: spec.cert

proof.cert: proof.lisp
proof.cert: fmul-star.cert

rtl.cert: rtl.lisp

spec.cert: spec.lisp
spec.cert: ../../../rtl/rel1/support/fp.cert
spec.cert: ../../../rtl/rel1/lib1/top.cert
spec.cert: rtl.cert
spec.cert: fmul.cert

fmul.lisp: compiler.cert fmul.trans

fmul-star.lisp fmul.lisp: compiler.cert fmul.trans
	@echo '(value :q)' > workxxx
	@echo '(LP)' >> workxxx
	@echo '(include-book "compiler")' >> workxxx
	@echo '(compile-pipeline "fmul" z)' >> workxxx
	@echo '(acl2::value :q)' >> workxxx
	@echo '(acl2::exit-lisp)' >> workxxx
	$(ACL2) < workxxx > fmul.lisp.log
	@rm -f workxxx

fmul-star.cert: spec.cert

fmul.cert: rtl.cert

clean: clean-more

clean-more:
	rm -f fmul.lisp fmul-star.lisp
