top1:
	@echo "Using ACL2=$(ACL2)"
	$(MAKE) top

top: fmul.lisp proof.cert

include ../../../Makefile-generic

# Avoid provisional certification since we are not using Makefile-deps, which is
# because there are generated .lisp files.
override ACL2_PCERT =

# Note: this ensures that all books here will get rebuilt when either
# of these two universal dependencies is updated.
UNIVERSAL_DEPS := \
  ../../../build/universal-dependency.certdep \
  ../../../build/acl2-version.certdep

compiler.cert: $(UNIVERSAL_DEPS)
rtl.cert: $(UNIVERSAL_DEPS)
proof.cert: $(UNIVERSAL_DEPS)

compiler.cert: compiler.lisp

proof.cert: proof.lisp
proof.cert: fmul-star.cert

rtl.cert: rtl.lisp

spec.cert: spec.lisp
spec.cert: ../../../rtl/rel1/support/fp.cert
spec.cert: ../../../rtl/rel1/lib1/top.cert
spec.cert: rtl.cert
spec.cert: fmul.cert

fmul-star.lisp: fmul.lisp

fmul.lisp: compiler.cert fmul.trans
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

# Added by Matt K. Sept. 2010 because many *.tem files were lying around:
# rm -f *.tem
clean-more:
	rm -f fmul.lisp fmul-star.lisp
	rm -f *.tem
