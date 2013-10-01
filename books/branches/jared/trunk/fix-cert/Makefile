# This is an unusual make process, given the way we copy and move
# files, so we disable provisional certification.
override ACL2_PCERT :=

# This copies the .cert files as they are, but doesn't get them into their
# final state.  We put this rule before the inclusion of Makefile-generic,
# so that it will take priority over the rule for target %.cert in that file.
moved/%.cert: %.cert
	cp -v $^ $@

include ../Makefile-generic
-include Makefile-deps

# Certifying this one actually updates the moved/*.cert files to reflect
# their new location.
test-fix-cert0.cert: moved/test1bb.cert moved/test1bp.cert moved/test1pp.cert moved/test1pb.cert moved/test1b.cert moved/test1p.cert moved/test1.cert moved/test2.cert

# And these test that we can then include them.
test-fix-cert1.cert: test-fix-cert0.cert
test-fix-cert2.cert: test-fix-cert0.cert

clean: moved-clean

moved-clean:
	rm -f moved/*.cert

# We skip all books for "make fasl" etc., i.e., for compiling
# already-certified books, because of the unusual nature of this
# directory.
BOOKS_SKIP_COMP := $(BOOKS)
