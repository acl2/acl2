# ACL2 Makefile Wrapper
#
# ACL2's makefile unfortunately always rebuilds ACL2, even if it's already
# up to date.  For our build server, this isn't a good idea.
#
# Usage:
#
# make acl2 LISP=<command>
# make acl2r LISP=<command>
# make acl2h LISP=<command>


ACL2_ALL_SOURCES  := $(wildcard acl2-devel/*.lisp)
ACL2_FAKE_SOURCES := acl2-devel/acl2-proclaims.lisp acl2-devel/acl2r.lisp
ACL2_SOURCES      := $(filter-out $(ACL2_FAKE_SOURCES), $(ACL2_ALL_SOURCES))
ACL2_DEPS         := $(ACL2_SOURCES) acl2-devel/GNUmakefile

.PHONY: acl2 acl2r acl2h

acl2: acl2-devel/saved_acl2
acl2r: acl2-devel/saved_acl2r
acl2h: acl2-devel/saved_acl2h

acl2-devel/saved_acl2: $(ACL2_DEPS)
	echo "Making ACL2() on $(LISP)"
	cd acl2-devel; time make LISP=$(LISP) &> make.log
	wait.pl acl2-devel/make.log
	cat acl2-devel/make.log
	wait.pl acl2-devel/saved_acl2
	ls -lah acl2-devel/saved_acl2


acl2-devel/saved_acl2r: $(ACL2_DEPS)
	echo "Making ACL2(r) on $(LISP)"
	cd acl2-devel; time make LISP=$(LISP) large-acl2r &> make.log
	wait.pl acl2-devel/make.log
	cat acl2-devel/make.log
	wait.pl acl2-devel/saved_acl2r
	ls -lah acl2-devel/saved_acl2r

acl2-devel/saved_acl2h: $(ACL2_DEPS)
	echo "Making ACL2(h) on $(LISP)"
	cd acl2-devel; time make LISP=$(LISP) ACL2_HONS=h &> make.log
	wait.pl acl2-devel/make.log
	cat acl2-devel/make.log
	wait.pl acl2-devel/saved_acl2h
	ls -lah acl2-devel/saved_acl2h





