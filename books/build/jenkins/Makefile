# ACL2 Makefile Wrapper
#
# ACL2's makefile unfortunately always rebuilds ACL2, even if it's
# already up to date.  For our build server, this isn't a good idea.
# Run this from your top-level acl2 directory.
#
# General usage:
#
# make -f books/build/jenkins/Makefile <target> LISP=<command>
#
# Example usages:
#
# make -f books/build/jenkins/Makefile acl2 LISP=ccl
# make -f books/build/jenkins/Makefile acl2hr LISP=ccl
# make -f books/build/jenkins/Makefile saved_acl2p LISP=ccl
#
# TODO: get rid of NFS Lag? messages.  For now, just ignore them.

ACL2_ALL_SOURCES  := $(wildcard *.lisp)
ACL2_FAKE_SOURCES := acl2-proclaims.lisp acl2r.lisp
ACL2_SOURCES      := $(filter-out $(ACL2_FAKE_SOURCES), $(ACL2_ALL_SOURCES))
ACL2_DEPS         := $(ACL2_SOURCES) GNUmakefile

.PHONY: acl2 acl2h acl2p acl2r acl2hp acl2hr acl2pr acl2hpr

acl2: saved_acl2
acl2h: saved_acl2h
acl2p: saved_acl2p
acl2r: saved_acl2r
acl2hp: saved_acl2hp
acl2hr: saved_acl2hr
acl2pr: saved_acl2pr
acl2hpr: saved_acl2hpr

saved_acl2: $(ACL2_DEPS)
	echo "Making ACL2() on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) &> make.log
	./books/build/wait.pl make.log
	cat make.log
	./books/build/wait.pl saved_acl2
	ls -lah saved_acl2

saved_acl2h: $(ACL2_DEPS)
	echo "Making ACL2(h) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS=h &> make.log
	./books/build/wait.pl make.log
	cat make.log
	./books/build/wait.pl saved_acl2h
	ls -lah saved_acl2h

saved_acl2p: $(ACL2_DEPS)
	echo "Making ACL2(p) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) ACL2_PAR=p &> make.log
	./books/build/wait.pl make.log
	cat make.log
	./books/build/wait.pl saved_acl2p
	ls -lah saved_acl2p

saved_acl2r: $(ACL2_DEPS)
	echo "Making ACL2(r) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) NONSTD=r &> make.log
	./books/build/wait.pl make.log
	cat make.log
	./books/build/wait.pl saved_acl2r
	ls -lah saved_acl2r

saved_acl2hp: $(ACL2_DEPS)
	echo "Making ACL2(hp) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS=h ACL2_PAR=p &> make.log
	./books/build/wait.pl make.log
	cat make.log
	./books/build/wait.pl saved_acl2hp
	ls -lah saved_acl2hp

saved_acl2hr: $(ACL2_DEPS)
	echo "Making ACL2(hr) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS=h NONSTD=r &> make.log
	./books/build/wait.pl make.log
	cat make.log
	./books/build/wait.pl saved_acl2hr
	ls -lah saved_acl2hr

saved_acl2pr: $(ACL2_DEPS)
	echo "Making ACL2(pr) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) ACL2_PAR=p NONSTD=r &> make.log
	./books/build/wait.pl make.log
	cat make.log
	./books/build/wait.pl saved_acl2pr
	ls -lah saved_acl2pr

saved_acl2hpr: $(ACL2_DEPS)
	echo "Making ACL2(hpr) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS=h ACL2_PAR=p NONSTD=r &> make.log
	./books/build/wait.pl make.log
	cat make.log
	./books/build/wait.pl saved_acl2hpr
	ls -lah saved_acl2hpr
