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
# make -f books/build/jenkins/Makefile acl2r LISP=ccl
# make -f books/build/jenkins/Makefile saved_acl2p LISP=ccl

ACL2_ALL_SOURCES  := $(wildcard *.lisp)
ACL2_FAKE_SOURCES := acl2-proclaims.lisp acl2r.lisp
ACL2_SOURCES      := $(filter-out $(ACL2_FAKE_SOURCES), $(ACL2_ALL_SOURCES))
ACL2_DEPS         := $(ACL2_SOURCES) GNUmakefile

#.PHONY: acl2c acl2cp acl2cr acl2cpr
.PHONY: acl2 acl2p acl2r acl2pr

#acl2c: saved_acl2c
#acl2cp: saved_acl2cp
#acl2cr: saved_acl2cr
#acl2cpr: saved_acl2cpr

# Note that we don't use &>, because otherwise the process goes on
# immediately, and waiting 100 seconds isn't enough for SBCL builds.

#saved_acl2c: $(ACL2_DEPS)
#	echo "Making ACL2(c) on $(LISP)"
#	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS= ACL2_PAR= ACL2_REAL= > make-acl2.log
#	./books/build/wait.pl make-acl2.log
#	cat make-acl2.log
#	./books/build/wait.pl saved_acl2c
#	ls -lah saved_acl2c

#saved_acl2cp: $(ACL2_DEPS)
#	echo "Making ACL2(cp) on $(LISP)"
#	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS= ACL2_PAR=p ACL2_REAL= > make-acl2.log
#	./books/build/wait.pl make-acl2.log
#	cat make-acl2.log
#	./books/build/wait.pl saved_acl2cp
#	ls -lah saved_acl2cp

#saved_acl2cr: $(ACL2_DEPS)
#	echo "Making ACL2(cr) on $(LISP)"
#	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS= ACL2_PAR= ACL2_REAL=r > make-acl2.log
#	./books/build/wait.pl make-acl2.log
#	cat make-acl2.log
#	./books/build/wait.pl saved_acl2cr
#	ls -lah saved_acl2cr

#saved_acl2cpr: $(ACL2_DEPS)
#	echo "Making ACL2(cpr) on $(LISP)"
#	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS= ACL2_PAR=p ACL2_REAL=r > make-acl2.log
#	./books/build/wait.pl make-acl2.log
#	cat make-acl2.log
#	./books/build/wait.pl saved_acl2cpr
#	ls -lah saved_acl2cpr




acl2:   saved_acl2
acl2p:  saved_acl2p
acl2r:  saved_acl2r
acl2pr: saved_acl2pr

saved_acl2: $(ACL2_DEPS)
	echo "Making ACL2(h) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS=h ACL2_PAR= ACL2_REAL= > make-acl2.log
	./books/build/wait.pl make-acl2.log
	cat make-acl2.log
	./books/build/wait.pl saved_acl2
	ls -lah saved_acl2

saved_acl2p: $(ACL2_DEPS)
	echo "Making ACL2(hp) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS=h ACL2_PAR=p ACL2_REAL= > make-acl2.log
	./books/build/wait.pl make-acl2.log
	cat make-acl2.log
	./books/build/wait.pl saved_acl2p
	ls -lah saved_acl2p

saved_acl2r: $(ACL2_DEPS)
	echo "Making ACL2(hr) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS=h ACL2_PAR= ACL2_REAL=r > make-acl2.log
	./books/build/wait.pl make-acl2.log
	cat make-acl2.log
	./books/build/wait.pl saved_acl2r
	ls -lah saved_acl2r

saved_acl2pr: $(ACL2_DEPS)
	echo "Making ACL2(hpr) on $(LISP)"
	time make --file=GNUmakefile LISP=$(LISP) ACL2_HONS=h ACL2_PAR=p ACL2_REAL=r > make-acl2.log
	./books/build/wait.pl make-acl2.log
	cat make-acl2.log
	./books/build/wait.pl saved_acl2pr
	ls -lah saved_acl2pr
