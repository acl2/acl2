# Dummy Makefile for detecting non-GNU makes
# Original author: Jared Davis <jared@centtech.com>
#
# This file is inspired by ACL2's Makefile.  It is just a dummy Makefile whose
# sole purpose is to detect and complain about uses of non-GNU make.

error:
	@echo "Error: non-GNU make detected."
	@echo "On some platforms (such as FreeBSD), GNU make may be available"
	@echo "by running 'gmake' instead of 'make'."
	@exit 1

# Just listing the "error" target above should be good enough for someone who
# just types 'make'.  But it won't be good enough when someone types 'make
# basic' or something more complex.  The following suffix rule should work in
# case they try to type, e.g., 'make centaur/doc.cert' or similar.

.SUFFIXES: .cert .lisp

.lisp.cert: error

# Then we can mimic the GNUmakefile and try to notice if they type "make basic"
# or similar.  Here's a command you can use to update this list:
#
#    grep '^[a-zA-Z].*:[^=]' GNUmakefile | sed 's/:.*//' | awk '{print $1,": error"}' | sort -u

all : error
arithmetic-2 : error
arithmetic-3 : error
arithmetic-3/extra/ext.cert : error
arithmetic-5 : error
arithmetic : error
basic : error
bdd/benchmarks.cert : error
bdd/benchmarks.lisp : error
centaur : error
centaur/vl/bin/vl : error
certify-books : error
chk-include-book-worlds : error
clause-processors/SULFA/target.cert : error
clean : error
coi : error
concurrent-programs : error
critpath.txt : error
data-structures : error
des : error
equational : error
ihs : error
jfkr : error
leftist-trees : error
legacy-defrstobj : error
make-event/local-elided-include.pcert1 : error
make-event/local-requires-skip-check-include.pcert1 : error
make-event/macros-include.pcert1 : error
milawa-test-basic : error
milawa-test-extended : error
misc : error
moreclean : error
paco : error
projects/translators/l3-to-acl2/target.cert : error
security : error
sha-2 : error
special : error
std : error
str : error
system/pcert/sub.$(ACL2_COMP_EXT) : error
system/pcert/sub.cert : error
taspi : error
tools : error
vl : error
workshop1999 : error
workshop2000 : error
workshop2001 : error
workshop2002 : error
workshop2003 : error
workshop2004 : error
workshop2006 : error
workshop2007 : error
workshop2009 : error
workshop2011 : error
workshop2013 : error
workshops/1999/multiplier/proof.cert : error
workshops/2003/greve-wilding-vanfleet/support/firewallworks.cert : error
workshops/2003/kaufmann/support/input/defs-in.cert : error
workshops/2011/verbeek-schmaltz/sources/correctness2.cert : error
workshops : error
wp-gen : error
xdoc : error