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
#    grep '^[a-zA-Z_-/]*:[^=]' GNUmakefile | sed 's/:.*//' | awk '{print $1,": error"}' | sort -u

add-ons : error
all : error
arithmetic : error
basic : error
bdd : error
ccg : error
centaur : error
centaur/vl/bin/vl : error
certify-books : error
cgen : error
chk-include-book-worlds : error
clause-processors : error
clean : error
coi : error
concurrent-programs : error
cowles : error
data-structures : error
defsort : error
des : error
equational : error
finite-set-theory : error
hacking : error
hints : error
ihs : error
jfkr : error
leftist-trees : error
legacy-defrstobj : error
make-event : error
memoize : error
meta : error
milawa-test-basic : error
milawa-test-extended : error
misc : error
models : error
moreclean : error
ordinals : error
oslib : error
paco : error
parsers : error
powerlists : error
proofstyles : error
regex : error
rtl : error
security : error
serialize : error
sorting : error
special : error
std : error
str : error
system : error
taspi : error
tau : error
textbook : error
tools : error
unicode : error
vl : error
workshops : error
wp-gen : error
xdoc : error