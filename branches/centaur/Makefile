# Only GNU make should be used.  The real makefile is GNUmakefile.

# The following include all targets in GNUmakefile, obtained by:
# grep '^[a-zA-Z].*:' GNUmakefile

all: err
small:
	echo 'Target "small" is no longer supported.  Use "make large" or simply "make".'
	exit 1
acl2r: err
protections: err
chmod_image: err
do_saved: err
check_compile_ok: err
check_init_ok: err
fast: err
check: err
compile-ok: err
very-fast: err
fast-meter: err
check-sum: err
full: err
full-meter: err
copy: err
copy-distribution: err
copy-workshops: err
copy-nonstd: err
copy-developers: err
TAGS: err
move-to-old: err
move-new: err
init: err
proofs: err
DOC: err
TEXINFO: err
HTML: err
clean: err
red: err
large: err
large-acl2r: err
move-large: err
certify-books: err
regression: err
regression-nonstd: err
certify-books-fresh: err
regression-fresh: err
regression-nonstd-fresh: err
certify-books-short: err
certify-books-test: err
infix-init: err
infix-init10: err
infix-fin: err
clean-doc: err
clean-books: err
clean-books-nonstd: err
tar: err
tar-workshops: err
tar-nonstd: err
test: err
big-test: err
arch: err
mini-proveall: err
allegro-app: err

err:
	@echo "ERROR:"
	@echo "Apparently you are using other than GNU make"
	@echo "(which MIGHT be found in /lusr/gnu/bin/make)."
	@echo "Only GNU make is supported.  If you think your"
	@echo "'make' might work, you can move or delete"
	@echo "ACL2's Makefile and copy or rename ACL2's"
	@echo "GNUmakefile to Makefile."
	@echo "Exiting with error...."
	@exit 1
