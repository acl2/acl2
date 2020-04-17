TOP_MODULE = FOO
TOP_FILE = foo.v

run:
	@echo "Using ACL2=$(ACL2)"
	$(MAKE) diffs.out

diffs.out: bvecp.cert
	rm -f diffs.out
	diff model.lisp results/model.lisp > diffs.out
	diff bvecp.lisp results/bvecp.lisp >> diffs.out
	diff model-eq.lisp results/model-eq.lisp >> diffs.out
	@if [ ! -z "`head -1 diffs.out`" ] ; then \
	  echo "**ERROR**: Found unexpected results." ;\
	  exit 1 ;\
	  fi

BOOKS_DIR = ../../../../..
LIB_DIR = $(BOOKS_DIR)/rtl/rel4/lib

include $(BOOKS_DIR)/Makefile-generic

# Avoid provisional certification since we are not using Makefile-deps
# (because there are generated .lisp files):
override ACL2_PCERT =

INHIBIT = (assign inhibit-output-lst (list (quote prove) (quote proof-tree) (quote warning) (quote observation) (quote event)))

model-eq.lisp bvecp.lisp: model-defs.lisp

# The following target writes out not only file model-defs.lisp, but
# also files model-eq.lisp and bvecp.lisp.
model-defs.lisp: ../tool/simplify-defuns.cert ../tool/wrapper.cert bvecp-raw.cert
	echo "Running transform-defuns."
	echo '(acl2::value :q)' > workxxx
	echo '(acl2::lp)' >> workxxx
	echo '(include-book "../tool/simplify-defuns")' >> workxxx
	echo '(include-book "../tool/wrapper")' >> workxxx
	echo '(simplify-model)' >> workxxx
	echo '(acl2::value :q)' >> workxxx
	echo '(acl2::exit-lisp)' >> workxxx
	$(ACL2) < workxxx > model.lisp.out
	rm -f workxxx

model.lisp: model-defs.lisp model-macro-aliases.lsp
	cat model-defs.lisp model-macro-aliases.lsp > model.lisp

clean-extra:
	-rm -f model.lisp model-defs.lisp model-eq.lisp model.lisp bvecp.lisp

clean: clean-extra

bvecp-raw.cert: bvecp-raw.lisp
bvecp-raw.cert: model-raw.cert
bvecp-raw.cert: ../../../../../rtl/rel4/lib/top.cert
bvecp-raw.cert: ../../../../../rtl/rel4/support/bvecp-helpers.cert
bvecp-raw.cert: cert.acl2
bvecp-raw.cert: pkgs.lsp

bvecp.cert: bvecp.lisp
bvecp.cert: model.cert
bvecp.cert: model-eq.cert
bvecp.cert: bvecp-raw.cert
bvecp.cert: ../../../../../rtl/rel4/support/bvecp-helpers.cert
bvecp.cert: cert.acl2
bvecp.cert: pkgs.lsp

common.cert: common.lisp
common.cert: ../../../../../rtl/rel4/lib/rtl.cert
common.cert: ../../../../../rtl/rel4/lib/rtlarr.cert
common.cert: ../../../../../rtl/rel4/lib/util.cert
common.cert: ../../../../../misc/symbol-btree.cert
common.cert: ../../../../../misc/rtl-untranslate.cert
common.cert: cert.acl2
common.cert: pkgs.lsp

model-defs.cert: model-defs.lisp
model-defs.cert: ../../../../../ordinals/e0-ordinal.cert
model-defs.cert: common.cert
model-defs.cert: model-macros.cert
model-defs.cert: cert.acl2
model-defs.cert: pkgs.lsp

model-eq.cert: model-eq.lisp
model-eq.cert: bvecp-raw.cert
model-eq.cert: ../../../../../rtl/rel4/lib/top.cert
model-eq.cert: ../../../../../rtl/rel4/lib/simplify-model-helpers.cert
model-eq.cert: model-raw.cert
model-eq.cert: model.cert
model-eq.cert: cert.acl2
model-eq.cert: pkgs.lsp

model-macros.cert: model-macros.lisp
model-macros.cert: cert.acl2
model-macros.cert: pkgs.lsp

model-raw.cert: model-raw.lisp
model-raw.cert: ../../../../../ordinals/e0-ordinal.cert
model-raw.cert: common.cert
model-raw.cert: cert.acl2
model-raw.cert: pkgs.lsp

model.cert: model.lisp
model.cert: ../../../../../ordinals/e0-ordinal.cert
model.cert: common.cert
model.cert: model-macros.cert
model.cert: cert.acl2
model.cert: pkgs.lsp

package-defs.cert: package-defs.lisp
package-defs.cert: package-defs.acl2

# Added manually, since cert.acl2 contains (ld "pkgs.lsp"), which contains
# (include-book "package-defs"):

bvecp-raw.cert: package-defs.cert
bvecp.cert: package-defs.cert
common.cert: package-defs.cert
model-defs.cert: package-defs.cert
model-eq.cert: package-defs.cert
model-macros.cert: package-defs.cert
model-raw.cert: package-defs.cert
model.cert: package-defs.cert

# make sure all these books get recertified if either certdep is updated
UNIVERSAL_DEPS := \
  ../../../../../build/acl2-version.certdep \
  ../../../../../build/universal-dependency.certdep

package-defs.cert: $(UNIVERSAL_DEPS)
