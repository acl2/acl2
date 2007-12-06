include ../Makefile-generic
ACL2 = ../../saved_acl2

clean+:
	cd embedded-defaxioms ; $(MAKE) clean

clean: clean+

# Dependencies:

assert-check-include-1.cert: assert-check-include-1.lisp
assert-check-include-1.cert: assert-check.cert
assert-check-include-1.cert: assert-check-include-1.acl2
assert-check-include-1.cert: eval.cert

assert-check-include.cert: assert-check-include.lisp
assert-check-include.cert: assert-check.cert

assert-check.cert: assert-check.lisp
assert-check.cert: eval-check.cert

assert-include.cert: assert-include.lisp
assert-include.cert: assert.cert
assert-include.cert: assert-include.acl2

assert.cert: assert.lisp
assert.cert: eval.cert

basic-check.cert: basic-check.lisp

basic-pkg-check.cert: basic-pkg-check.lisp
basic-pkg-check.cert: basic-pkg-check.acl2

basic-pkg.cert: basic-pkg.lisp
basic-pkg.cert: basic-pkg.acl2

basic.cert: basic.lisp

defconst-fast-examples.cert: defconst-fast-examples.lisp
defconst-fast-examples.cert: defconst-fast.cert

defconst-fast.cert: defconst-fast.lisp

defrefine.cert: defrefine.lisp
defrefine.cert: eval.cert

defspec.cert: defspec.lisp
# defspec.cert: $(ACL2_SYSTEM_BOOKS)/make-event/eval.cert
# Added manually based on the above:
defspec.cert: eval.cert

dotimes.cert: dotimes.lisp

embedded-defaxioms.cert: embedded-defaxioms.lisp
embedded-defaxioms.cert: embedded-defaxioms.acl2
embedded-defaxioms.cert: eval.cert

eval-check-tests.cert: eval-check-tests.lisp
eval-check-tests.cert: eval-check.cert

eval-check.cert: eval-check.lisp

eval-tests.cert: eval-tests.lisp
eval-tests.cert: eval.cert

eval.cert: eval.lisp

gen-defthm-check.cert: gen-defthm-check.lisp
# gen-defthm-check.cert: $(ACL2_SYSTEM_BOOKS)/misc/expander.cert

gen-defthm.cert: gen-defthm.lisp
# gen-defthm.cert: $(ACL2_SYSTEM_BOOKS)/misc/expander.cert

gen-defun-check.cert: gen-defun-check.lisp

gen-defun.cert: gen-defun.lisp

local-requires-skip-check-include.cert: local-requires-skip-check-include.lisp
local-requires-skip-check-include.cert: local-requires-skip-check.cert
local-requires-skip-check-include.cert: eval.cert
# local-requires-skip-check-include.cert: $(ACL2_SYSTEM_BOOKS)/misc/file-io.cert

local-requires-skip-check.cert: local-requires-skip-check.lisp
local-requires-skip-check.cert: eval.cert

logical-tangent.cert: logical-tangent.lisp

macros-include.cert: macros-include.lisp
macros-include.cert: macros.cert
macros-include.cert: eval.cert
# macros-include.cert: $(ACL2_SYSTEM_BOOKS)/misc/file-io.cert

macros-skip-proofs-include.cert: macros-skip-proofs-include.lisp
macros-skip-proofs-include.cert: macros-skip-proofs.cert
macros-skip-proofs-include.cert: eval.cert
# macros-skip-proofs-include.cert: $(ACL2_SYSTEM_BOOKS)/misc/file-io.cert
macros-skip-proofs-include.cert: macros-skip-proofs-include.acl2

macros-skip-proofs.cert: macros-skip-proofs.lisp
macros-skip-proofs.cert: macros-skip-proofs.acl2

macros.cert: macros.lisp
macros.cert: eval.cert

nested-check.cert: nested-check.lisp

nested.cert: nested.lisp

portcullis-expansion-include.cert: portcullis-expansion-include.lisp
portcullis-expansion-include.cert: portcullis-expansion.cert
portcullis-expansion-include.cert: portcullis-expansion-include.acl2
portcullis-expansion-include.cert: portcullis-expansion.cert

portcullis-expansion.cert: portcullis-expansion.lisp
portcullis-expansion.cert: eval.cert
portcullis-expansion.cert: portcullis-expansion.acl2

proof-by-arith.cert: proof-by-arith.lisp
# Added manually, based on *default-arith-book-alist*:
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
# proof-by-arith.cert: $(ACL2_SYSTEM_BOOKS)/rtl/rel5/arithmetic/top.cert

read-from-file.cert: read-from-file.lisp
# read-from-file.cert: $(ACL2_SYSTEM_BOOKS)/misc/file-io.cert
# read-from-file.cert: $(ACL2_SYSTEM_BOOKS)/misc/file-io.cert

stobj-test.cert: stobj-test.lisp

test-case-check.cert: test-case-check.lisp
test-case-check.cert: assert-check.cert

test-case.cert: test-case.lisp
test-case.cert: assert.cert

