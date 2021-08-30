# Note that ACL2 and ACL2_SYSTEM_BOOKS should be defined, e.g.:
# bash
# ACL2_DIR=/Users/kaufmann/acl2/v6-2/acl2-sources
# export ACL2=${ACL2_DIR}/saved_acl2
# export ACL2_SYSTEM_BOOKS=${ACL2_DIR}/books

# WARNING: Do not run with -j (unless it's -j 1)!  Otherwise you may
# get errors.  (Note from Matt K.: I've tried, but I can't seem to
# figure out why file tiny.lisp can be created more than once when -j
# is supplied a value greater than 1.)

# Given the warning above, I'm not going to try to support provisional
# certification for this directory.

override ACL2_PCERT =

top: all run-check.txt run-test

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
# See the end for dependencies -- we don't auto-generate
# Makefile-deps, because tiny.lisp and tiny-logic.lisp are generated
# files.
# -include Makefile-deps

ifneq ($(findstring MINGW, $(shell uname)),)
L3_TO_ACL2_DIR ?= $(shell cd ../../translator/ ; pwd -W)
else
ifneq ($(findstring CYGWIN, $(shell uname)),)
L3_TO_ACL2_DIR ?= $(shell cd ../../translator/ ; cygpath -m `pwd`)
else
L3_TO_ACL2_DIR ?= $(shell cd ../../translator/ ; pwd)
endif
endif

# $(warning L3_TO_ACL2_DIR is $(L3_TO_ACL2_DIR))

BOOKS = tiny run tiny-logic tiny-manual

tiny.lisp: ../../translator/l3-to-acl2.cert tiny-acl2.txt
	@echo "Creating file `pwd`/$@"
	@echo '(include-book "$(L3_TO_ACL2_DIR)/l3-to-acl2")' > workxxx.$@
	@echo '(l3-to-acl2 "tiny-acl2.txt" "tiny.lisp"' >> workxxx.$@
	@echo '            :str-to-sym' >> workxxx.$@
	@echo '            (quote (("PC" . pctr) ("alu" . alu_var) ("function" . function0))))' >> workxxx.$@
	@$(ACL2) < workxxx.$@ > $@.out
	@diff tiny.lisp gold/tiny.lisp
	@echo "Successfully built `pwd`/$@"

tiny-logic.lisp: ../../translator/l3-to-acl2.cert tiny-acl2.txt
	@echo "Creating file `pwd`/$@"
	@echo '(include-book "$(L3_TO_ACL2_DIR)/l3-to-acl2")' > workxxx.$@
	@echo '(l3-to-acl2 "tiny-acl2.txt" "tiny-logic.lisp"' >> workxxx.$@
	@echo '            :logic :logic-only' >> workxxx.$@
	@echo '            :str-to-sym' >> workxxx.$@
	@echo '            (quote (("PC" . pctr) ("alu" . alu_var) ("function" . function0))))' >> workxxx.$@
	@$(ACL2) < workxxx.$@ > $@.out
	@diff tiny-logic.lisp gold/tiny-logic.lisp
	@echo "Successfully built `pwd`/$@"

# Check that the model runs as expected.
run-check.txt: run.cert
	@echo "Starting target $@ (in directory `pwd`)"
	@echo '(include-book "run")' > workxxx.$@
	@echo '(run-output st$$ state)' >> workxxx.$@
	@$(ACL2) < workxxx.$@ > run-check.out
	@diff run-check.txt gold/run-check.txt
	@echo "Successfully completed target $@"

# Run :program mode test (from auto-generated tiny.lisp).
run-test.out: run.cert
	@echo "Starting target $@ (in directory `pwd`)"
	@-rm -f workxxx.$@
	@./run-test.sh $@ > run-test.log

# Run :logic mode test (from auto-generated tiny-logic.lisp).
run-test-logic.out: run.cert tiny-logic.cert
	@echo "Starting target $@ (in directory `pwd`)"
	@echo '(include-book "tiny-logic")' > workxxx.$@
	@./run-test.sh $@ > run-test.log

# Run test for guard-verified functions (from manually produced tiny-manual.lisp).
run-test-guard-verified.out: run.cert tiny-manual.cert
	@echo "Starting target $@ (in directory `pwd`)"
	@echo '(include-book "tiny-manual")' > workxxx.$@
	@./run-test.sh $@ > run-test.log

# We use recursive calls of make below so that even if -j is used,
# they are run sequentially -- so that their output isn't interleaved.
run-test:
	@$(MAKE) run-test.out
	@$(MAKE) run-test-logic.out
	@$(MAKE) run-test-guard-verified.out

clean: clean-more

clean-more:
	rm -f tiny.lisp tiny-logic.lisp run-check.txt run-test.log

# Dependencies for generated files:

tiny.cert: tiny.lisp
tiny-logic.cert: tiny-logic.lisp

# From Makefile-deps generated after a manual cleaning:

run.cert: tiny.cert

tiny-manual.cert: ../../translator/l3.cert
