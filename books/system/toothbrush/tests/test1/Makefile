include ../test-Makefile

tb_top: tb-exec-test

.PHONY: tb-exec-test
tb-exec-test: tb-exec
	@echo "$(TEST_DIR_STRING)Starting step to test tb-exec (see tb-exec-test.out)..."
	@rm -f workxxx.$@
	@echo '(load "$(TB_TEST)")' >> workxxx.$@
	@echo '(acl2::exit-lisp)' >> workxxx.$@
	@(./tb-exec < workxxx.$@ 2>&1) > $@.out
	@if [ "`fgrep SUCCESS $@.out`" = "" ] ; then \
	echo "Test failed!  See `pwd`/$@.out ." ;\
	exit 1 ;\
	else \
	(echo "Test succeeded." > $@) ;\
	echo "$(TEST_DIR_STRING)Completed step to test tb-exec successfully." ;\
	fi

tb-exec: success.txt
	@echo "$(TEST_DIR_STRING)Starting step to save tb-exec (see tb-exec.out)..."
	@rm -f workxxx.$@
	@echo '(defparameter *acl2-dir* "$(ACL2_DIR)")' > workxxx.$@
	@echo '(load "../../load-toothbrush.lsp")' >> workxxx.$@
	@echo '(acl2::with-suppression (load "$(TB_OUTPUT)"))' >> workxxx.$@
	@echo '(compile-file "$(TB_OUTPUT).lsp")' >> workxxx.$@
	@echo '(in-package "ACL2")' >> workxxx.$@
	@echo '(save-exec "tb-exec" "Toothbrush for test1")' >> workxxx.$@
	@($(TB_LISP) < workxxx.$@ 2>&1) > tb-exec.out
	@echo "$(TEST_DIR_STRING)Completed step to save tb-exec."
