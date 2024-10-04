BASE = /home/hbl/currentwork
SRC  = $(BASE)/src
ACL2 = $(BASE)/bin/acl2/acl2-sources/saved_acl2

PYTHON = python

include $(SRC)/Makefile-generic


.SUFFIXES: .cert .lisp

.PHONY: X

%.cert: %.lisp X
	@$(PYTHON) $(BASE)/bin/acl2_make_wrap.py -b $(SRC) $@


clean: 	
	rm -f *.cert
	rm -f *.o
	rm -f *.h
	rm -f *.c
	rm -f *.lib
	rm -f *.fasl
	rm -f *.fas
	rm -f *.sbin
	rm -f *.lbin
	rm -f *.pfsl
	rm -f *.cfsl
	rm -f *.bin
	rm -f *.sparcf
	rm -f *.ufsl
	rm -f *.dfsl
	rm -f *.x86f
	rm -f *.axpf
	rm -f *.out
	rm -f *.date
	rm -f *.log
	rm -f TMP.*
	rm -f TMP1.*
	rm -f workxxx*

dependencies:
	@cd $(SRC); make dependencies