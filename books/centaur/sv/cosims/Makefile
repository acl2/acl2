# SV - Symbolic Vector Hardware Analysis Framework
# Copyright (C) 2014-2015 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# License: (An MIT/X11-style license)
#
#   Permission is hereby granted, free of charge, to any person obtaining a
#   copy of this software and associated documentation files (the "Software"),
#   to deal in the Software without restriction, including without limitation
#   the rights to use, copy, modify, merge, publish, distribute, sublicense,
#   and/or sell copies of the Software, and to permit persons to whom the
#   Software is furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in
#   all copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#   DEALINGS IN THE SOFTWARE.
#
# Original author: Sol Swords <sswords@centtech.com>

.PHONY: all

all:

# ---------------------------------------
#  Building the cosim image

STARTJOB ?= $(SHELL)
ACL2 ?= acl2

CORE := ./cosim-core
IMG_EXT ?= lx86cl64

ACL2_SYSTEM_BOOKS ?= ../../..

$(info Rebuilding Makefile-books...)
REBUILD_MAKEFILE_BOOKS := $(shell \
	$(ACL2_SYSTEM_BOOKS)/build/cert.pl cosims.lisp \
		--quiet \
		--static-makefile Makefile-books \
		--var-prefix BOOKS_TOP; \
        ls -l Makefile-books ;\
	)
$(info $(REBUILD_MAKEFILE_BOOKS))
$(info Done rebuilding makefiles)

-include Makefile-books

cosim-core: cosims.cert make-cosim.lsp
	rm -f $(CORE) 
	$(STARTJOB) -c "$(ACL2) < make-cosim.lsp &> make-cosim.out"

all: cosim-core symlinks

.PHONY: symlinks

# ------------------------------------------
#  Test setup.

SPECFILES := $(wildcard */spec.sv)
TESTS := $(patsubst %/spec.sv,%,$(SPECFILES))
TESTCERTS := $(patsubst %,%/ok,$(TESTS))
OUTDATAS_NCV := $(patsubst %,%/outputs.ncv.data,$(TESTS))
OUTDATAS_VCS := $(patsubst %,%/outputs.vcs.data,$(TESTS))
print_tests :
	@echo $(TESTS)

%/ok : %/outputs.ncv.data %/outputs.vcs.data cosim-core
	COSIM_TESTDIR=$* $(STARTJOB) -c "./cosim-core < run.lsp > $*/cosim.out"
	@! egrep -i "failed|error" $*/cosim.out > /dev/null
	@mv $*/cosim.out $*/ok
	@ls -l $*/ok

%/outputs.ncv.data : %/spec.sv %/inputs.data test.sv
	@cd $*; \
	 if [ -e no_ncv ]; then \
		touch outputs.ncv.data; \
	 else \
		ncverilog spec.sv ../test.sv +define+outfile=\"outputs.ncv.data\"; \
	 fi
	@ls -l $*/outputs.ncv.data

%/outputs.vcs.data : %/spec.sv %/inputs.data test.sv
	@cd $*; \
	 if [ -e no_vcs ]; then \
		touch outputs.vcs.data; \
	 else \
		 vcs -sverilog spec.sv ../test.sv +define+outfile=\"outputs.vcs.data\" && ./simv; \
	 fi
	@ls -l $*/outputs.vcs.data

.PHONY: ncv
ncv : $(OUTDATAS_NCV)

.PHONY: vcs
vcs : $(OUTDATAS_VCS)

all : $(TESTCERTS) ncv vcs

.PHONY: cleansim
cleansim :
	rm -f $(OUTDATAS_NCV) $(OUTDATAS_VCS)
