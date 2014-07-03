# VL Verilog Toolkit
# Copyright (C) 2008-2014 Centaur Technology
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
# Original author: Jared Davis <jared@centtech.com>

.PHONY: all clean debug

ACL2     ?= acl2
VERILOG  ?= ncverilog +access+r +sv
STARTJOB ?= bash
VL       ?= $(PWD)/../bin/vl

SPEC_FILES := $(wildcard */spec.v)
TEST_DIRS  := $(patsubst %/spec.v, %, $(SPEC_FILES))
IMPL_FILES := $(patsubst %/spec.v, %/impl.v, $(SPEC_FILES))
RUN_OKS    := $(patsubst %/spec.v, %/run.ok, $(SPEC_FILES))

all:

debug:
	@echo "PWD is $(PWD)"
	@echo "SPEC_FILES = $(SPEC_FILES)"
	@echo "TEST_DIRS = $(TEST_DIRS)"
	@echo "IMPL_FILES = $(IMPL_FILES)"


%/impl.v: %/spec.v
	@echo "Making $*/impl.v"
	@cd $*; $(STARTJOB) -c \
	  'echo `hostname` &> impl.out; $(VL) model spec.v --verilog-file=impl.v --mem=2 --search=. &>> impl.out'
	@ls -l $*/impl.v

%/run.ok: %/impl.v $(wildcard %/*.v)
	@echo "Making $*/run.ok"
	@cd $*; $(STARTJOB) -c \
	  "$(VERILOG) compare.v &> run.out"
	@ls -l $*/run.out
	@./errcheck.pl $*/run.out
# Dumb, need some kind of certificate here
	@cp $*/run.out $*/run.ok

clean:
	rm -f */impl.v */*.sao */*.log */*.out */run.ok
	rm -rf */INCA_libs */*.vcd */*.key

all: $(IMPL_FILES)
all: $(RUN_OKS)

