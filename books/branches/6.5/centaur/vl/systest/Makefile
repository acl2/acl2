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

VERILOG    ?= ncverilog +access+r
SYSVERILOG ?= ncverilog +access+r +sv +define+SYSTEM_VERILOG_MODE

STARTJOB ?= bash
VL       ?= $(PWD)/../bin/vl

SPEC_FILES    := $(wildcard */spec.v)
TEST_DIRS     := $(patsubst %/spec.v, %,               $(SPEC_FILES))
V_IMPL_FILES  := $(patsubst %/spec.v, %/impl.v,        $(SPEC_FILES))
SV_IMPL_FILES := $(patsubst %/spec.v, %/impl.sv,       $(SPEC_FILES))
V_OKS         := $(patsubst %/spec.v, %/verilog.ok,    $(SPEC_FILES))
SV_OKS        := $(patsubst %/spec.v, %/sysverilog.ok, $(SPEC_FILES))

all:

debug:
	@echo "PWD is $(PWD)"
	@echo "SPEC_FILES = $(SPEC_FILES)"
	@echo "TEST_DIRS = $(TEST_DIRS)"
	@echo "IMPL_FILES = $(IMPL_FILES)"


TRANSLATE_V  := $(VL) model spec.v --mem=2 --search=. --verilog-file=impl.v  --edition=Verilog
TRANSLATE_SV := $(VL) model spec.v --mem=2 --search=. --verilog-file=impl.sv --edition=SystemVerilog --define=SYSTEM_VERILOG_MODE

%/impl.sv: %/spec.v
	@echo "Making $*/impl.sv"
	@cd $*; $(STARTJOB) -c \
	  'echo `hostname` &> impl.out; $(TRANSLATE_SV) &>> impl.sv.out'
	@ls -l $*/impl.sv

%/impl.v: %/spec.v
	@echo "Making $*/impl.v"
	@cd $*; $(STARTJOB) -c \
	  'echo `hostname` &> impl.out; $(TRANSLATE_V) &>> impl.out'
	@ls -l $*/impl.v

%/verilog.ok: %/impl.v $(wildcard %/*.v)
	@echo "Making $*/verilog.ok"
	@cd $*; $(STARTJOB) -c "$(VERILOG) compare.v &> verilog.out"
	@ls -l $*/verilog.out
	@./errcheck.pl $*/verilog.out
# Dumb, need some kind of certificate here
	@cp $*/verilog.out $*/verilog.ok

%/sysverilog.ok: %/impl.sv $(wildcard %/*.v)
	@echo "Making $*/sysverilog.ok"
	@cd $*; $(STARTJOB) -c "$(SYSVERILOG) compare.v &> sysverilog.out"
	@ls -l $*/sysverilog.out
	@./errcheck.pl $*/sysverilog.out
# Dumb, need some kind of certificate here
	@cp $*/sysverilog.out $*/sysverilog.ok

clean:
	rm -f */impl.v */impl.sv */*.sao */*.log */*.out */*.ok
	rm -rf */INCA_libs */*.vcd */*.key

all: $(V_IMPL_FILES)
all: $(SV_IMPL_FILES)
all: $(V_OKS)
all: $(SV_OKS)

