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

STARTJOB ?= bash
VL       ?= $(PWD)/../bin/vl

NCV_VERILOG    ?= ncverilog +access+r
NCV_SYSVERILOG ?= ncverilog +access+r +sv +define+SYSTEM_VERILOG_MODE

VCS_VERILOG    ?= vcs -o simv.v
VCS_SYSVERILOG ?= vcs -sverilog +define+SYSTEM_VERILOG_MODE -o simv.sv

SPEC_FILES    := $(wildcard */spec.v)
TEST_DIRS     := $(patsubst %/spec.v, %,                   $(SPEC_FILES))
V_IMPL_FILES  := $(patsubst %/spec.v, %/impl.v,            $(SPEC_FILES))
SV_IMPL_FILES := $(patsubst %/spec.v, %/impl.sv,           $(SPEC_FILES))
NCV_V_OKS     := $(patsubst %/spec.v, %/ncv.verilog.ok,    $(SPEC_FILES))
NCV_SV_OKS    := $(patsubst %/spec.v, %/ncv.sysverilog.ok, $(SPEC_FILES))
VCS_V_OKS     := $(patsubst %/spec.v, %/vcs.verilog.ok,    $(SPEC_FILES))
VCS_SV_OKS    := $(patsubst %/spec.v, %/vcs.sysverilog.ok, $(SPEC_FILES))

all:


.PHONY: ncv
ncv: $(NCV_V_OKS) $(NCV_SV_OKS)

.PHONY: vcs
vcs: $(VCS_V_OKS) $(VCS_SV_OKS)

debug:
	@echo "PWD is $(PWD)"
	@echo "SPEC_FILES = $(SPEC_FILES)"
	@echo "TEST_DIRS = $(TEST_DIRS)"
	@echo "IMPL_FILES = $(IMPL_FILES)"

TRANSLATE_V  := $(VL) model spec.v --mem=2 --search=. --verilog-file=impl.v  --edition=Verilog
TRANSLATE_SV := $(VL) model spec.v --mem=2 --search=. --verilog-file=impl.sv --edition=SystemVerilog --define=SYSTEM_VERILOG_MODE

%/impl.sv: %/spec.v
	@echo "Making $*/impl.sv"
	@rm -f %/impl.sv
	@cd $*; $(STARTJOB) -c \
	  'echo `hostname` &> impl.sv.out; $(TRANSLATE_SV) &>> impl.sv.out'
	@ls -l $*/impl.sv

%/impl.v: %/spec.v
	@echo "Making $*/impl.v"
	@rm -f %/impl.v
	@cd $*; $(STARTJOB) -c \
	  'echo `hostname` &> impl.v.out; $(TRANSLATE_V) &>> impl.v.out'
	@ls -l $*/impl.v

%/ncv.verilog.ok: %/impl.v $(wildcard %/*.v)
	@echo "Making $*/ncv.verilog.ok"
	@cd $*; $(STARTJOB) -c "$(NCV_VERILOG) compare.v &> ncv.verilog.out"
	@ls -l $*/ncv.verilog.out
	@./errcheck.pl $*/ncv.verilog.out
# Dumb, need some kind of certificate here
	@cp $*/ncv.verilog.out $*/ncv.verilog.ok

%/ncv.sysverilog.ok: %/impl.sv $(wildcard %/*.v)
	@echo "Making $*/ncv.sysverilog.ok"
	@cd $*; $(STARTJOB) -c "$(NCV_SYSVERILOG) compare.v &> ncv.sysverilog.out"
	@ls -l $*/ncv.sysverilog.out
	@./errcheck.pl $*/ncv.sysverilog.out
# Dumb, need some kind of certificate here
	@cp $*/ncv.sysverilog.out $*/ncv.sysverilog.ok



%/vcs.verilog.ok: %/impl.v $(wildcard %/*.v)
	@echo "Making $*/vcs.verilog.ok"
	@cd $*; $(STARTJOB) -c "$(VCS_VERILOG) compare.v &> vcs.verilog.out; ./simv.v &>> vcs.verilog.out"
	@ls -l $*/vcs.verilog.out
	@./errcheck.pl $*/vcs.verilog.out
# Dumb, need some kind of certificate here
	@cp $*/vcs.verilog.out $*/vcs.verilog.ok

%/vcs.sysverilog.ok: %/impl.sv $(wildcard %/*.v)
	@echo "Making $*/vcs.sysverilog.ok"
	@cd $*; $(STARTJOB) -c "$(VCS_SYSVERILOG) compare.v &> vcs.sysverilog.out; ./simv.sv &>> vcs.sysverilog.out"
	@ls -l $*/vcs.sysverilog.out
	@./errcheck.pl $*/vcs.sysverilog.out
# Dumb, need some kind of certificate here
	@cp $*/vcs.sysverilog.out $*/vcs.sysverilog.ok



clean:
	rm -f */impl.v */impl.sv */*.sao */*.log */*.out */*.ok
	rm -rf */INCA_libs */*.vcd */*.key

all: $(V_IMPL_FILES)
all: $(SV_IMPL_FILES)
all: $(NCV_V_OKS)
all: $(NCV_SV_OKS)
all: $(VCS_V_OKS)
all: $(VCS_SV_OKS)



# Stupid little aliases so you can just type, e.g., "make case" to do the
# testes in the case/ directory.

.PHONY: $(TEST_DIRS)

define mkDirTarget
$(1): $(1)/ncv.sysverilog.ok
$(1): $(1)/ncv.verilog.ok
$(1): $(1)/vcs.sysverilog.ok
$(1): $(1)/vcs.verilog.ok
endef

$(foreach dir, $(TEST_DIRS), $(eval $(call mkDirTarget, $(dir))))
