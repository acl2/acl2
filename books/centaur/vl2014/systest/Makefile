# VL 2014 -- VL Verilog Toolkit, 2014 Edition
# Copyright (C) 2008-2015 Centaur Technology
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

.PHONY: all clean debug ncv vcs

all: ncv vcs

STARTJOB ?= bash
VL       ?= $(PWD)/../bin/vl2014

SPEC_FILES        := $(wildcard */spec.v)
TEST_DIRS         := $(patsubst %/spec.v, %,                   $(SPEC_FILES))

NCV_V_IMPL_FILES  := $(patsubst %/spec.v, %/impl.ncv.v,        $(SPEC_FILES))
NCV_SV_IMPL_FILES := $(patsubst %/spec.v, %/impl.ncv.sv,       $(SPEC_FILES))
NCV_V_OKS         := $(patsubst %/spec.v, %/ncv.v.ok,          $(SPEC_FILES))
NCV_SV_OKS        := $(patsubst %/spec.v, %/ncv.sv.ok,         $(SPEC_FILES))

ncv: $(NCV_V_IMPL_FILES)
ncv: $(NCV_SV_IMPL_FILES)
ncv: $(NCV_V_OKS)
ncv: $(NCV_SV_OKS)

VCS_V_IMPL_FILES  := $(patsubst %/spec.v, %/impl.vcs.v,        $(SPEC_FILES))
VCS_SV_IMPL_FILES := $(patsubst %/spec.v, %/impl.vcs.sv,       $(SPEC_FILES))
VCS_V_OKS         := $(patsubst %/spec.v, %/vcs.v.ok,          $(SPEC_FILES))
VCS_SV_OKS        := $(patsubst %/spec.v, %/vcs.sv.ok,         $(SPEC_FILES))

vcs: $(VCS_V_IMPL_FILES)
vcs: $(VCS_SV_IMPL_FILES)
vcs: $(VCS_V_OKS)
vcs: $(VCS_SV_OKS)

impls: $(NCV_V_IMPL_FILES) $(NCV_SV_IMPL_FILES) $(VCS_V_IMPL_FILES) $(VCS_SV_IMPL_FILES)

NCV_VERILOG    := ncverilog +access+r      +define+VL_SYSTEST_NCV
NCV_SYSVERILOG := ncverilog +access+r +sv  +define+VL_SYSTEST_NCV +define+SYSTEM_VERILOG_MODE
VCS_VERILOG    := vcs -o simv.v            +define+VL_SYSTEST_VCS
VCS_SYSVERILOG := vcs -o simv.sv -sverilog +define+VL_SYSTEST_VCS +define+SYSTEM_VERILOG_MODE

XLATE_NCV_V    := $(VL) model spec.v --mem=2 --search=. --verilog-file=impl.ncv.v  --define=VL_SYSTEST_NCV --edition=Verilog
XLATE_NCV_SV   := $(VL) model spec.v --mem=2 --search=. --verilog-file=impl.ncv.sv --define=VL_SYSTEST_NCV --edition=SystemVerilog --define=SYSTEM_VERILOG_MODE
XLATE_VCS_V    := $(VL) model spec.v --mem=2 --search=. --verilog-file=impl.vcs.v  --define=VL_SYSTEST_VCS --edition=Verilog
XLATE_VCS_SV   := $(VL) model spec.v --mem=2 --search=. --verilog-file=impl.vcs.sv --define=VL_SYSTEST_VCS --edition=SystemVerilog --define=SYSTEM_VERILOG_MODE

%/impl.ncv.v: %/spec.v $(VL)
	@echo "Making $*/impl.ncv.v"
	@rm -f %/impl.ncv.v %/impl.ncv.v.out
	@cd $*; $(STARTJOB) -c \
	  'echo `hostname` &> impl.ncv.v.out; $(XLATE_NCV_V) &>> impl.ncv.v.out'
	@ls -l $*/impl.ncv.v

%/impl.ncv.sv: %/spec.v $(VL)
	@echo "Making $*/impl.ncv.sv"
	@rm -f %/impl.ncv.sv %/impl.ncv.sv.out
	@cd $*; $(STARTJOB) -c \
	  'echo `hostname` &> impl.ncv.sv.out; $(XLATE_NCV_SV) &>> impl.ncv.sv.out'
	@ls -l $*/impl.ncv.sv

%/impl.vcs.v: %/spec.v $(VL)
	@echo "Making $*/impl.vcs.v"
	@rm -f %/impl.vcs.v %/impl.vcs.v.out
	@cd $*; $(STARTJOB) -c \
	  'echo `hostname` &> impl.vcs.v.out; $(XLATE_VCS_V) &>> impl.vcs.v.out'
	@ls -l $*/impl.vcs.v

%/impl.vcs.sv: %/spec.v $(VL)
	@echo "Making $*/impl.vcs.sv"
	@rm -f %/impl.vcs.sv %/impl.vcs.sv.out
	@cd $*; $(STARTJOB) -c \
	  'echo `hostname` &> impl.vcs.sv.out; $(XLATE_VCS_SV) &>> impl.vcs.sv.out'
	@ls -l $*/impl.vcs.sv

%/ncv.v.ok: %/impl.ncv.v %/spec.v $(wildcard %/compare*.v)
	@echo "Making $*/ncv.v.out"
	@cd $*; $(STARTJOB) -c "$(NCV_VERILOG) compare.v spec.v impl.ncv.v &> ncv.v.out" \
           || (echo "NCV command failed for $*." ;\
	       ../errcheck.pl ncv.v.out ;\
	       false)
	@ls -l $*/ncv.v.out
	@./errcheck.pl $*/ncv.v.out
	@cp $*/ncv.v.out $*/ncv.v.ok

%/ncv.sv.ok: %/impl.ncv.sv %/spec.v $(wildcard %/compare*.v)
	@echo "Making $*/ncv.sv.out"
	@cd $*; $(STARTJOB) -c "$(NCV_SYSVERILOG) compare.v spec.v impl.ncv.sv &> ncv.sv.out" \
           || (echo "NCV command failed for $*." ;\
	       ../errcheck.pl ncv.sv.out ;\
	       false)
	@ls -l $*/ncv.sv.out
	@./errcheck.pl $*/ncv.sv.out
	@cp $*/ncv.sv.out $*/ncv.sv.ok

%/vcs.v.ok: %/impl.vcs.v $(wildcard %/compare*.v)
	@echo "Making $*/vcs.v.out"
	@cd $*; $(STARTJOB) -c "$(VCS_VERILOG) compare.v spec.v impl.vcs.v &> vcs.v.out; ./simv.v &>> vcs.v.out" \
            || (echo "VCS command failed for $*." ;\
	       ../errcheck.pl vcs.v.out ;\
	       false)
	@ls -l $*/vcs.v.out
	@./errcheck.pl $*/vcs.v.out
	@cp $*/vcs.v.out $*/vcs.v.ok

%/vcs.sv.ok: %/impl.vcs.sv $(wildcard %/compare*.v)
	@echo "Making $*/vcs.sv.out"
	@cd $*; $(STARTJOB) -c "$(VCS_SYSVERILOG) compare.v spec.v impl.vcs.sv &> vcs.sv.out; ./simv.sv &>> vcs.sv.out" \
            || (echo "VCS command failed for $*." ;\
	       ../errcheck.pl vcs.sv.out ;\
	       false)
	@ls -l $*/vcs.sv.out
	@./errcheck.pl $*/vcs.sv.out
	@cp $*/vcs.sv.out $*/vcs.sv.ok



# Stupid little aliases so you can just type, e.g., "make case" to do the
# testes in the case/ directory.

.PHONY: $(TEST_DIRS)

define mkDirTarget
$(1): $(1)/ncv.sv.ok
$(1): $(1)/ncv.v.ok
$(1): $(1)/vcs.sv.ok
$(1): $(1)/vcs.v.ok
endef

$(foreach dir, $(TEST_DIRS), $(eval $(call mkDirTarget, $(dir))))




clean:
	rm -f */impl.*.v */impl.*.sv
	rm -f */*.sao */*.sao.ver
	rm -f */*.log */*.out */*.ok
	rm -rf */INCA_libs */*.vcd */*.key
	rm -rf */simv.*.daidir */simv.v */simv.sv
	rm -rf */csrc
	rm -f .joblist */.joblist
	rm -f */*.tem
