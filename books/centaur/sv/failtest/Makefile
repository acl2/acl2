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
# Original author: Jared Davis <jared@centtech.com>

.PHONY: all clean passing
all:


STARTJOB  ?= bash
COSIM_DIR := $(PWD)/../cosims
CORE      := $(COSIM_DIR)/cosim-core

SPEC_FILES := $(wildcard *.v)
TESTNAMES  := $(patsubst %.v, %, $(SPEC_FILES))
VOK_FILES  := $(patsubst %.v, %.vok,  $(SPEC_FILES))
SVOK_FILES := $(patsubst %.v, %.svok, $(SPEC_FILES))

FAILING_TEST_TARGETS := \
  bigwire1.svok \
  fn1.vok fn1.svok \
  gates2.svok \
  gates5.svok \
  iface8.svok \
  inc8.svok \
  inc9.svok \
  inst9.svok \
  inst12.svok \
  param1.svok \
  elab6.vok elab6.svok \
  stmt1.svok  \
  gen8b.vok gen8b.svok \
  iface26.svok \
  names4.svok names4.vok \
  names5.svok names5.vok \
  names6.svok names6.vok

$(CORE):
	cd $(COSIM_DIR); $(MAKE) cosim-core
	ls -lah $(COSIM_DIR)/cosim-core

%.vok: %.v $(CORE)
	@echo "Making $*.vok"
	@rm -f $*.vok
	@ACL2_CUSTOMIZATION=NONE TESTNAME=$* EDITION=VERILOG-2005 \
          $(STARTJOB) -c "$(CORE) < run.lsp &> $*.vok.log"
	@ls -l $*.vok

%.svok: %.v $(CORE)
	@echo "Making $*.svok"
	@rm -f $*.svok
	@ACL2_CUSTOMIZATION=NONE TESTNAME=$* EDITION=SYSTEM-VERILOG-2012 \
          $(STARTJOB) -c "$(CORE) < run.lsp &> $*.svok.log"
	@ls -l $*.svok

all: $(VOK_FILES) $(SVOK_FILES)

PASSING_VOK := $(filter-out $(FAILING_TEST_TARGETS), $(VOK_FILES))
PASSING_SVOK := $(filter-out $(FAILING_TEST_TARGETS), $(SVOK_FILES))
passing: $(PASSING_VOK) $(PASSING_SVOK)

.phony: failing
failing: $(FAILING_TEST_TARGETS)

clean:
	rm -f *.vok *.svok *.log
	rm -rf csrc INCA_libs simv.daidir
	rm -f simv ucli.key *.history


# [Jared] hack so you can just write "make ansi1" or similar, adapted
# from vl linttests

.PHONY: $(TESTNAMES)

define mkTestTarget
$(1): $(1).vok $(1).svok
endef

$(foreach test, $(TESTNAMES), $(eval $(call mkTestTarget, $(test))))



