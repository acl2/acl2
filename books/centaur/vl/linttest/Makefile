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

.PHONY: all clean

all:

STARTJOB              ?= bash
VL                    ?= $(PWD)/../bin/vl
VL_LINTTEST_RUBYFLAGS ?=
RUBY                  ?= ruby $(VL_LINTTEST_RUBYFLAGS)

SPEC_FILES := $(wildcard */spec.sv)
TEST_DIRS  := $(patsubst %/spec.sv, %, $(SPEC_FILES))
JSON_FILES := $(patsubst %/spec.sv, %/vl-warnings.json, $(SPEC_FILES))
OK_FILES   := $(patsubst %/spec.sv, %/vl-warnings.ok, $(SPEC_FILES))

%/vl-warnings.json: %/spec.sv $(VL)
	@echo "Making $*/vl-warnings.json"
	@rm -f $*/vl-warnings.json $*/vl-*.txt $*/vl-lint.log
	cd $*; LINTARGS=`if [ -e lintargs ]; then cat lintargs; fi`; $(STARTJOB) -c "$(VL) lint spec.sv $$LINTARGS &> vl-lint.log"
	@ls -l $*/vl-warnings.json

%/vl-warnings.ok: %/vl-warnings.json %/check.rb utils.rb
	@echo "Making $*/vl-warnings.ok"
	@rm -f $*/vl-warnings.ok
	@cd $*; $(STARTJOB) -c "$(RUBY) check.rb &> check.log" || (echo "*** FAIL: $* ***"; cat check.log; false)
	@ls -l $*/vl-warnings.ok

all: $(OK_FILES) $(JSON_FILES)

# Stupid little aliases so you can just type, e.g., "make case" to do the
# testes in the case/ directory.

.PHONY: $(TEST_DIRS)

define mkDirTarget
$(1): $(1)/vl-warnings.ok
endef

$(foreach dir, $(TEST_DIRS), $(eval $(call mkDirTarget, $(dir))))

clean:
	rm -f */vl-*.txt
	rm -f */vl-lint.log
	rm -f */vl-warnings.json
	rm -f */vl-warnings.ok
	rm -f */check.log
	rm -f vl-*.txt vl-warnings.json
	rm -rf */INCA_libs */simv.daidir */simv */csrc */ncverilog.log
