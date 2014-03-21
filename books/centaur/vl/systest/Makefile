# VL Verilog Toolkit
# Copyright (C) 2008-2014 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.  This program is distributed in the hope that it will be useful but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.  You should have received a copy of the GNU General Public
# License along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
#
# Original author: Jared Davis <jared@centtech.com>

.PHONY: all clean debug

ACL2     ?= acl2
VERILOG  ?= ncverilog
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
	  "$(VL) model spec.v --verilog-file=impl.v --mem=2 --search=. &> impl.out"
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

