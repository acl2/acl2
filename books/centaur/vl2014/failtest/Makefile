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

.PHONY: all clean

STARTJOB ?= bash
VL       ?= $(PWD)/../bin/vl2014

SPEC_FILES := $(wildcard *.v)
VOK_FILES  := $(patsubst %.v, %.vok,  $(SPEC_FILES))
SVOK_FILES := $(patsubst %.v, %.svok, $(SPEC_FILES))



%.vok: %.v $(VL)
	echo "Making $*.ok"
	rm -f $*.vok
	$(STARTJOB) -c "$(VL) model $*.v --mem=2 --search=. --mustfail=top --edition=Verilog --model-file=$*.v.model.sao --esims-file=$*.v.esims.sao --verilog-file=$*.v.pp &> $*.vok.log"
	rm $*.v.esims.sao $*.v.model.sao $*.v.model.sao.ver $*.v.pp
	cp $*.vok.log $*.vok
	ls -l $*.vok

%.svok: %.v $(VL)
	echo "Making $*.svok"
	rm -f $*.svok
	$(STARTJOB) -c "$(VL) model $*.v --mem=2 --search=. --mustfail=top --edition=SystemVerilog --model-file=$*.sv.model.sao --esims-file=$*.sv.esims.sao --verilog-file=$*.sv.pp &> $*.svok.log"
	rm $*.sv.esims.sao $*.sv.model.sao $*.sv.model.sao.ver $*.sv.pp
	cp $*.svok.log $*.svok
	ls -l $*.svok

all: $(VOK_FILES) $(SVOK_FILES)



clean:
	rm -f *.vok *.svok *.log *.sao *.pp *.sao.ver
	rm -rf csrc INCA_libs simv.daidir
	rm -f simv ucli.key *.log
