# ESIM Symbolic Hardware Simulator
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

.PHONY: all clean
all:

ifndef STV_GCC_DIR
$(error STV_GCC_DIR environment variable is required, but not set. \
        Please set STV_GCC_DIR to point at the installation of GCC \
        to use, or edit the Makefile to suit your system.)
endif

STARTJOB  ?= bash
CXX       := $(STV_GCC_DIR)/bin/g++
CXXFLAGS  := -Wall -std=gnu++11 -g -O3
LINKFLAGS := -L$(STV_GCC_DIR)/lib64 -Wl,-rpath,$(STV_GCC_DIR)/lib64

all: test_bits alu16

%.o: %.cc
	$(CXX) -c $(CXXFLAGS) $<

test_bits: test_bits.o
	$(CXX) $(CXXFLAGS) $(LINKFLAGS) test_bits.o -o test_bits


# ALU16 Tutorial Example.  For this command to work, you'll have to build the
# VL toolkit and add it to your path (see acl2/books/Makefile)

alu16_test.cc: alu16_test.stv ../../../tutorial/alu16.v
	$(STARTJOB) -c \
	  "vl stv2c --stv alu16_test.stv ../../../tutorial/alu16.v &> alu16_test.out"

alu16_test.o: alu16_test.cc fourval.h bits.h


# C++ test bench for the generated ALU16 code.

alu16: alu16_test.o alu16.cc
	$(CXX) $(CXXFLAGS) $(LINKFLAGS) alu16.cc alu16_test.o -o alu16


# I won't delete the cert files, because you can just run clean.pl if you
# really want to do that.

clean:
	rm -f test_bits test_bits.o
	rm -f alu16 alu16_test.h alu16_test.cc alu16_test.out
