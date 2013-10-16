# ESIM Symbolic Hardware Simulator
# Copyright (C) 2010-2013 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http:#www.centtech.com/
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
