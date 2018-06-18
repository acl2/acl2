#!/usr/bin/env ruby

# VL Verilog Toolkit
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

require 'require_relative' if RUBY_VERSION =~ /1\.8/
require_relative '../utils'

outlaw_bad_warnings()
outlaw_warning_global("VL-PROGRAMMING-ERROR")

def overflow(mod, substring)
  match_warning(mod, "VL-WARN-OVERFLOW", substring)
  outlaw_warning(mod, "VL-WARN-INCOMPATIBLE", substring)
end

def incompat(mod, substring)
  match_warning(mod, "VL-WARN-INCOMPATIBLE", substring)
  outlaw_warning(mod, "VL-WARN-OVERFLOW", substring)
end

def normal(mod, substring)
  outlaw_warning(mod, "VL-WARN-OVERFLOW", substring)
  outlaw_warning(mod, "VL-WARN-INCOMPATIBLE", substring)
end

overflow(:top, "8'h FFF")
overflow(:top, "8'o 7777")
overflow(:top, "8'b 1111_1111_1111")

normal(:top, "8'hFE")
normal(:top, "8'o176")
normal(:top, "8'b1111_1110")
normal(:top, "8'd254")

overflow(:top, "18446744073709551616")
overflow(:top, "2147483648")
normal(:top, "2147483647")
normal(:top, "9876")

normal(:top, "9'h 1FF")
overflow(:top, "9'h 3FF")


overflow(:weird, "8'h FXF")
overflow(:weird, "8'o 77X7")
overflow(:weird, "8'b 111X_1111_1111")

normal(:weird, "8'h XXX")

normal(:weird, "20'h FX")
normal(:weird, "20'o 7X")
normal(:weird, "20'b 11X")

normal(:weird, "20'h XF")
normal(:weird, "20'o X7")
normal(:weird, "20'b X11")

incompat(:weird, "'h XA")
incompat(:weird, "'o X6")
incompat(:weird, "'b X10")

test_passed()



