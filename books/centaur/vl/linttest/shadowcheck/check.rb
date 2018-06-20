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

def fine(modname, wirename)
  outlaw_warning(modname, "VL-PROGRAMMING-ERROR", wirename)
  outlaw_warning(modname, "VL-ILLEGAL-IMPORT", wirename)
  outlaw_warning(modname, "VL-IMPORT-CONFLICT", wirename)
  outlaw_warning(modname, "VL-TRICKY-SCOPE", wirename)
end

def tricky(modname, wirename)
  match_warning(modname, "VL-TRICKY-SCOPE", wirename)
  outlaw_warning(modname, "VL-PROGRAMMING-ERROR", wirename)
  outlaw_warning(modname, "VL-ILLEGAL-IMPORT", wirename)
  outlaw_warning(modname, "VL-IMPORT-CONFLICT", wirename)
end

fine(:m0, "clk")
fine(:m0, "shadowed_p1")
fine(:m0, "fine_w1")
fine(:m0, "fine_r2")

fine(:m1, "clk")
tricky(:m1, "shadowed_p1")
fine(:m1, "whatever")

fine(:m2, "m2in1")
fine(:m2, "m2var1")
fine(:m2, "m2var2")
fine(:m2, "m2var3")

test_passed()
