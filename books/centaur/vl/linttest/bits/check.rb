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

def normal(wire)
  outlaw_warning(:top, "VL-WARN-TRUNCATION", wire);
  outlaw_warning(:top, "VL-WARN-EXTENSION", wire);
end

def ext(wire)
  match_warning(:top, "VL-WARN-EXTENSION", wire);
  outlaw_warning(:top, "VL-WARN-TRUNCATION", wire);
end

def trunc(wire)
  match_warning(:top, "VL-WARN-TRUNCATION", wire);
  outlaw_warning(:top, "VL-WARN-EXTENSION", wire);
end

normal("normal1")
ext("ext1")
trunc("trunc1")

normal("normal2")
normal("normal3")
normal("normal4")

normal("normal_op1")
ext("ext_op1")
trunc("trunc_op1")

normal("normal_inst1")
ext("ext_inst1")
trunc("trunc_inst1")

normal("normal_op2")
ext("ext_op2")
trunc("trunc_op2")

normal("normal_inst2")
ext("ext_inst2")
trunc("trunc_inst2")

normal("normal_op3")
ext("ext_op3")
trunc("trunc_op3")

normal("normal_inst3")
ext("ext_inst3")
trunc("trunc_inst3")

normal("normal_arr1")
ext("ext_arr1")
trunc("trunc_arr1")

normal("normal_arr2")
ext("ext_arr2")
trunc("trunc_arr2")

normal("normal_arr3")
ext("ext_arr3")
trunc("trunc_arr3")

normal("normal_arr4")
ext("ext_arr4")
trunc("trunc_arr4")


test_passed()



