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

def dupe(w)
  match_warning(:top, "VL-WARN-DUPLICATES", w)
end

def nodupe(w)
  outlaw_warning(:top, "VL-WARN-DUPLICATES", w)
end

dupe("w1_dupe")
dupe("w2_dupe")
dupe("w3a_dupe")
dupe("w3b_dupe")
dupe("w4a_dupe")
dupe("w4b_dupe")
dupe("w4c_dupe")
dupe("w5_dupe")
dupe("w6_dupe")
dupe("w7_dupe")
dupe("w8_dupe")
dupe("w9_dupe")
dupe("w10_dupe")
dupe("w11_dupe")

nodupe("w1_nodupe")
nodupe("w2_nodupe")
nodupe("w3a_nodupe")
nodupe("w3b_nodupe")
nodupe("w3c_nodupe")
nodupe("w4a_nodupe")
nodupe("w4b_nodupe")
nodupe("w4c_nodupe")
nodupe("w4d_nodupe")
nodupe("w4e_nodupe")
nodupe("w4f_nodupe")
nodupe("w5_nodupe")
nodupe("w6_nodupe")
nodupe("w7_nodupe")
nodupe("w8_nodupe")
nodupe("w9_nodupe")
nodupe("w10_nodupe")
nodupe("w11_nodupe")
nodupe("w12_nodupe")
nodupe("w13_nodupe")

nodupe("busclk")
nodupe("bus1")
nodupe("bus2")

test_passed()



