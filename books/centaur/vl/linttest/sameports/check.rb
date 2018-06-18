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

def normal(w)
  outlaw_warning(:top, "VL-WARN-SAME-PORTS", w)
  outlaw_warning(:top, "VL-WARN-SAME-INPUTS", w)
end

def sameports(w)
  match_warning(:top, "VL-WARN-SAME-PORTS", w)
  outlaw_warning(:top, "VL-WARN-SAME-INPUTS", w)
end

def sameins(w)
  match_warning(:top, "VL-WARN-SAME-INPUTS", w)
  outlaw_warning(:top, "VL-WARN-SAME-PORTS", w)
end

normal("m0_normal")
sameports("m0_sp_a")
sameports("m0_sp_b")
sameins("m0_si_a")
sameins("m0_si_b")

normal("m1_normal_a")
normal("m1_normal_b")

normal("i0_normal_a")
normal("i0_normal_b")

normal("i1_normal_a")
normal("i1_normal_b")

normal("i1_normal_c")
normal("i1_normal_d")

# BOZO I broke this in order to get m0_gen and m1_gen to not complain.
# Fixing this would require some more sensible approach to telling which
# generate blocks are going to be elaborated.  (Maybe we should do this
# whole thing post-elaboration?)

#sameports("m0arr")
#sameports("xx0")
#sameports("xx1")
#sameports("xx2")

normal("i0arr")

normal("m0_gen1")
normal("m0_gen2")

test_passed()



