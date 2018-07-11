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

match_warning(:m0, "VL-WARN-TRUNCATION", "trunc1")
match_warning(:m0, "VL-WARN-TRUNCATION", "trunc2")
match_warning(:m0, "VL-WARN-TRUNCATION", "trunc3")
match_warning(:m0, "VL-WARN-TRUNCATION", "trunc4")
match_warning(:m0, "VL-WARN-TRUNCATION", "trunc5")
match_warning(:m0, "VL-WARN-TRUNCATION", "trunc6")
match_warning(:m0, "VL-WARN-TRUNCATION", "trunc7")
match_warning(:m0, "VL-WARN-TRUNCATION", "trunc8")

# BOZO this isn't working yet, why not?
# match_warning(:m0, "VL-WARN-TRUNCATION", "trunc9")

# This isn't working, I guess we aren't sizing tasks yet?
# match_warning(:m0, "VL-WARN-TRUNCATION", "trunc10")
# match_warning(:m0, "VL-WARN-TRUNCATION", "trunc11")

# BOZO this isn't working yet, why not?
# match_warning(:m0, "VL-WARN-TRUNCATION", "truncfun")

match_warning(:m0, "VL-WARN-TRUNCATION", "trunc12")
match_warning(:m0, "VL-WARN-TRUNCATION", "trunc13")



outlaw_warning(:m1, "VL-WARN-TRUNCATION", "normal1")
outlaw_warning(:m1, "VL-WARN-TRUNCATION", "normal2")
outlaw_warning(:m1, "VL-WARN-TRUNCATION", "normal3")

match_warning(:m1, "VL-WARN-TRUNCATION", "trunc1")



test_passed()



