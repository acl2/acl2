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

# BOZO what is going on??? outlaw_warning_global("VL-PROGRAMMING-ERROR")


def yes(modname, wirename)
  match_warning(modname, "VL-WARN-LEFTRIGHT", wirename)
end

def no(modname, wirename)
  outlaw_warning(modname, "VL-WARN-LEFTRIGHT", wirename)
end

no(:m0, "plain_no1")
no(:m0, "plain_no2")
no(:m0, "plain_no3")
no(:m0, "plain_no4")
no(:m0, "plain_no5")
no(:m0, "plain_no6")
no(:m0, "plain_no7")
no(:m0, "plain_no8")

no(:m0, "and_no1")
no(:m0, "and_no2")
yes(:m0, "and_warn1")
yes(:m0, "and_warn2")
yes(:m0, "and_warn3")

no(:m0, "or_no1")
no(:m0, "or_no2")
yes(:m0, "or_warn1")
yes(:m0, "or_warn2")
yes(:m0, "or_warn3")

no(:m0, "eq_no1")
no(:m0, "eq_no2")
no(:m0, "eq_no3")
yes(:m0, "eq_warn1")
yes(:m0, "eq_warn2")
yes(:m0, "eq_warn3")

no(:m0, "lt_no1")
no(:m0, "lt_no2")
no(:m0, "lt_no3")
yes(:m0, "lt_warn1")
yes(:m0, "lt_warn2")
yes(:m0, "lt_warn3")

no(:m0, "lte_no1")
no(:m0, "lte_no2")
no(:m0, "lte_no3")
yes(:m0, "lte_warn1")
yes(:m0, "lte_warn2")
yes(:m0, "lte_warn3")

no(:m0, "shl_no1")
no(:m0, "shl_no2")
no(:m0, "shl_no3")
no(:m0, "shl_no4")
no(:m0, "shl_no5")
no(:m0, "shl_no6")
yes(:m0, "shl_warn1")
yes(:m0, "shl_warn2")
yes(:m0, "shl_warn3")
yes(:m0, "shl_warn4")

no(:m0, "ashl_no1")
no(:m0, "ashl_no2")
no(:m0, "ashl_no3")
no(:m0, "ashl_no4")
no(:m0, "ashl_no5")
no(:m0, "ashl_no6")
yes(:m0, "ashl_warn1")
yes(:m0, "ashl_warn2")
yes(:m0, "ashl_warn3")
yes(:m0, "ashl_warn4")

no(:m0, "shr_no1")
no(:m0, "shr_no2")
no(:m0, "shr_no3")
no(:m0, "shr_no4")
no(:m0, "shr_no5")
yes(:m0, "shr_warn1")
yes(:m0, "shr_warn2")
yes(:m0, "shr_warn3")
yes(:m0, "shr_warn4")
yes(:m0, "shr_warn5")

no(:m0, "ashr_no1")
no(:m0, "ashr_no2")
no(:m0, "ashr_no3")
no(:m0, "ashr_no4")
no(:m0, "ashr_no5")
yes(:m0, "ashr_warn1")
yes(:m0, "ashr_warn2")
yes(:m0, "ashr_warn3")
yes(:m0, "ashr_warn4")
yes(:m0, "ashr_warn5")

no(:m0, "times_no1")
no(:m0, "times_no2")
no(:m0, "times_no3")
no(:m0, "times_no4")
no(:m0, "times_no5")
no(:m0, "times_no6")
no(:m0, "times_no7")
no(:m0, "times_no8")
no(:m0, "times_no9")
no(:m0, "times_no10")

no(:m0, "plus_no1")
no(:m0, "plus_no2")
no(:m0, "plus_no3")
no(:m0, "plus_no4")
no(:m0, "plus_no5")
no(:m0, "plus_no6")
no(:m0, "plus_no7")
no(:m0, "plus_no8")
no(:m0, "plus_no9")
no(:m0, "plus_no10")
yes(:m0, "plus_warn1")
yes(:m0, "plus_warn2")
yes(:m0, "plus_warn3")
yes(:m0, "plus_warn4")
yes(:m0, "plus_warn5")
yes(:m0, "plus_warn6")

no(:m0, "minus_no1")
no(:m0, "minus_no2")
no(:m0, "minus_no3")
no(:m0, "minus_no4")
no(:m0, "minus_no5")
no(:m0, "minus_no6")
no(:m0, "minus_no7")
no(:m0, "minus_no8")
no(:m0, "minus_no9")
yes(:m0, "minus_warn1")
yes(:m0, "minus_warn2")
yes(:m0, "minus_warn3")
yes(:m0, "minus_warn4")
yes(:m0, "minus_warn5")

no(:m0, "qmark_no1")
no(:m0, "qmark_no2")
no(:m0, "qmark_no3")
yes(:m0, "qmark_warn1")
yes(:m0, "qmark_warn2")
yes(:m0, "qmark_warn3")

no(:m0, "wire_no1")
no(:m0, "wire_no2")
no(:m0, "wire_no3")
no(:m0, "wire_no4")

yes(:m0, "subinst1")
no(:m0, "subinst2")
no(:m0, "subinst3")

test_passed()
