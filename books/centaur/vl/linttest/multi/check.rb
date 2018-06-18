#!/usr/bin/env ruby

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

require 'require_relative' if RUBY_VERSION =~ /1\.8/
require_relative '../utils'

# Don't outlaw bad warnings because the "buggy" module has parse errors.

def multi(modname, wirename)
  match_warning(modname, "VL-LUCID-MULTIDRIVE", wirename)
end

def normal(modname, wirename)
  outlaw_warning(modname, "VL-LUCID-MULTIDRIVE", wirename)
end

normal(:m0, "clk");
normal(:m0, "normal_a1")
normal(:m0, "normal_a2")
normal(:m0, "normal_a3")
normal(:m0, "normal_a4")
multi(:m0, "multi_a1")
multi(:m0, "multi_a2")
multi(:m0, "multi_a3")
multi(:m0, "multi_a4")

normal(:m0, "normal_i1")
multi(:m0, "multi_i1")

normal(:m1, "normal_a1")
normal(:m1, "normal_a2")
normal(:m1, "normal_a3")
normal(:m1, "normal_a4")
normal(:m1, "normal_a5")
normal(:m1, "normal_a6")
normal(:m1, "normal_a7")
normal(:m1, "normal_a8")
normal(:m1, "normal_a9")
normal(:m1, "normal_a10")
multi(:m1, "multi_a1")
multi(:m1, "multi_a2")
multi(:m1, "multi_a3")

multi(:m2, "multi_a1")
normal(:m2, "normal_a1")
normal(:m2, "normal_a2")
normal(:m2, "normal_a3")
normal(:m2, "normal_b1")
normal(:m2, "normal_b2")
normal(:m2, "normal_b3")

normal(:m3, "normal_f1")
normal(:m3, "normal_f2")

# It's not yet smart enough to get this one:
# multi(:m3, "multi_f1")
# multi(:m3, "multi_f2")

normal(:m4, "normal_a1")
normal(:m4, "normal_a2")
multi(:m4, "multi_a1")
multi(:m4, "multi_a2")
multi(:m4, "multi_a3")
multi(:m4, "multi_a4")

multi(:m5, "multi_a0")
normal(:m5, "normal_p1")
normal(:m5, "normal_p2")
normal(:Protocol, "req")
normal(:Protocol, "ack")
normal(:Protocol, "dat")


# It's not smart enough for this.
# multi(:m5, "multi_p1")


normal(:m6, "normal_a1")

# We probably aren't going to try to be smart enough to figure this out:
# multi(:m6, "multi_a1")

multi(:m7, "multi_a1")
normal(:m7, "normal_a1")
normal(:m7, "normal_a2")
normal(:m7, "normal_a3")
normal(:m7, "normal_a4")
normal(:m7, "normal_a5")
normal(:m7, "normal_a6")
normal(:m7, "normal_a7")
normal(:m7, "normal_a8")


multi(:m8, "multi_a1")
normal(:m8, "normal_a1")


multi(:m9, "multi_a1")
normal(:m9, "normal_i1")
normal(:m9, "normal_i2")
normal(:m9, "normal_o1a")
normal(:m9, "normal_o2a")
normal(:m9, "normal_o3a")
normal(:m9, "normal_o1b")
normal(:m9, "normal_o2b")
normal(:m9, "normal_o3b")

multi(:m10, "multi_a1")
normal(:m10, "normal_r1")

multi(:m11, "multi_a1")
normal(:m11, "clk")

normal(:m12, "normal1")
normal(:m12, "normal2")

normal(:m13, "nowarn_w1")
normal(:m13, "nowarn_w2")
normal(:m13, "nowarn_w3")

test_passed()
