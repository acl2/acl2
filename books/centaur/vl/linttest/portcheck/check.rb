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

# BOZO -- consider normalizing vl-bad-port, vl-bad-ports, and vl-port-mismatch
# warnings into a single type.

def badport(modname, wirename)
  match_warning(modname, "VL-BAD-PORT", wirename)
end

def badports(modname, wirename)
  match_warning(modname, "VL-BAD-PORTS", wirename)
end

def mismatch(modname, wirename)
  match_warning(modname, "VL-PORT-MISMATCH", wirename)
end

def badstyle(modname, wirename)
  match_warning(modname, "VL-WARN-PORT-STYLE", wirename)
  outlaw_warning(modname, "VL-BAD-PORT", wirename)
  outlaw_warning(modname, "VL-BAD-PORTS", wirename)
  outlaw_warning(modname, "VL-PORT-MISMATCH", wirename)
end

def normal(modname, wirename)
  outlaw_warning(modname, "VL-BAD-PORT", wirename)
  outlaw_warning(modname, "VL-BAD-PORTS", wirename)
  outlaw_warning(modname, "VL-WARN-PORT-STYLE", wirename)
  outlaw_warning(modname, "VL-PORT-MISMATCH", wirename)
end


normal(:m0, "port1")
normal(:m0, "port2")
normal(:m0, "port3")

normal(:m1, "port1")
normal(:m1, "port2")
normal(:m1, "port3")

normal(:m2, "port1")
normal(:m2, "port2")
normal(:m2, "port3")
badstyle(:m2, "Unnamed port")

normal(:m4, "port1")
badstyle(:m4, "port2")
normal(:m4, "port3")

normal(:m5, "port1")
badstyle(:m5, "port2")
badstyle(:m5, "port3")
normal(:m5, "port4")

normal(:m6, "port1")
normal(:m6, "port2")
normal(:m6, "port3")

badports(:m7, "port1")

normal(:m8, "port1")
mismatch(:m8, "port2")

normal(:m9, "port1")
normal(:m9, "port2")
mismatch(:m9, "port3")

test_passed()
