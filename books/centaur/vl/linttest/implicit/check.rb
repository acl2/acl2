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

require_relative '../utils'

outlaw_warning_global("VL-PARSE-ERROR")
outlaw_warning_global("VL-PARSE-FAILED")

def normal(modname, wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
end

def unused(modname, wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  match_warning(modname, "VL-LUCID-UNUSED", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
end

def unset(modname, wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  match_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
end

def spurious(modname, wirename)
  match_warning(modname, "VL-LUCID-SPURIOUS", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
end

def undeclared(modname, wirename)
  match_warning(modname, "VL-WARN-UNDECLARED", wirename)
end


normal(:sub, "out")
normal(:sub, "in")

normal(:m0, "w1_declared")

unused(:m0, "g1_implicit")
unset(:m0, "g2_implicit")
unset(:m0, "g3_implicit")
unset(:m0, "g4_implicit")
unset(:m0, "g5_implicit")
unused(:m0, "g6_implicit")
unused(:m0, "g7_implicit")
unused(:"Design Root", "top_g1")
unset(:m0, "g8_implicit")

unset(:m0, "m1_implicit")
unused(:m0, "m2_implicit")
unused(:m0, "m3_implicit")
unset(:m0, "m4_implicit")
unset(:m0, "m5_implicit")
unset(:m0, "m5_implicit")
unused(:"Design Root", "top_m1")
unset(:m0, "m6_implicit")
unset(:m0, "m7_implicit")
unset(:m0, "m8_implicit")

unused(:m0, "a1_implicit")
unused(:m0, "a2_implicit")
unused(:m0, "a3_implicit")
unused(:"Design Root", "top_a1")
undeclared(:m0, "a4_undeclared")
normal(:m0, "a5_implicit")  # BOZO maybe check for selfassign

spurious(:m0, "al_implicit1")
spurious(:m0, "al_implicit2")
spurious(:m0, "al_implicit3")
unused(:m0, "al_implicit4")
spurious(:m0, "al_implicit5")
spurious(:m0, "al_implicit6")
unset(:m0, "al_implicit7")


undeclared(:m1, "w1_undeclared")
undeclared(:m1, "w2_undeclared")
undeclared(:m1, "w3_undeclared")



test_passed()
