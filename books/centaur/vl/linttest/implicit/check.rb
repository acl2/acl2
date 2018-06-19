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

outlaw_warning_global("VL-PARSE-ERROR")
outlaw_warning_global("VL-PARSE-FAILED")

def normal(modname, wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
end

def unused(modname, wirename)
  match_warning(modname, "VL-LUCID-UNUSED", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET", wirename)
end

def unset(modname, wirename)
  match_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
end

def spurious(modname, wirename)
  match_warning(modname, "VL-LUCID-SPURIOUS", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED", wirename)
end

def undeclared(modname, wirename)
  match_warning(modname, "VL-WARN-UNDECLARED", wirename)
end


normal(:sub, "out")
normal(:sub, "in")

## BOZO fixing this will be harder.
## undeclared(:"Design Root", "undeclared_param1");
unused(:"Design Root", "unused_param2");

unused(:"Design Root", "derived_param1");
unused(:"Design Root", "derived_param2");


normal(:m0, "w1_declared")

unused(:m0, "a1_implicit")
unused(:m0, "a2_implicit")
unused(:m0, "a3_implicit")
unused(:"Design Root", "top_a1")
undeclared(:m0, "a4_undeclared")
normal(:m0, "a5_implicit")  # BOZO maybe check for selfassign
normal(:m0, "a6_implicit")
normal(:m0, "a7_implicit")
undeclared(:m0, "a8_undeclared")
normal(:m0, "a9_implicit")  # looks both set and used (as an index) by the assignment
undeclared(:m0, "a10_undeclared")


unused(:m0, "g1_implicit")
unset(:m0, "g2_implicit")
unset(:m0, "g3_implicit")
unset(:m0, "g4_implicit")
unset(:m0, "g5_implicit")
unused(:m0, "g6_implicit")
unused(:m0, "g7_implicit")
unused(:"Design Root", "top_g1")
unset(:m0, "g8_implicit")
unset(:m0, "g9_implicit")
unset(:m0, "g10_implicit")
unset(:m0, "g11_implicit")
unset(:m0, "g12_implicit")
unset(:m0, "g13_implicit")
unset(:m0, "g14_implicit")
unset(:m0, "g15_implicit")
undeclared(:m0, "g16_undeclared")
undeclared(:m0, "g17_undeclared")

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

unset(:m1, "w4_unset")
unused(:m1, "w5_unused")
outlaw_warning(:m1, "VL-WARN-UNDECLARED", "triple_t")

undeclared(:m1, "undeclared_t")

unused(:m1, "w6_unused")
unused(:m1, "w7_unused")
outlaw_warning(:m1, "VL-WARN-UNDECLARED", "pkg1_decl1")
outlaw_warning(:m1, "VL-WARN-UNDECLARED", "pkg1_decl2")

normal(:pkg1, "pkg1_decl1")
normal(:pkg1, "pkg1_decl2")

undeclared(:m2, "subname_in1")

## These warnings are different only because they're checked later in
## argresolve instead of earlier in make-implicit
match_warning(:m3, "VL-BAD-INSTANCE", "subname_in1")
match_warning(:m3, "VL-BAD-INSTANCE", "subname_out1")

unset(:m4, "subname_in1")
unused(:m4, "subname_out1")

unset(:m5, "subname_in1")
unused(:m5, "subname_out1")

normal(:m6, "messy_out")
normal(:m6, "messy_in")

normal(:m7, "messy_out")
normal(:m7, "messy_in")

undeclared(:m9, "m9type_t")
undeclared(:m10, "m10type_t")
undeclared(:m11, "m11type_t")

normal(:m12, " m12type_t")
unused(:m12, "in")

normal(:m13, " m13type_t")
unused(:m13, "in")

normal(:m14, "fun1type_t")
undeclared(:m14, "fun2type_t")
undeclared(:m14, "fun3width")
normal(:m14, "fun4width")
undeclared(:m14, "fun5width")
normal(:m14, "fun6")

normal(:m14, "task1type_t")
undeclared(:m14, "task2type_t")
undeclared(:m14, "task3width")
normal(:m14, "task4type_t")
undeclared(:m14, "task5type_t")



normal(:i1, "w1_declared")

unused(:i1, "a1_implicit")
unused(:i1, "a2_implicit")
unused(:i1, "a3_implicit")
undeclared(:i1, "a4_undeclared")
normal(:i1, "a5_implicit")  # BOZO maybe check for selfassign
normal(:i1, "a6_implicit")
normal(:i1, "a7_implicit")



test_passed()
