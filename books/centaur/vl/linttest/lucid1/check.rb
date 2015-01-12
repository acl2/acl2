# VL Verilog Toolkit
# Copyright (C) 2008-2014 Centaur Technology
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

def unset(modname, wirename)
  match_warning(modname, "VL-LUCID-UNSET", wirename)
end

def unused(modname, wirename)
  match_warning(modname, "VL-LUCID-UNUSED", wirename)
end

def spurious(modname, wirename)
  match_warning(modname, "VL-LUCID-SPURIOUS", wirename)
end

def normal(modname, wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED", wirename)
end

normal(:"Design Root", "of top_normal")
spurious(:"Design Root", "of top_spurious")
unset(:"Design Root", "of top_unset")
unused(:"Design Root", "of top_unused")


normal(:m0, "of w1_normal")
spurious(:m0, "of w1_spurious")
unset(:m0, "of w1_unset")
unused(:m0, "of w1_unused")

unused(:"Design Root", "of top_unused_t")
normal(:"Design Root", "of top_used_t")

unused(:"Design Root", "unction top_f_unused")
normal(:"Design Root", "unction top_f_used")

normal(:m1, "myout")


normal(:m2, "of l1_normal")
spurious(:m2, "of l1_spurious")
unset(:m2, "of l1_unset")
unused(:m2, "of l1_unused")


normal(:m3, "of delay")
unset(:m3, "of clk")
spurious(:m3, "of r1_spurious")
unset(:m3, "of r1_unset")
normal(:m3, "of r1_normal")
unused(:m3, "of r1_unused")

normal(:"Design Root", "of opcode_t")
unused(:"Design Root", "of instruction_t")


normal(:pkg1, "of p1_normal")
unset(:pkg1, "of p1_unset")
unused(:pkg1, "of p1_unused")
spurious(:pkg1, "of p1_spurious")

unset(:pkg1, "of pr1_unset")
unset(:pkg1, "of pr2_unset")
unused(:pkg1, "of pr1_unused")
unused(:pkg1, "of pr2_unused")
normal(:pkg1, "of pr1_normal")
normal(:pkg1, "of pr2_normal")

normal(:pkg1, "unction pfn_used")
unused(:pkg1, "unction pfn_unused")

normal(:m4, "u1")
normal(:m4, "u2")


unused(:"Design Root", "unction noreturn")
unused(:"Design Root", "nr_unused")
unset(:"Design Root", "noreturn")

normal(:m5, "of width")
unused(:m5, "of m5_unused")
unset(:m5, "of m5_unset")

unset(:m5, "of doublebad")
unused(:m5, "of doublebad")

normal(:m6, "of width")
normal(:m6, "of xout")
normal(:m6, "of xin")

unset(:m6, "foo")

unused(:m7, "of unused1")
unused(:m7, "of unused2")
unused(:m7, "of unused3")
unset(:m7, "of unset1")
unset(:m7, "of unset2")
unset(:m7, "of unset3")

normal(:m8, "of normal_trans")
unset(:m8, "of unset_trans")
unused(:m8, "of unused_trans")
unused(:m8, "of xx0")
unused(:m8, "of xx1")

test_passed()



