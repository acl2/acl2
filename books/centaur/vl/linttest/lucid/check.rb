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

outlaw_bad_warnings()

# BOZO whaaat is going on here??
# outlaw_warning_global("VL-PROGRAMMING-ERROR")

def unset(modname, wirename)
  # It's okay for it to be unset and unused, because some bits may be unset
  # while other bits may be unused.  However, nothing should ever be marked
  # as both unset and spurious.
  match_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
end

def unused(modname, wirename)
  # It's okay for it to be unset and unused, because some bits may be unset
  # while other bits may be unused.  However, nothing should ever be marked as
  # both unused and spurious.
  match_warning(modname, "VL-LUCID-UNUSED", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
end

def spurious(modname, wirename)
  match_warning(modname, "VL-LUCID-SPURIOUS", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED", wirename)
end

def normal(modname, wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED", wirename)
end

# We no longer expect to support top-level unset parameters
#spurious(:"Design Root", "top_spurious ")
#unset(:"Design Root", "top_unset ")


normal(:"Design Root", "top_normal ")
unused(:"Design Root", "top_unused ")


normal(:m0, "w1_normal ")
spurious(:m0, "w1_spurious ")
unset(:m0, "w1_unset ")
unused(:m0, "w1_unused ")

unused(:"Design Root", "Type top_unused_t ")
normal(:"Design Root", "Type top_used_t ")

unused(:"Design Root", "Function top_f_unused ")
normal(:"Design Root", "Function top_f_used ")

normal(:m1, "myout ")

normal(:m2, "l1_normal ")
spurious(:m2, "l1_spurious ")
unset(:m2, "l1_unset ")
unused(:m2, "l1_unused ")


normal(:m3, "delay ")
unset(:m3, "clk ")
spurious(:m3, "r1_spurious ")
unset(:m3, "r1_unset ")
normal(:m3, "r1_normal ")
unused(:m3, "r1_unused ")

normal(:"Design Root", "Type opcode_t ")
unused(:"Design Root", "Type instruction_t ")

normal(:pkg1, "p1_normal ")
unset(:pkg1, "p1_unset ")
unused(:pkg1, "p1_unused ")
spurious(:pkg1, "p1_spurious ")

unset(:pkg1, "pr1_unset ")
unset(:pkg1, "pr2_unset ")
unused(:pkg1, "pr1_unused ")
unused(:pkg1, "pr2_unused ")
normal(:pkg1, "pr1_normal ")
normal(:pkg1, "pr2_normal ")

normal(:pkg1, "Function pfn_used ")
unused(:pkg1, "Function pfn_unused ")

normal(:m4, "u1 ")
normal(:m4, "u2 ")


unused(:"Design Root", "Function noreturn ")
unused(:"Design Root", "nr_unused ")
unset(:"Design Root", "noreturn ")

normal(:m5, "width ")
unused(:m5, "m5_unused ")
unset(:m5, "m5_unset ")

unset(:m5, "doublebad ")
unused(:m5, "doublebad ")

normal(:m6, "width ")
normal(:m6, "xout ")
normal(:m6, "xin ")

unset(:m6, "foo ")

unused(:m7, "unused1 ")
unused(:m7, "unused2 ")
unused(:m7, "unused3 ")
unset(:m7, "unset1 ")
unset(:m7, "unset2 ")
unset(:m7, "unset3 ")

normal(:m8sub, "outtrans ");
normal(:m8sub, "intrans ");

normal(:m8, "normal_trans ")
unset(:m8, "unset_trans ")
unused(:m8, "unused_trans ")
spurious(:m8, "spurious_trans ")
unused(:m8, "xx0 ")
unused(:m8, "xx1 ")
unused(:m8, "subout ");
unset(:m8, "subin ");


normal(:MemReq, "w1_normal ")
unset(:MemReq, "w1_unset ")
unused(:MemReq, "w1_unused ")
unset(:MemReq, "w1_partial_unset ")
unused(:MemReq, "w1_partial_unused ")
spurious(:MemReq, "w1_spurious")

normal(:m9write, "foo ")
normal(:m9read, "foo ")
unused(:m9read, "blah ")

normal(:m9writewrap, "foo ")
normal(:m9readwrap, "foo ")

normal(:m9, "mr_used1 ")
normal(:m9, "mr_used2 ")
spurious(:m9, "mr_spurious ")


spurious(:mh1, "w1_spurious ")
normal(:mh1, "w1_normal ")
unused(:mh1, "w1_unused ")
unset(:mh1, "w1_unset ")

normal(:idx1, "normal1 ")
normal(:idx1, "normal2 ")
normal(:idx1, "normal3 ")
normal(:idx1, "a1 ")
normal(:idx1, "a2 ")

unused(:idx1, "unused1 ")
unused(:idx1, "unused2 ")
unused(:idx1, "unused3 ")


spurious(:dsInterface, "dsi_spurious")
normal(:dsInterface, "dsi_normal")
unused(:dsInterface, "dsi_unused")
unset(:dsInterface, "dsi_unset")

normal(:dotstar, "out1 ")
normal(:dotstar, "out2 ")
normal(:dotstar, "in1 ")
normal(:dotstar, "in2 ")
normal(:dotstar, "dsi ")

unused(:dotstarwrap, "out1 ")
unused(:dotstarwrap, "out2 ")
unset(:dotstarwrap, "in1 ")
unset(:dotstarwrap, "in2 ")
normal(:dotstar, "dsi ")


spurious(:ImPort, "dataSpurious ")
spurious(:ImPort, "reqMain ")
unused(:ImPort, "dataVld ")
unused(:ImPort, "dataMain ")
unset(:ImPort, "reqVld ")

normal(:imserve, "w1_normal ")
spurious(:imserve, "w1_spurious ")
unset(:imserve, "w1_unset ")
unused(:imserve, "w1_unused ")
normal(:imserve, "foo ")
normal(:imserve, "bar ")

normal(:imservewrap, "foo ")
normal(:imservewrap, "bar ")
normal(:imservewrap, "port1 ")
normal(:imservewrap, "port2 ")

unset(:imsim, "foo ")
unused(:imsim, "bar ")
normal(:imsim, "port1 ")
normal(:imsim, "port2 ")

# I know these don't work yet
#normal(:mg1, "p1_used ")
#normal(:mg1, "w1_normal ")

unset(:useprim, "w1_unset ")
unused(:useprim, "w1_unused ")
spurious(:useprim, "w1_spurious ")

unused(:trickyscope, "counter_unused ")

unset(:minuscolon, "normal2")
unused(:minuscolon, "normal1")

test_passed()
