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

outlaw_bad_warnings()

# BOZO whaaat is going on here??
# outlaw_warning_global("VL-PROGRAMMING-ERROR")

def unset(modname, wirename, var=1)
  # It's okay for it to be unset and unused, because some bits may be unset
  # while other bits may be unused.  However, nothing should ever be marked
  # as both unset and spurious.
  match_warning(modname, var ? "VL-LUCID-UNSET-VARIABLE" : "VL-LUCID-UNSET", wirename)
  # outlaw_warning(modname, var ? "VL-LUCID-UNSET" : "VL-LUCID-UNSET-VARIABLE", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS-VARIABLE", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
end

def unused(modname, wirename, var=1)
  # It's okay for it to be unset and unused, because some bits may be unset
  # while other bits may be unused.  However, nothing should ever be marked as
  # both unused and spurious.
  match_warning(modname, var ? "VL-LUCID-UNUSED-VARIABLE" : "VL-LUCID-UNUSED", wirename)
  # outlaw_warning(modname, var ? "VL-LUCID-UNUSED" : "VL-LUCID-UNUSED-VARIABLE", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS-VARIABLE", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
end

def spurious(modname, wirename, var=1)
  match_warning(modname, var ? "VL-LUCID-SPURIOUS-VARIABLE" : "VL-LUCID-SPURIOUS", wirename)
  # outlaw_warning(modname, var ? "VL-LUCID-SPURIOUS" : "VL-LUCID-SPURIOUS-VARIABLE", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET-VARIABLE", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED-VARIABLE", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
end

def normal(modname, wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED", wirename)
  outlaw_warning(modname, "VL-LUCID-SPURIOUS-VARIABLE", wirename)
  outlaw_warning(modname, "VL-LUCID-UNSET-VARIABLE", wirename)
  outlaw_warning(modname, "VL-LUCID-UNUSED-VARIABLE", wirename)
  outlaw_warning(modname, "VL-WARN-UNDECLARED", wirename)
end

# We no longer expect to support top-level unset parameters
#spurious(:"Design Root", "top_spurious ")
#unset(:"Design Root", "top_unset ")


normal(:"Design Root", "top_normal ")
unused(:"Design Root", "top_unused ", false)


normal(:m0, "w1_normal ")
spurious(:m0, "w1_spurious ")
unset(:m0, "w1_unset ")
unused(:m0, "w1_unused ")

unused(:"Design Root", "Type top_unused_t ", false)
normal(:"Design Root", "Type top_used_t ")

unused(:"Design Root", "Function top_f_unused ", false)
normal(:"Design Root", "Function top_f_used ")
normal(:"Design Root", "Function top_f_dpiexported ")
unused(:"Design Root", "top_f_dpiimported_unused ", false)
normal(:"Design Root", "top_f_dpiimported_normal ")

normal(:m1, "myout ")
unused(:m1, "temp ")


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
unused(:"Design Root", "Type instruction_t ", false)

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
unused(:pkg1, "Function pfn_unused ", false)

normal(:m4, "u1 ")
normal(:m4, "u2 ")


unused(:"Design Root", "Function noreturn ", false)
unused(:"Design Root", "nr_unused ")
unset(:"Design Root", "noreturn ")
# this doesn't work yet
# normal(:"Design Root", "noreturn2 ")

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
spurious(:m9, "mr_spurious ", false)


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
unused(:ImPort, "client ", false)
normal(:ImPort, "server ")

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

normal(:mg1, "p1_used ")
unused(:mg1, "w1_normal ")

normal(:mg2, "genvar1")
spurious(:mg2, "genvar2", false)


unset(:useprim, "w1_unset ")
unused(:useprim, "w1_unused ")
spurious(:useprim, "w1_spurious ")

unused(:trickyscope, "counter_unused ")
normal(:trickyscope, "loopvar1")
unset(:trickyscope, "loopvar2")
unused(:trickyscope, "loopvar3")
spurious(:trickyscope, "loopvar4")


unset(:minuscolon, "normal2")
unused(:minuscolon, "normal1")


normal(:"Design Root", "Type instruction2_t ")
unused(:pattern, "myinst")
normal(:pattern, "opcode")
normal(:pattern, "arg1")
normal(:pattern, "arg2")

normal(:tricky_init, "w1_normal ")
normal(:tricky_init, "w2_normal ")
unused(:tricky_init, "w3_unused ")
unset(:tricky_init, "w4_unset ")
spurious(:tricky_init, "w5_spurious ")


spurious(:fancy_mp, "foo")
normal(:fancy_mp, "mp1")
normal(:fancy_mp, "mp2")
normal(:fancy_mp, "mp3")
unused(:fancy_mp, "mp4", false)


spurious(:'fancy_mp_param$width=5', "foo")
normal(:'fancy_mp_param$width=5', "mp1")
normal(:'fancy_mp_param$width=5', "mp2")
normal(:'fancy_mp_param$width=5', "mp3")
unused(:'fancy_mp_param$width=5', "mp4", false)


normal(:fcasttest_package, "yes_usedfun1")
normal(:fcasttest_package, "yes_usedfun2")
unused(:fcasttest_package, "not_usedfun", false)

normal(:fcasttest, "yes_usedfun1")
normal(:fcasttest, "yes_usedfun2")


spurious(:gen3, "Variable aa ")
unused(:gen3, "Variable bb ")

unset(:cosim_gen7, "Variable aa1_unset")
unused(:cosim_gen7, "Variable aa1_unused")
spurious(:cosim_gen7, "Variable bb1_spurious")
spurious(:cosim_gen7, "Variable aa1_spurious")
unused(:cosim_gen7, "Variable cc1_unused")
unused(:cosim_gen7, "Variable bb1_unused")
normal(:cosim_gen7, "version")
normal(:cosim_gen7, "mode")

# Currently this fails.  It's correctly handled in the second pass of lucid,
# but incorrectly handled by the first pass because the scoping is too hard: we
# the assignment to aa1_unused is the only place where bb1_unset is used, and
# when we try to look up "foo" there, it's not in the scopestack because it's
# hidden under these transparent IFs that haven't been expanded away yet.  We
# might be able to avoid this by working much harder to do the scope lookups
# and marking all possible candidates that we find.

#unset(:cosim_gen7, "Variable bb1_unset")



test_passed()
